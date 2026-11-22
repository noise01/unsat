"""Congruence Closure solver for Equality and Uninterpreted Functions (EUF).

Implements:
- Eager-representative Union-Find with union-by-size.
- Copy-free chronological undo trail for incremental ``push``/``pop``.
- ``O(1)`` hash-indexed signature table + use lists for congruence closure.
- Proof forest with smaller-tree edge reversal for minimal conflict/prop reasons.
- Equality/predicate watch lists and finite-domain model construction.

Depends on: ``syntax``, ``model``.
"""

from collections import deque
from collections.abc import Mapping, Sequence
from fractions import Fraction

from unsat.model import FuncInterp, Model, Value
from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl, Sort, SortKind
from unsat.theories.base import EUFStats, TheoryLit

type _Reason = TheoryLit | tuple[int, int]

# Undo opcodes stored on _history when _trail_marks is non-empty.
_OP_NEW_NODE = 0
_OP_NEW_EQ = 1
_OP_REG_BOOL = 2
_OP_USE_POP = 3
_OP_SIG_SET = 4
_OP_SIG_DEL = 5
_OP_CONST_SET = 6
_OP_PROOF_LINK = 7
_OP_UNION = 8
_OP_WATCH_APPEND = 9
_OP_ASSERT_SET = 10

_EUF_CONGRUENCE_KINDS = frozenset(
    {
        DeclKind.UNINTERPRETED,
        DeclKind.SELECT,
        DeclKind.STORE,
        DeclKind.CONST_ARRAY,
    }
)


def _dedup_lits(lits: Sequence[TheoryLit]) -> list[TheoryLit]:
    return list(dict.fromkeys(lits))


class EUFSolver:
    """Incremental Congruence Closure solver for ``QF_UF``."""

    def __init__(self, ctx: Context) -> None:
        self._ctx = ctx
        self._stats = EUFStats()

        self._expr_to_id: dict[Expr, int] = {}
        self._id_to_expr: list[Expr] = []
        self._arg_ids: list[tuple[int, ...]] = []
        self._decl_ids: list[int] = []

        # Union-Find (eager representative at _rep[nid], members/uses at roots).
        self._rep: list[int] = []
        self._class_members: list[list[int]] = []
        self._use_list: list[list[int]] = []
        self._class_const: list[Const | None] = []
        self._class_bool_terms: list[list[int]] = []

        # Congruence Signature Table: (decl.id, rep(arg_0), ...) -> App id.
        self._sig_table: dict[tuple[int, ...], int] = {}

        # Proof Forest: parent pointer (-1 for root) and edge justification.
        self._proof_parent: list[int] = []
        self._proof_reason: list[_Reason | None] = []

        # Equality atoms and two-watch lists indexed by class representative.
        self._eq_atoms: list[tuple[int, int, Expr]] = []
        self._eq_atom_to_idx: dict[Expr, int] = {}
        self._eq_watches: list[list[int]] = []

        # Registered Bool terms (0-arity / predicate apps / Bool args) and assertions.
        self._registered_bools: set[int] = set()
        self._asserted_atoms: dict[Expr, bool] = {}

        # Work queues & current decision-level status.
        self._merge_queue: deque[tuple[int, int, _Reason]] = deque()
        self._pending_diseqs: list[tuple[int, int, Expr]] = []
        self._pending_props: list[tuple[Expr, bool]] = []
        self._pending_prop_set: set[Expr] = set()
        self._conflict: list[TheoryLit] | None = None

        # Copy-free backtracking undo trail.
        self._history: list[tuple[object, ...]] = []
        self._trail_marks: list[tuple[int, list[TheoryLit] | None]] = []

        # Pre-register Boolean singletons so predicate truth values live in UF directly.
        self._true_id = self._ensure_term(ctx.true_expr)
        self._false_id = self._ensure_term(ctx.false_expr)

    @property
    def ctx(self) -> Context:
        """AST context associated with this theory solver."""
        return self._ctx

    @property
    def stats(self) -> EUFStats:
        """Counters tracking EUF merges, congruences, explanations, and conflicts."""
        return self._stats

    @property
    def decision_level(self) -> int:
        """Current incremental backtracking depth."""
        return len(self._trail_marks)

    def push(self) -> None:
        """Push a new backtracking frame onto the undo stack."""
        self._drain()
        self._trail_marks.append((len(self._history), self._conflict))

    def pop(self, num_levels: int = 1) -> None:
        """Pop ``num_levels`` frames and revert all theory state changes."""
        if num_levels < 0:
            msg = f"Cannot pop negative levels: {num_levels}"
            raise ValueError(msg)
        if num_levels == 0:
            return
        if num_levels > len(self._trail_marks):
            msg = (
                f"Cannot pop {num_levels} levels: only {len(self._trail_marks)} active"
            )
            raise ValueError(msg)

        target_len, saved_conflict = self._trail_marks[
            len(self._trail_marks) - num_levels
        ]
        del self._trail_marks[len(self._trail_marks) - num_levels :]

        # Discard any pending work or conflict from the popped levels.
        self._merge_queue.clear()
        self._pending_diseqs.clear()
        self._pending_props.clear()
        self._pending_prop_set.clear()
        self._conflict = saved_conflict

        history = self._history
        while len(history) > target_len:
            entry = history.pop()
            op = entry[0]
            if op == _OP_ASSERT_SET:
                atom = entry[1]
                assert isinstance(atom, Expr)
                del self._asserted_atoms[atom]
            elif op == _OP_WATCH_APPEND:
                _, root, old_len = entry
                assert isinstance(root, int)
                assert isinstance(old_len, int)
                del self._eq_watches[root][old_len:]
            elif op == _OP_UNION:
                _, r_small, r_large, mem_len, bool_len, use_len = entry
                assert isinstance(r_small, int)
                assert isinstance(r_large, int)
                assert isinstance(mem_len, int)
                assert isinstance(bool_len, int)
                assert isinstance(use_len, int)
                for member in self._class_members[r_small]:
                    self._rep[member] = r_small
                del self._class_members[r_large][mem_len:]
                del self._class_bool_terms[r_large][bool_len:]
                del self._use_list[r_large][use_len:]
            elif op == _OP_PROOF_LINK:
                chain = entry[1]
                assert isinstance(chain, tuple)
                for node_id, old_parent, old_reason in chain:
                    self._proof_parent[node_id] = old_parent
                    self._proof_reason[node_id] = old_reason
            elif op == _OP_CONST_SET:
                root = entry[1]
                assert isinstance(root, int)
                self._class_const[root] = None
            elif op == _OP_SIG_DEL:
                _, sig, p_id = entry
                assert isinstance(sig, tuple)
                assert isinstance(p_id, int)
                self._sig_table[sig] = p_id
            elif op == _OP_SIG_SET:
                sig = entry[1]
                assert isinstance(sig, tuple)
                self._sig_table.pop(sig, None)
            elif op == _OP_USE_POP:
                rep_arg = entry[1]
                assert isinstance(rep_arg, int)
                self._use_list[rep_arg].pop()
            elif op == _OP_REG_BOOL:
                _, b_id, root = entry
                assert isinstance(b_id, int)
                assert isinstance(root, int)
                self._registered_bools.remove(b_id)
                self._class_bool_terms[root].pop()
            elif op == _OP_NEW_EQ:
                _, _eq_idx, eq_atom, r_lhs, r_rhs = entry
                assert isinstance(eq_atom, Expr)
                assert isinstance(r_lhs, int)
                assert isinstance(r_rhs, int)
                if r_rhs >= 0:
                    self._eq_watches[r_rhs].pop()
                if r_lhs >= 0:
                    self._eq_watches[r_lhs].pop()
                del self._eq_atom_to_idx[eq_atom]
                self._eq_atoms.pop()
            elif op == _OP_NEW_NODE:
                nid = entry[1]
                assert isinstance(nid, int)
                expr = self._id_to_expr.pop()
                del self._expr_to_id[expr]
                self._arg_ids.pop()
                self._decl_ids.pop()
                self._rep.pop()
                self._class_members.pop()
                self._use_list.pop()
                self._class_const.pop()
                self._class_bool_terms.pop()
                self._proof_parent.pop()
                self._proof_reason.pop()
                self._eq_watches.pop()

    def register_term(self, term: Expr) -> None:
        """Register ``term`` and its uninterpreted subterms with the theory solver."""
        self._check_expr(term)
        self._ensure_term(term)

    def register_eq(self, atom: Expr) -> None:
        """Register a non-Bool equality atom ``lhs = rhs``."""
        self._check_expr(atom)
        if not (isinstance(atom, App) and atom.decl.kind is DeclKind.EQ):
            msg = f"Expected Eq expression, got '{atom}'"
            raise TypeError(msg)
        if atom.args[0].is_bool:
            msg = f"Expected non-Bool Eq in EUF, got Bool equality '{atom}'"
            raise TypeError(msg)
        if atom in self._eq_atom_to_idx:
            return

        lhs_id = self._ensure_term(atom.args[0])
        rhs_id = self._ensure_term(atom.args[1])
        eq_idx = len(self._eq_atoms)
        self._eq_atoms.append((lhs_id, rhs_id, atom))
        self._eq_atom_to_idx[atom] = eq_idx

        r_lhs = self._rep[lhs_id]
        r_rhs = self._rep[rhs_id]
        if r_lhs != r_rhs:
            self._eq_watches[r_lhs].append(eq_idx)
            self._eq_watches[r_rhs].append(eq_idx)
            if self._trail_marks:
                self._history.append((_OP_NEW_EQ, eq_idx, atom, r_lhs, r_rhs))
        else:
            if self._trail_marks:
                self._history.append((_OP_NEW_EQ, eq_idx, atom, -1, -1))
            if atom not in self._asserted_atoms:
                self._enqueue_prop(atom, True)

    def register_bool_term(self, term: Expr) -> None:
        """Register a Bool-sorted term (predicate or Bool arg) for congruence."""
        self._check_expr(term)
        if not term.is_bool:
            msg = f"Expected Bool expression, got sort '{term.sort}'"
            raise TypeError(msg)
        nid = self._ensure_term(term)
        if nid in self._registered_bools:
            return

        root = self._rep[nid]
        self._registered_bools.add(nid)
        self._class_bool_terms[root].append(nid)
        if self._trail_marks:
            self._history.append((_OP_REG_BOOL, nid, root))

        const = self._class_const[root]
        if term in self._asserted_atoms:
            asserted_pol = self._asserted_atoms[term]
            target_id = self._true_id if asserted_pol else self._false_id
            self._merge_queue.append((nid, target_id, TheoryLit(term, asserted_pol)))
        elif const is not None and term not in self._asserted_atoms:
            self._enqueue_prop(term, bool(const.value))

    def assert_atom(self, atom: Expr, polarity: bool) -> None:
        """Assert ``atom`` with truth value ``polarity`` at the current level."""
        self._check_expr(atom)
        if not atom.is_bool:
            msg = f"Asserted theory atom must have Bool sort, got '{atom.sort}'"
            raise TypeError(msg)

        existing = self._asserted_atoms.get(atom)
        if existing is not None:
            if existing == polarity:
                return
            if self._conflict is None:
                self._conflict = [TheoryLit(atom, True), TheoryLit(atom, False)]
                self._stats.conflicts += 1
            return

        if isinstance(atom, App) and atom.decl.kind is DeclKind.EQ:
            if atom.args[0].is_bool:
                msg = f"EUFSolver handles non-Bool Eq atoms only, got '{atom}'"
                raise TypeError(msg)
            self.register_eq(atom)
            lhs_id, rhs_id, _ = self._eq_atoms[self._eq_atom_to_idx[atom]]
            self._asserted_atoms[atom] = polarity
            if self._trail_marks:
                self._history.append((_OP_ASSERT_SET, atom))
            if polarity:
                self._merge_queue.append((lhs_id, rhs_id, TheoryLit(atom, True)))
            else:
                self._pending_diseqs.append((lhs_id, rhs_id, atom))
            eq_term_id = self._expr_to_id.get(atom)
            if eq_term_id is not None and eq_term_id in self._registered_bools:
                target_id = self._true_id if polarity else self._false_id
                self._merge_queue.append(
                    (eq_term_id, target_id, TheoryLit(atom, polarity))
                )
            return

        self.register_bool_term(atom)
        nid = self._expr_to_id[atom]
        self._asserted_atoms[atom] = polarity
        if self._trail_marks:
            self._history.append((_OP_ASSERT_SET, atom))
        target_id = self._true_id if polarity else self._false_id
        self._merge_queue.append((nid, target_id, TheoryLit(atom, polarity)))

    def propagate(
        self,
    ) -> tuple[Sequence[tuple[Expr, bool]], Sequence[TheoryLit] | None]:
        """Drain pending merges/diseqs and return propagations or a conflict."""
        self._drain()
        if self._conflict is not None:
            return (), list(self._conflict)
        if not self._pending_props:
            return (), None
        props = list(self._pending_props)
        self._pending_props.clear()
        self._pending_prop_set.clear()
        return props, None

    def explain_propagation(self, atom: Expr, polarity: bool) -> Sequence[TheoryLit]:
        """Return minimal asserted reasons explaining why ``(atom, polarity)`` holds."""
        self._check_expr(atom)
        if isinstance(atom, App) and atom.decl.kind is DeclKind.EQ:
            if not polarity:
                msg = f"Negative equality propagation explanation unsupported: {atom}"
                raise ValueError(msg)
            eq_idx = self._eq_atom_to_idx.get(atom)
            if eq_idx is None:
                msg = f"Unknown equality atom '{atom}'"
                raise KeyError(msg)
            lhs_id, rhs_id, _ = self._eq_atoms[eq_idx]
            if self._rep[lhs_id] != self._rep[rhs_id]:
                msg = f"Equality '{atom}' does not hold in current EUF state"
                raise ValueError(msg)
            return self._explain_eq(lhs_id, rhs_id)

        nid = self._expr_to_id.get(atom)
        if nid is None:
            msg = f"Unknown Bool term '{atom}'"
            raise KeyError(msg)
        target_id = self._true_id if polarity else self._false_id
        if self._rep[nid] != self._rep[target_id]:
            msg = f"Bool term '{atom}' is not merged with {polarity} in current state"
            raise ValueError(msg)
        return self._explain_eq(nid, target_id)

    def explain_conflict(self) -> Sequence[TheoryLit]:
        """Return asserted ``TheoryLit`` reasons for the current theory conflict."""
        if self._conflict is None:
            return ()
        return list(self._conflict)

    def check(self) -> Sequence[Sequence[TheoryLit]]:
        """Verify global EUF consistency; returns a conflict lemma list if unsat."""
        self._stats.checks += 1
        self._drain()
        if self._conflict is not None:
            return [list(self._conflict)]
        return ()

    def are_equal(self, lhs: Expr, rhs: Expr) -> bool:
        """Return whether two registered expressions are currently congruent."""
        self._check_expr(lhs)
        self._check_expr(rhs)
        self._drain()
        lhs_id = self._expr_to_id.get(lhs)
        rhs_id = self._expr_to_id.get(rhs)
        if lhs_id is None or rhs_id is None:
            return lhs is rhs
        return self._rep[lhs_id] == self._rep[rhs_id]

    def rep_expr(self, term: Expr) -> Expr:
        """Return the canonical representative ``Expr`` of ``term`` in EUF."""
        self._check_expr(term)
        self._drain()
        nid = self._expr_to_id.get(term)
        if nid is None:
            return term
        return self._id_to_expr[self._rep[nid]]

    def explain_terms_equal(self, lhs: Expr, rhs: Expr) -> list[TheoryLit]:
        """Return minimal asserted ``TheoryLit`` reasons why ``lhs == rhs``."""
        self._check_expr(lhs)
        self._check_expr(rhs)
        self._drain()
        lhs_id = self._expr_to_id.get(lhs)
        rhs_id = self._expr_to_id.get(rhs)
        if lhs_id is None or rhs_id is None:
            if lhs is rhs:
                return []
            msg = f"Terms '{lhs}' and '{rhs}' are not registered in EUF"
            raise ValueError(msg)
        if self._rep[lhs_id] != self._rep[rhs_id]:
            msg = f"Terms '{lhs}' and '{rhs}' are not equal in current EUF state"
            raise ValueError(msg)
        return self._explain_eq(lhs_id, rhs_id)

    def eclasses(self) -> list[Expr]:
        """Return the canonical representative ``Expr`` of each current E-class."""
        self._drain()
        return [
            self._id_to_expr[nid]
            for nid in range(len(self._id_to_expr))
            if self._rep[nid] == nid
        ]

    def eclass_members(self, term: Expr) -> tuple[Expr, ...]:
        """Return all registered members in ``term``'s current E-class."""
        self._check_expr(term)
        self._drain()
        nid = self._expr_to_id.get(term)
        if nid is None:
            return (term,)
        root = self._rep[nid]
        return tuple(self._id_to_expr[mid] for mid in self._class_members[root])

    def apps_by_decl(self, decl: FuncDecl) -> list[App]:
        """Return all registered ``App`` terms whose declaration is ``decl``."""
        if decl.ctx is not self._ctx:
            msg = f"FuncDecl '{decl}' belongs to a different Context"
            raise ValueError(msg)
        self._drain()
        return [
            expr
            for expr in self._id_to_expr
            if isinstance(expr, App) and expr.decl is decl
        ]

    def terms_of_sort(self, sort: Sort) -> list[Expr]:
        """Return canonical E-class representatives of sort ``sort``."""
        if sort.ctx is not self._ctx:
            msg = f"Sort '{sort}' belongs to a different Context"
            raise ValueError(msg)
        self._drain()
        return [
            self._id_to_expr[nid]
            for nid in range(len(self._id_to_expr))
            if self._rep[nid] == nid and self._id_to_expr[nid].sort is sort
        ]

    def _assign_root_values(
        self,
        external_values: Mapping[Expr, Expr] | None = None,
    ) -> tuple[dict[int, Expr], dict[Sort, list[Const]]]:
        sort_roots: dict[Sort, list[int]] = {}
        int_roots: list[int] = []
        real_roots: list[int] = []
        bv_roots: dict[Sort, list[int]] = {}
        array_roots: dict[Sort, list[int]] = {}
        for nid, expr in enumerate(self._id_to_expr):
            if self._rep[nid] != nid:
                continue
            kind = expr.sort.kind
            if kind is SortKind.UNINTERPRETED:
                sort_roots.setdefault(expr.sort, []).append(nid)
            elif kind is SortKind.INT:
                int_roots.append(nid)
            elif kind is SortKind.REAL:
                real_roots.append(nid)
            elif kind is SortKind.BITVEC:
                bv_roots.setdefault(expr.sort, []).append(nid)
            elif kind is SortKind.ARRAY:
                array_roots.setdefault(expr.sort, []).append(nid)

        root_val: dict[int, Expr] = {}
        universes: dict[Sort, list[Const]] = {}

        for sort, roots in sort_roots.items():
            used_indices: set[int] = set()
            for r in roots:
                fixed = self._class_const[r]
                if fixed is not None:
                    assert isinstance(fixed.value, int)
                    assert not isinstance(fixed.value, bool)
                    root_val[r] = fixed
                    used_indices.add(fixed.value)
                elif external_values is not None:
                    for member in self._class_members[r]:
                        ext = external_values.get(self._id_to_expr[member])
                        if isinstance(ext, Const) and ext.sort is sort:
                            assert isinstance(ext.value, int)
                            assert not isinstance(ext.value, bool)
                            root_val[r] = ext
                            used_indices.add(ext.value)
                            break

            next_idx = 0
            sort_elems: list[Const] = []
            for r in roots:
                if r in root_val:
                    existing_c = root_val[r]
                    assert isinstance(existing_c, Const)
                    sort_elems.append(existing_c)
                    continue
                while next_idx in used_indices:
                    next_idx += 1
                elem = self._ctx.mk_domain_val(sort, next_idx)
                used_indices.add(next_idx)
                next_idx += 1
                root_val[r] = elem
                sort_elems.append(elem)
            universes[sort] = sort_elems

        used_ints: set[int] = set()
        for r in int_roots:
            fixed = self._class_const[r]
            if fixed is not None:
                assert isinstance(fixed.value, int)
                assert not isinstance(fixed.value, bool)
                root_val[r] = fixed
                used_ints.add(fixed.value)
            elif external_values is not None:
                for member in self._class_members[r]:
                    ext = external_values.get(self._id_to_expr[member])
                    if isinstance(ext, Const) and ext.is_int:
                        assert isinstance(ext.value, int)
                        assert not isinstance(ext.value, bool)
                        root_val[r] = ext
                        used_ints.add(ext.value)
                        break

        next_int = 0
        for r in int_roots:
            if r not in root_val:
                while next_int in used_ints:
                    next_int += 1
                root_val[r] = self._ctx.mk_int_val(next_int)
                used_ints.add(next_int)
                next_int += 1

        used_reals: set[Fraction] = set()
        for r in real_roots:
            fixed = self._class_const[r]
            if fixed is not None:
                assert isinstance(fixed.value, Fraction)
                root_val[r] = fixed
                used_reals.add(fixed.value)
            elif external_values is not None:
                for member in self._class_members[r]:
                    ext = external_values.get(self._id_to_expr[member])
                    if isinstance(ext, Const) and ext.is_real:
                        assert isinstance(ext.value, Fraction)
                        root_val[r] = ext
                        used_reals.add(ext.value)
                        break

        next_real = 0
        for r in real_roots:
            if r not in root_val:
                while Fraction(next_real) in used_reals:
                    next_real += 1
                root_val[r] = self._ctx.mk_real_val(next_real)
                used_reals.add(Fraction(next_real))
                next_real += 1

        for bv_sort, roots in bv_roots.items():
            used_bvs: set[int] = set()
            width = bv_sort.size
            limit = 1 << width
            for r in roots:
                fixed = self._class_const[r]
                if fixed is not None:
                    assert isinstance(fixed.value, int)
                    assert not isinstance(fixed.value, bool)
                    root_val[r] = fixed
                    used_bvs.add(fixed.value)
                elif external_values is not None:
                    for member in self._class_members[r]:
                        ext = external_values.get(self._id_to_expr[member])
                        if isinstance(ext, Const) and ext.sort is bv_sort:
                            assert isinstance(ext.value, int)
                            assert not isinstance(ext.value, bool)
                            root_val[r] = ext
                            used_bvs.add(ext.value)
                            break

            next_bv = 0
            for r in roots:
                if r not in root_val:
                    while next_bv in used_bvs and len(used_bvs) < limit:
                        next_bv = (next_bv + 1) % limit
                    cand = self._ctx.mk_bv_val(next_bv, width)
                    root_val[r] = cand
                    used_bvs.add(next_bv % limit)
                    next_bv = (next_bv + 1) % limit

        # Assign Boolean equivalence classes: fixed true/false or false by default.
        for nid, expr in enumerate(self._id_to_expr):
            if self._rep[nid] == nid and expr.is_bool:
                fixed = self._class_const[nid]
                root_val[nid] = fixed if fixed is not None else self._ctx.mk_false()

        for arr_sort, roots in array_roots.items():
            for offset, r in enumerate(roots):
                if external_values is not None:
                    for member in self._class_members[r]:
                        ext = external_values.get(self._id_to_expr[member])
                        if ext is not None:
                            root_val[r] = ext
                            break
                if r not in root_val:
                    root_val[r] = self._default_expr_for_sort(
                        arr_sort, universes, tag=offset
                    )

        return root_val, universes

    def _default_expr_for_sort(
        self,
        sort: Sort,
        universes: dict[Sort, list[Const]],
        *,
        tag: int = 0,
    ) -> Expr:
        chain: list[Sort] = []
        cur = sort
        while cur.kind is SortKind.ARRAY:
            chain.append(cur.index_sort)
            cur = cur.element_sort

        if cur.kind is SortKind.BOOL:
            elem: Expr = self._ctx.mk_true() if (tag % 2 == 1) else self._ctx.mk_false()
        elif cur.kind is SortKind.INT:
            elem = self._ctx.mk_int_val(tag)
        elif cur.kind is SortKind.REAL:
            elem = self._ctx.mk_real_val(tag)
        elif cur.kind is SortKind.BITVEC:
            elem = self._ctx.mk_bv_val(tag, cur.size)
        else:
            sort_univ = universes.setdefault(cur, [])
            if tag < len(sort_univ):
                elem = sort_univ[tag]
            else:
                elem = self._ctx.mk_domain_val(cur, tag)
                if elem not in sort_univ:
                    sort_univ.append(elem)

        for idx_sort in reversed(chain):
            elem = self._ctx.mk_const_array(idx_sort, elem)
        return elem

    def resolve_scalar_values(
        self, external_values: Mapping[Expr, Expr] | None = None
    ) -> dict[Expr, Expr]:
        """Return concrete ``Const`` values for registered non-Array terms."""
        self._drain()
        if self._conflict is not None:
            msg = "Cannot resolve EUF values in a conflicted state"
            raise ValueError(msg)
        root_val, _ = self._assign_root_values(external_values)
        out: dict[Expr, Expr] = {}
        for nid, expr in enumerate(self._id_to_expr):
            if expr.is_array:
                continue
            r = self._rep[nid]
            val = root_val.get(r)
            if val is not None:
                out[expr] = val
        return out

    def build_model(
        self,
        external_values: Mapping[Expr, Expr] | None = None,
    ) -> Model:
        """Construct a model realizing all current EUF equivalences."""
        self._drain()
        if self._conflict is not None:
            msg = "Cannot build an EUF model in a conflicted state"
            raise ValueError(msg)

        root_val, universes = self._assign_root_values(external_values)

        values: dict[FuncDecl, Value] = {}
        func_tables: dict[FuncDecl, dict[tuple[Expr, ...], Expr]] = {}

        for nid, expr in enumerate(self._id_to_expr):
            if not isinstance(expr, App) or not expr.decl.is_uninterpreted:
                continue
            r = self._rep[nid]
            val = root_val[r]
            if expr.is_const_symbol:
                if expr.is_bool:
                    assert isinstance(val, Const)
                    values[expr.decl] = bool(val.value)
                elif expr.is_int:
                    assert isinstance(val, Const)
                    assert isinstance(val.value, int)
                    assert not isinstance(val.value, bool)
                    values[expr.decl] = val.value
                elif expr.is_real:
                    assert isinstance(val, Const)
                    assert isinstance(val.value, Fraction)
                    values[expr.decl] = val.value
                elif expr.is_bv:
                    assert isinstance(val, Const)
                    assert isinstance(val.value, int)
                    assert not isinstance(val.value, bool)
                    values[expr.decl] = val.value
                else:
                    values[expr.decl] = val
                continue

            table = func_tables.setdefault(expr.decl, {})
            arg_vals = tuple(root_val[self._rep[aid]] for aid in self._arg_ids[nid])
            table[arg_vals] = val

        functions: dict[FuncDecl, FuncInterp] = {}
        for decl, table in func_tables.items():
            else_val = self._default_expr_for_sort(decl.range_sort, universes)
            functions[decl] = FuncInterp(decl, table, else_val)

        return Model(self._ctx, values, functions=functions, universes=universes)

    # ------------------------------------------------------------------
    # Internal node registration, union-find, signature table & explain
    # ------------------------------------------------------------------

    def _check_expr(self, expr: Expr) -> None:
        if expr.ctx is not self._ctx:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)

    def _ensure_term(self, expr: Expr) -> int:
        existing = self._expr_to_id.get(expr)
        if existing is not None:
            return existing

        stack: list[tuple[Expr, bool]] = [(expr, False)]
        while stack:
            node, expanded = stack.pop()
            if node in self._expr_to_id:
                continue
            if (
                not expanded
                and isinstance(node, App)
                and node.decl.kind in _EUF_CONGRUENCE_KINDS
                and node.args
            ):
                stack.append((node, True))
                for arg in reversed(node.args):
                    if arg not in self._expr_to_id:
                        stack.append((arg, False))
                continue
            self._alloc_node(node)
        return self._expr_to_id[expr]

    def _alloc_node(self, expr: Expr) -> int:
        nid = len(self._id_to_expr)
        self._expr_to_id[expr] = nid
        self._id_to_expr.append(expr)
        self._rep.append(nid)
        self._class_members.append([nid])
        self._use_list.append([])
        self._class_const.append(expr if isinstance(expr, Const) else None)
        self._class_bool_terms.append([])
        self._proof_parent.append(-1)
        self._proof_reason.append(None)
        self._eq_watches.append([])

        is_uapp = (
            isinstance(expr, App)
            and expr.decl.kind in _EUF_CONGRUENCE_KINDS
            and bool(expr.args)
        )
        if is_uapp:
            assert isinstance(expr, App)
            arg_ids = tuple(self._expr_to_id[arg] for arg in expr.args)
            decl_id = expr.decl.id
        else:
            arg_ids = ()
            decl_id = -1
        self._arg_ids.append(arg_ids)
        self._decl_ids.append(decl_id)

        if self._trail_marks:
            self._history.append((_OP_NEW_NODE, nid))

        if is_uapp:
            seen_arg_reps: set[int] = set()
            for arg_id in arg_ids:
                rep_arg = self._rep[arg_id]
                if rep_arg not in seen_arg_reps:
                    seen_arg_reps.add(rep_arg)
                    self._use_list[rep_arg].append(nid)
                    if self._trail_marks:
                        self._history.append((_OP_USE_POP, rep_arg))

            sig = self._compute_sig(nid)
            existing = self._sig_table.get(sig)
            if existing is None:
                self._sig_set(sig, nid)
            elif self._rep[nid] != self._rep[existing]:
                self._merge_queue.append((nid, existing, (nid, existing)))
                self._stats.congruences += 1

        return nid

    def _compute_sig(self, nid: int) -> tuple[int, ...]:
        rep = self._rep
        return (self._decl_ids[nid], *(rep[aid] for aid in self._arg_ids[nid]))

    def _sig_set(self, sig: tuple[int, ...], nid: int) -> None:
        self._sig_table[sig] = nid
        if self._trail_marks:
            self._history.append((_OP_SIG_SET, sig))

    def _sig_del(self, sig: tuple[int, ...], prev_nid: int) -> None:
        del self._sig_table[sig]
        if self._trail_marks:
            self._history.append((_OP_SIG_DEL, sig, prev_nid))

    def _enqueue_prop(self, atom: Expr, polarity: bool) -> None:
        if atom in self._asserted_atoms or atom in self._pending_prop_set:
            return
        self._pending_prop_set.add(atom)
        self._pending_props.append((atom, polarity))
        self._stats.propagations += 1

    def _drain(self) -> None:
        if self._conflict is not None:
            return

        while self._merge_queue:
            u, v, reason = self._merge_queue.popleft()
            if not self._union(u, v, reason):
                return

        if not self._pending_diseqs:
            return

        for lhs_id, rhs_id, eq_expr in self._pending_diseqs:
            if self._rep[lhs_id] == self._rep[rhs_id]:
                conflict = [
                    *self._explain_eq(lhs_id, rhs_id),
                    TheoryLit(eq_expr, False),
                ]
                self._conflict = _dedup_lits(conflict)
                self._stats.conflicts += 1
                self._pending_diseqs.clear()
                return
        self._pending_diseqs.clear()

    def _union(self, u: int, v: int, reason: _Reason) -> bool:
        r_u = self._rep[u]
        r_v = self._rep[v]
        if r_u == r_v:
            return True

        if len(self._class_members[r_u]) <= len(self._class_members[r_v]):
            r_small, u_side = r_u, u
            r_large, v_side = r_v, v
        else:
            r_small, u_side = r_v, v
            r_large, v_side = r_u, u

        c_small = self._class_const[r_small]
        c_large = self._class_const[r_large]
        if c_small is not None and c_large is not None and c_small is not c_large:
            c_small_id = self._expr_to_id[c_small]
            c_large_id = self._expr_to_id[c_large]
            conflict = (
                self._explain_eq(u_side, c_small_id)
                + self._explain_eq(v_side, c_large_id)
                + self._explain_reason(reason)
            )
            self._conflict = _dedup_lits(conflict)
            self._stats.conflicts += 1
            return False

        self._stats.merges += 1

        if c_large is None and c_small is not None:
            self._class_const[r_large] = c_small
            if self._trail_marks:
                self._history.append((_OP_CONST_SET, r_large))

        # Step 1: Delete current signatures of affected parents before changing _rep.
        parents: list[int] = []
        seen_parents: set[int] = set()
        for p in self._use_list[r_small]:
            if p not in seen_parents:
                seen_parents.add(p)
                parents.append(p)
                old_sig = self._compute_sig(p)
                if self._sig_table.get(old_sig) == p:
                    self._sig_del(old_sig, p)

        # Step 2: Re-root smaller Proof Forest tree at u_side and link to v_side.
        self._link_proof(u_side, v_side, reason)

        # Step 3: Merge E-class members, Bool terms, and use-lists into r_large.
        mem_len = len(self._class_members[r_large])
        bool_len = len(self._class_bool_terms[r_large])
        use_len = len(self._use_list[r_large])
        if self._trail_marks:
            self._history.append(
                (_OP_UNION, r_small, r_large, mem_len, bool_len, use_len)
            )

        for member in self._class_members[r_small]:
            self._rep[member] = r_large
        self._class_members[r_large].extend(self._class_members[r_small])
        self._class_bool_terms[r_large].extend(self._class_bool_terms[r_small])
        self._use_list[r_large].extend(self._use_list[r_small])

        # Step 4: Propagate Boolean constant value to newly unified Bool terms.
        if c_large is None and c_small is not None:
            bval = bool(c_small.value)
            for b_id in self._class_bool_terms[r_large][:bool_len]:
                self._enqueue_prop(self._id_to_expr[b_id], bval)
        elif c_large is not None and c_small is None:
            bval = bool(c_large.value)
            for b_id in self._class_bool_terms[r_small]:
                self._enqueue_prop(self._id_to_expr[b_id], bval)

        # Step 5: Re-insert affected parent signatures and detect congruences.
        for p in parents:
            new_sig = self._compute_sig(p)
            existing = self._sig_table.get(new_sig)
            if existing is None:
                self._sig_set(new_sig, p)
            elif self._rep[p] != self._rep[existing]:
                self._merge_queue.append((p, existing, (p, existing)))
                self._stats.congruences += 1

        # Step 6: Check equality watches attached to r_small for newly equal pairs.
        watches_small = self._eq_watches[r_small]
        if watches_small:
            watches_large = self._eq_watches[r_large]
            old_watch_len = len(watches_large)
            seen_eqs: set[int] = set()
            conflict_found: list[TheoryLit] | None = None
            for eq_idx in watches_small:
                if eq_idx in seen_eqs:
                    continue
                seen_eqs.add(eq_idx)
                lhs_id, rhs_id, eq_expr = self._eq_atoms[eq_idx]
                if self._rep[lhs_id] == self._rep[rhs_id]:
                    asserted = self._asserted_atoms.get(eq_expr)
                    if asserted is False:
                        conflict_found = [
                            *self._explain_eq(lhs_id, rhs_id),
                            TheoryLit(eq_expr, False),
                        ]
                        break
                    if asserted is None:
                        self._enqueue_prop(eq_expr, True)
                else:
                    watches_large.append(eq_idx)
            if self._trail_marks and len(watches_large) > old_watch_len:
                self._history.append((_OP_WATCH_APPEND, r_large, old_watch_len))
            if conflict_found is not None:
                self._conflict = _dedup_lits(conflict_found)
                self._stats.conflicts += 1
                return False

        return True

    def _link_proof(self, u_side: int, v_side: int, reason: _Reason) -> None:
        # Walk up from u_side to the current root of its Proof Forest tree.
        path: list[int] = []
        cur = u_side
        while cur != -1:
            path.append(cur)
            cur = self._proof_parent[cur]

        if self._trail_marks:
            saved = tuple(
                (node, self._proof_parent[node], self._proof_reason[node])
                for node in path
            )
            self._history.append((_OP_PROOF_LINK, saved))

        # Reverse pointers along the path so u_side becomes the subtree root.
        for i in range(len(path) - 1, 0, -1):
            child = path[i]
            orig_child = path[i - 1]
            self._proof_parent[child] = orig_child
            self._proof_reason[child] = self._proof_reason[orig_child]

        self._proof_parent[u_side] = v_side
        self._proof_reason[u_side] = reason

    def _explain_reason(self, reason: _Reason) -> list[TheoryLit]:
        if isinstance(reason, TheoryLit):
            return [reason]
        p1, p2 = reason
        lits: list[TheoryLit] = []
        for a_id, b_id in zip(self._arg_ids[p1], self._arg_ids[p2], strict=True):
            if a_id != b_id:
                lits.extend(self._explain_eq(a_id, b_id))
        return lits

    def _explain_eq(self, lhs_id: int, rhs_id: int) -> list[TheoryLit]:
        if lhs_id == rhs_id:
            return []

        self._stats.explanations += 1
        result: list[TheoryLit] = []
        seen_lits: set[TheoryLit] = set()
        explained_pairs: set[tuple[int, int]] = set()
        seen_edge_nodes: set[int] = set()
        pending: list[tuple[int, int]] = [(lhs_id, rhs_id)]

        while pending:
            a, b = pending.pop()
            if a == b:
                continue
            pair = (a, b) if a < b else (b, a)
            if pair in explained_pairs:
                continue
            explained_pairs.add(pair)

            ancestors: set[int] = set()
            cur = a
            while cur != -1:
                ancestors.add(cur)
                cur = self._proof_parent[cur]

            lca = b
            while lca not in ancestors:
                lca = self._proof_parent[lca]

            for start in (a, b):
                cur = start
                while cur != lca:
                    if cur not in seen_edge_nodes:
                        seen_edge_nodes.add(cur)
                        reason = self._proof_reason[cur]
                        assert reason is not None
                        if isinstance(reason, TheoryLit):
                            if reason not in seen_lits:
                                seen_lits.add(reason)
                                result.append(reason)
                        else:
                            p1, p2 = reason
                            for a_arg, b_arg in zip(
                                self._arg_ids[p1], self._arg_ids[p2], strict=True
                            ):
                                if a_arg != b_arg:
                                    pending.append((a_arg, b_arg))
                    cur = self._proof_parent[cur]

        return result
