"""CDCL(T) core orchestrator.

Bridges ``syntax`` expressions with the standalone ``sat`` solver, handles Tseitin
clausification and Model-Based Theory Combination (MBTC), coordinates ``theories``
(``EUF``, ``LRA``, ``LIA``), ``tactics``, ``quantifiers``, and ``model`` construction,
and injects callbacks/protocols into lower layers (``sat`` and ``quantifiers``).
Will promote to a ``smt/`` subpackage as implementation grows.

Depends on: ``syntax``, ``sat``, ``theories``, ``tactics``, ``quantifiers``, ``model``.
"""

from collections.abc import Callable, Sequence

from unsat.model import Model, Value
from unsat.sat import (
    Lit,
    SATSolver,
    SolveResult,
    Var,
    negate,
    pos_lit,
)
from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl, Sort
from unsat.tactics import BitBlaster, bv_simplify, simplify
from unsat.theories import (
    ArraySolver,
    EUFSolver,
    LIACutLemma,
    LIASplitLemma,
    LRASolver,
    TheoryLit,
    find_lia_lemma,
)

_CMP_KINDS = frozenset({DeclKind.LT, DeclKind.LE, DeclKind.GT, DeclKind.GE})
_ARITH_OP_KINDS = frozenset(
    {
        DeclKind.NEG,
        DeclKind.ADD,
        DeclKind.SUB,
        DeclKind.MUL,
        DeclKind.DIV,
        DeclKind.TO_REAL,
    }
)
_BV_CMP_KINDS = frozenset(
    {
        DeclKind.BV_ULT,
        DeclKind.BV_ULE,
        DeclKind.BV_UGT,
        DeclKind.BV_UGE,
        DeclKind.BV_SLT,
        DeclKind.BV_SLE,
        DeclKind.BV_SGT,
        DeclKind.BV_SGE,
    }
)
_BV_OP_KINDS = frozenset(
    {
        DeclKind.BV_NOT,
        DeclKind.BV_AND,
        DeclKind.BV_OR,
        DeclKind.BV_XOR,
        DeclKind.BV_NEG,
        DeclKind.BV_ADD,
        DeclKind.BV_SUB,
        DeclKind.BV_MUL,
        DeclKind.BV_UDIV,
        DeclKind.BV_UREM,
        DeclKind.BV_SDIV,
        DeclKind.BV_SREM,
        DeclKind.BV_SMOD,
        DeclKind.BV_SHL,
        DeclKind.BV_LSHR,
        DeclKind.BV_ASHR,
        DeclKind.BV_CONCAT,
        DeclKind.BV_EXTRACT,
        DeclKind.BV_ZERO_EXT,
        DeclKind.BV_SIGN_EXT,
        DeclKind.BV_ROTATE_LEFT,
        DeclKind.BV_ROTATE_RIGHT,
        DeclKind.BV_REPEAT,
    }
)
_ARRAY_OP_KINDS = frozenset({DeclKind.SELECT, DeclKind.STORE, DeclKind.CONST_ARRAY})


def _strip_nots(expr: Expr) -> tuple[Expr, bool]:
    flip = False
    current = expr
    while isinstance(current, App) and current.decl.kind is DeclKind.NOT:
        flip = not flip
        current = current.args[0]
    return current, flip


def _is_bool_fixed_distinct(node: Expr) -> bool:
    return (
        isinstance(node, App)
        and node.decl.kind is DeclKind.DISTINCT
        and len(node.args) != 2
        and (not node.args or node.args[0].is_bool)
    )


class _CombinedPropagator:
    """Propagator coordinating ``EUF``, ``LRA``, ``LIA``, ``Arrays``, and ``MBTC``."""

    def __init__(
        self,
        ctx: Context,
        euf_solver: EUFSolver,
        lra_solver: LRASolver,
        array_solver: ArraySolver,
        bitblaster: BitBlaster,
    ) -> None:
        self._ctx = ctx
        self._sat: SATSolver | None = None
        self._euf = euf_solver
        self._lra = lra_solver
        self._arrays = array_solver
        self._bitblaster = bitblaster
        self._encoder: _PlaistedGreenbaumEncoder | None = None

        self._euf_lit_to_atoms: dict[Lit, list[tuple[Expr, bool]]] = {}
        self._euf_atom_to_pos_lit: dict[Expr, Lit] = {}

        self._lra_lit_to_atoms: dict[Lit, list[tuple[Expr, bool]]] = {}
        self._lra_atom_to_pos_lit: dict[Expr, Lit] = {}

        self._shared_arith_terms: dict[Sort, list[Expr]] = {}
        self._shared_arith_set: set[Expr] = set()
        self._shared_bv_terms: dict[Sort, list[Expr]] = {}
        self._shared_bv_set: set[Expr] = set()
        self._emitted_cuts: set[Expr] = set()

    def attach(self, sat_solver: SATSolver, encoder: _PlaistedGreenbaumEncoder) -> None:
        """Bind the owning ``SATSolver`` and encoder after construction."""
        self._sat = sat_solver
        self._encoder = encoder

    def reset_check_state(self) -> None:
        """Clear per-solve deduplication state before a fresh ``check()``."""
        self._emitted_cuts.clear()

    def add_shared_arith_term(self, term: Expr) -> None:
        """Record an ``Int``/``Real`` term participating in EUF for MBTC."""
        if term in self._shared_arith_set or not term.is_arith:
            return
        self._shared_arith_set.add(term)
        self._shared_arith_terms.setdefault(term.sort, []).append(term)
        self._euf.register_term(term)
        self._lra.register_term(term)

    def add_shared_bv_term(self, term: Expr) -> None:
        """Record a ``BitVec`` term participating in EUF/Arrays for BV MBTC."""
        if term in self._shared_bv_set or not term.is_bv:
            return
        self._shared_bv_set.add(term)
        self._shared_bv_terms.setdefault(term.sort, []).append(term)
        self._euf.register_term(term)

    def all_shared_arith_terms(self) -> list[Expr]:
        """Return all registered mixed EUF+arithmetic interface terms."""
        return [t for terms in self._shared_arith_terms.values() for t in terms]

    def all_shared_bv_terms(self) -> list[Expr]:
        """Return all registered mixed EUF/Array+BitVec interface terms."""
        return [t for terms in self._shared_bv_terms.values() for t in terms]

    def has_shared_term(self, term: Expr) -> bool:
        """Return whether ``term`` is an arithmetic/EUF interface term."""
        return term in self._shared_arith_set

    def bind_euf(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None:
        """Bind positive ``lit`` to EUF atom ``(atom, True)``."""
        if atom in self._euf_atom_to_pos_lit:
            return
        self._euf_atom_to_pos_lit[atom] = lit
        self._euf_lit_to_atoms.setdefault(lit, []).append((atom, True))
        self._euf_lit_to_atoms.setdefault(negate(lit), []).append((atom, False))

        if not catch_up:
            return
        assert self._sat is not None
        val = self._sat.value(lit)
        if val is None:
            return
        self._euf.assert_atom(atom, val)
        props, conflict = self._euf.propagate()
        if conflict is not None:
            self._sat.add_clause(self._euf_conflict_to_clause(conflict))
            return
        for p_atom, p_sign in props:
            p_lit = self._euf_atom_to_pos_lit.get(p_atom)
            if p_lit is None:
                continue
            sat_p_lit = p_lit if p_sign else negate(p_lit)
            if self._sat.value(sat_p_lit) is None:
                reasons = self._euf.explain_propagation(p_atom, p_sign)
                lemma = [
                    sat_p_lit,
                    *(negate(self._euf_lit_to_sat(tl)) for tl in reasons),
                ]
                self._sat.add_clause(lemma)

    def bind_lra(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None:
        """Bind positive ``lit`` to LRA comparison atom ``(atom, True)``."""
        if atom in self._lra_atom_to_pos_lit:
            return
        self._lra_atom_to_pos_lit[atom] = lit
        self._lra_lit_to_atoms.setdefault(lit, []).append((atom, True))
        self._lra_lit_to_atoms.setdefault(negate(lit), []).append((atom, False))

        if not catch_up:
            return
        assert self._sat is not None
        val = self._sat.value(lit)
        if val is None:
            return
        self._lra.assert_atom(atom, val)
        props, conflict = self._lra.propagate()
        if conflict is not None:
            self._sat.add_clause(self._lra_conflict_to_clause(conflict))
            return
        for p_atom, p_sign in props:
            p_lit = self._lra_atom_to_pos_lit.get(p_atom)
            if p_lit is None:
                continue
            sat_p_lit = p_lit if p_sign else negate(p_lit)
            if self._sat.value(sat_p_lit) is None:
                reasons = self._lra.explain_propagation(p_atom, p_sign)
                lemma = [
                    sat_p_lit,
                    *(negate(self._lra_lit_to_sat(tl)) for tl in reasons),
                ]
                self._sat.add_clause(lemma)

    def push(self) -> None:
        self._euf.push()
        self._lra.push()

    def pop(self, num_levels: int) -> None:
        self._euf.pop(num_levels)
        self._lra.pop(num_levels)

    def on_assign(self, lit: Lit) -> None:
        euf_entries = self._euf_lit_to_atoms.get(lit)
        if euf_entries is not None:
            for atom, sign in euf_entries:
                self._euf.assert_atom(atom, sign)
        lra_entries = self._lra_lit_to_atoms.get(lit)
        if lra_entries is not None:
            for atom, sign in lra_entries:
                self._lra.assert_atom(atom, sign)

    def propagate(self) -> tuple[Sequence[Lit], Sequence[Lit] | None]:
        euf_props, euf_conflict = self._euf.propagate()
        if euf_conflict is not None:
            return (), self._euf_conflict_to_clause(euf_conflict)

        lra_props, lra_conflict = self._lra.propagate()
        if lra_conflict is not None:
            return (), self._lra_conflict_to_clause(lra_conflict)

        sat_props: list[Lit] = []
        for atom, sign in euf_props:
            pos = self._euf_atom_to_pos_lit.get(atom)
            if pos is not None:
                sat_props.append(pos if sign else negate(pos))
        for atom, sign in lra_props:
            pos = self._lra_atom_to_pos_lit.get(atom)
            if pos is not None:
                sat_props.append(pos if sign else negate(pos))
        return sat_props, None

    def explain_propagation(self, lit: Lit) -> Sequence[Lit]:
        euf_entries = self._euf_lit_to_atoms.get(lit)
        if euf_entries:
            for atom, sign in euf_entries:
                try:
                    reasons = self._euf.explain_propagation(atom, sign)
                except KeyError, ValueError:
                    continue
                return [lit, *(negate(self._euf_lit_to_sat(tl)) for tl in reasons)]

        lra_entries = self._lra_lit_to_atoms.get(lit)
        if lra_entries:
            for atom, sign in lra_entries:
                try:
                    reasons = self._lra.explain_propagation(atom, sign)
                except KeyError, ValueError:
                    continue
                return [lit, *(negate(self._lra_lit_to_sat(tl)) for tl in reasons)]

        msg = f"SAT literal {lit} has no valid theory explanation in current state"
        raise ValueError(msg)

    def check(self) -> Sequence[Sequence[Lit]]:
        euf_lemmas = self._euf.check()
        if euf_lemmas:
            return [self._euf_conflict_to_clause(lemma) for lemma in euf_lemmas]

        lra_lemmas = self._lra.check()
        if lra_lemmas:
            return [self._lra_conflict_to_clause(lemma) for lemma in lra_lemmas]

        lia_lemma = find_lia_lemma(self._lra, emitted_cuts=self._emitted_cuts)
        if lia_lemma is not None:
            if isinstance(lia_lemma, LIACutLemma):
                base = self._lra_conflict_to_clause(lia_lemma.reasons)
                if lia_lemma.cut_atom is self._ctx.false_expr:
                    return [base]
                self._emitted_cuts.add(lia_lemma.cut_atom)
                cut_lit = self._ensure_lra_lemma_lit(lia_lemma.cut_atom)
                return [[*base, cut_lit]]
            assert isinstance(lia_lemma, LIASplitLemma)
            if lia_lemma.prefer_ge:
                lit_first = self._ensure_lra_lemma_lit(lia_lemma.ge_atom)
                lit_second = self._ensure_lra_lemma_lit(lia_lemma.le_atom)
            else:
                lit_first = self._ensure_lra_lemma_lit(lia_lemma.le_atom)
                lit_second = self._ensure_lra_lemma_lit(lia_lemma.ge_atom)
            return [[lit_first, lit_second]]

        if self._shared_arith_terms:
            mbtc_lemmas = self._check_mbtc()
            if mbtc_lemmas:
                return mbtc_lemmas

        if self._shared_bv_terms:
            bv_mbtc = self._check_mbtc_bv()
            if bv_mbtc:
                return bv_mbtc

        array_lemmas = self._arrays.check(self._euf)
        if array_lemmas:
            assert self._encoder is not None
            out: list[list[Lit]] = []
            for lemma in array_lemmas:
                base = self._euf_conflict_to_clause(lemma.reasons)
                if lemma.formula is self._ctx.true_expr:
                    continue
                if lemma.formula is self._ctx.false_expr:
                    out.append(base)
                    continue
                f_lit, def_clauses = self._encoder.encode_lemma(
                    lemma.formula, polarity=1
                )
                out.extend(def_clauses)
                out.append([*base, f_lit])
            if out:
                return out

        return ()

    def _sat_bit_lookup(self) -> Callable[[Expr], bool]:
        assert self._sat is not None
        assert self._encoder is not None
        sat = self._sat
        enc = self._encoder

        def _lookup(node: Expr) -> bool:
            var = enc.expr_var_or_none(node)
            if var is None:
                return False
            val = sat.value(pos_lit(var))
            return bool(val) if val is not None else False

        return _lookup

    def _check_mbtc_bv(self) -> list[list[Lit]]:
        assert self._encoder is not None
        lookup = self._sat_bit_lookup()
        vals: dict[Expr, int] = {
            term: self._bitblaster.eval_term_bits(term, lookup)
            for term in self.all_shared_bv_terms()
        }

        # Direction 1 (EUF -> BV): force matching bit vectors on EUF-equal terms.
        sort_reps: dict[Sort, dict[Expr, Expr]] = {}
        for sort, terms in self._shared_bv_terms.items():
            groups: dict[Expr, Expr] = {}
            for term in terms:
                rep = self._euf.rep_expr(term)
                leader = groups.get(rep)
                if leader is None:
                    groups[rep] = term
                    continue
                if vals[term] != vals[leader]:
                    reasons = self._euf.explain_terms_equal(term, leader)
                    base = self._euf_conflict_to_clause(reasons)
                    eq_atom = self._ctx.mk_eq(term, leader)
                    if eq_atom is self._ctx.true_expr:
                        continue
                    if eq_atom is self._ctx.false_expr:
                        return [base]
                    lit_eq, def_clauses = self._encoder.encode_lemma(
                        eq_atom, polarity=0
                    )
                    return [*def_clauses, [*base, lit_eq]]
            sort_reps[sort] = groups

        # Direction 2 (BV -> EUF): speculate interface equalities when BV values match.
        for groups in sort_reps.values():
            seen_val: dict[int, Expr] = {}
            for leader in groups.values():
                val = vals[leader]
                other = seen_val.get(val)
                if other is None:
                    seen_val[val] = leader
                    continue
                eq_atom = self._ctx.mk_eq(leader, other)
                if eq_atom is self._ctx.false_expr or eq_atom is self._ctx.true_expr:
                    continue
                _, def_clauses = self._encoder.encode_lemma(eq_atom, polarity=0)
                if def_clauses:
                    return def_clauses

        return []

    def _ensure_lra_lemma_lit(self, atom: Expr) -> Lit:
        assert self._encoder is not None
        existing = self._lra_atom_to_pos_lit.get(atom)
        if existing is not None:
            return existing
        self._lra.register_atom(atom)
        lit = pos_lit(self._encoder.ensure_expr_var(atom))
        self.bind_lra(lit, atom, catch_up=False)
        return lit

    def _ensure_euf_lemma_lit(self, eq_atom: Expr) -> Lit:
        assert self._encoder is not None
        existing = self._euf_atom_to_pos_lit.get(eq_atom)
        if existing is not None:
            return existing
        self._euf.register_eq(eq_atom)
        lit = pos_lit(self._encoder.ensure_expr_var(eq_atom))
        self.bind_euf(lit, eq_atom, catch_up=False)
        return lit

    def _check_mbtc(self) -> list[list[Lit]]:
        all_terms = self.all_shared_arith_terms()
        vals = self._lra.term_values(all_terms)

        # Direction 1 (EUF -> LRA): propagate EUF equalities into LRA bounds.
        sort_reps: dict[Sort, dict[Expr, Expr]] = {}
        for sort, terms in self._shared_arith_terms.items():
            groups: dict[Expr, Expr] = {}
            for term in terms:
                rep = self._euf.rep_expr(term)
                leader = groups.get(rep)
                if leader is None:
                    groups[rep] = term
                    continue
                if vals[term] != vals[leader]:
                    reasons = self._euf.explain_terms_equal(term, leader)
                    base = self._euf_conflict_to_clause(reasons)
                    le = self._ctx.mk_le(term, leader)
                    ge = self._ctx.mk_ge(term, leader)
                    lemmas: list[list[Lit]] = []
                    for cmp_atom in (le, ge):
                        if cmp_atom is self._ctx.true_expr:
                            continue
                        if cmp_atom is self._ctx.false_expr:
                            lemmas.append(list(base))
                        else:
                            lemmas.append([*base, self._ensure_lra_lemma_lit(cmp_atom)])
                    if lemmas:
                        return lemmas
            sort_reps[sort] = groups

        # Direction 2 (LRA -> EUF): speculate interface equalities for matching vals.
        for groups in sort_reps.values():
            seen_val: dict[object, Expr] = {}
            for leader in groups.values():
                val = vals[leader]
                other = seen_val.get(val)
                if other is None:
                    seen_val[val] = leader
                    continue
                eq_atom = self._ctx.mk_eq(leader, other)
                if eq_atom is self._ctx.false_expr or eq_atom is self._ctx.true_expr:
                    continue
                lit_eq = self._ensure_euf_lemma_lit(eq_atom)
                le = self._ctx.mk_le(leader, other)
                ge = self._ctx.mk_ge(leader, other)
                lit_le = (
                    None if isinstance(le, Const) else self._ensure_lra_lemma_lit(le)
                )
                lit_ge = (
                    None if isinstance(ge, Const) else self._ensure_lra_lemma_lit(ge)
                )

                out_lemmas: list[list[Lit]] = []
                if lit_le is not None:
                    out_lemmas.append([negate(lit_eq), lit_le])
                elif le is self._ctx.false_expr:
                    out_lemmas.append([negate(lit_eq)])

                if lit_ge is not None:
                    out_lemmas.append([negate(lit_eq), lit_ge])
                elif ge is self._ctx.false_expr:
                    out_lemmas.append([negate(lit_eq)])

                clause3: list[Lit] = [lit_eq]
                satisfied_neg = False
                for opt_atom, opt_lit in ((le, lit_le), (ge, lit_ge)):
                    if opt_atom is self._ctx.false_expr:
                        satisfied_neg = True
                        break
                    if opt_lit is not None:
                        clause3.append(negate(opt_lit))
                if not satisfied_neg:
                    out_lemmas.append(clause3)
                return out_lemmas

        return []

    def _euf_lit_to_sat(self, tlit: TheoryLit) -> Lit:
        pos = self._euf_atom_to_pos_lit[tlit.atom]
        return pos if tlit.sign else negate(pos)

    def _lra_lit_to_sat(self, tlit: TheoryLit) -> Lit:
        pos = self._lra_atom_to_pos_lit[tlit.atom]
        return pos if tlit.sign else negate(pos)

    def _euf_conflict_to_clause(self, conflict: Sequence[TheoryLit]) -> list[Lit]:
        return [negate(self._euf_lit_to_sat(tl)) for tl in conflict]

    def _lra_conflict_to_clause(self, conflict: Sequence[TheoryLit]) -> list[Lit]:
        return [negate(self._lra_lit_to_sat(tl)) for tl in conflict]


class _PlaistedGreenbaumEncoder:
    """Polarity-aware incremental Tseitin, EUF, LRA/LIA, BV, and Array encoder."""

    def __init__(
        self,
        ctx: Context,
        sat_solver: SATSolver,
        euf_solver: EUFSolver,
        lra_solver: LRASolver,
        array_solver: ArraySolver,
        bitblaster: BitBlaster,
        prop: _CombinedPropagator,
    ) -> None:
        self._ctx = ctx
        self._sat = sat_solver
        self._euf = euf_solver
        self._lra = lra_solver
        self._arrays = array_solver
        self._bitblaster = bitblaster
        self._prop = prop
        self._expr_to_var: dict[Expr, Var] = {}
        self._decl_to_var: dict[FuncDecl, Var] = {}
        self._pos_encoded: set[Expr] = set()
        self._neg_encoded: set[Expr] = set()
        self._terms_non_euf: set[Expr] = set()
        self._terms_euf: set[Expr] = set()
        self._true_lit: Lit | None = None
        self._first_lit: Lit | None = None
        self._clause_sink: list[list[Lit]] | None = None

    @property
    def decl_to_var(self) -> dict[FuncDecl, Var]:
        """Mapping from Boolean 0-arity declarations to SAT variable indices."""
        return self._decl_to_var

    def expr_var_or_none(self, expr: Expr) -> Var | None:
        """Return SAT variable index allocated for ``expr``, or ``None``."""
        return self._expr_to_var.get(expr)

    def _emit_clause(self, lits: list[Lit]) -> None:
        if self._clause_sink is not None:
            self._clause_sink.append(lits)
        else:
            self._sat.add_clause(lits)

    def encode_lemma(
        self, expr: Expr, polarity: int = 1
    ) -> tuple[Lit, list[list[Lit]]]:
        """Encode ``expr`` during ``check()``, capturing definition clauses."""
        prev_sink = self._clause_sink
        clauses: list[list[Lit]] = []
        self._clause_sink = clauses
        try:
            lit = self.encode(expr, polarity=polarity)
        finally:
            self._clause_sink = prev_sink
        return lit, clauses

    def any_lit(self) -> Lit | None:
        """Return an allocated SAT literal if any variable exists yet."""
        return self._first_lit

    def ensure_expr_var(self, expr: Expr) -> Var:
        """Return existing SAT variable index for ``expr`` or allocate a new one."""
        var = self._expr_to_var.get(expr)
        if var is None:
            var = self._sat.new_var()
            self._expr_to_var[expr] = var
            if self._first_lit is None:
                self._first_lit = pos_lit(var)
            if isinstance(expr, App) and expr.is_const_symbol:
                self._decl_to_var[expr.decl] = var
        return var

    def _get_true_lit(self) -> Lit:
        if self._true_lit is None:
            lit = pos_lit(self._sat.new_var())
            self._emit_clause([lit])
            self._true_lit = lit
            if self._first_lit is None:
                self._first_lit = lit
        return self._true_lit

    def _get_false_lit(self) -> Lit:
        return negate(self._get_true_lit())

    def _register_term(self, term: Expr, *, in_euf: bool = True) -> None:
        """Walk ``term`` registering EUF/LRA/Array/BV subterms and non-Bool ITEs."""
        bool_args: list[Expr] = []
        non_bool_ites: list[App] = []
        stack: list[tuple[Expr, bool, bool]] = [(term, in_euf, False)]

        while stack:
            node, euf_flag, expanded = stack.pop()
            if euf_flag:
                if node in self._terms_euf:
                    continue
            elif node in self._terms_euf or node in self._terms_non_euf:
                continue

            if isinstance(node, Const):
                if euf_flag:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            if not isinstance(node, App):
                if euf_flag:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            kind = node.decl.kind
            if kind is DeclKind.ITE and not node.is_bool:
                eff_euf = euf_flag or node.is_array
                if node.is_bv and not eff_euf:
                    if not expanded:
                        stack.append((node, euf_flag, True))
                        stack.append((node.args[2], euf_flag, False))
                        stack.append((node.args[1], euf_flag, False))
                        continue
                    self._terms_non_euf.add(node)
                    continue

                if not expanded:
                    stack.append((node, eff_euf, True))
                    stack.append((node.args[2], eff_euf, False))
                    stack.append((node.args[1], eff_euf, False))
                    continue
                if eff_euf:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                    if node.is_array:
                        self._arrays.register_term(node)
                else:
                    self._terms_non_euf.add(node)
                if node.is_arith:
                    self._lra.register_term(node)
                non_bool_ites.append(node)
                continue

            if kind in _ARITH_OP_KINDS:
                if not expanded:
                    stack.append((node, euf_flag, True))
                    for arg in reversed(node.args):
                        stack.append((arg, euf_flag, False))
                    continue
                if euf_flag:
                    self._terms_euf.add(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            if kind in _BV_OP_KINDS:
                if not expanded:
                    stack.append((node, euf_flag, True))
                    for arg in reversed(node.args):
                        stack.append((arg, euf_flag, False))
                    continue
                if euf_flag:
                    self._terms_euf.add(node)
                    if node.is_bv:
                        self._prop.add_shared_bv_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            if kind in _ARRAY_OP_KINDS:
                if not expanded:
                    stack.append((node, True, True))
                    for arg in reversed(node.args):
                        if arg.is_bool:
                            bool_args.append(arg)
                        else:
                            stack.append((arg, True, False))
                    continue
                self._terms_euf.add(node)
                self._arrays.register_term(node)
                self._euf.register_term(node)
                if node.is_arith:
                    self._prop.add_shared_arith_term(node)
                elif node.is_bv:
                    self._prop.add_shared_bv_term(node)
                continue

            if node.decl.is_uninterpreted:
                if node.args:
                    if not expanded:
                        stack.append((node, euf_flag, True))
                        for arg in reversed(node.args):
                            if arg.is_bool:
                                bool_args.append(arg)
                            else:
                                # Arguments of an uninterpreted App always touch EUF.
                                stack.append((arg, True, False))
                        continue
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                    elif node.is_array:
                        self._arrays.register_term(node)
                else:
                    if euf_flag:
                        self._terms_euf.add(node)
                        self._euf.register_term(node)
                        if node.is_arith:
                            self._prop.add_shared_arith_term(node)
                        elif node.is_bv:
                            self._prop.add_shared_bv_term(node)
                        elif node.is_array:
                            self._arrays.register_term(node)
                    else:
                        self._terms_non_euf.add(node)
                continue

            if node.is_bool:
                self._terms_euf.add(node)
                bool_args.append(node)
                continue

            if euf_flag:
                self._terms_euf.add(node)
                self._euf.register_term(node)
            else:
                self._terms_non_euf.add(node)

        for b_arg in bool_args:
            if isinstance(b_arg, Const):
                self._euf.register_term(b_arg)
                continue
            lit_arg = self.encode(b_arg, polarity=0)
            self._euf.register_bool_term(b_arg)
            self._prop.bind_euf(lit_arg, b_arg, catch_up=(self._clause_sink is None))

        for ite_node in non_bool_ites:
            cond, then_b, else_b = ite_node.args
            lit_c = self.encode(cond, polarity=0)
            lit_then = self.encode(self._ctx.mk_eq(ite_node, then_b), polarity=1)
            lit_else = self.encode(self._ctx.mk_eq(ite_node, else_b), polarity=1)
            self._emit_clause([negate(lit_c), lit_then])
            self._emit_clause([lit_c, lit_else])

    def _is_encoded(self, node: Expr, pol: int) -> bool:
        if pol > 0:
            return node in self._pos_encoded
        if pol < 0:
            return node in self._neg_encoded
        return node in self._pos_encoded and node in self._neg_encoded

    def _get_lit(self, expr: Expr) -> Lit:
        base, flip = _strip_nots(expr)
        if isinstance(base, Const):
            lit = self._get_true_lit() if base.value else self._get_false_lit()
        elif _is_bool_fixed_distinct(base):
            assert isinstance(base, App)
            lit = self._get_true_lit() if len(base.args) <= 1 else self._get_false_lit()
        else:
            lit = pos_lit(self._expr_to_var[base])
        return negate(lit) if flip else lit

    def _distinct_eq_pairs(self, node: App) -> list[Expr]:
        args = node.args
        return [
            self._ctx.mk_eq(args[i], args[j])
            for i in range(len(args))
            for j in range(i + 1, len(args))
        ]

    def _child_polarities(self, node: App, pol: int) -> list[tuple[Expr, int]]:
        kind = node.decl.kind
        match kind:
            case DeclKind.AND | DeclKind.OR:
                return [(arg, pol) for arg in node.args]
            case DeclKind.IMPLIES:
                neg_pol = -pol if pol != 0 else 0
                return [(node.args[0], neg_pol), (node.args[1], pol)]
            case DeclKind.XOR | DeclKind.EQ:
                return [(arg, 0) for arg in node.args]
            case DeclKind.DISTINCT:
                if node.args and not node.args[0].is_bool:
                    neg_pol = -pol if pol != 0 else 0
                    return [
                        (eq_expr, neg_pol) for eq_expr in self._distinct_eq_pairs(node)
                    ]
                return [(arg, 0) for arg in node.args]
            case DeclKind.ITE:
                return [(node.args[0], 0), (node.args[1], pol), (node.args[2], pol)]
            case _:
                msg = f"Unsupported Boolean operator in Tseitin encoder: {kind}"
                raise TypeError(msg)

    def _emit_gate_clauses(self, node: App, pol: int) -> None:
        v = pos_lit(self.ensure_expr_var(node))
        nv = negate(v)
        emit_pos = pol >= 0 and node not in self._pos_encoded
        emit_neg = pol <= 0 and node not in self._neg_encoded

        if (
            node.decl.kind is DeclKind.DISTINCT
            and node.args
            and not node.args[0].is_bool
        ):
            pair_lits = [
                self._get_lit(eq_expr) for eq_expr in self._distinct_eq_pairs(node)
            ]
            if emit_pos:
                for eq_lit in pair_lits:
                    self._emit_clause([nv, negate(eq_lit)])
                self._pos_encoded.add(node)
            if emit_neg:
                self._emit_clause([v, *pair_lits])
                self._neg_encoded.add(node)
            return

        lits = [self._get_lit(arg) for arg in node.args]

        match node.decl.kind:
            case DeclKind.AND:
                if emit_pos:
                    for lit in lits:
                        self._emit_clause([nv, lit])
                if emit_neg:
                    self._emit_clause([v, *(negate(lit) for lit in lits)])
            case DeclKind.OR:
                if emit_pos:
                    self._emit_clause([nv, *lits])
                if emit_neg:
                    for lit in lits:
                        self._emit_clause([v, negate(lit)])
            case DeclKind.IMPLIES:
                la, lb = lits
                if emit_pos:
                    self._emit_clause([nv, negate(la), lb])
                if emit_neg:
                    self._emit_clause([v, la])
                    self._emit_clause([v, negate(lb)])
            case DeclKind.XOR | DeclKind.DISTINCT:
                la, lb = lits
                if emit_pos:
                    self._emit_clause([nv, la, lb])
                    self._emit_clause([nv, negate(la), negate(lb)])
                if emit_neg:
                    self._emit_clause([v, negate(la), lb])
                    self._emit_clause([v, la, negate(lb)])
            case DeclKind.EQ:
                la, lb = lits
                if emit_pos:
                    self._emit_clause([nv, negate(la), lb])
                    self._emit_clause([nv, la, negate(lb)])
                if emit_neg:
                    self._emit_clause([v, la, lb])
                    self._emit_clause([v, negate(la), negate(lb)])
            case DeclKind.ITE:
                lc, lt, le = lits
                if emit_pos:
                    self._emit_clause([nv, negate(lc), lt])
                    self._emit_clause([nv, lc, le])
                if emit_neg:
                    self._emit_clause([v, negate(lc), negate(lt)])
                    self._emit_clause([v, lc, negate(le)])
            case _:
                msg = f"Unsupported Boolean operator in Tseitin encoder: {node.decl}"
                raise TypeError(msg)

        if emit_pos:
            self._pos_encoded.add(node)
        if emit_neg:
            self._neg_encoded.add(node)

    def encode(self, expr: Expr, polarity: int = 1) -> Lit:
        """Encode ``expr`` iteratively with polarity ``+1``, ``-1``, or ``0``."""
        root_base, root_flip = _strip_nots(expr)
        root_pol = -polarity if (root_flip and polarity != 0) else polarity
        stack: list[tuple[Expr, int, bool]] = [(root_base, root_pol, False)]
        catch_up = self._clause_sink is None

        while stack:
            node, pol, expanded = stack.pop()
            if self._is_encoded(node, pol):
                continue

            if isinstance(node, Const) or _is_bool_fixed_distinct(node):
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if not isinstance(node, App):
                msg = f"Unsupported AST node in Tseitin encoder: {node!r}"
                raise TypeError(msg)

            if node.is_const_symbol:
                self.ensure_expr_var(node)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            kind = node.decl.kind
            if kind in _CMP_KINDS:
                self._register_term(node.args[0], in_euf=False)
                self._register_term(node.args[1], in_euf=False)
                self._lra.register_atom(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_lra(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind in _BV_CMP_KINDS:
                self._register_term(node.args[0], in_euf=False)
                self._register_term(node.args[1], in_euf=False)
                self._bitblaster.register_reserved(node)
                blasted = self._bitblaster.blast_bool(node)
                lit_blast = self.encode(blasted, polarity=0)
                lit_v = pos_lit(self.ensure_expr_var(node))
                self._emit_clause([negate(lit_v), lit_blast])
                self._emit_clause([lit_v, negate(lit_blast)])
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.EQ and not node.args[0].is_bool:
                lhs, rhs = node.args
                if lhs.is_arith:
                    le = self._ctx.mk_le(lhs, rhs)
                    ge = self._ctx.mk_ge(lhs, rhs)
                    lit_le = self.encode(le, polarity=0)
                    lit_ge = self.encode(ge, polarity=0)
                    lit_eq = pos_lit(self.ensure_expr_var(node))
                    self._emit_clause([negate(lit_eq), lit_le])
                    self._emit_clause([negate(lit_eq), lit_ge])
                    self._emit_clause([lit_eq, negate(lit_le), negate(lit_ge)])
                    self._euf.register_eq(node)
                    self._prop.bind_euf(lit_eq, node, catch_up=catch_up)
                elif lhs.is_bv:
                    self._register_term(lhs, in_euf=False)
                    self._register_term(rhs, in_euf=False)
                    self._bitblaster.register_reserved(node)
                    blasted = self._bitblaster.blast_eq(lhs, rhs)
                    lit_blast = self.encode(blasted, polarity=0)
                    lit_eq = pos_lit(self.ensure_expr_var(node))
                    self._emit_clause([negate(lit_eq), lit_blast])
                    self._emit_clause([lit_eq, negate(lit_blast)])
                    self._euf.register_eq(node)
                    self._prop.bind_euf(lit_eq, node, catch_up=catch_up)
                else:
                    self._register_term(lhs, in_euf=True)
                    self._register_term(rhs, in_euf=True)
                    self._euf.register_eq(node)
                    var = self.ensure_expr_var(node)
                    self._prop.bind_euf(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.SELECT:
                self._register_term(node, in_euf=True)
                self._euf.register_bool_term(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_euf(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if node.decl.is_uninterpreted and node.args:
                self._register_term(node, in_euf=True)
                self._euf.register_bool_term(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_euf(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if not expanded:
                stack.append((node, pol, True))
                for child, child_pol in reversed(self._child_polarities(node, pol)):
                    c_base, c_flip = _strip_nots(child)
                    eff_pol = -child_pol if (c_flip and child_pol != 0) else child_pol
                    if not self._is_encoded(c_base, eff_pol):
                        stack.append((c_base, eff_pol, False))
                continue

            self._emit_gate_clauses(node, pol)

        return self._get_lit(expr)


class SMTSolver:
    """Incremental CDCL(T) SMT solver over a specific :class:`Context`."""

    def __init__(self, ctx: Context) -> None:
        self._ctx = ctx
        self._init_backend()
        self._scope_lits: list[Lit] = []
        self._assertions_by_scope: list[list[Expr]] = [[]]
        self._last_result: SolveResult | None = None
        self._unsat_core: list[Expr] = []

    def _init_backend(self) -> None:
        self._euf = EUFSolver(self._ctx)
        self._lra = LRASolver(self._ctx)
        self._arrays = ArraySolver(self._ctx)
        self._bitblaster = BitBlaster(self._ctx)
        self._propagator = _CombinedPropagator(
            self._ctx, self._euf, self._lra, self._arrays, self._bitblaster
        )
        self._sat = SATSolver(propagator=self._propagator)
        self._encoder = _PlaistedGreenbaumEncoder(
            self._ctx,
            self._sat,
            self._euf,
            self._lra,
            self._arrays,
            self._bitblaster,
            self._propagator,
        )
        self._propagator.attach(self._sat, self._encoder)

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._ctx

    @property
    def num_scopes(self) -> int:
        """Current incremental ``push`` nesting depth."""
        return len(self._scope_lits)

    def _validate_bool_expr(self, expr: Expr) -> None:
        if expr.ctx is not self._ctx:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)
        if not expr.is_bool:
            msg = f"Expected Bool expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _ensure_base_level(self) -> None:
        if self._last_result is None:
            return
        any_lit = self._encoder.any_lit()
        if any_lit is None and self._scope_lits:
            any_lit = self._scope_lits[0]
        if any_lit is not None:
            self._sat.add_clause([any_lit, negate(any_lit)])

    def add(self, *formulas: Expr) -> None:
        """Assert one or more Boolean formulas into the current scope."""
        self._ensure_base_level()
        for formula in formulas:
            self._validate_bool_expr(formula)
            self._assertions_by_scope[-1].append(formula)
            simplified = bv_simplify(simplify(formula))
            conjuncts = (
                simplified.args
                if isinstance(simplified, App) and simplified.decl.kind is DeclKind.AND
                else (simplified,)
            )
            for conjunct in conjuncts:
                if conjunct is self._ctx.true_expr:
                    continue
                if conjunct is self._ctx.false_expr:
                    if not self._scope_lits:
                        self._sat.add_clause([])
                    else:
                        self._sat.add_clause([negate(self._scope_lits[-1])])
                    continue
                lit = self._encoder.encode(conjunct, polarity=1)
                if not self._scope_lits:
                    self._sat.add_clause([lit])
                else:
                    self._sat.add_clause([negate(self._scope_lits[-1]), lit])
        self._last_result = None

    def push(self) -> None:
        """Push a new incremental assertion scope."""
        self._ensure_base_level()
        act_lit = pos_lit(self._sat.new_var())
        self._scope_lits.append(act_lit)
        self._assertions_by_scope.append([])
        self._last_result = None

    def pop(self, levels: int = 1) -> None:
        """Pop ``levels`` incremental scopes, retracting their assertions."""
        if levels < 0 or levels > len(self._scope_lits):
            msg = f"Cannot pop {levels} scopes (current depth: {len(self._scope_lits)})"
            raise ValueError(msg)
        self._ensure_base_level()
        for _ in range(levels):
            act_lit = self._scope_lits.pop()
            self._sat.add_clause([negate(act_lit)])
            self._assertions_by_scope.pop()
        self._last_result = None

    def reset(self) -> None:
        """Reset all assertions, scopes, and learned state."""
        self._init_backend()
        self._scope_lits.clear()
        self._assertions_by_scope = [[]]
        self._last_result = None
        self._unsat_core = []

    def check(self, *assumptions: Expr) -> SolveResult:
        """Check satisfiability of asserted formulas under ``assumptions``."""
        self._ensure_base_level()
        self._propagator.reset_check_state()
        sat_assumptions = list(self._scope_lits)
        lit_to_exprs: dict[Lit, list[Expr]] = {}

        for assumption in assumptions:
            self._validate_bool_expr(assumption)
            simplified = bv_simplify(simplify(assumption))
            lit = self._encoder.encode(simplified, polarity=1)
            sat_assumptions.append(lit)
            lit_to_exprs.setdefault(lit, []).append(assumption)

        result = self._sat.solve(sat_assumptions)
        self._last_result = result
        if result is SolveResult.UNSAT:
            core: list[Expr] = []
            for lit in self._sat.unsat_core():
                mapped = lit_to_exprs.get(lit)
                if mapped:
                    core.append(mapped[0])
            self._unsat_core = list(dict.fromkeys(core))
        else:
            self._unsat_core = []
        return result

    def model(self) -> Model:
        """Return a satisfying :class:`Model` from the latest ``check()`` call."""
        if self._last_result is not SolveResult.SAT:
            msg = "Model is only available after check() returns SolveResult.SAT"
            raise ValueError(msg)
        sat_model = self._sat.model()
        internal_decls = self._bitblaster.internal_decls | self._arrays.internal_decls
        lra_conc = self._lra.concrete_values()
        shared_terms = self._propagator.all_shared_arith_terms()
        shared_conc = self._lra.term_values(shared_terms) if shared_terms else {}

        external_vals: dict[Expr, Expr] = {}
        for expr, frac in {**lra_conc, **shared_conc}.items():
            if expr.is_int:
                assert frac.denominator == 1
                external_vals[expr] = self._ctx.mk_int_val(frac.numerator)
            elif expr.is_real:
                external_vals[expr] = self._ctx.mk_real_val(frac)

        def _bit_lookup(node: Expr) -> bool:
            var = self._encoder.expr_var_or_none(node)
            return sat_model[var] if var is not None else False

        bv_decl_vals: dict[FuncDecl, int] = {}
        for bv_decl, bits in self._bitblaster.bv_const_bits.items():
            if bv_decl not in internal_decls:
                bv_decl_vals[bv_decl] = self._bitblaster.eval_bits(bits, _bit_lookup)
        for bv_term in self._propagator.all_shared_bv_terms():
            bv_int = self._bitblaster.eval_term_bits(bv_term, _bit_lookup)
            external_vals[bv_term] = self._ctx.mk_bv_val(bv_int, bv_term.bv_size)

        for decl, var in self._encoder.decl_to_var.items():
            if decl not in internal_decls:
                external_vals[decl()] = self._ctx.mk_bool_val(sat_model[var])

        scalar_vals = self._euf.resolve_scalar_values(external_values=external_vals)
        array_input = {**scalar_vals, **external_vals}
        array_vals = self._arrays.build_array_values(self._euf, array_input)
        all_external = {**external_vals, **array_vals}

        euf_model = self._euf.build_model(external_values=all_external)
        values: dict[FuncDecl, Value] = {
            decl: val for decl, val in euf_model.items() if decl not in internal_decls
        }
        for expr, frac in lra_conc.items():
            if isinstance(expr, App) and expr.is_const_symbol:
                if expr.is_int:
                    assert frac.denominator == 1
                    values[expr.decl] = frac.numerator
                elif expr.is_real:
                    values[expr.decl] = frac
        values.update(bv_decl_vals)
        for decl, var in self._encoder.decl_to_var.items():
            if decl not in internal_decls:
                values[decl] = sat_model[var]
        for term, arr_val in array_vals.items():
            if (
                isinstance(term, App)
                and term.is_const_symbol
                and term.decl not in internal_decls
            ):
                values[term.decl] = arr_val

        functions = {
            decl: euf_model.func_interp(decl)
            for decl in euf_model.func_decls()
            if decl not in internal_decls
        }
        universes = {sort: euf_model.universe(sort) for sort in euf_model.sorts()}
        return Model(self._ctx, values, functions=functions, universes=universes)

    def unsat_core(self) -> list[Expr]:
        """Return the assumption subset responsible for the last ``UNSAT``."""
        return list(self._unsat_core)

    def assertions(self) -> list[Expr]:
        """Return all currently active asserted formulas in insertion order."""
        return [formula for scope in self._assertions_by_scope for formula in scope]

    def statistics(self) -> dict[str, int]:
        """Return merged SAT, EUF, LRA/LIA, and Array search counters."""
        stats: dict[str, int] = {
            k: v for k, v in self._sat.statistics().items() if isinstance(v, int)
        }
        stats.update(self._euf.stats.to_dict())
        stats.update(self._lra.stats.to_dict())
        stats.update(self._arrays.stats.to_dict())
        return stats


__all__ = ["SMTSolver", "SolveResult"]
