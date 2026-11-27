"""Lazy Theory of Arrays solver cooperating with EUF & MBTC.

Implements McCarthy Read-over-Write (RoW1, RoW2-down, RoW2-up), constant-array
consistency (``(as const (Array I E))``), extensionality lemma generation with
cached witness constants, and concrete finite-override model synthesis.

Depends on: ``syntax``, ``model``, ``theories.base``, ``theories.euf``.
"""

from collections import deque
from collections.abc import Callable, Mapping
from dataclasses import dataclass

from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl, Sort, SortKind
from unsat.theories.base import ArrayStats, TheoryLit
from unsat.theories.euf import EUFSolver


@dataclass(frozen=True, slots=True)
class ArrayLemma:
    """Conditional array axiom lemma ``(reasons => formula)``."""

    reasons: tuple[TheoryLit, ...]
    formula: Expr


def _array_depth(sort: Sort) -> int:
    depth = 0
    stack: list[tuple[Sort, int]] = [(sort, 0)]
    while stack:
        cur, d = stack.pop()
        if cur.kind is SortKind.ARRAY:
            nxt = d + 1
            if nxt > depth:
                depth = nxt
            stack.append((cur.index_sort, nxt))
            stack.append((cur.element_sort, nxt))
    return depth


class ArraySolver:
    """On-demand lazy axiom generator and model synthesizer for SMT arrays."""

    def __init__(self, ctx: Context) -> None:
        self._ctx = ctx
        self._stats = ArrayStats()

        self._registered: set[Expr] = set()
        self._arrays_by_sort: dict[Sort, list[Expr]] = {}
        self._selects: list[App] = []
        self._select_set: set[App] = set()
        self._stores: list[App] = []
        self._store_set: set[App] = set()
        self._const_arrays: list[App] = []
        self._const_set: set[App] = set()

        self._ext_witness: dict[tuple[Expr, Expr], App] = {}
        self._internal_decls: set[FuncDecl] = set()

    @property
    def ctx(self) -> Context:
        """AST context associated with this array solver."""
        return self._ctx

    @property
    def stats(self) -> ArrayStats:
        """Instrumentation counters for RoW, const-array, and extensionality."""
        return self._stats

    @property
    def internal_decls(self) -> set[FuncDecl]:
        """Witness declarations introduced by array extensionality."""
        return self._internal_decls

    def register_term(self, term: Expr) -> None:
        """Register an array term or ``select``/``store``/``const_array`` app."""
        if term.ctx is not self._ctx:
            msg = f"Expr '{term}' belongs to a different Context"
            raise ValueError(msg)
        if term in self._registered:
            return

        stack: list[Expr] = [term]
        while stack:
            node = stack.pop()
            if node in self._registered:
                continue
            self._registered.add(node)
            if node.is_array:
                self._arrays_by_sort.setdefault(node.sort, []).append(node)
            if isinstance(node, App):
                kind = node.decl.kind
                if kind is DeclKind.SELECT and node not in self._select_set:
                    self._select_set.add(node)
                    self._selects.append(node)
                elif kind is DeclKind.STORE and node not in self._store_set:
                    self._store_set.add(node)
                    self._stores.append(node)
                elif kind is DeclKind.CONST_ARRAY and node not in self._const_set:
                    self._const_set.add(node)
                    self._const_arrays.append(node)
                for arg in reversed(node.args):
                    if arg not in self._registered and (
                        arg.is_array
                        or (
                            isinstance(arg, App)
                            and arg.decl.kind
                            in (DeclKind.SELECT, DeclKind.STORE, DeclKind.CONST_ARRAY)
                        )
                    ):
                        stack.append(arg)

    def _get_ext_witness(self, a: Expr, b: Expr) -> App:
        key = (a, b) if a.id <= b.id else (b, a)
        existing = self._ext_witness.get(key)
        if existing is not None:
            return existing
        idx_sort = key[0].sort.index_sort
        name = f"__arr_ext!{key[0].id}!{key[1].id}"
        witness = self._ctx.mk_const(name, idx_sort)
        self._ext_witness[key] = witness
        self._internal_decls.add(witness.decl)
        return witness

    def check(self, euf: EUFSolver) -> list[ArrayLemma]:
        """Inspect current EUF classes and emit missing array axiom lemmas."""
        self._stats.checks += 1
        lemmas: list[ArrayLemma] = []
        seen: set[tuple[tuple[TheoryLit, ...], Expr]] = set()

        def _add(reasons: tuple[TheoryLit, ...], formula: Expr) -> bool:
            if formula is self._ctx.true_expr:
                return False
            sig = (reasons, formula)
            if sig in seen:
                return False
            seen.add(sig)
            lemmas.append(ArrayLemma(reasons, formula))
            return True

        # 1. RoW1-self & store equivalence-class member reads.
        for st in self._stores:
            _, idx, val = st.args
            sel_self = self._ctx.mk_select(st, idx)
            if not euf.are_equal(sel_self, val) and _add(
                (), self._ctx.mk_eq(sel_self, val)
            ):
                self._stats.row1_lemmas += 1
            rep = euf.rep_expr(st)
            for member in sorted(euf.eclass_members(rep), key=lambda t: t.id):
                if member is st:
                    continue
                sel_m = self._ctx.mk_select(member, idx)
                if not euf.are_equal(sel_m, val):
                    reasons = tuple(dict.fromkeys(euf.explain_terms_equal(st, member)))
                    if _add(reasons, self._ctx.mk_eq(sel_m, val)):
                        self._stats.row1_lemmas += 1

        # 2. RoW1 & RoW2-down: select(b, j) where b == store(a, i, v).
        for sel in self._selects:
            b, j = sel.args
            rep_b = euf.rep_expr(b)
            for st in self._stores:
                if st.sort is not b.sort or euf.rep_expr(st) is not rep_b:
                    continue
                a, i, v = st.args
                base_reasons = euf.explain_terms_equal(b, st)
                if euf.are_equal(i, j):
                    if not euf.are_equal(sel, v):
                        reasons = tuple(
                            dict.fromkeys(
                                [*base_reasons, *euf.explain_terms_equal(i, j)]
                            )
                        )
                        if _add(reasons, self._ctx.mk_eq(sel, v)):
                            self._stats.row1_lemmas += 1
                else:
                    sel_a = self._ctx.mk_select(a, j)
                    if not euf.are_equal(sel, sel_a):
                        formula = self._ctx.mk_or(
                            self._ctx.mk_eq(i, j),
                            self._ctx.mk_eq(sel, sel_a),
                        )
                        if _add(tuple(dict.fromkeys(base_reasons)), formula):
                            self._stats.row2_lemmas += 1

        # 3. RoW2-up: select(b, j) where b == a in store(a, i, v).
        for sel in self._selects:
            b, j = sel.args
            rep_b = euf.rep_expr(b)
            for st in self._stores:
                a, i, _ = st.args
                if a.sort is not b.sort or euf.rep_expr(a) is not rep_b:
                    continue
                if euf.are_equal(i, j):
                    continue
                sel_s = self._ctx.mk_select(st, j)
                if not euf.are_equal(sel, sel_s):
                    base_reasons = tuple(dict.fromkeys(euf.explain_terms_equal(b, a)))
                    formula = self._ctx.mk_or(
                        self._ctx.mk_eq(i, j),
                        self._ctx.mk_eq(sel, sel_s),
                    )
                    if _add(base_reasons, formula):
                        self._stats.row2_lemmas += 1

        # 3b. Propagate Const-index reads across transparent Const stores.
        self._propagate_const_index_reads(euf, _add)

        if lemmas:
            return lemmas

        # 4. Constant-array consistency.
        if self._const_arrays:
            self._check_const_arrays(euf, _add)
        if lemmas:
            return lemmas

        # 5. Extensionality across distinct array EUF classes.
        self._check_extensionality(euf, _add)
        return lemmas

    def _check_const_arrays(
        self,
        euf: EUFSolver,
        emit,
    ) -> None:
        for sel in self._selects:
            b, _ = sel.args
            rep_b = euf.rep_expr(b)
            for c_arr in self._const_arrays:
                if c_arr.sort is b.sort and euf.rep_expr(c_arr) is rep_b:
                    v = c_arr.args[0]
                    if not euf.are_equal(sel, v):
                        reasons = tuple(
                            dict.fromkeys(euf.explain_terms_equal(b, c_arr))
                        )
                        if emit(reasons, self._ctx.mk_eq(sel, v)):
                            self._stats.const_lemmas += 1

        for idx, c1 in enumerate(self._const_arrays):
            rep1 = euf.rep_expr(c1)
            for c2 in self._const_arrays[idx + 1 :]:
                if (
                    c1.sort is c2.sort
                    and euf.rep_expr(c2) is rep1
                    and not euf.are_equal(c1.args[0], c2.args[0])
                ):
                    reasons = tuple(dict.fromkeys(euf.explain_terms_equal(c1, c2)))
                    if emit(reasons, self._ctx.mk_eq(c1.args[0], c2.args[0])):
                        self._stats.const_lemmas += 1

        for st in self._stores:
            rep_s = euf.rep_expr(st)
            v_s = st.args[2]
            for c_arr in self._const_arrays:
                if st.sort is c_arr.sort and euf.rep_expr(c_arr) is rep_s:
                    v_c = c_arr.args[0]
                    if not euf.are_equal(v_s, v_c):
                        reasons = tuple(
                            dict.fromkeys(euf.explain_terms_equal(st, c_arr))
                        )
                        if emit(reasons, self._ctx.mk_eq(v_s, v_c)):
                            self._stats.const_lemmas += 1

        # Store-connected components containing multiple constant arrays.
        consts_by_sort: dict[Sort, list[App]] = {}
        for c_arr in self._const_arrays:
            consts_by_sort.setdefault(c_arr.sort, []).append(c_arr)

        for sort, sort_consts in consts_by_sort.items():
            if len(sort_consts) < 2:
                continue
            adj: dict[Expr, list[tuple[Expr, Expr, Expr]]] = {}
            for st in self._stores:
                if st.sort is not sort:
                    continue
                a = st.args[0]
                rep_a = euf.rep_expr(a)
                rep_s = euf.rep_expr(st)
                adj.setdefault(rep_a, []).append((rep_s, a, st))
                adj.setdefault(rep_s, []).append((rep_a, st, a))

            visited: set[Expr] = set()
            for start_c in sort_consts:
                start_rep = euf.rep_expr(start_c)
                if start_rep in visited:
                    continue
                comp_reps: set[Expr] = set()
                queue: deque[Expr] = deque([start_rep])
                visited.add(start_rep)
                while queue:
                    cur = queue.popleft()
                    comp_reps.add(cur)
                    for nxt_rep, _, _ in adj.get(cur, ()):
                        if nxt_rep not in visited:
                            visited.add(nxt_rep)
                            queue.append(nxt_rep)

                comp_consts = [c for c in sort_consts if euf.rep_expr(c) in comp_reps]
                if len(comp_consts) < 2:
                    continue

                comp_stores = [
                    st
                    for st in self._stores
                    if st.sort is sort and euf.rep_expr(st) in comp_reps
                ]
                idx_sort = sort.index_sort
                finite_size: int | None = None
                if idx_sort.is_bool:
                    finite_size = 2
                elif idx_sort.is_bv and idx_sort.size <= 8:
                    finite_size = 1 << idx_sort.size

                if finite_size is None or len(comp_stores) < finite_size:
                    c1 = comp_consts[0]
                    for c2 in comp_consts[1:]:
                        if euf.are_equal(c1.args[0], c2.args[0]):
                            continue
                        path_reasons = self._explain_store_path(euf, adj, c1, c2)
                        if path_reasons is not None and emit(
                            path_reasons, self._ctx.mk_eq(c1.args[0], c2.args[0])
                        ):
                            self._stats.const_lemmas += 1
                else:
                    domain_elems: tuple[Expr, ...] = (
                        (self._ctx.false_expr, self._ctx.true_expr)
                        if idx_sort.is_bool
                        else tuple(
                            self._ctx.mk_bv_val(i, idx_sort.size)
                            for i in range(finite_size)
                        )
                    )
                    for st in comp_stores:
                        rep_s = euf.rep_expr(st)
                        for c_arr in comp_consts:
                            if euf.rep_expr(c_arr) is not rep_s:
                                continue
                            reasons = tuple(
                                dict.fromkeys(euf.explain_terms_equal(st, c_arr))
                            )
                            v_c = c_arr.args[0]
                            for elem in domain_elems:
                                sel_e = self._ctx.mk_select(st, elem)
                                if not euf.are_equal(sel_e, v_c) and emit(
                                    reasons, self._ctx.mk_eq(sel_e, v_c)
                                ):
                                    self._stats.const_lemmas += 1
                        a_st, i_st, v_st = st.args
                        for elem in domain_elems:
                            sel_e = self._ctx.mk_select(st, elem)
                            if euf.are_equal(i_st, elem):
                                if not euf.are_equal(sel_e, v_st):
                                    reasons = tuple(
                                        dict.fromkeys(
                                            euf.explain_terms_equal(i_st, elem)
                                        )
                                    )
                                    if emit(reasons, self._ctx.mk_eq(sel_e, v_st)):
                                        self._stats.const_lemmas += 1
                            else:
                                sel_a = self._ctx.mk_select(a_st, elem)
                                if not euf.are_equal(sel_e, sel_a):
                                    formula = self._ctx.mk_or(
                                        self._ctx.mk_eq(i_st, elem),
                                        self._ctx.mk_eq(sel_e, sel_a),
                                    )
                                    if emit((), formula):
                                        self._stats.const_lemmas += 1

    @staticmethod
    def _explain_store_path(
        euf: EUFSolver,
        adj: dict[Expr, list[tuple[Expr, Expr, Expr]]],
        src_c: App,
        dst_c: App,
    ) -> tuple[TheoryLit, ...] | None:
        src_rep = euf.rep_expr(src_c)
        dst_rep = euf.rep_expr(dst_c)
        if src_rep is dst_rep:
            return tuple(dict.fromkeys(euf.explain_terms_equal(src_c, dst_c)))

        parent: dict[Expr, tuple[Expr, Expr, Expr]] = {}
        seen: set[Expr] = {src_rep}
        queue: deque[Expr] = deque([src_rep])
        while queue:
            cur = queue.popleft()
            if cur is dst_rep:
                break
            for nxt_rep, from_term, to_term in adj.get(cur, ()):
                if nxt_rep not in seen:
                    seen.add(nxt_rep)
                    parent[nxt_rep] = (cur, from_term, to_term)
                    queue.append(nxt_rep)

        if dst_rep not in parent:
            return None

        edges: list[tuple[Expr, Expr]] = []
        walk = dst_rep
        while walk is not src_rep:
            prev, from_term, to_term = parent[walk]
            edges.append((from_term, to_term))
            walk = prev
        edges.reverse()

        reasons: list[TheoryLit] = []
        cur_node: Expr = src_c
        for from_term, to_term in edges:
            reasons.extend(euf.explain_terms_equal(cur_node, from_term))
            cur_node = to_term
        reasons.extend(euf.explain_terms_equal(cur_node, dst_c))
        return tuple(dict.fromkeys(reasons))

    def _propagate_const_index_reads(
        self,
        euf: EUFSolver,
        emit: Callable[[tuple[TheoryLit, ...], Expr], bool],
    ) -> None:
        """Bridge ``Const``-index reads across ``store(_, Const, _)`` nodes.

        ``Context.mk_select`` eagerly simplifies ``select(store(a, c1, v), c2)``
        for distinct ``Const`` indices ``c1 != c2`` to ``select(a, c2)`` and
        ``select(store(a, c, v), c)`` to ``v``. That bypasses EUF equalities on
        intermediate ``store`` terms; this pass restores propagation across
        transparent ``Const`` store edges.
        """
        seeds: dict[tuple[Sort, Expr], list[tuple[Expr, Expr, bool]]] = {}
        for sel in self._selects:
            b, j = sel.args
            if isinstance(j, Const):
                seeds.setdefault((b.sort, j), []).append((b, sel, False))
        for st in self._stores:
            _, i, v = st.args
            if isinstance(i, Const):
                seeds.setdefault((st.sort, i), []).append((st, v, True))
        if not seeds:
            return

        stores_by_sort: dict[Sort, list[App]] = {}
        stores_by_res_rep: dict[Sort, dict[Expr, list[App]]] = {}
        stores_by_base_rep: dict[Sort, dict[Expr, list[App]]] = {}
        for st in self._stores:
            sort = st.sort
            stores_by_sort.setdefault(sort, []).append(st)
            stores_by_res_rep.setdefault(sort, {}).setdefault(
                euf.rep_expr(st), []
            ).append(st)
            stores_by_base_rep.setdefault(sort, {}).setdefault(
                euf.rep_expr(st.args[0]), []
            ).append(st)

        consts_by_sort_rep: dict[Sort, dict[Expr, list[App]]] = {}
        for c_arr in self._const_arrays:
            consts_by_sort_rep.setdefault(c_arr.sort, {}).setdefault(
                euf.rep_expr(c_arr), []
            ).append(c_arr)

        selects_by_sort_rep: dict[Sort, dict[Expr, list[App]]] = {}
        for sel in self._selects:
            arr_arg = sel.args[0]
            selects_by_sort_rep.setdefault(arr_arg.sort, {}).setdefault(
                euf.rep_expr(arr_arg), []
            ).append(sel)

        for (sort, j), seed_list in seeds.items():
            adj_j: dict[Expr, list[tuple[Expr, Expr, Expr]]] = {}
            for st in stores_by_sort.get(sort, ()):
                a, i, _ = st.args
                if isinstance(i, Const) and i is not j:
                    rep_a = euf.rep_expr(a)
                    rep_s = euf.rep_expr(st)
                    if rep_a is not rep_s:
                        adj_j.setdefault(rep_a, []).append((rep_s, a, st))
                        adj_j.setdefault(rep_s, []).append((rep_a, st, a))

            sort_consts = consts_by_sort_rep.get(sort, {})
            sort_selects = selects_by_sort_rep.get(sort, {})
            sort_stores_res = stores_by_res_rep.get(sort, {})
            sort_stores_base = stores_by_base_rep.get(sort, {})

            for src_arr, src_val, is_store_self in seed_list:
                start_rep = euf.rep_expr(src_arr)
                parent: dict[Expr, tuple[Expr, Expr, Expr]] = {}
                reached: list[Expr] = [start_rep]
                seen: set[Expr] = {start_rep}
                queue: deque[Expr] = deque([start_rep])
                while queue:
                    cur = queue.popleft()
                    for nxt_rep, from_term, to_term in adj_j.get(cur, ()):
                        if nxt_rep not in seen:
                            seen.add(nxt_rep)
                            parent[nxt_rep] = (cur, from_term, to_term)
                            reached.append(nxt_rep)
                            queue.append(nxt_rep)

                def _explain(
                    target_rep: Expr,
                    target_term: Expr,
                    *,
                    _start_rep: Expr = start_rep,
                    _src_arr: Expr = src_arr,
                    _parent: dict[Expr, tuple[Expr, Expr, Expr]] = parent,
                ) -> tuple[TheoryLit, ...]:
                    if target_rep is _start_rep:
                        return tuple(
                            dict.fromkeys(
                                euf.explain_terms_equal(_src_arr, target_term)
                            )
                        )
                    edges: list[tuple[Expr, Expr]] = []
                    walk = target_rep
                    while walk is not _start_rep:
                        prev, from_term, to_term = _parent[walk]
                        edges.append((from_term, to_term))
                        walk = prev
                    edges.reverse()
                    reasons: list[TheoryLit] = []
                    cur_node = _src_arr
                    for from_term, to_term in edges:
                        reasons.extend(euf.explain_terms_equal(cur_node, from_term))
                        cur_node = to_term
                    reasons.extend(euf.explain_terms_equal(cur_node, target_term))
                    return tuple(dict.fromkeys(reasons))

                for target_rep in reached:
                    if target_rep is start_rep:
                        if is_store_self:
                            for st_up in sort_stores_base.get(target_rep, ()):
                                a2, i2, _ = st_up.args
                                if isinstance(i2, Const) or euf.are_equal(i2, j):
                                    continue
                                sel_up = self._ctx.mk_select(st_up, j)
                                if not euf.are_equal(src_val, sel_up):
                                    formula = self._ctx.mk_or(
                                        self._ctx.mk_eq(i2, j),
                                        self._ctx.mk_eq(src_val, sel_up),
                                    )
                                    if emit(_explain(target_rep, a2), formula):
                                        self._stats.row2_lemmas += 1
                        continue

                    for c_arr in sort_consts.get(target_rep, ()):
                        v_c = c_arr.args[0]
                        if not euf.are_equal(src_val, v_c) and emit(
                            _explain(target_rep, c_arr),
                            self._ctx.mk_eq(src_val, v_c),
                        ):
                            self._stats.const_lemmas += 1

                    for sel2 in sort_selects.get(target_rep, ()):
                        b2, j2 = sel2.args
                        if euf.are_equal(j2, j) and not euf.are_equal(src_val, sel2):
                            reasons = tuple(
                                dict.fromkeys(
                                    [
                                        *_explain(target_rep, b2),
                                        *euf.explain_terms_equal(j, j2),
                                    ]
                                )
                            )
                            if emit(reasons, self._ctx.mk_eq(src_val, sel2)):
                                self._stats.row2_lemmas += 1

                    for st2 in sort_stores_res.get(target_rep, ()):
                        _, i2, v2 = st2.args
                        if euf.are_equal(i2, j):
                            if not euf.are_equal(src_val, v2):
                                reasons = tuple(
                                    dict.fromkeys(
                                        [
                                            *_explain(target_rep, st2),
                                            *euf.explain_terms_equal(i2, j),
                                        ]
                                    )
                                )
                                if emit(reasons, self._ctx.mk_eq(src_val, v2)):
                                    self._stats.row1_lemmas += 1
                        elif not isinstance(i2, Const):
                            sel_st2 = self._ctx.mk_select(st2, j)
                            if not euf.are_equal(src_val, sel_st2) and emit(
                                _explain(target_rep, st2),
                                self._ctx.mk_eq(src_val, sel_st2),
                            ):
                                self._stats.row2_lemmas += 1

                    for st_up in sort_stores_base.get(target_rep, ()):
                        a2, i2, _ = st_up.args
                        if isinstance(i2, Const) or euf.are_equal(i2, j):
                            continue
                        sel_up = self._ctx.mk_select(st_up, j)
                        if not euf.are_equal(src_val, sel_up):
                            formula = self._ctx.mk_or(
                                self._ctx.mk_eq(i2, j),
                                self._ctx.mk_eq(src_val, sel_up),
                            )
                            if emit(_explain(target_rep, a2), formula):
                                self._stats.row2_lemmas += 1

    def _check_extensionality(self, euf: EUFSolver, emit) -> None:
        const_val_by_rep: dict[Expr, Expr] = {}
        for c_arr in self._const_arrays:
            const_val_by_rep.setdefault(
                euf.rep_expr(c_arr), euf.rep_expr(c_arr.args[0])
            )

        reads_by_rep: dict[Expr, dict[Expr, Expr]] = {}
        for sel in self._selects:
            arr_rep = euf.rep_expr(sel.args[0])
            idx_rep = euf.rep_expr(sel.args[1])
            reads_by_rep.setdefault(arr_rep, {}).setdefault(idx_rep, sel)

        for sort in sorted(self._arrays_by_sort, key=lambda s: s.id):
            terms = self._arrays_by_sort[sort]
            groups: dict[Expr, list[Expr]] = {}
            for term in terms:
                groups.setdefault(euf.rep_expr(term), []).append(term)
            rep_list = list(groups)
            if len(rep_list) < 2:
                continue

            for idx, r1 in enumerate(rep_list):
                reads1 = reads_by_rep.get(r1, {})
                cval1 = const_val_by_rep.get(r1)
                leader1 = min(groups[r1], key=lambda t: t.id)
                for r2 in rep_list[idx + 1 :]:
                    reads2 = reads_by_rep.get(r2, {})
                    cval2 = const_val_by_rep.get(r2)
                    witnessed = False
                    for j_rep, sel1 in reads1.items():
                        sel2 = reads2.get(j_rep)
                        if sel2 is not None:
                            if euf.rep_expr(sel1) is not euf.rep_expr(sel2):
                                witnessed = True
                                break
                        elif cval2 is not None and euf.rep_expr(sel1) is not cval2:
                            witnessed = True
                            break
                    if not witnessed and cval1 is not None:
                        for sel2 in reads2.values():
                            if euf.rep_expr(sel2) is not cval1:
                                witnessed = True
                                break
                    if witnessed:
                        continue

                    leader2 = min(groups[r2], key=lambda t: t.id)
                    witness = self._get_ext_witness(leader1, leader2)
                    sel_1 = self._ctx.mk_select(leader1, witness)
                    sel_2 = self._ctx.mk_select(leader2, witness)
                    formula = self._ctx.mk_or(
                        self._ctx.mk_eq(leader1, leader2),
                        self._ctx.mk_not(self._ctx.mk_eq(sel_1, sel_2)),
                    )
                    if emit((), formula):
                        self._stats.ext_lemmas += 1

    def build_array_values(
        self,
        euf: EUFSolver,
        concrete_values: Mapping[Expr, Expr],
    ) -> dict[Expr, Expr]:
        """Construct concrete ``store``/``const_array`` AST values for array terms."""
        resolved: dict[Expr, Expr] = dict(concrete_values)
        rep_scalar: dict[Expr, Expr] = {}
        for expr, val in resolved.items():
            if not expr.is_array:
                rep_scalar.setdefault(euf.rep_expr(expr), val)

        def _default_for(sort: Sort) -> Expr:
            chain: list[Sort] = []
            cur = sort
            while cur.kind is SortKind.ARRAY:
                chain.append(cur.index_sort)
                cur = cur.element_sort
            if cur.kind is SortKind.BOOL:
                elem: Expr = self._ctx.mk_false()
            elif cur.kind is SortKind.INT:
                elem = self._ctx.mk_int_val(0)
            elif cur.kind is SortKind.REAL:
                elem = self._ctx.mk_real_val(0)
            elif cur.kind is SortKind.BITVEC:
                elem = self._ctx.mk_bv_val(0, cur.size)
            else:
                elem = self._ctx.mk_domain_val(cur, 0)
            for idx_s in reversed(chain):
                elem = self._ctx.mk_const_array(idx_s, elem)
            return elem

        def _resolve_val(expr: Expr) -> Expr:
            if expr in resolved:
                return resolved[expr]
            rep = euf.rep_expr(expr)
            if rep in resolved:
                return resolved[rep]
            if rep in rep_scalar:
                return rep_scalar[rep]
            if isinstance(expr, Const):
                return expr
            if expr.is_bool:
                return (
                    self._ctx.mk_true()
                    if euf.are_equal(expr, self._ctx.true_expr)
                    else self._ctx.mk_false()
                )
            return _default_for(expr.sort)

        sorted_sorts = sorted(
            self._arrays_by_sort, key=lambda s: (_array_depth(s), s.id)
        )
        out: dict[Expr, Expr] = {}

        for sort in sorted_sorts:
            terms = self._arrays_by_sort[sort]
            groups: dict[Expr, list[Expr]] = {}
            for term in terms:
                groups.setdefault(euf.rep_expr(term), []).append(term)

            adj: dict[Expr, list[Expr]] = {}
            for st in self._stores:
                if st.sort is sort:
                    ra = euf.rep_expr(st.args[0])
                    rs = euf.rep_expr(st)
                    adj.setdefault(ra, []).append(rs)
                    adj.setdefault(rs, []).append(ra)

            consts_for_sort = [c for c in self._const_arrays if c.sort is sort]
            comp_default: dict[Expr, Expr] = {}
            comp_nodes: list[list[Expr]] = []
            visited: set[Expr] = set()
            for r in groups:
                if r in visited:
                    continue
                comp: list[Expr] = []
                q: deque[Expr] = deque([r])
                visited.add(r)
                while q:
                    cur = q.popleft()
                    comp.append(cur)
                    for nxt in adj.get(cur, ()):
                        if nxt not in visited:
                            visited.add(nxt)
                            q.append(nxt)
                comp_nodes.append(comp)
                comp_set = set(comp)
                dflt: Expr | None = None
                for c_arr in consts_for_sort:
                    if euf.rep_expr(c_arr) in comp_set:
                        dflt = _resolve_val(c_arr.args[0])
                        break
                if dflt is None:
                    dflt = _default_for(sort.element_sort)
                for cr in comp:
                    comp_default[cr] = dflt

            val_at: dict[Expr, dict[Expr, Expr]] = {r: {} for r in groups}
            for sel in self._selects:
                if sel.args[0].sort is sort:
                    r_arr = euf.rep_expr(sel.args[0])
                    if r_arr in val_at:
                        val_at[r_arr][_resolve_val(sel.args[1])] = _resolve_val(sel)
            sort_stores: list[tuple[Expr, Expr, Expr, Expr]] = []
            for st in self._stores:
                if st.sort is sort:
                    r_a = euf.rep_expr(st.args[0])
                    r_s = euf.rep_expr(st)
                    k_i = _resolve_val(st.args[1])
                    v_i = _resolve_val(st.args[2])
                    val_at.setdefault(r_s, {})[k_i] = v_i
                    sort_stores.append((r_a, r_s, k_i, v_i))

            for comp in comp_nodes:
                comp_set = set(comp)
                comp_edges = [
                    (ra, rs, ki) for ra, rs, ki, _ in sort_stores if rs in comp_set
                ]
                for _ in range(len(comp) + 1):
                    changed = False
                    for ra, rs, ki in comp_edges:
                        map_a = val_at.setdefault(ra, {})
                        map_s = val_at.setdefault(rs, {})
                        for k, v in list(map_a.items()):
                            if k is not ki and k not in map_s:
                                map_s[k] = v
                                changed = True
                        for k, v in list(map_s.items()):
                            if k is not ki and k not in map_a:
                                map_a[k] = v
                                changed = True
                    if not changed:
                        break

            for r, members in groups.items():
                default_val = comp_default[r]
                entries = val_at.get(r, {})
                filtered = {k: v for k, v in entries.items() if v is not default_val}
                arr_val: Expr = self._ctx.mk_const_array(sort.index_sort, default_val)
                for k in sorted(filtered, key=lambda e: e.id):
                    arr_val = self._ctx.mk_store(arr_val, k, filtered[k])

                resolved[r] = arr_val
                for m in members:
                    resolved[m] = arr_val
                    out[m] = arr_val

        return out
