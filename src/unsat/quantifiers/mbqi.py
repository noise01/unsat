"""Model-Based Quantifier Instantiation (MBQI) verification & refinement.

Depends on: ``syntax``, ``model``, ``theories``, ``quantifiers.base``.
"""

from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from unsat.model import FuncInterp, Model
from unsat.quantifiers.base import (
    QuantifierBudget,
    QuantifierStats,
    SubSolver,
    SubSolverStatus,
)
from unsat.syntax import (
    App,
    Const,
    Context,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
    SortKind,
    collect_func_decls,
    instantiate_quantifier,
    iter_subexprs,
)
from unsat.theories import EUFSolver


@dataclass(frozen=True, slots=True)
class MBQIResult:
    """Outcome of one MBQI model-checking & counterexample-refinement step."""

    verified: bool
    model: Model | None
    instantiations: tuple[tuple[Quantifier, tuple[Expr, ...], Expr], ...]
    budget_exhausted: bool = False


def _default_expr_for_model(model: Model, sort: Sort) -> Expr:
    chain: list[Sort] = []
    cur = sort
    while cur.kind is SortKind.ARRAY:
        chain.append(cur.index_sort)
        cur = cur.element_sort
    if cur.kind is SortKind.BOOL:
        elem: Expr = model.ctx.mk_false()
    elif cur.kind is SortKind.INT:
        elem = model.ctx.mk_int_val(0)
    elif cur.kind is SortKind.REAL:
        elem = model.ctx.mk_real_val(0)
    elif cur.kind is SortKind.BITVEC:
        elem = model.ctx.mk_bv_val(0, cur.size)
    else:
        univ = model.universe(cur)
        elem = univ[0] if univ else model.ctx.mk_domain_val(cur, 0)
    for idx_sort in reversed(chain):
        elem = model.ctx.mk_const_array(idx_sort, elem)
    return elem


def _interpret_under_model(
    ctx: Context,
    expr: Expr,
    model: Model,
    bound_consts: set[Expr],
) -> Expr | None:
    """Interpret non-bound symbols & UFs in ``expr`` under ``model``."""
    memo: dict[Expr, Expr] = {}
    for node in iter_subexprs(expr):
        if isinstance(node, Quantifier):
            return None
        if isinstance(node, Const) or node in bound_consts:
            memo[node] = node
            continue
        if not isinstance(node, App):
            memo[node] = node
            continue
        if node.is_const_symbol:
            memo[node] = model.eval(node, model_completion=True)
            continue

        eval_args = [memo[arg] for arg in node.args]
        if node.decl.is_uninterpreted:
            if model.has_func_interp(node.decl):
                interp = model.func_interp(node.decl)
                res = interp.else_value
                for key_args, val_expr in reversed(interp.entries()):
                    cond = ctx.mk_and(*(ctx.mk_eq(ea, ka) for ea, ka in zip(eval_args, key_args, strict=True)))
                    res = ctx.mk_ite(cond, val_expr, res)
                memo[node] = res
            else:
                memo[node] = _default_expr_for_model(model, node.decl.range_sort)
        else:
            memo[node] = ctx.mk_app(node.decl, *eval_args)
    return memo[expr]


class MBQIEngine:
    """Model-Based Quantifier Instantiation with finite-model verification."""

    def __init__(self) -> None:
        self._witness_by_val: dict[tuple[Sort, Expr], App] = {}
        self._internal_decls: set[FuncDecl] = set()
        self._witness_seq = 0

    @property
    def internal_decls(self) -> frozenset[FuncDecl]:
        """Witness declarations synthesized for uninterpreted-sort instances."""
        return frozenset(self._internal_decls)

    def _fresh_witness_for_domain(self, ctx: Context, sort: Sort, domain_val: Expr, reserved_names: set[str]) -> App:
        key = (sort, domain_val)
        existing = self._witness_by_val.get(key)
        if existing is not None:
            return existing
        while True:
            name = f"__mbqi_dom!{self._witness_seq}"
            self._witness_seq += 1
            if name not in reserved_names:
                reserved_names.add(name)
                witness = ctx.mk_const(name, sort)
                self._witness_by_val[key] = witness
                self._internal_decls.add(witness.decl)
                return witness

    def _candidate_models(self, model: Model, quantifiers: Sequence[Quantifier]) -> list[Model]:
        """Generate ``model`` plus safe ``else_value`` generalizations."""
        candidates = [model]
        func_decls = model.func_decls()
        if not func_decls:
            return candidates

        q_funcs: set[FuncDecl] = set()
        for q in quantifiers:
            for decl in collect_func_decls(q):
                if decl.arity >= 1:
                    q_funcs.add(decl)

        relevant = [d for d in func_decls if d in q_funcs] or list(func_decls)
        values = dict(model.items())
        universes = {sort: model.universe(sort) for sort in model.sorts()}

        def _make_variant(else_override: Mapping[FuncDecl, Expr]) -> Model | None:
            new_funcs: dict[FuncDecl, FuncInterp] = {}
            changed = False
            for decl in func_decls:
                interp = model.func_interp(decl)
                alt = else_override.get(decl)
                if alt is not None and alt is not interp.else_value:
                    table = dict(interp.entries())
                    new_funcs[decl] = FuncInterp(decl, table, alt)
                    changed = True
                else:
                    new_funcs[decl] = interp
            if not changed:
                return None
            return Model(model.ctx, values, functions=new_funcs, universes=universes)

        bool_true = {d: model.ctx.mk_true() for d in relevant if d.range_sort.is_bool}
        cand_t = _make_variant(bool_true)
        if cand_t is not None:
            candidates.append(cand_t)

        bool_false = {d: model.ctx.mk_false() for d in relevant if d.range_sort.is_bool}
        cand_f = _make_variant(bool_false)
        if cand_f is not None:
            candidates.append(cand_f)

        entry_override: dict[FuncDecl, Expr] = {}
        for d in relevant:
            entries = model.func_interp(d).entries()
            if entries:
                entry_override[d] = entries[0][1]
        cand_e = _make_variant(entry_override)
        if cand_e is not None:
            candidates.append(cand_e)

        return candidates

    def _map_value_to_ground_term(
        self,
        ctx: Context,
        sort: Sort,
        raw_val: Expr,
        model: Model,
        euf: EUFSolver,
        reserved_names: set[str],
    ) -> Expr:
        # Prefer an existing 0-arity const or canonical representative matching raw_val.
        candidates: list[tuple[tuple[int, int], Expr]] = []
        for rep in euf.terms_of_sort(sort):
            for member in euf.eclass_members(rep):
                if isinstance(member, Const) or (isinstance(member, App) and member.is_const_symbol):
                    mval = model.eval(member, model_completion=True)
                    if mval is raw_val:
                        pri = 0 if (isinstance(member, App) and member.is_const_symbol) else 1
                        candidates.append(((pri, member.id), member))
        if candidates:
            candidates.sort(key=lambda item: item[0])
            return candidates[0][1]
        if sort.kind is not SortKind.UNINTERPRETED:
            return raw_val
        return self._fresh_witness_for_domain(ctx, sort, raw_val, reserved_names)

    def check_and_refine(
        self,
        quantifiers: Sequence[Quantifier],
        model: Model,
        euf: EUFSolver,
        sub_solver: SubSolver,
        budget: QuantifierBudget,
        stats: QuantifierStats,
        *,
        already_emitted: frozenset[tuple[Quantifier, tuple[Expr, ...]]] | None = None,
    ) -> MBQIResult:
        """Verify ``quantifiers`` under model variants or refine counterexamples."""
        if not quantifiers:
            return MBQIResult(True, model, (), budget_exhausted=False)

        ctx = quantifiers[0].ctx
        reserved: set[str] = {d.name for d in model.decls()} | {d.name for d in model.func_decls()}
        for q in quantifiers:
            for d in collect_func_decls(q):
                reserved.add(d.name)

        counterexamples: list[tuple[Quantifier, tuple[Expr, ...]]] = []
        any_unknown = False

        for cand_idx, cand_m in enumerate(self._candidate_models(model, quantifiers)):
            all_verified = True
            for q in quantifiers:
                bconsts: list[App] = []
                domain_constraints: list[Expr] = []
                for idx, sort in enumerate(q.var_sorts):
                    bname = f"__mbqi!{idx}"
                    suffix = 0
                    while bname in reserved:
                        suffix += 1
                        bname = f"__mbqi!{idx}_{suffix}"
                    bc = ctx.mk_const(bname, sort)
                    bconsts.append(bc)
                    if sort.kind is SortKind.UNINTERPRETED:
                        univ = cand_m.universe(sort)
                        if not univ:
                            univ = (ctx.mk_domain_val(sort, 0),)
                        domain_constraints.append(ctx.mk_or(*(ctx.mk_eq(bc, u) for u in univ)))

                inst_body = instantiate_quantifier(q, bconsts)
                interpreted = _interpret_under_model(ctx, inst_body, cand_m, set(bconsts))
                if interpreted is None:
                    all_verified = False
                    any_unknown = True
                    continue

                neg_query = [*domain_constraints, ctx.mk_not(interpreted)]
                status, cex_model = sub_solver.check_formula(neg_query)
                if status is SubSolverStatus.UNSAT:
                    continue
                all_verified = False
                if status is SubSolverStatus.UNKNOWN or cex_model is None:
                    any_unknown = True
                    continue
                if cand_idx == 0:
                    raw_tuple = tuple(cex_model.eval(bc, model_completion=True) for bc in bconsts)
                    counterexamples.append((q, raw_tuple))

            if all_verified:
                stats.mbqi_verified += 1
                return MBQIResult(True, cand_m, (), budget_exhausted=False)

        if not counterexamples:
            return MBQIResult(False, None, (), budget_exhausted=False)

        stats.mbqi_rounds += 1
        emitted_set = set(already_emitted) if already_emitted is not None else set()
        insts: list[tuple[Quantifier, tuple[Expr, ...], Expr]] = []
        truncated = False
        for q, raw_tuple in counterexamples:
            if len(insts) >= budget.max_instantiations:
                truncated = True
                break
            mapped_args = tuple(
                self._map_value_to_ground_term(ctx, sort, raw_val, model, euf, reserved)
                for sort, raw_val in zip(q.var_sorts, raw_tuple, strict=True)
            )
            rep_key = (q, tuple(euf.rep_expr(arg) for arg in mapped_args))
            if rep_key in emitted_set:
                mixed_args = tuple(
                    raw_v if sort.kind is not SortKind.UNINTERPRETED else m_v
                    for sort, raw_v, m_v in zip(q.var_sorts, raw_tuple, mapped_args, strict=True)
                )
                conc_key = (q, tuple(euf.rep_expr(arg) for arg in mixed_args))
                if conc_key not in emitted_set:
                    mapped_args = mixed_args
                    rep_key = conc_key
                else:
                    continue
            emitted_set.add(rep_key)
            insts.append((q, mapped_args, instantiate_quantifier(q, mapped_args)))
            stats.mbqi_instantiations += 1

        if truncated or not insts:
            stats.budget_exhausted += 1
            return MBQIResult(False, None, tuple(insts), budget_exhausted=True)

        return MBQIResult(False, None, tuple(insts), budget_exhausted=any_unknown)
