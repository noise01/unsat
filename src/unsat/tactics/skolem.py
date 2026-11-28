"""NNF Skolemization and prenex universal hoisting tactics."""

from collections.abc import Iterable, Sequence

from unsat.model import ProjectionModelConverter
from unsat.syntax import (
    App,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
    collect_func_decls,
    free_bound_var_indices,
    instantiate_quantifier,
    shift_bound_vars,
)
from unsat.tactics.base import TacticResult
from unsat.tactics.nnf import to_nnf


def _pull_foralls(ctx: Context, is_and: bool, args: list[Expr]) -> Expr:
    comb_names: list[str] = []
    comb_sorts: list[Sort] = []
    per_arg_k: list[int] = []
    for arg in args:
        if isinstance(arg, Quantifier) and arg.is_forall:
            comb_names.extend(arg.var_names)
            comb_sorts.extend(arg.var_sorts)
            per_arg_k.append(arg.num_vars)
        else:
            per_arg_k.append(0)

    k_total = sum(per_arg_k)
    if k_total == 0:
        return ctx.mk_and(*args) if is_and else ctx.mk_or(*args)

    shifted_args: list[Expr] = []
    comb_pats: list[tuple[Expr, ...]] = []
    before = 0
    for arg, k_j in zip(args, per_arg_k, strict=True):
        after = k_total - before - k_j
        if k_j == 0:
            shifted_args.append(shift_bound_vars(arg, k_total))
        else:
            assert isinstance(arg, Quantifier)
            body1 = shift_bound_vars(arg.body, before, cutoff=k_j)
            body2 = shift_bound_vars(body1, after)
            shifted_args.append(body2)
            for pat in arg.patterns:
                shifted_pat = tuple(shift_bound_vars(shift_bound_vars(term, before, cutoff=k_j), after) for term in pat)
                comb_pats.append(shifted_pat)
        before += k_j

    joined = ctx.mk_and(*shifted_args) if is_and else ctx.mk_or(*shifted_args)
    return ctx.mk_quantifier(True, comb_names, comb_sorts, joined, patterns=comb_pats)


def _skolemize_nnf(
    ctx: Context,
    root: Expr,
    used_names: set[str],
    prefix: str,
    created_decls: set[FuncDecl],
) -> Expr:
    seq = 0

    def _fresh_skolem_decl(domain: tuple[Sort, ...], range_sort: Sort) -> FuncDecl:
        nonlocal seq
        while True:
            name = f"{prefix}!{seq}"
            seq += 1
            if name not in used_names:
                used_names.add(name)
                decl = ctx.mk_decl(name, domain, range_sort)
                created_decls.add(decl)
                return decl

    def _walk(node: Expr, univ_sorts: tuple[Sort, ...]) -> Expr:
        depth = len(univ_sorts)
        if isinstance(node, Quantifier):
            if node.is_exists:
                free = free_bound_var_indices(node)
                # Keep only enclosing universal slots referenced inside this Exists.
                needed_slots = sorted((slot for slot in free if slot < depth), reverse=True)
                sk_domain = tuple(univ_sorts[depth - 1 - slot] for slot in needed_slots)
                sk_args = tuple(ctx.mk_bound_var(slot, univ_sorts[depth - 1 - slot]) for slot in needed_slots)
                replacements = tuple(_fresh_skolem_decl(sk_domain, sort)(*sk_args) for sort in node.var_sorts)
                instantiated = instantiate_quantifier(node, replacements)
                return _walk(instantiated, univ_sorts)

            new_univ = (*univ_sorts, *node.var_sorts)
            body_sk = _walk(node.body, new_univ)
            if isinstance(body_sk, Quantifier) and body_sk.is_forall:
                k_inner = body_sk.num_vars
                shifted_pats = [tuple(shift_bound_vars(term, k_inner) for term in pat) for pat in node.patterns]
                shifted_pats.extend(body_sk.patterns)
                return ctx.mk_quantifier(
                    True,
                    (*node.var_names, *body_sk.var_names),
                    (*node.var_sorts, *body_sk.var_sorts),
                    body_sk.body,
                    patterns=shifted_pats,
                )
            return ctx.mk_quantifier(
                True,
                node.var_names,
                node.var_sorts,
                body_sk,
                patterns=node.patterns,
            )

        if isinstance(node, App):
            kind = node.decl.kind
            if kind is DeclKind.AND:
                args_sk = [_walk(arg, univ_sorts) for arg in node.args]
                if depth > 0:
                    return _pull_foralls(ctx, True, args_sk)
                return ctx.mk_and(*args_sk)
            if kind is DeclKind.OR:
                args_sk = [_walk(arg, univ_sorts) for arg in node.args]
                return _pull_foralls(ctx, False, args_sk)

        return node

    return _walk(root, ())


def skolemize(
    expr: Expr,
    *,
    reserved_names: Iterable[str] | None = None,
    prefix: str = "__sk",
) -> tuple[Expr, frozenset[FuncDecl]]:
    """Eliminate positive existentials in ``expr`` after converting to NNF."""
    if not expr.is_bool:
        msg = f"Skolemization requires a Bool expression, got sort '{expr.sort}'"
        raise TypeError(msg)
    ctx = expr.ctx
    nnf = to_nnf(expr)
    used_names = {decl.name for decl in collect_func_decls(nnf)}
    if reserved_names is not None:
        used_names.update(reserved_names)
    created: set[FuncDecl] = set()
    skolemized = _skolemize_nnf(ctx, nnf, used_names, prefix, created)
    return skolemized, frozenset(created)


class SkolemizeTactic:
    """Skolemizes goals via NNF and projects away introduced Skolem symbols."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Skolemize each formula in ``formulas`` cleanly without name clashes."""
        if not formulas:
            return TacticResult((), ProjectionModelConverter(()))
        ctx = formulas[0].ctx
        reserved: set[str] = set()
        for formula in formulas:
            for decl in collect_func_decls(formula):
                reserved.add(decl.name)

        all_skolems: set[FuncDecl] = set()
        kept: list[Expr] = []
        for formula in formulas:
            sk_expr, new_sk = skolemize(formula, reserved_names=reserved)
            all_skolems.update(new_sk)
            for decl in new_sk:
                reserved.add(decl.name)
            if sk_expr is ctx.false_expr:
                return TacticResult((ctx.false_expr,), ProjectionModelConverter(all_skolems))
            if sk_expr is not ctx.true_expr:
                kept.append(sk_expr)

        return TacticResult(tuple(kept), ProjectionModelConverter(all_skolems))
