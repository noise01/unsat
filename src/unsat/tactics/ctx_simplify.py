"""Contextual simplification tactic propagating unit truths and equalities."""

from collections.abc import Sequence

from unsat.model import IdentityModelConverter
from unsat.syntax import (
    App,
    BoundVar,
    Const,
    Context,
    DeclKind,
    Expr,
    Quantifier,
    free_bound_var_indices,
)
from unsat.tactics.base import TacticResult
from unsat.tactics.simplify import simplify


def _strip_not(expr: Expr) -> tuple[Expr, bool]:
    flip = False
    cur = expr
    while isinstance(cur, App) and cur.decl.kind is DeclKind.NOT:
        flip = not flip
        cur = cur.args[0]
    return cur, flip


def _assert_context_fact(
    expr: Expr,
    polarity: bool,
    truths: dict[Expr, bool],
    const_map: dict[Expr, Expr],
) -> bool:
    """Record ``expr == polarity`` into contextual maps; return False if conflict."""
    stack: list[tuple[Expr, bool]] = [(expr, polarity)]
    while stack:
        cur, pol = stack.pop()
        base, flip = _strip_not(cur)
        eff = pol ^ flip
        if isinstance(base, Const):
            if bool(base.value) != eff:
                return False
            continue
        if isinstance(base, App):
            kind = base.decl.kind
            if eff and kind is DeclKind.AND:
                for arg in reversed(base.args):
                    stack.append((arg, True))
                continue
            if (not eff) and kind is DeclKind.OR:
                for arg in reversed(base.args):
                    stack.append((arg, False))
                continue
            if eff and kind is DeclKind.EQ:
                lhs, rhs = base.args
                if isinstance(rhs, Const) and not isinstance(lhs, Const):
                    if lhs.is_bool:
                        rhs_pol = bool(rhs.value)
                        prev = truths.get(lhs)
                        if prev is not None and prev != rhs_pol:
                            return False
                        truths[lhs] = rhs_pol
                    else:
                        prev_c = const_map.get(lhs)
                        if prev_c is not None and prev_c is not rhs:
                            return False
                        const_map[lhs] = rhs
                elif isinstance(lhs, Const) and not isinstance(rhs, Const):
                    if rhs.is_bool:
                        lhs_pol = bool(lhs.value)
                        prev = truths.get(rhs)
                        if prev is not None and prev != lhs_pol:
                            return False
                        truths[rhs] = lhs_pol
                    else:
                        prev_c = const_map.get(rhs)
                        if prev_c is not None and prev_c is not lhs:
                            return False
                        const_map[rhs] = lhs
                elif (
                    isinstance(lhs, Const) and isinstance(rhs, Const) and lhs is not rhs
                ):
                    return False

        prev_t = truths.get(base)
        if prev_t is not None:
            if prev_t != eff:
                return False
        else:
            truths[base] = eff
    return True


def _rewrite_with_env(
    ctx: Context,
    node: Expr,
    truths: dict[Expr, bool],
    const_map: dict[Expr, Expr],
) -> Expr:
    if isinstance(node, Const):
        return node

    ground_truths: dict[Expr, bool] | None = None
    ground_consts: dict[Expr, Expr] | None = None

    def _ground_maps() -> tuple[dict[Expr, bool], dict[Expr, Expr]]:
        nonlocal ground_truths, ground_consts
        if ground_truths is None:
            ground_truths = {
                k: v for k, v in truths.items() if not free_bound_var_indices(k)
            }
        if ground_consts is None:
            ground_consts = {
                k: v for k, v in const_map.items() if not free_bound_var_indices(k)
            }
        return ground_truths, ground_consts

    def _step(
        cur: Expr, depth: int, t_env: dict[Expr, bool], c_env: dict[Expr, Expr]
    ) -> Expr:
        if depth == 0 or not free_bound_var_indices(cur):
            if cur in c_env:
                return c_env[cur]
            if cur in t_env:
                return ctx.mk_bool_val(t_env[cur])

        if isinstance(cur, (Const, BoundVar)):
            return cur

        if isinstance(cur, Quantifier):
            gt, gc = _ground_maps()
            new_body = _step(cur.body, depth + cur.num_vars, gt, gc)
            new_pats = tuple(
                tuple(_step(t, depth + cur.num_vars, gt, gc) for t in pat)
                for pat in cur.patterns
            )
            return simplify(
                ctx.mk_quantifier(
                    cur.is_forall,
                    cur.var_names,
                    cur.var_sorts,
                    new_body,
                    patterns=new_pats,
                )
            )

        if not isinstance(cur, App):
            return cur

        kind = cur.decl.kind
        if kind is DeclKind.AND:
            cur_t = dict(t_env)
            cur_c = dict(c_env)
            out_args: list[Expr] = []
            for idx, arg in enumerate(cur.args):
                rewritten = _step(arg, depth, cur_t, cur_c)
                if rewritten is ctx.false_expr:
                    return ctx.false_expr
                if rewritten is ctx.true_expr:
                    continue
                out_args.append(rewritten)
                if idx + 1 < len(cur.args) and not _assert_context_fact(
                    rewritten, True, cur_t, cur_c
                ):
                    return ctx.false_expr
            return ctx.mk_and(*out_args)

        if kind is DeclKind.OR:
            cur_t = dict(t_env)
            cur_c = dict(c_env)
            out_args = []
            for idx, arg in enumerate(cur.args):
                rewritten = _step(arg, depth, cur_t, cur_c)
                if rewritten is ctx.true_expr:
                    return ctx.true_expr
                if rewritten is ctx.false_expr:
                    continue
                out_args.append(rewritten)
                if idx + 1 < len(cur.args):
                    _assert_context_fact(rewritten, False, cur_t, cur_c)
            return ctx.mk_or(*out_args)

        if kind is DeclKind.IMPLIES:
            lhs = _step(cur.args[0], depth, t_env, c_env)
            if lhs is ctx.false_expr:
                return ctx.true_expr
            rhs_t = dict(t_env)
            rhs_c = dict(c_env)
            if not _assert_context_fact(lhs, True, rhs_t, rhs_c):
                return ctx.true_expr
            rhs = _step(cur.args[1], depth, rhs_t, rhs_c)
            return simplify(ctx.mk_implies(lhs, rhs))

        if kind is DeclKind.ITE:
            cond = _step(cur.args[0], depth, t_env, c_env)
            if cond is ctx.true_expr:
                return _step(cur.args[1], depth, t_env, c_env)
            if cond is ctx.false_expr:
                return _step(cur.args[2], depth, t_env, c_env)
            t_truth, t_const = dict(t_env), dict(c_env)
            e_truth, e_const = dict(t_env), dict(c_env)
            then_ok = _assert_context_fact(cond, True, t_truth, t_const)
            else_ok = _assert_context_fact(cond, False, e_truth, e_const)
            if not then_ok:
                return _step(cur.args[2], depth, t_env, c_env)
            if not else_ok:
                return _step(cur.args[1], depth, t_env, c_env)
            then_b = _step(cur.args[1], depth, t_truth, t_const)
            else_b = _step(cur.args[2], depth, e_truth, e_const)
            return simplify(ctx.mk_ite(cond, then_b, else_b))

        new_args = [_step(arg, depth, t_env, c_env) for arg in cur.args]
        rebuilt = (
            cur
            if all(n is o for n, o in zip(new_args, cur.args, strict=True))
            else ctx.mk_app(cur.decl, *new_args)
        )
        return simplify(rebuilt)

    return simplify(_step(node, 0, truths, const_map))


def ctx_simplify(expr: Expr) -> Expr:
    """Simplify ``expr`` by propagating contextual truths down connectives."""
    return _rewrite_with_env(expr.ctx, expr, {}, {})


class CtxSimplifyTactic:
    """Contextual simplification propagating top-level & branch facts."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Simplify ``formulas`` across conjunctive/conditional context."""
        if not formulas:
            return TacticResult((), IdentityModelConverter())
        ctx = formulas[0].ctx
        truths: dict[Expr, bool] = {}
        const_map: dict[Expr, Expr] = {}
        kept: list[Expr] = []
        seen: set[Expr] = set()

        for raw in formulas:
            simplified = _rewrite_with_env(ctx, raw, truths, const_map)
            if simplified is ctx.false_expr:
                return TacticResult((ctx.false_expr,), IdentityModelConverter())
            if simplified is ctx.true_expr:
                continue
            if simplified not in seen:
                seen.add(simplified)
                kept.append(simplified)
            if not _assert_context_fact(simplified, True, truths, const_map):
                return TacticResult((ctx.false_expr,), IdentityModelConverter())

        return TacticResult(tuple(kept), IdentityModelConverter())
