"""Algebraic Boolean simplification pass and tactic."""

from collections.abc import Sequence

from unsat.model import IdentityModelConverter
from unsat.syntax import App, Const, DeclKind, Expr, iter_subexprs
from unsat.tactics.base import TacticResult


def _is_not_of(candidate: Expr, target: Expr) -> bool:
    return (
        isinstance(candidate, App)
        and candidate.decl.kind is DeclKind.NOT
        and candidate.args[0] is target
    )


def simplify(expr: Expr) -> Expr:
    """Simplify Boolean expression ``expr`` via iterative bottom-up rewriting."""
    ctx = expr.ctx
    memo: dict[Expr, Expr] = {}

    for node in iter_subexprs(expr):
        if isinstance(node, Const) or not isinstance(node, App):
            memo[node] = node
            continue

        if node.is_const_symbol:
            memo[node] = node
            continue

        args = [memo[arg] for arg in node.args]
        match node.decl.kind:
            case DeclKind.NOT:
                memo[node] = ctx.mk_not(args[0])
            case DeclKind.AND:
                memo[node] = ctx.mk_and(*args)
            case DeclKind.OR:
                memo[node] = ctx.mk_or(*args)
            case DeclKind.IMPLIES:
                lhs, rhs = args
                if _is_not_of(lhs, rhs) or _is_not_of(rhs, lhs):
                    memo[node] = rhs
                else:
                    memo[node] = ctx.mk_implies(lhs, rhs)
            case DeclKind.XOR:
                memo[node] = ctx.mk_xor(args[0], args[1])
            case DeclKind.EQ:
                lhs, rhs = args
                if lhs is ctx.true_expr:
                    memo[node] = rhs
                elif rhs is ctx.true_expr:
                    memo[node] = lhs
                elif lhs is ctx.false_expr:
                    memo[node] = ctx.mk_not(rhs)
                elif rhs is ctx.false_expr:
                    memo[node] = ctx.mk_not(lhs)
                else:
                    memo[node] = ctx.mk_eq(lhs, rhs)
            case DeclKind.DISTINCT:
                if args and args[0].is_bool:
                    if len(args) <= 1:
                        memo[node] = ctx.mk_true()
                    elif len(args) == 2:
                        memo[node] = ctx.mk_xor(args[0], args[1])
                    else:
                        memo[node] = ctx.mk_false()
                else:
                    memo[node] = ctx.mk_distinct(*args)
            case DeclKind.ITE:
                cond, then_b, else_b = args
                if not then_b.is_bool:
                    memo[node] = ctx.mk_ite(cond, then_b, else_b)
                elif then_b is ctx.true_expr and else_b is ctx.false_expr:
                    memo[node] = cond
                elif then_b is ctx.false_expr and else_b is ctx.true_expr:
                    memo[node] = ctx.mk_not(cond)
                elif then_b is ctx.true_expr:
                    memo[node] = ctx.mk_or(cond, else_b)
                elif else_b is ctx.false_expr:
                    memo[node] = ctx.mk_and(cond, then_b)
                elif then_b is ctx.false_expr:
                    memo[node] = ctx.mk_and(ctx.mk_not(cond), else_b)
                elif else_b is ctx.true_expr:
                    memo[node] = ctx.mk_or(ctx.mk_not(cond), then_b)
                elif cond is then_b:
                    memo[node] = ctx.mk_or(cond, else_b)
                elif cond is else_b:
                    memo[node] = ctx.mk_and(cond, then_b)
                else:
                    memo[node] = ctx.mk_ite(cond, then_b, else_b)
            case DeclKind.NEG:
                memo[node] = ctx.mk_neg(args[0])
            case DeclKind.ADD:
                memo[node] = ctx.mk_add(*args)
            case DeclKind.SUB:
                memo[node] = ctx.mk_sub(args[0], args[1])
            case DeclKind.MUL:
                memo[node] = ctx.mk_mul(*args)
            case DeclKind.DIV:
                memo[node] = ctx.mk_div(args[0], args[1])
            case DeclKind.LT:
                memo[node] = ctx.mk_lt(args[0], args[1])
            case DeclKind.LE:
                memo[node] = ctx.mk_le(args[0], args[1])
            case DeclKind.GT:
                memo[node] = ctx.mk_gt(args[0], args[1])
            case DeclKind.GE:
                memo[node] = ctx.mk_ge(args[0], args[1])
            case DeclKind.TO_REAL:
                memo[node] = ctx.mk_to_real(args[0])
            case DeclKind.UNINTERPRETED:
                memo[node] = ctx.mk_app(node.decl, *args)

    return memo[expr]


class SimplifyTactic:
    """Applies :func:`simplify` across a goal sequence and removes trivial truth."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Simplify ``formulas``, short-circuiting if any reduces to ``false``."""
        if not formulas:
            return TacticResult((), IdentityModelConverter())

        ctx = formulas[0].ctx
        kept: list[Expr] = []
        seen: set[Expr] = set()
        for formula in formulas:
            simplified = simplify(formula)
            if simplified is ctx.false_expr:
                return TacticResult((ctx.false_expr,), IdentityModelConverter())
            if simplified is ctx.true_expr or simplified in seen:
                continue
            seen.add(simplified)
            kept.append(simplified)

        return TacticResult(tuple(kept), IdentityModelConverter())
