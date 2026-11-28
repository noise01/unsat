"""Negation Normal Form (NNF) conversion pass and tactic."""

from collections.abc import Sequence

from unsat.model import IdentityModelConverter
from unsat.syntax import App, BoundVar, Const, DeclKind, Expr, Quantifier
from unsat.tactics.base import TacticResult


def to_nnf(expr: Expr) -> Expr:
    """Convert Boolean expression ``expr`` iteratively into Negation Normal Form."""
    if not expr.is_bool:
        msg = f"NNF requires a Bool expression, got sort '{expr.sort}'"
        raise TypeError(msg)

    ctx = expr.ctx
    memo: dict[tuple[Expr, bool], Expr] = {}
    stack: list[tuple[Expr, bool, bool]] = [(expr, False, False)]

    while stack:
        node, neg, expanded = stack.pop()
        key = (node, neg)
        if key in memo:
            continue

        if isinstance(node, Const):
            val = bool(node.value)
            memo[key] = ctx.mk_bool_val((not val) if neg else val)
            continue

        if isinstance(node, BoundVar):
            memo[key] = ctx.mk_not(node) if neg else node
            continue

        if isinstance(node, Quantifier):
            if not expanded:
                if (node.body, neg) in memo:
                    memo[key] = ctx.mk_quantifier(
                        node.is_forall ^ neg,
                        node.var_names,
                        node.var_sorts,
                        memo[(node.body, neg)],
                        patterns=node.patterns,
                    )
                else:
                    stack.append((node, neg, True))
                    stack.append((node.body, neg, False))
            else:
                memo[key] = ctx.mk_quantifier(
                    node.is_forall ^ neg,
                    node.var_names,
                    node.var_sorts,
                    memo[(node.body, neg)],
                    patterns=node.patterns,
                )
            continue

        if not isinstance(node, App):
            memo[key] = node
            continue

        if node.is_const_symbol:
            memo[key] = ctx.mk_not(node) if neg else node
            continue

        kind = node.decl.kind
        if not expanded:
            if kind is DeclKind.NOT:
                child_key = (node.args[0], not neg)
                if child_key in memo:
                    memo[key] = memo[child_key]
                else:
                    stack.append((node, neg, True))
                    stack.append((node.args[0], not neg, False))
                continue

            if kind in (DeclKind.AND, DeclKind.OR):
                stack.append((node, neg, True))
                stack.extend((arg, neg, False) for arg in reversed(node.args) if (arg, neg) not in memo)
                continue

            if kind is DeclKind.IMPLIES:
                lhs, rhs = node.args
                stack.append((node, neg, True))
                for child, child_neg in ((rhs, neg), (lhs, not neg)):
                    if (child, child_neg) not in memo:
                        stack.append((child, child_neg, False))
                continue

            if kind is DeclKind.EQ:
                if not node.args[0].is_bool:
                    memo[key] = ctx.mk_not(node) if neg else node
                    continue
                lhs, rhs = node.args
                stack.append((node, neg, True))
                for child, child_neg in (
                    (rhs, True),
                    (rhs, False),
                    (lhs, True),
                    (lhs, False),
                ):
                    if (child, child_neg) not in memo:
                        stack.append((child, child_neg, False))
                continue

            if kind is DeclKind.XOR:
                lhs, rhs = node.args
                stack.append((node, neg, True))
                for child, child_neg in (
                    (rhs, True),
                    (rhs, False),
                    (lhs, True),
                    (lhs, False),
                ):
                    if (child, child_neg) not in memo:
                        stack.append((child, child_neg, False))
                continue

            if kind is DeclKind.DISTINCT:
                if node.args and not node.args[0].is_bool:
                    memo[key] = ctx.mk_not(node) if neg else node
                    continue
                if len(node.args) <= 1:
                    memo[key] = ctx.mk_bool_val(not neg)
                elif len(node.args) >= 3:
                    memo[key] = ctx.mk_bool_val(neg)
                else:
                    lhs, rhs = node.args
                    stack.append((node, neg, True))
                    for child, child_neg in (
                        (rhs, True),
                        (rhs, False),
                        (lhs, True),
                        (lhs, False),
                    ):
                        if (child, child_neg) not in memo:
                            stack.append((child, child_neg, False))
                continue

            if kind is DeclKind.ITE:
                cond, then_b, else_b = node.args
                stack.append((node, neg, True))
                for child, child_neg in (
                    (else_b, neg),
                    (then_b, neg),
                    (cond, True),
                    (cond, False),
                ):
                    if (child, child_neg) not in memo:
                        stack.append((child, child_neg, False))
                continue

            memo[key] = ctx.mk_not(node) if neg else node
            continue

        # Second visit: all required children are now in memo.
        match kind:
            case DeclKind.NOT:
                memo[key] = memo[(node.args[0], not neg)]
            case DeclKind.AND:
                args = [memo[(arg, neg)] for arg in node.args]
                memo[key] = ctx.mk_or(*args) if neg else ctx.mk_and(*args)
            case DeclKind.OR:
                args = [memo[(arg, neg)] for arg in node.args]
                memo[key] = ctx.mk_and(*args) if neg else ctx.mk_or(*args)
            case DeclKind.IMPLIES:
                lhs, rhs = node.args
                lhs_nnf = memo[(lhs, not neg)]
                rhs_nnf = memo[(rhs, neg)]
                memo[key] = ctx.mk_and(lhs_nnf, rhs_nnf) if neg else ctx.mk_or(lhs_nnf, rhs_nnf)
            case DeclKind.XOR:
                lhs, rhs = node.args
                lhs_t, lhs_f = memo[(lhs, False)], memo[(lhs, True)]
                rhs_t, rhs_f = memo[(rhs, False)], memo[(rhs, True)]
                if neg:
                    memo[key] = ctx.mk_or(ctx.mk_and(lhs_t, rhs_t), ctx.mk_and(lhs_f, rhs_f))
                else:
                    memo[key] = ctx.mk_or(ctx.mk_and(lhs_t, rhs_f), ctx.mk_and(lhs_f, rhs_t))
            case DeclKind.EQ:
                lhs, rhs = node.args
                lhs_t, lhs_f = memo[(lhs, False)], memo[(lhs, True)]
                rhs_t, rhs_f = memo[(rhs, False)], memo[(rhs, True)]
                if neg:
                    memo[key] = ctx.mk_or(ctx.mk_and(lhs_t, rhs_f), ctx.mk_and(lhs_f, rhs_t))
                else:
                    memo[key] = ctx.mk_or(ctx.mk_and(lhs_t, rhs_t), ctx.mk_and(lhs_f, rhs_f))
            case DeclKind.DISTINCT:
                lhs, rhs = node.args
                lhs_t, lhs_f = memo[(lhs, False)], memo[(lhs, True)]
                rhs_t, rhs_f = memo[(rhs, False)], memo[(rhs, True)]
                if neg:
                    memo[key] = ctx.mk_or(ctx.mk_and(lhs_t, rhs_t), ctx.mk_and(lhs_f, rhs_f))
                else:
                    memo[key] = ctx.mk_or(ctx.mk_and(lhs_t, rhs_f), ctx.mk_and(lhs_f, rhs_t))
            case DeclKind.ITE:
                cond, then_b, else_b = node.args
                memo[key] = ctx.mk_or(
                    ctx.mk_and(memo[(cond, False)], memo[(then_b, neg)]),
                    ctx.mk_and(memo[(cond, True)], memo[(else_b, neg)]),
                )

    return memo[(expr, False)]


class NNFTactic:
    """Converts a sequence of Boolean formulas into Negation Normal Form."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Transform every formula in ``formulas`` to NNF."""
        return TacticResult(
            tuple(to_nnf(formula) for formula in formulas),
            IdentityModelConverter(),
        )
