"""Algebraic Boolean simplification pass and tactic."""

from collections.abc import Sequence

from unsat.model import IdentityModelConverter
from unsat.syntax import App, BoundVar, Const, DeclKind, Expr, Quantifier, iter_subexprs
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
        if isinstance(node, Quantifier):
            new_body = memo[node.body]
            new_pats = tuple(tuple(memo[term] for term in pat) for pat in node.patterns)
            memo[node] = ctx.mk_quantifier(
                node.is_forall,
                node.var_names,
                node.var_sorts,
                new_body,
                patterns=new_pats,
            )
            continue
        if isinstance(node, (Const, BoundVar)) or not isinstance(node, App):
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
            case DeclKind.IDIV:
                memo[node] = ctx.mk_idiv(args[0], args[1])
            case DeclKind.MOD:
                memo[node] = ctx.mk_mod(args[0], args[1])
            case DeclKind.ABS:
                memo[node] = ctx.mk_abs(args[0])
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
            case DeclKind.TO_INT:
                memo[node] = ctx.mk_to_int(args[0])
            case DeclKind.IS_INT:
                memo[node] = ctx.mk_is_int(args[0])
            case DeclKind.DIVISIBLE:
                memo[node] = ctx.mk_divisible(node.decl.params[0], args[0])
            case DeclKind.SELECT:
                memo[node] = ctx.mk_select(args[0], args[1])
            case DeclKind.STORE:
                arr_a, idx_a, val_a = args
                if (
                    isinstance(val_a, App)
                    and val_a.decl.kind is DeclKind.SELECT
                    and val_a.args[0] is arr_a
                    and val_a.args[1] is idx_a
                ):
                    memo[node] = arr_a
                else:
                    memo[node] = ctx.mk_store(arr_a, idx_a, val_a)
            case DeclKind.CONST_ARRAY:
                memo[node] = ctx.mk_const_array(node.sort.index_sort, args[0])
            case DeclKind.STR_CONCAT:
                memo[node] = ctx.mk_str_concat(*args)
            case DeclKind.STR_LEN:
                memo[node] = ctx.mk_str_len(args[0])
            case DeclKind.STR_AT:
                memo[node] = ctx.mk_str_at(args[0], args[1])
            case DeclKind.STR_SUBSTR:
                memo[node] = ctx.mk_str_substr(args[0], args[1], args[2])
            case DeclKind.STR_INDEXOF:
                memo[node] = ctx.mk_str_indexof(args[0], args[1], args[2])
            case DeclKind.STR_REPLACE:
                memo[node] = ctx.mk_str_replace(args[0], args[1], args[2])
            case DeclKind.STR_REPLACE_ALL:
                memo[node] = ctx.mk_str_replace_all(args[0], args[1], args[2])
            case DeclKind.STR_CONTAINS:
                memo[node] = ctx.mk_str_contains(args[0], args[1])
            case DeclKind.STR_PREFIXOF:
                memo[node] = ctx.mk_str_prefixof(args[0], args[1])
            case DeclKind.STR_SUFFIXOF:
                memo[node] = ctx.mk_str_suffixof(args[0], args[1])
            case DeclKind.STR_LT:
                memo[node] = ctx.mk_str_lt(args[0], args[1])
            case DeclKind.STR_LE:
                memo[node] = ctx.mk_str_le(args[0], args[1])
            case DeclKind.STR_TO_INT:
                memo[node] = ctx.mk_str_to_int(args[0])
            case DeclKind.STR_FROM_INT:
                memo[node] = ctx.mk_str_from_int(args[0])
            case DeclKind.STR_TO_CODE:
                memo[node] = ctx.mk_str_to_code(args[0])
            case DeclKind.STR_FROM_CODE:
                memo[node] = ctx.mk_str_from_code(args[0])
            case DeclKind.STR_IS_DIGIT:
                memo[node] = ctx.mk_str_is_digit(args[0])
            case DeclKind.STR_IN_RE:
                memo[node] = ctx.mk_str_in_re(args[0], args[1])
            case DeclKind.STR_TO_RE:
                memo[node] = ctx.mk_str_to_re(args[0])
            case DeclKind.RE_NONE:
                memo[node] = ctx.mk_re_none()
            case DeclKind.RE_ALL:
                memo[node] = ctx.mk_re_all()
            case DeclKind.RE_ALLCHAR:
                memo[node] = ctx.mk_re_allchar()
            case DeclKind.RE_CONCAT:
                memo[node] = ctx.mk_re_concat(*args)
            case DeclKind.RE_UNION:
                memo[node] = ctx.mk_re_union(*args)
            case DeclKind.RE_INTER:
                memo[node] = ctx.mk_re_inter(*args)
            case DeclKind.RE_STAR:
                memo[node] = ctx.mk_re_star(args[0])
            case DeclKind.RE_PLUS:
                memo[node] = ctx.mk_re_plus(args[0])
            case DeclKind.RE_OPT:
                memo[node] = ctx.mk_re_opt(args[0])
            case DeclKind.RE_RANGE:
                memo[node] = ctx.mk_re_range(args[0], args[1])
            case DeclKind.RE_COMP:
                memo[node] = ctx.mk_re_comp(args[0])
            case DeclKind.RE_DIFF:
                memo[node] = ctx.mk_re_diff(args[0], args[1])
            case DeclKind.RE_POWER:
                memo[node] = ctx.mk_re_power(node.decl.params[0], args[0])
            case DeclKind.RE_LOOP:
                memo[node] = ctx.mk_re_loop(
                    node.decl.params[0], node.decl.params[1], args[0]
                )
            case (
                DeclKind.BV_NOT
                | DeclKind.BV_AND
                | DeclKind.BV_OR
                | DeclKind.BV_XOR
                | DeclKind.BV_NEG
                | DeclKind.BV_ADD
                | DeclKind.BV_SUB
                | DeclKind.BV_MUL
                | DeclKind.BV_UDIV
                | DeclKind.BV_UREM
                | DeclKind.BV_SDIV
                | DeclKind.BV_SREM
                | DeclKind.BV_SMOD
                | DeclKind.BV_SHL
                | DeclKind.BV_LSHR
                | DeclKind.BV_ASHR
                | DeclKind.BV_ULT
                | DeclKind.BV_ULE
                | DeclKind.BV_UGT
                | DeclKind.BV_UGE
                | DeclKind.BV_SLT
                | DeclKind.BV_SLE
                | DeclKind.BV_SGT
                | DeclKind.BV_SGE
                | DeclKind.BV_CONCAT
                | DeclKind.BV_EXTRACT
                | DeclKind.BV_ZERO_EXT
                | DeclKind.BV_SIGN_EXT
                | DeclKind.BV_ROTATE_LEFT
                | DeclKind.BV_ROTATE_RIGHT
                | DeclKind.BV_REPEAT
            ):
                memo[node] = ctx.mk_app(node.decl, *args)
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
