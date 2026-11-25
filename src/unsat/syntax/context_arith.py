"""Arithmetic expression normalization helpers for :class:`Context`."""

from fractions import Fraction
from typing import TYPE_CHECKING

from unsat.syntax.expr import App, Const, Expr, Sort
from unsat.syntax.kinds import DeclKind

if TYPE_CHECKING:
    from unsat.syntax.context import Context


def mk_arith_const(ctx: Context, sort: Sort, val: int | Fraction) -> Const:
    """Construct an ``Int`` or ``Real`` constant matching ``sort``."""
    if sort.is_int:
        assert isinstance(val, int)
        assert not isinstance(val, bool)
        return ctx.mk_int_val(val)
    return ctx.mk_real_val(val)


def check_arith_pair(ctx: Context, lhs: Expr, rhs: Expr, op_name: str) -> Sort:
    """Validate that ``lhs`` and ``rhs`` share an arithmetic sort in ``ctx``."""
    sort = ctx._check_arith(lhs)
    ctx._check_expr(rhs)
    if lhs.sort is not rhs.sort:
        msg = f"Sort mismatch in {op_name}: '{lhs.sort}' vs '{rhs.sort}'"
        raise TypeError(msg)
    return sort


def build_to_real(ctx: Context, arg: Expr) -> Expr:
    """Convert an ``Int`` expression to ``Real`` via ``to_real``."""
    ctx._check_int(arg)
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        return ctx.mk_real_val(arg.value)
    decl = ctx._intern_decl(DeclKind.TO_REAL, "to_real", (ctx.int_sort,), ctx.real_sort)
    return ctx._intern_app(decl, (arg,))


def build_neg(ctx: Context, arg: Expr) -> Expr:
    """Build a normalized arithmetic negation."""
    sort = ctx._check_arith(arg)
    if isinstance(arg, Const):
        if sort.is_int:
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return ctx.mk_int_val(-arg.value)
        assert isinstance(arg.value, Fraction)
        return ctx.mk_real_val(-arg.value)
    if isinstance(arg, App) and arg.decl.kind is DeclKind.NEG:
        return arg.args[0]
    decl = ctx._intern_decl(DeclKind.NEG, "-", (sort,), sort)
    return ctx._intern_app(decl, (arg,))


def build_add(ctx: Context, *args: Expr) -> Expr:
    """Build a normalized n-ary arithmetic sum."""
    if not args:
        msg = "mk_add requires at least one argument"
        raise ValueError(msg)
    sort = ctx._check_arith(args[0])
    const_sum: int | Fraction = 0 if sort.is_int else Fraction(0)
    non_const: list[Expr] = []

    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in Add: expected '{sort}', got '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.ADD:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert not isinstance(item.value, bool)
            if sort.is_int:
                assert isinstance(item.value, int)
                assert isinstance(const_sum, int)
                const_sum += item.value
            else:
                assert isinstance(item.value, Fraction)
                assert isinstance(const_sum, Fraction)
                const_sum += item.value
        else:
            non_const.append(item)

    if not non_const:
        return mk_arith_const(ctx, sort, const_sum)
    if const_sum != 0:
        non_const.append(mk_arith_const(ctx, sort, const_sum))
    if len(non_const) == 1:
        return non_const[0]

    decl = ctx._intern_decl(DeclKind.ADD, "+", (sort,) * len(non_const), sort)
    return ctx._intern_app(decl, tuple(non_const))


def build_sub(ctx: Context, lhs: Expr, rhs: Expr) -> Expr:
    """Build a normalized arithmetic difference ``lhs - rhs``."""
    sort = check_arith_pair(ctx, lhs, rhs, "Sub")
    if lhs is rhs:
        return mk_arith_const(ctx, sort, 0 if sort.is_int else Fraction(0))
    if isinstance(lhs, Const) and isinstance(rhs, Const):
        assert not isinstance(lhs.value, bool)
        assert not isinstance(rhs.value, bool)
        if sort.is_int:
            assert isinstance(lhs.value, int)
            assert isinstance(rhs.value, int)
            return ctx.mk_int_val(lhs.value - rhs.value)
        assert isinstance(lhs.value, Fraction)
        assert isinstance(rhs.value, Fraction)
        return ctx.mk_real_val(lhs.value - rhs.value)
    if isinstance(rhs, Const) and rhs.value == 0:
        return lhs
    if isinstance(lhs, Const) and lhs.value == 0:
        return ctx.mk_neg(rhs)
    decl = ctx._intern_decl(DeclKind.SUB, "-", (sort, sort), sort)
    return ctx._intern_app(decl, (lhs, rhs))


def build_mul(ctx: Context, *args: Expr) -> Expr:
    """Build a normalized arithmetic product."""
    if not args:
        msg = "mk_mul requires at least one argument"
        raise ValueError(msg)
    sort = ctx._check_arith(args[0])
    const_prod: int | Fraction = 1 if sort.is_int else Fraction(1)
    non_const: list[Expr] = []

    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in Mul: expected '{sort}', got '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.MUL:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert not isinstance(item.value, bool)
            if sort.is_int:
                assert isinstance(item.value, int)
                assert isinstance(const_prod, int)
                const_prod *= item.value
            else:
                assert isinstance(item.value, Fraction)
                assert isinstance(const_prod, Fraction)
                const_prod *= item.value
        else:
            non_const.append(item)

    if const_prod == 0:
        return mk_arith_const(ctx, sort, 0 if sort.is_int else Fraction(0))
    if not non_const:
        return mk_arith_const(ctx, sort, const_prod)
    if const_prod == -1 and len(non_const) == 1:
        return ctx.mk_neg(non_const[0])
    if const_prod == 1:
        if len(non_const) == 1:
            return non_const[0]
        factors = tuple(non_const)
    else:
        factors = (mk_arith_const(ctx, sort, const_prod), *non_const)

    decl = ctx._intern_decl(DeclKind.MUL, "*", (sort,) * len(factors), sort)
    return ctx._intern_app(decl, factors)


def build_div(ctx: Context, lhs: Expr, rhs: Expr) -> Expr:
    """Build a normalized ``Real`` division ``lhs / rhs``."""
    ctx._check_real(lhs)
    ctx._check_real(rhs)
    if isinstance(rhs, Const):
        assert isinstance(rhs.value, Fraction)
        if rhs.value == 1:
            return lhs
        if rhs.value == -1:
            return ctx.mk_neg(lhs)
        if isinstance(lhs, Const) and rhs.value != 0:
            assert isinstance(lhs.value, Fraction)
            return ctx.mk_real_val(lhs.value / rhs.value)
    decl = ctx._intern_decl(
        DeclKind.DIV, "/", (ctx.real_sort, ctx.real_sort), ctx.real_sort
    )
    return ctx._intern_app(decl, (lhs, rhs))


def build_arith_cmp(ctx: Context, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
    """Build a normalized arithmetic comparison atom."""
    sort = check_arith_pair(ctx, lhs, rhs, kind.value)
    if lhs is rhs:
        return ctx.mk_bool_val(kind in (DeclKind.LE, DeclKind.GE))
    if isinstance(lhs, Const) and isinstance(rhs, Const):
        assert not isinstance(lhs.value, bool)
        assert not isinstance(rhs.value, bool)
        if sort.is_int:
            assert isinstance(lhs.value, int)
            assert isinstance(rhs.value, int)
            lv, rv = lhs.value, rhs.value
            res = (
                lv < rv
                if kind is DeclKind.LT
                else lv <= rv
                if kind is DeclKind.LE
                else lv > rv
                if kind is DeclKind.GT
                else lv >= rv
            )
        else:
            assert isinstance(lhs.value, Fraction)
            assert isinstance(rhs.value, Fraction)
            lf, rf = lhs.value, rhs.value
            res = (
                lf < rf
                if kind is DeclKind.LT
                else lf <= rf
                if kind is DeclKind.LE
                else lf > rf
                if kind is DeclKind.GT
                else lf >= rf
            )
        return ctx.mk_bool_val(res)

    decl = ctx._intern_decl(kind, kind.value, (sort, sort), ctx.bool_sort)
    return ctx._intern_app(decl, (lhs, rhs))
