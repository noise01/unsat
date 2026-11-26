"""Thin user-facing Z3Py-style Python DSL and builder layer.

Provides default-context management, syntactic sugar, and the ``Solver`` facade
directly over ``syntax`` objects without duplicating an AST wrapper hierarchy.

Depends on: ``syntax``, ``smt``, ``model``.
"""

from collections.abc import Sequence
from fractions import Fraction

from unsat.model import FuncInterp, Model
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, BoundVar, Const, Context, Expr, FuncDecl, Quantifier, Sort

_default_ctx = Context()

SAT = SolveResult.SAT
UNSAT = SolveResult.UNSAT
UNKNOWN = SolveResult.UNKNOWN


def default_context() -> Context:
    """Return the active default AST :class:`Context`."""
    return _default_ctx


def set_default_context(ctx: Context) -> None:
    """Set the active default AST :class:`Context`."""
    global _default_ctx
    _default_ctx = ctx


def reset_default_context() -> Context:
    """Replace the default AST :class:`Context` with a fresh instance."""
    global _default_ctx
    _default_ctx = Context()
    return _default_ctx


def _resolve_ctx(ctx: Context | None) -> Context:
    return _default_ctx if ctx is None else ctx


def _flatten_coercible_args(
    args: tuple[
        Expr
        | bool
        | int
        | Fraction
        | str
        | Sequence[Expr | bool | int | Fraction | str],
        ...,
    ],
) -> tuple[Expr | bool | int | Fraction | str, ...]:
    if (
        len(args) == 1
        and isinstance(args[0], Sequence)
        and not isinstance(args[0], (Expr, str, bytes, bytearray))
    ):
        return tuple(args[0])
    flat: list[Expr | bool | int | Fraction | str] = []
    for item in args:
        if isinstance(item, (bytes, bytearray)):
            msg = f"Unsupported bytes argument: {item!r}"
            raise TypeError(msg)
        if isinstance(item, Sequence) and not isinstance(item, (Expr, str)):
            flat.extend(item)
        else:
            flat.append(item)
    return tuple(flat)


def _coerce_literal_pair(
    ctx: Context,
    then_val: bool | int | Fraction | str,
    else_val: bool | int | Fraction | str,
) -> tuple[Expr, Expr]:
    if isinstance(then_val, bool) and isinstance(else_val, bool):
        return ctx.mk_bool_val(then_val), ctx.mk_bool_val(else_val)
    if isinstance(then_val, str) and isinstance(else_val, str):
        return ctx.mk_string_val(then_val), ctx.mk_string_val(else_val)
    if isinstance(then_val, (bool, str)) or isinstance(else_val, (bool, str)):
        msg = f"Cannot unify If branches {then_val!r} and {else_val!r}"
        raise TypeError(msg)
    if isinstance(then_val, int) and isinstance(else_val, int):
        return ctx.mk_int_val(then_val), ctx.mk_int_val(else_val)
    if isinstance(then_val, (int, Fraction)) and isinstance(else_val, (int, Fraction)):
        return ctx.mk_real_val(then_val), ctx.mk_real_val(else_val)
    msg = f"Unsupported If branch literals: {then_val!r} and {else_val!r}"
    raise TypeError(msg)


def _flatten_expr_args(
    args: tuple[Expr | Sequence[Expr], ...],
) -> tuple[Expr, ...]:
    if (
        len(args) == 1
        and isinstance(args[0], Sequence)
        and not isinstance(args[0], Expr)
    ):
        return tuple(args[0])
    flat: list[Expr] = []
    for item in args:
        if isinstance(item, Expr):
            flat.append(item)
        else:
            flat.extend(item)
    return tuple(flat)


def _bv_coerce_pair(a: Expr | int, b: Expr | int, op_name: str) -> tuple[Expr, Expr]:
    if isinstance(a, Expr) and isinstance(b, Expr):
        return a, b
    if (
        isinstance(a, Expr)
        and a.is_bv
        and isinstance(b, int)
        and not isinstance(b, bool)
    ):
        return a, a.ctx.mk_bv_val(b, a.bv_size)
    if (
        isinstance(b, Expr)
        and b.is_bv
        and isinstance(a, int)
        and not isinstance(a, bool)
    ):
        return b.ctx.mk_bv_val(a, b.bv_size), b
    msg = f"{op_name} requires BitVec expressions"
    raise TypeError(msg)


def _coerce_arg_for_sort(sort: Sort, value: Expr | bool | int | Fraction | str) -> Expr:
    if isinstance(value, Expr):
        return value
    if sort.is_bool and isinstance(value, bool):
        return sort.ctx.mk_bool_val(value)
    if sort.is_int and isinstance(value, int) and not isinstance(value, bool):
        return sort.ctx.mk_int_val(value)
    if (
        sort.is_real
        and not isinstance(value, bool)
        and isinstance(value, (int, Fraction))
    ):
        return sort.ctx.mk_real_val(value)
    if sort.is_bv and isinstance(value, int) and not isinstance(value, bool):
        return sort.ctx.mk_bv_val(value, sort.size)
    if sort.is_string and isinstance(value, str):
        return sort.ctx.mk_string_val(value)
    msg = f"Cannot coerce value {value!r} to sort '{sort}'"
    raise TypeError(msg)


def BoolSort(ctx: Context | None = None) -> Sort:
    """Return the ``Bool`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_bool_sort()


def IntSort(ctx: Context | None = None) -> Sort:
    """Return the ``Int`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_int_sort()


def RealSort(ctx: Context | None = None) -> Sort:
    """Return the ``Real`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_real_sort()


def BitVecSort(size: int, ctx: Context | None = None) -> Sort:
    """Return the fixed-width ``(_ BitVec size)`` sort."""
    return _resolve_ctx(ctx).mk_bv_sort(size)


def ArraySort(domain: Sort, range_sort: Sort) -> Sort:
    """Return the ``(Array domain range_sort)`` sort."""
    if domain.ctx is not range_sort.ctx:
        msg = "ArraySort domain and range belong to different Contexts"
        raise ValueError(msg)
    return domain.ctx.mk_array_sort(domain, range_sort)


def DeclareSort(name: str, ctx: Context | None = None) -> Sort:
    """Declare or retrieve an uninterpreted sort named ``name``."""
    return _resolve_ctx(ctx).mk_uninterpreted_sort(name)


def StringSort(ctx: Context | None = None) -> Sort:
    """Return the ``String`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_string_sort()


def RegLanSort(ctx: Context | None = None) -> Sort:
    """Return the ``RegLan`` regular-expression sort in ``ctx``."""
    return _resolve_ctx(ctx).mk_reglan_sort()


def String(name: str, ctx: Context | None = None) -> App:
    """Create a ``String`` symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_string(name)


def Strings(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple ``String`` constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_string(name) for name in name_list]


def StringVal(value: str, ctx: Context | None = None) -> Const:
    """Create a ``String`` literal constant."""
    return _resolve_ctx(ctx).mk_string_val(value)


def Bool(name: str, ctx: Context | None = None) -> App:
    """Create a Boolean symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_bool(name)


def Bools(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple Boolean symbolic constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_bool(name) for name in name_list]


def Int(name: str, ctx: Context | None = None) -> App:
    """Create an ``Int`` symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_int(name)


def Ints(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple ``Int`` symbolic constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_int(name) for name in name_list]


def Real(name: str, ctx: Context | None = None) -> App:
    """Create a ``Real`` symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_real(name)


def Reals(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple ``Real`` symbolic constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_real(name) for name in name_list]


def BitVec(name: str, bv: int | Sort, ctx: Context | None = None) -> App:
    """Create a fixed-width ``BitVec`` symbolic constant named ``name``."""
    if isinstance(bv, Sort):
        if not bv.is_bv:
            msg = f"Expected BitVec sort, got '{bv}'"
            raise TypeError(msg)
        return bv.ctx.mk_const(name, bv)
    return _resolve_ctx(ctx).mk_bv(name, bv)


def BitVecs(
    names: str | Sequence[str], bv: int | Sort, ctx: Context | None = None
) -> list[App]:
    """Create multiple ``BitVec`` constants from whitespace-separated names."""
    name_list = names.split() if isinstance(names, str) else list(names)
    return [BitVec(name, bv, ctx) for name in name_list]


def Array(name: str, index_sort: Sort, element_sort: Sort) -> App:
    """Create an ``Array`` symbolic constant over ``index_sort -> element_sort``."""
    if index_sort.ctx is not element_sort.ctx:
        msg = "Array index and element sorts belong to different Contexts"
        raise ValueError(msg)
    return index_sort.ctx.mk_array(name, index_sort, element_sort)


def Constant(name: str, sort: Sort) -> App:
    """Create a 0-arity symbolic constant named ``name`` of ``sort``."""
    return sort.ctx.mk_const(name, sort)


def Constants(names: str | Sequence[str], sort: Sort) -> list[App]:
    """Create multiple 0-arity constants of ``sort`` from names."""
    name_list = names.split() if isinstance(names, str) else list(names)
    return [sort.ctx.mk_const(name, sort) for name in name_list]


def Function(name: str, *sorts: Sort) -> FuncDecl:
    """Declare an uninterpreted function ``name`` over ``sorts[:-1] -> sorts[-1]``."""
    if not sorts:
        msg = "Function requires at least a range sort"
        raise ValueError(msg)
    range_sort = sorts[-1]
    domain = sorts[:-1]
    return range_sort.ctx.mk_decl(name, domain, range_sort)


def BoolVal(value: bool, ctx: Context | None = None) -> Const:
    """Create a Boolean literal constant ``true`` or ``false``."""
    return _resolve_ctx(ctx).mk_bool_val(value)


def IntVal(value: int, ctx: Context | None = None) -> Const:
    """Create an exact integer literal constant."""
    return _resolve_ctx(ctx).mk_int_val(value)


def RealVal(value: int | Fraction | str, ctx: Context | None = None) -> Const:
    """Create an exact rational ``Real`` literal constant."""
    return _resolve_ctx(ctx).mk_real_val(value)


def BitVecVal(val: int, bv: int | Sort, ctx: Context | None = None) -> Const:
    """Create a fixed-width ``BitVec`` constant literal."""
    if isinstance(bv, Sort):
        if not bv.is_bv:
            msg = f"Expected BitVec sort, got '{bv}'"
            raise TypeError(msg)
        return bv.ctx.mk_bv_val(val, bv.size)
    return _resolve_ctx(ctx).mk_bv_val(val, bv)


def _coerce_int_pair(a: Expr | int, b: Expr | int, op_name: str) -> tuple[Expr, Expr]:
    if isinstance(a, bool) or isinstance(b, bool):
        msg = f"{op_name} does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(a, Expr) and isinstance(b, Expr):
        return a, b
    if isinstance(a, Expr) and isinstance(b, int):
        return a, a.ctx.mk_int_val(b)
    if isinstance(b, Expr) and isinstance(a, int):
        return b.ctx.mk_int_val(a), b
    if isinstance(a, int) and isinstance(b, int):
        ctx = _default_ctx
        return ctx.mk_int_val(a), ctx.mk_int_val(b)
    msg = (
        f"{op_name} requires Int expressions or ints, "
        f"got {type(a).__name__} and {type(b).__name__}"
    )
    raise TypeError(msg)


def ToReal(expr: Expr | int) -> Expr:
    """Convert an ``Int`` expression to ``Real``."""
    if isinstance(expr, bool):
        msg = "ToReal does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(expr, int):
        return _default_ctx.mk_to_real(_default_ctx.mk_int_val(expr))
    return expr.ctx.mk_to_real(expr)


def ToInt(expr: Expr | int | Fraction) -> Expr:
    """Convert a ``Real`` expression to ``Int`` via ``to_int`` (floor)."""
    if isinstance(expr, bool):
        msg = "ToInt does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(expr, (int, Fraction)):
        return _default_ctx.mk_to_int(_default_ctx.mk_real_val(expr))
    return expr.ctx.mk_to_int(expr)


def IsInt(expr: Expr | int | Fraction) -> Expr:
    """Build integrality predicate ``(is_int expr)`` on a ``Real`` expression."""
    if isinstance(expr, bool):
        msg = "IsInt does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(expr, (int, Fraction)):
        return _default_ctx.mk_is_int(_default_ctx.mk_real_val(expr))
    return expr.ctx.mk_is_int(expr)


def Abs(expr: Expr | int) -> Expr:
    """Build integer absolute value ``(abs expr)``."""
    if isinstance(expr, bool):
        msg = "Abs does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(expr, int):
        return _default_ctx.mk_abs(_default_ctx.mk_int_val(expr))
    return expr.ctx.mk_abs(expr)


def IDiv(a: Expr | int, b: Expr | int) -> Expr:
    """Euclidean integer division ``(div a b)``."""
    lhs, rhs = _coerce_int_pair(a, b, "IDiv")
    return lhs.ctx.mk_idiv(lhs, rhs)


def Mod(a: Expr | int, b: Expr | int) -> Expr:
    """Euclidean integer remainder ``(mod a b)``."""
    lhs, rhs = _coerce_int_pair(a, b, "Mod")
    return lhs.ctx.mk_mod(lhs, rhs)


def Divisible(n: int, expr: Expr | int) -> Expr:
    """Build divisibility predicate ``((_ divisible n) expr)``."""
    if isinstance(expr, bool):
        msg = "Divisible does not accept Bool operands"
        raise TypeError(msg)
    target = _default_ctx.mk_int_val(expr) if isinstance(expr, int) else expr
    return target.ctx.mk_divisible(n, target)


def UDiv(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector division ``bvudiv(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "UDiv")
    return lhs.ctx.mk_bv_udiv(lhs, rhs)


def URem(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector remainder ``bvurem(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "URem")
    return lhs.ctx.mk_bv_urem(lhs, rhs)


def SDiv(a: Expr | int, b: Expr | int) -> Expr:
    """Signed bit-vector division ``bvsdiv(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "SDiv")
    return lhs.ctx.mk_bv_sdiv(lhs, rhs)


def SRem(a: Expr | int, b: Expr | int) -> Expr:
    """Signed bit-vector remainder ``bvsrem(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "SRem")
    return lhs.ctx.mk_bv_srem(lhs, rhs)


def SMod(a: Expr | int, b: Expr | int) -> Expr:
    """Signed bit-vector modulo ``bvsmod(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "SMod")
    return lhs.ctx.mk_bv_smod(lhs, rhs)


def LShR(a: Expr | int, b: Expr | int) -> Expr:
    """Logical right shift ``bvlshr(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "LShR")
    return lhs.ctx.mk_bv_lshr(lhs, rhs)


def ULT(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector less-than ``bvult(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "ULT")
    return lhs.ctx.mk_bv_ult(lhs, rhs)


def ULE(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector less-or-equal ``bvule(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "ULE")
    return lhs.ctx.mk_bv_ule(lhs, rhs)


def UGT(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector greater-than ``bvugt(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "UGT")
    return lhs.ctx.mk_bv_ugt(lhs, rhs)


def UGE(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector greater-or-equal ``bvuge(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "UGE")
    return lhs.ctx.mk_bv_uge(lhs, rhs)


def Concat(*args: Expr | str | Sequence[Expr | str]) -> Expr:
    """Concatenate bit-vectors, strings, or regular expressions."""
    flat: list[Expr | str] = []
    for item in args:
        if isinstance(item, (Expr, str)):
            flat.append(item)
        else:
            flat.extend(item)
    if not flat:
        msg = "Concat requires at least one BitVec, String, or RegLan argument"
        raise ValueError(msg)

    anchor = next((item for item in flat if isinstance(item, Expr)), None)
    if anchor is None:
        strs = [_default_ctx.mk_string_val(str(item)) for item in flat]
        return _default_ctx.mk_str_concat(*strs)

    ctx = anchor.ctx
    if anchor.is_string:
        str_args = [
            ctx.mk_string_val(item) if isinstance(item, str) else item for item in flat
        ]
        return ctx.mk_str_concat(*str_args)
    if anchor.is_reglan:
        re_args = [
            ctx.mk_str_to_re(ctx.mk_string_val(item)) if isinstance(item, str) else item
            for item in flat
        ]
        return ctx.mk_re_concat(*re_args)

    bv_args: list[Expr] = []
    for item in flat:
        if not isinstance(item, Expr):
            msg = f"Expected BitVec expression in Concat, got {item!r}"
            raise TypeError(msg)
        bv_args.append(item)
    return ctx.mk_concat(*bv_args)


def _coerce_str(arg: Expr | str, ctx: Context | None = None) -> Expr:
    if isinstance(arg, Expr):
        return arg
    return _resolve_ctx(ctx).mk_string_val(arg)


def _coerce_str_pair(a: Expr | str, b: Expr | str) -> tuple[Expr, Expr]:
    if isinstance(a, Expr):
        return a, _coerce_str(b, a.ctx)
    if isinstance(b, Expr):
        return _coerce_str(a, b.ctx), b
    return _default_ctx.mk_string_val(a), _default_ctx.mk_string_val(b)


def Length(expr: Expr | str) -> Expr:
    """Return string length ``(str.len expr)``."""
    s = _coerce_str(expr)
    return s.ctx.mk_str_len(s)


def At(s: Expr | str, index: Expr | int) -> Expr:
    """Return single-character substring at ``index`` via ``(str.at s index)``."""
    target = _coerce_str(s)
    idx_expr = _coerce_arg_for_sort(target.ctx.int_sort, index)
    return target.ctx.mk_str_at(target, idx_expr)


def SubString(s: Expr | str, offset: Expr | int, length: Expr | int) -> Expr:
    """Return substring ``(str.substr s offset length)``."""
    target = _coerce_str(s)
    ctx = target.ctx
    return ctx.mk_str_substr(
        target,
        _coerce_arg_for_sort(ctx.int_sort, offset),
        _coerce_arg_for_sort(ctx.int_sort, length),
    )


def IndexOf(s: Expr | str, substr: Expr | str, offset: Expr | int = 0) -> Expr:
    """Return first index of ``substr`` in ``s`` from ``offset`` (default ``0``)."""
    lhs, rhs = _coerce_str_pair(s, substr)
    ctx = lhs.ctx
    return ctx.mk_str_indexof(lhs, rhs, _coerce_arg_for_sort(ctx.int_sort, offset))


def Replace(s: Expr | str, src: Expr | str, dst: Expr | str) -> Expr:
    """Replace first occurrence of ``src`` with ``dst`` in ``s``."""
    anchor = next((x for x in (s, src, dst) if isinstance(x, Expr)), None)
    ctx = anchor.ctx if anchor is not None else _default_ctx
    return ctx.mk_str_replace(
        _coerce_str(s, ctx), _coerce_str(src, ctx), _coerce_str(dst, ctx)
    )


def ReplaceAll(s: Expr | str, src: Expr | str, dst: Expr | str) -> Expr:
    """Replace all occurrences of ``src`` with ``dst`` in ``s``."""
    anchor = next((x for x in (s, src, dst) if isinstance(x, Expr)), None)
    ctx = anchor.ctx if anchor is not None else _default_ctx
    return ctx.mk_str_replace_all(
        _coerce_str(s, ctx), _coerce_str(src, ctx), _coerce_str(dst, ctx)
    )


def Contains(s: Expr | str, substr: Expr | str) -> Expr:
    """Build substring predicate ``(str.contains s substr)``."""
    lhs, rhs = _coerce_str_pair(s, substr)
    return lhs.ctx.mk_str_contains(lhs, rhs)


def PrefixOf(prefix: Expr | str, s: Expr | str) -> Expr:
    """Build prefix predicate ``(str.prefixof prefix s)``."""
    lhs, rhs = _coerce_str_pair(prefix, s)
    return lhs.ctx.mk_str_prefixof(lhs, rhs)


def SuffixOf(suffix: Expr | str, s: Expr | str) -> Expr:
    """Build suffix predicate ``(str.suffixof suffix s)``."""
    lhs, rhs = _coerce_str_pair(suffix, s)
    return lhs.ctx.mk_str_suffixof(lhs, rhs)


def StrToInt(s: Expr | str) -> Expr:
    """Convert decimal digit string ``s`` to ``Int`` via ``str.to_int``."""
    target = _coerce_str(s)
    return target.ctx.mk_str_to_int(target)


def IntToStr(n: Expr | int) -> Expr:
    """Convert non-negative integer ``n`` to ``String`` via ``str.from_int``."""
    if isinstance(n, bool):
        msg = "IntToStr does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(n, int):
        return _default_ctx.mk_str_from_int(_default_ctx.mk_int_val(n))
    return n.ctx.mk_str_from_int(n)


def StrToCode(s: Expr | str) -> Expr:
    """Return Unicode code point of single-character ``s`` via ``str.to_code``."""
    target = _coerce_str(s)
    return target.ctx.mk_str_to_code(target)


def StrFromCode(n: Expr | int) -> Expr:
    """Return 1-character string for code point ``n`` via ``str.from_code``."""
    if isinstance(n, bool):
        msg = "StrFromCode does not accept Bool operands"
        raise TypeError(msg)
    if isinstance(n, int):
        return _default_ctx.mk_str_from_code(_default_ctx.mk_int_val(n))
    return n.ctx.mk_str_from_code(n)


def IsDigit(s: Expr | str) -> Expr:
    """Build ASCII digit predicate ``(str.is_digit s)``."""
    target = _coerce_str(s)
    return target.ctx.mk_str_is_digit(target)


def InRe(s: Expr | str, re: Expr) -> Expr:
    """Build regular-expression membership ``(str.in_re s re)``."""
    if isinstance(s, Expr):
        return s.ctx.mk_str_in_re(s, re)
    return re.ctx.mk_str_in_re(re.ctx.mk_string_val(s), re)


def Re(s: Expr | str, ctx: Context | None = None) -> Expr:
    """Lift a string into singleton regular expression ``(str.to_re s)``."""
    if isinstance(s, Expr):
        return s.ctx.mk_str_to_re(s)
    resolved = _resolve_ctx(ctx)
    return resolved.mk_str_to_re(resolved.mk_string_val(s))


def Union(*args: Expr | Sequence[Expr]) -> Expr:
    """Build regular-expression union ``(re.union ...)``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_re_none()
    return flat[0].ctx.mk_re_union(*flat)


def Intersect(*args: Expr | Sequence[Expr]) -> Expr:
    """Build regular-expression intersection ``(re.inter ...)``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_re_all()
    return flat[0].ctx.mk_re_inter(*flat)


def Complement(re: Expr) -> Expr:
    """Build regular-expression complement ``(re.comp re)``."""
    return re.ctx.mk_re_comp(re)


def ReDiff(lhs: Expr, rhs: Expr) -> Expr:
    """Build regular-expression difference ``(re.diff lhs rhs)``."""
    return lhs.ctx.mk_re_diff(lhs, rhs)


def Star(re: Expr) -> Expr:
    """Build Kleene closure ``(re.* re)``."""
    return re.ctx.mk_re_star(re)


def Plus(re: Expr) -> Expr:
    """Build non-empty Kleene closure ``(re.+ re)``."""
    return re.ctx.mk_re_plus(re)


def Option(re: Expr) -> Expr:
    """Build optional regular expression ``(re.opt re)``."""
    return re.ctx.mk_re_opt(re)


def Range(lo: Expr | str, hi: Expr | str, ctx: Context | None = None) -> Expr:
    """Build single-character range regular expression ``(re.range lo hi)``."""
    if isinstance(lo, Expr):
        return lo.ctx.mk_re_range(lo, _coerce_str(hi, lo.ctx))
    if isinstance(hi, Expr):
        return hi.ctx.mk_re_range(_coerce_str(lo, hi.ctx), hi)
    resolved = _resolve_ctx(ctx)
    return resolved.mk_re_range(resolved.mk_string_val(lo), resolved.mk_string_val(hi))


def ReEmpty(ctx: Context | None = None) -> Expr:
    """Return the empty regular language ``re.none``."""
    return _resolve_ctx(ctx).mk_re_none()


def ReFull(ctx: Context | None = None) -> Expr:
    """Return the universal regular language ``re.all``."""
    return _resolve_ctx(ctx).mk_re_all()


def ReAllChar(ctx: Context | None = None) -> Expr:
    """Return the single-character wildcard regex ``re.allchar``."""
    return _resolve_ctx(ctx).mk_re_allchar()


def RePower(re: Expr, n: int) -> Expr:
    """Build bounded regex repetition ``((_ re.^ n) re)``."""
    return re.ctx.mk_re_power(n, re)


def Loop(re: Expr, lo: int, hi: int) -> Expr:
    """Build bounded regex loop ``((_ re.loop lo hi) re)``."""
    return re.ctx.mk_re_loop(lo, hi, re)


def Extract(high: int, low: int, a: Expr) -> Expr:
    """Extract bit slice ``a[high:low]`` (inclusive, 0 = LSB)."""
    return a.ctx.mk_extract(high, low, a)


def ZeroExt(n: int, a: Expr) -> Expr:
    """Zero-extend bit-vector ``a`` by ``n`` bits."""
    return a.ctx.mk_zero_ext(n, a)


def SignExt(n: int, a: Expr) -> Expr:
    """Sign-extend bit-vector ``a`` by ``n`` bits."""
    return a.ctx.mk_sign_ext(n, a)


def RotateLeft(a: Expr, n: int) -> Expr:
    """Rotate bit-vector ``a`` left by ``n`` bits."""
    return a.ctx.mk_rotate_left(n, a)


def RotateRight(a: Expr, n: int) -> Expr:
    """Rotate bit-vector ``a`` right by ``n`` bits."""
    return a.ctx.mk_rotate_right(n, a)


def Repeat(n: int, a: Expr) -> Expr:
    """Concatenate ``n`` copies of bit-vector ``a``."""
    return a.ctx.mk_repeat(n, a)


def Select(array: Expr, index: Expr | bool | int | Fraction) -> Expr:
    """Read the element at ``index`` in ``array``."""
    if not array.is_array:
        msg = f"Expected Array expression in Select, got '{array.sort}'"
        raise TypeError(msg)
    idx_expr = _coerce_arg_for_sort(array.sort.index_sort, index)
    return array.ctx.mk_select(array, idx_expr)


def Store(
    array: Expr,
    index: Expr | bool | int | Fraction,
    value: Expr | bool | int | Fraction,
) -> Expr:
    """Store ``value`` at ``index`` in ``array``, returning the updated array."""
    if not array.is_array:
        msg = f"Expected Array expression in Store, got '{array.sort}'"
        raise TypeError(msg)
    idx_expr = _coerce_arg_for_sort(array.sort.index_sort, index)
    val_expr = _coerce_arg_for_sort(array.sort.element_sort, value)
    return array.ctx.mk_store(array, idx_expr, val_expr)


def K(domain: Sort, value: Expr | bool | int | Fraction | str) -> App:
    """Construct a constant array mapping every key in ``domain`` to ``value``."""
    if isinstance(value, Expr):
        return domain.ctx.mk_const_array(domain, value)
    if isinstance(value, bool):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_bool_val(value))
    if isinstance(value, int):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_int_val(value))
    if isinstance(value, Fraction):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_real_val(value))
    if isinstance(value, str):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_string_val(value))
    msg = f"Unsupported constant array value: {value!r}"
    raise TypeError(msg)


def Sum(*args: Expr | Sequence[Expr]) -> Expr:
    """Build an n-ary arithmetic sum over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_int_val(0)
    return flat[0].ctx.mk_add(*flat)


def And(*args: Expr | Sequence[Expr]) -> Expr:
    """Build a logical conjunction over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_true()
    return flat[0].ctx.mk_and(*flat)


def Or(*args: Expr | Sequence[Expr]) -> Expr:
    """Build a logical disjunction over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_false()
    return flat[0].ctx.mk_or(*flat)


def Not(arg: Expr) -> Expr:
    """Build the logical negation of ``arg``."""
    return arg.ctx.mk_not(arg)


def Implies(lhs: Expr, rhs: Expr) -> Expr:
    """Build the logical implication ``lhs => rhs``."""
    return lhs.ctx.mk_implies(lhs, rhs)


def Xor(lhs: Expr, rhs: Expr) -> Expr:
    """Build the logical exclusive-OR ``lhs xor rhs``."""
    return lhs.ctx.mk_xor(lhs, rhs)


def Eq(
    lhs: Expr | bool | int | Fraction | str,
    rhs: Expr | bool | int | Fraction | str,
) -> Expr:
    """Build the formula-level equality ``lhs = rhs``."""
    if isinstance(lhs, Expr):
        return lhs.ctx.mk_eq(lhs, _coerce_arg_for_sort(lhs.sort, rhs))
    if isinstance(rhs, Expr):
        return rhs.ctx.mk_eq(_coerce_arg_for_sort(rhs.sort, lhs), rhs)
    msg = f"Eq requires at least one Expr argument, got {lhs!r} and {rhs!r}"
    raise TypeError(msg)


def Distinct(
    *args: Expr
    | bool
    | int
    | Fraction
    | str
    | Sequence[Expr | bool | int | Fraction | str],
) -> Expr:
    """Build a pairwise-distinct constraint over ``args``."""
    flat = _flatten_coercible_args(args)
    if not flat:
        return _default_ctx.mk_true()
    anchor = next((item for item in flat if isinstance(item, Expr)), None)
    if anchor is None:
        msg = "Distinct requires at least one Expr argument when non-empty"
        raise TypeError(msg)
    coerced = [_coerce_arg_for_sort(anchor.sort, item) for item in flat]
    return anchor.ctx.mk_distinct(*coerced)


def If(
    cond: Expr,
    then_branch: Expr | bool | int | Fraction | str,
    else_branch: Expr | bool | int | Fraction | str,
) -> Expr:
    """Build an if-then-else expression ``ite(cond, then_branch, else_branch)``."""
    if not isinstance(cond, Expr):
        msg = f"If condition must be an Expr, got {cond!r}"
        raise TypeError(msg)
    if isinstance(then_branch, Expr):
        return cond.ctx.mk_ite(
            cond, then_branch, _coerce_arg_for_sort(then_branch.sort, else_branch)
        )
    if isinstance(else_branch, Expr):
        return cond.ctx.mk_ite(
            cond, _coerce_arg_for_sort(else_branch.sort, then_branch), else_branch
        )
    t_expr, e_expr = _coerce_literal_pair(cond.ctx, then_branch, else_branch)
    return cond.ctx.mk_ite(cond, t_expr, e_expr)


def ForAll(
    vs: Expr | Sequence[Expr],
    body: Expr,
    *,
    patterns: Sequence[Expr | Sequence[Expr]] = (),
) -> Expr:
    """Build a universally quantified formula ``ForAll(vs, body)``."""
    bound = (vs,) if isinstance(vs, Expr) else tuple(vs)
    if not bound:
        return _default_ctx.mk_forall(bound, body, patterns=patterns)
    return bound[0].ctx.mk_forall(bound, body, patterns=patterns)


def Exists(
    vs: Expr | Sequence[Expr],
    body: Expr,
    *,
    patterns: Sequence[Expr | Sequence[Expr]] = (),
) -> Expr:
    """Build an existentially quantified formula ``Exists(vs, body)``."""
    bound = (vs,) if isinstance(vs, Expr) else tuple(vs)
    if not bound:
        return _default_ctx.mk_exists(bound, body, patterns=patterns)
    return bound[0].ctx.mk_exists(bound, body, patterns=patterns)


def MultiPattern(*terms: Expr) -> tuple[Expr, ...]:
    """Group multiple trigger expressions into one multi-pattern tuple."""
    if not terms:
        msg = "MultiPattern requires at least one trigger expression"
        raise ValueError(msg)
    ctx = terms[0].ctx
    for term in terms[1:]:
        if term.ctx is not ctx:
            msg = f"Expr '{term}' belongs to a different Context"
            raise ValueError(msg)
    return tuple(terms)


class Solver:
    """User-facing incremental SMT solver facade."""

    def __init__(
        self,
        ctx: Context | None = None,
        *,
        max_quantifier_rounds: int | None = None,
        max_quantifier_matches: int | None = None,
        timeout: float | None = None,
        max_conflicts: int | None = None,
    ) -> None:
        self._solver = SMTSolver(
            _resolve_ctx(ctx),
            max_quantifier_rounds=max_quantifier_rounds,
            max_quantifier_matches=max_quantifier_matches,
            timeout=timeout,
            max_conflicts=max_conflicts,
        )

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._solver.ctx

    def add(self, *formulas: Expr) -> None:
        """Assert one or more formulas into the current scope."""
        self._solver.add(*formulas)

    def check(
        self,
        *assumptions: Expr,
        timeout: float | None = None,
        max_conflicts: int | None = None,
    ) -> SolveResult:
        """Check satisfiability under optional assumption formulas."""
        return self._solver.check(
            *assumptions, timeout=timeout, max_conflicts=max_conflicts
        )

    def model(self) -> Model:
        """Return a satisfying :class:`Model` from the latest ``check()``."""
        return self._solver.model()

    def unsat_core(self) -> list[Expr]:
        """Return the assumption subset responsible for the last ``UNSAT``."""
        return self._solver.unsat_core()

    def push(self) -> None:
        """Push a new incremental assertion scope."""
        self._solver.push()

    def pop(self, levels: int = 1) -> None:
        """Pop ``levels`` incremental assertion scopes."""
        self._solver.pop(levels)

    def reset(self) -> None:
        """Reset all asserted formulas and scopes."""
        self._solver.reset()

    def assertions(self) -> list[Expr]:
        """Return all active asserted formulas."""
        return self._solver.assertions()

    def statistics(self) -> dict[str, int]:
        """Return solver search counters."""
        stats = self._solver.statistics()
        return {key: val for key, val in stats.items() if isinstance(val, int)}


__all__ = [
    "SAT",
    "UGE",
    "UGT",
    "ULE",
    "ULT",
    "UNKNOWN",
    "UNSAT",
    "Abs",
    "And",
    "App",
    "Array",
    "ArraySort",
    "At",
    "BitVec",
    "BitVecSort",
    "BitVecVal",
    "BitVecs",
    "Bool",
    "BoolSort",
    "BoolVal",
    "Bools",
    "BoundVar",
    "Complement",
    "Concat",
    "Const",
    "Constant",
    "Constants",
    "Contains",
    "Context",
    "DeclareSort",
    "Distinct",
    "Divisible",
    "Eq",
    "Exists",
    "Expr",
    "Extract",
    "ForAll",
    "FuncDecl",
    "FuncInterp",
    "Function",
    "IDiv",
    "If",
    "Implies",
    "InRe",
    "IndexOf",
    "Int",
    "IntSort",
    "IntToStr",
    "IntVal",
    "Intersect",
    "Ints",
    "IsDigit",
    "IsInt",
    "K",
    "LShR",
    "Length",
    "Loop",
    "Mod",
    "Model",
    "MultiPattern",
    "Not",
    "Option",
    "Or",
    "Plus",
    "PrefixOf",
    "Quantifier",
    "Range",
    "Re",
    "ReAllChar",
    "ReDiff",
    "ReEmpty",
    "ReFull",
    "RePower",
    "Real",
    "RealSort",
    "RealVal",
    "Reals",
    "RegLanSort",
    "Repeat",
    "Replace",
    "ReplaceAll",
    "RotateLeft",
    "RotateRight",
    "SDiv",
    "SMod",
    "SRem",
    "Select",
    "SignExt",
    "SolveResult",
    "Solver",
    "Sort",
    "Star",
    "Store",
    "StrFromCode",
    "StrToCode",
    "StrToInt",
    "String",
    "StringSort",
    "StringVal",
    "Strings",
    "SubString",
    "SuffixOf",
    "Sum",
    "ToInt",
    "ToReal",
    "UDiv",
    "URem",
    "Union",
    "Xor",
    "ZeroExt",
    "default_context",
    "reset_default_context",
    "set_default_context",
]
