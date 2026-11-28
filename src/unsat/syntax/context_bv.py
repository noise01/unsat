"""Bit-vector and Array expression normalization helpers for :class:`Context`."""

from typing import TYPE_CHECKING

from unsat.syntax.bv_eval import (
    _bv_mask,
    _bv_sdiv,
    _bv_smod,
    _bv_srem,
    _bv_to_signed,
    _bv_udiv,
    _bv_urem,
)
from unsat.syntax.expr import App, Const, Expr, Sort
from unsat.syntax.kinds import DeclKind

if TYPE_CHECKING:
    from unsat.syntax.context import Context


def build_bv_not(ctx: Context, arg: Expr) -> Expr:
    """Build bitwise negation ``(bvnot arg)``."""
    width = ctx._check_bv(arg)
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        return ctx.mk_bv_val((~arg.value) & _bv_mask(width), width)
    if isinstance(arg, App) and arg.decl.kind is DeclKind.BV_NOT:
        return arg.args[0]
    decl = ctx._intern_decl(DeclKind.BV_NOT, "bvnot", (arg.sort,), arg.sort)
    return ctx._intern_app(decl, (arg,))


def build_bv_neg(ctx: Context, arg: Expr) -> Expr:
    """Build two's-complement negation ``(bvneg arg)``."""
    width = ctx._check_bv(arg)
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        return ctx.mk_bv_val((-arg.value) & _bv_mask(width), width)
    if isinstance(arg, App) and arg.decl.kind is DeclKind.BV_NEG:
        return arg.args[0]
    decl = ctx._intern_decl(DeclKind.BV_NEG, "bvneg", (arg.sort,), arg.sort)
    return ctx._intern_app(decl, (arg,))


def build_bv_and(ctx: Context, *args: Expr) -> Expr:
    """Build bitwise conjunction ``(bvand ...)``."""
    if not args:
        msg = "mk_bv_and requires at least one argument"
        raise ValueError(msg)
    width = ctx._check_bv(args[0])
    sort = args[0].sort
    mask = _bv_mask(width)
    const_bits = mask
    non_const: list[Expr] = []
    seen: set[Expr] = set()
    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in bvand: '{sort}' vs '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.BV_AND:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert isinstance(item.value, int)
            assert not isinstance(item.value, bool)
            const_bits &= item.value
        elif item not in seen:
            seen.add(item)
            non_const.append(item)
    if const_bits == 0 or not non_const:
        return ctx.mk_bv_val(const_bits, width)
    terms = tuple(non_const) if const_bits == mask else (*non_const, ctx.mk_bv_val(const_bits, width))
    if len(terms) == 1:
        return terms[0]
    decl = ctx._intern_decl(DeclKind.BV_AND, "bvand", (sort,) * len(terms), sort)
    return ctx._intern_app(decl, terms)


def build_bv_or(ctx: Context, *args: Expr) -> Expr:
    """Build bitwise disjunction ``(bvor ...)``."""
    if not args:
        msg = "mk_bv_or requires at least one argument"
        raise ValueError(msg)
    width = ctx._check_bv(args[0])
    sort = args[0].sort
    mask = _bv_mask(width)
    const_bits = 0
    non_const: list[Expr] = []
    seen: set[Expr] = set()
    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in bvor: '{sort}' vs '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.BV_OR:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert isinstance(item.value, int)
            assert not isinstance(item.value, bool)
            const_bits |= item.value
        elif item not in seen:
            seen.add(item)
            non_const.append(item)
    if const_bits == mask or not non_const:
        return ctx.mk_bv_val(const_bits, width)
    terms = tuple(non_const) if const_bits == 0 else (*non_const, ctx.mk_bv_val(const_bits, width))
    if len(terms) == 1:
        return terms[0]
    decl = ctx._intern_decl(DeclKind.BV_OR, "bvor", (sort,) * len(terms), sort)
    return ctx._intern_app(decl, terms)


def build_bv_xor(ctx: Context, *args: Expr) -> Expr:
    """Build bitwise exclusive-OR ``(bvxor ...)``."""
    if not args:
        msg = "mk_bv_xor requires at least one argument"
        raise ValueError(msg)
    width = ctx._check_bv(args[0])
    sort = args[0].sort
    const_bits = 0
    counts: dict[Expr, int] = {}
    order: list[Expr] = []
    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in bvxor: '{sort}' vs '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.BV_XOR:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert isinstance(item.value, int)
            assert not isinstance(item.value, bool)
            const_bits ^= item.value
        elif item not in counts:
            order.append(item)
            counts[item] = 1
        else:
            counts[item] += 1
    kept = [item for item in order if counts[item] % 2 == 1]
    if not kept:
        return ctx.mk_bv_val(const_bits, width)
    terms = tuple(kept) if const_bits == 0 else (*kept, ctx.mk_bv_val(const_bits, width))
    if len(terms) == 1:
        return terms[0]
    decl = ctx._intern_decl(DeclKind.BV_XOR, "bvxor", (sort,) * len(terms), sort)
    return ctx._intern_app(decl, terms)


def build_bv_add(ctx: Context, *args: Expr) -> Expr:
    """Build modular bit-vector addition ``(bvadd ...)``."""
    if not args:
        msg = "mk_bv_add requires at least one argument"
        raise ValueError(msg)
    width = ctx._check_bv(args[0])
    sort = args[0].sort
    mask = _bv_mask(width)
    const_sum = 0
    non_const: list[Expr] = []
    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in bvadd: '{sort}' vs '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.BV_ADD:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert isinstance(item.value, int)
            assert not isinstance(item.value, bool)
            const_sum = (const_sum + item.value) & mask
        else:
            non_const.append(item)
    if not non_const:
        return ctx.mk_bv_val(const_sum, width)
    if const_sum != 0:
        non_const.append(ctx.mk_bv_val(const_sum, width))
    if len(non_const) == 1:
        return non_const[0]
    decl = ctx._intern_decl(DeclKind.BV_ADD, "bvadd", (sort,) * len(non_const), sort)
    return ctx._intern_app(decl, tuple(non_const))


def build_bv_sub(ctx: Context, lhs: Expr, rhs: Expr) -> Expr:
    """Build modular bit-vector subtraction ``(bvsub lhs rhs)``."""
    width = ctx._check_bv_pair(lhs, rhs, "bvsub")
    if lhs is rhs:
        return ctx.mk_bv_val(0, width)
    if isinstance(lhs, Const) and isinstance(rhs, Const):
        assert isinstance(lhs.value, int)
        assert isinstance(rhs.value, int)
        assert not isinstance(lhs.value, bool)
        assert not isinstance(rhs.value, bool)
        return ctx.mk_bv_val(lhs.value - rhs.value, width)
    if isinstance(rhs, Const) and rhs.value == 0:
        return lhs
    decl = ctx._intern_decl(DeclKind.BV_SUB, "bvsub", (lhs.sort, rhs.sort), lhs.sort)
    return ctx._intern_app(decl, (lhs, rhs))


def build_bv_mul(ctx: Context, *args: Expr) -> Expr:
    """Build modular bit-vector multiplication ``(bvmul ...)``."""
    if not args:
        msg = "mk_bv_mul requires at least one argument"
        raise ValueError(msg)
    width = ctx._check_bv(args[0])
    sort = args[0].sort
    mask = _bv_mask(width)
    const_prod = 1
    non_const: list[Expr] = []
    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_expr(item)
        if item.sort is not sort:
            msg = f"Sort mismatch in bvmul: '{sort}' vs '{item.sort}'"
            raise TypeError(msg)
        if isinstance(item, App) and item.decl.kind is DeclKind.BV_MUL:
            stack.extend(reversed(item.args))
        elif isinstance(item, Const):
            assert isinstance(item.value, int)
            assert not isinstance(item.value, bool)
            const_prod = (const_prod * item.value) & mask
        else:
            non_const.append(item)
    if const_prod == 0 or not non_const:
        return ctx.mk_bv_val(const_prod, width)
    if const_prod == mask and len(non_const) == 1:
        return ctx.mk_bv_neg(non_const[0])
    if const_prod == 1:
        if len(non_const) == 1:
            return non_const[0]
        factors = tuple(non_const)
    else:
        factors = (ctx.mk_bv_val(const_prod, width), *non_const)
    decl = ctx._intern_decl(DeclKind.BV_MUL, "bvmul", (sort,) * len(factors), sort)
    return ctx._intern_app(decl, factors)


def build_bv_bin(ctx: Context, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
    """Build a normalized binary bit-vector division, remainder, or shift."""
    width = ctx._check_bv_pair(lhs, rhs, kind.value)
    mask = _bv_mask(width)
    if isinstance(lhs, Const) and isinstance(rhs, Const):
        assert isinstance(lhs.value, int)
        assert isinstance(rhs.value, int)
        assert not isinstance(lhs.value, bool)
        assert not isinstance(rhs.value, bool)
        a, b = lhs.value, rhs.value
        match kind:
            case DeclKind.BV_UDIV:
                return ctx.mk_bv_val(_bv_udiv(a, b, mask), width)
            case DeclKind.BV_UREM:
                return ctx.mk_bv_val(_bv_urem(a, b), width)
            case DeclKind.BV_SDIV:
                return ctx.mk_bv_val(_bv_sdiv(a, b, width, mask), width)
            case DeclKind.BV_SREM:
                return ctx.mk_bv_val(_bv_srem(a, b, width, mask), width)
            case DeclKind.BV_SMOD:
                return ctx.mk_bv_val(_bv_smod(a, b, width, mask), width)
            case DeclKind.BV_SHL:
                return ctx.mk_bv_val(0 if b >= width else (a << b) & mask, width)
            case DeclKind.BV_LSHR:
                return ctx.mk_bv_val(0 if b >= width else a >> b, width)
            case DeclKind.BV_ASHR:
                sign_bit = 1 << (width - 1)
                if b >= width:
                    return ctx.mk_bv_val(mask if (a & sign_bit) else 0, width)
                return ctx.mk_bv_val(_bv_to_signed(a, width) >> b, width)
            case _:
                pass
    decl = ctx._intern_decl(kind, kind.value, (lhs.sort, rhs.sort), lhs.sort)
    return ctx._intern_app(decl, (lhs, rhs))


def build_bv_cmp(ctx: Context, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
    """Build a normalized bit-vector comparison atom."""
    width = ctx._check_bv_pair(lhs, rhs, kind.value)
    if lhs is rhs:
        return ctx.mk_bool_val(kind in (DeclKind.BV_ULE, DeclKind.BV_UGE, DeclKind.BV_SLE, DeclKind.BV_SGE))
    if isinstance(lhs, Const) and isinstance(rhs, Const):
        assert isinstance(lhs.value, int)
        assert isinstance(rhs.value, int)
        assert not isinstance(lhs.value, bool)
        assert not isinstance(rhs.value, bool)
        a, b = lhs.value, rhs.value
        sa, sb = _bv_to_signed(a, width), _bv_to_signed(b, width)
        match kind:
            case DeclKind.BV_ULT:
                res = a < b
            case DeclKind.BV_ULE:
                res = a <= b
            case DeclKind.BV_UGT:
                res = a > b
            case DeclKind.BV_UGE:
                res = a >= b
            case DeclKind.BV_SLT:
                res = sa < sb
            case DeclKind.BV_SLE:
                res = sa <= sb
            case DeclKind.BV_SGT:
                res = sa > sb
            case DeclKind.BV_SGE:
                res = sa >= sb
            case _:
                res = False
        return ctx.mk_bool_val(res)
    decl = ctx._intern_decl(kind, kind.value, (lhs.sort, rhs.sort), ctx.bool_sort)
    return ctx._intern_app(decl, (lhs, rhs))


def build_concat(ctx: Context, *args: Expr) -> Expr:
    """Concatenate bit-vectors from most-significant to least-significant."""
    if not args:
        msg = "mk_concat requires at least one BitVec argument"
        raise ValueError(msg)
    flat: list[Expr] = []
    stack: list[Expr] = list(reversed(args))
    while stack:
        item = stack.pop()
        ctx._check_bv(item)
        if isinstance(item, App) and item.decl.kind is DeclKind.BV_CONCAT:
            stack.extend(reversed(item.args))
        else:
            flat.append(item)

    merged: list[Expr] = []
    for item in flat:
        if merged and isinstance(merged[-1], Const) and isinstance(item, Const):
            prev = merged[-1]
            assert isinstance(prev.value, int)
            assert isinstance(item.value, int)
            assert not isinstance(prev.value, bool)
            assert not isinstance(item.value, bool)
            w_item = item.sort.size
            merged[-1] = ctx.mk_bv_val((prev.value << w_item) | item.value, prev.sort.size + w_item)
        else:
            merged.append(item)

    if len(merged) == 1:
        return merged[0]
    total_width = sum(part.sort.size for part in merged)
    range_sort = ctx.mk_bv_sort(total_width)
    domain = tuple(part.sort for part in merged)
    decl = ctx._intern_decl(DeclKind.BV_CONCAT, "concat", domain, range_sort)
    return ctx._intern_app(decl, tuple(merged))


def build_extract(ctx: Context, high: int, low: int, arg: Expr) -> Expr:
    """Extract bits ``[high:low]`` (inclusive, 0 = LSB) from ``arg``."""
    width = ctx._check_bv(arg)
    if isinstance(high, bool) or isinstance(low, bool) or not isinstance(high, int) or not isinstance(low, int):
        msg = "Extract bounds must be int"
        raise TypeError(msg)
    if low < 0 or high < low or high >= width:
        msg = f"Invalid extract bounds [{high}:{low}] for {width}-bit vector"
        raise ValueError(msg)
    if low == 0 and high == width - 1:
        return arg
    out_width = high - low + 1
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        return ctx.mk_bv_val((arg.value >> low) & _bv_mask(out_width), out_width)
    out_sort = ctx.mk_bv_sort(out_width)
    decl = ctx._intern_decl(
        DeclKind.BV_EXTRACT,
        f"(_ extract {high} {low})",
        (arg.sort,),
        out_sort,
        params=(high, low),
    )
    return ctx._intern_app(decl, (arg,))


def build_zero_ext(ctx: Context, n: int, arg: Expr) -> Expr:
    """Zero-extend bit-vector ``arg`` by ``n`` high-order zero bits."""
    width = ctx._check_bv(arg)
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        msg = f"zero_extend width must be a non-negative int, got {n!r}"
        raise ValueError(msg)
    if n == 0:
        return arg
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        return ctx.mk_bv_val(arg.value, width + n)
    out_sort = ctx.mk_bv_sort(width + n)
    decl = ctx._intern_decl(
        DeclKind.BV_ZERO_EXT,
        f"(_ zero_extend {n})",
        (arg.sort,),
        out_sort,
        params=(n,),
    )
    return ctx._intern_app(decl, (arg,))


def build_sign_ext(ctx: Context, n: int, arg: Expr) -> Expr:
    """Sign-extend bit-vector ``arg`` by ``n`` high-order copies of its MSB."""
    width = ctx._check_bv(arg)
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        msg = f"sign_extend width must be a non-negative int, got {n!r}"
        raise ValueError(msg)
    if n == 0:
        return arg
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        return ctx.mk_bv_val(_bv_to_signed(arg.value, width), width + n)
    out_sort = ctx.mk_bv_sort(width + n)
    decl = ctx._intern_decl(
        DeclKind.BV_SIGN_EXT,
        f"(_ sign_extend {n})",
        (arg.sort,),
        out_sort,
        params=(n,),
    )
    return ctx._intern_app(decl, (arg,))


def build_rotate_left(ctx: Context, n: int, arg: Expr) -> Expr:
    """Rotate bit-vector ``arg`` left by ``n`` bits."""
    width = ctx._check_bv(arg)
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        msg = f"rotate_left distance must be a non-negative int, got {n!r}"
        raise ValueError(msg)
    shift = n % width
    if shift == 0:
        return arg
    mask = _bv_mask(width)
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        val = arg.value
        rot = ((val << shift) | (val >> (width - shift))) & mask
        return ctx.mk_bv_val(rot, width)
    decl = ctx._intern_decl(
        DeclKind.BV_ROTATE_LEFT,
        f"(_ rotate_left {shift})",
        (arg.sort,),
        arg.sort,
        params=(shift,),
    )
    return ctx._intern_app(decl, (arg,))


def build_rotate_right(ctx: Context, n: int, arg: Expr) -> Expr:
    """Rotate bit-vector ``arg`` right by ``n`` bits."""
    width = ctx._check_bv(arg)
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        msg = f"rotate_right distance must be a non-negative int, got {n!r}"
        raise ValueError(msg)
    shift = n % width
    if shift == 0:
        return arg
    mask = _bv_mask(width)
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        val = arg.value
        rot = ((val >> shift) | (val << (width - shift))) & mask
        return ctx.mk_bv_val(rot, width)
    decl = ctx._intern_decl(
        DeclKind.BV_ROTATE_RIGHT,
        f"(_ rotate_right {shift})",
        (arg.sort,),
        arg.sort,
        params=(shift,),
    )
    return ctx._intern_app(decl, (arg,))


def build_repeat(ctx: Context, n: int, arg: Expr) -> Expr:
    """Concatenate ``n >= 1`` copies of bit-vector ``arg``."""
    width = ctx._check_bv(arg)
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        msg = f"repeat count must be a positive int, got {n!r}"
        raise ValueError(msg)
    if n == 1:
        return arg
    if isinstance(arg, Const):
        assert isinstance(arg.value, int)
        assert not isinstance(arg.value, bool)
        acc = 0
        for _ in range(n):
            acc = (acc << width) | arg.value
        return ctx.mk_bv_val(acc, width * n)
    out_sort = ctx.mk_bv_sort(width * n)
    decl = ctx._intern_decl(
        DeclKind.BV_REPEAT,
        f"(_ repeat {n})",
        (arg.sort,),
        out_sort,
        params=(n,),
    )
    return ctx._intern_app(decl, (arg,))


def build_select(ctx: Context, array: Expr, index: Expr) -> Expr:
    """Read element at ``index`` from ``array``."""
    arr_sort = ctx._check_array(array)
    ctx._check_expr(index)
    if index.sort is not arr_sort.index_sort:
        msg = f"Sort mismatch in Array select index: expected '{arr_sort.index_sort}', got '{index.sort}'"
        raise TypeError(msg)

    cur = array
    while isinstance(cur, App):
        if cur.decl.kind is DeclKind.CONST_ARRAY:
            return cur.args[0]
        if cur.decl.kind is DeclKind.STORE:
            base, st_idx, st_val = cur.args
            if st_idx is index:
                return st_val
            if isinstance(st_idx, Const) and isinstance(index, Const):
                cur = base
                continue
            break
        break

    decl = ctx._intern_decl(
        DeclKind.SELECT,
        "select",
        (arr_sort, arr_sort.index_sort),
        arr_sort.element_sort,
    )
    return ctx._intern_app(decl, (cur, index))


def build_store(ctx: Context, array: Expr, index: Expr, value: Expr) -> Expr:
    """Write ``value`` at ``index`` in ``array``, returning a new array."""
    arr_sort = ctx._check_array(array)
    ctx._check_expr(index)
    ctx._check_expr(value)
    if index.sort is not arr_sort.index_sort:
        msg = f"Sort mismatch in Array store index: expected '{arr_sort.index_sort}', got '{index.sort}'"
        raise TypeError(msg)
    if value.sort is not arr_sort.element_sort:
        msg = f"Sort mismatch in Array store value: expected '{arr_sort.element_sort}', got '{value.sort}'"
        raise TypeError(msg)

    cur = array
    if isinstance(cur, App) and cur.decl.kind is DeclKind.CONST_ARRAY and cur.args[0] is value:
        return cur
    while isinstance(cur, App) and cur.decl.kind is DeclKind.STORE and cur.args[1] is index:
        cur = cur.args[0]
    if isinstance(cur, App) and cur.decl.kind is DeclKind.CONST_ARRAY and cur.args[0] is value:
        return cur

    decl = ctx._intern_decl(
        DeclKind.STORE,
        "store",
        (arr_sort, arr_sort.index_sort, arr_sort.element_sort),
        arr_sort,
    )
    return ctx._intern_app(decl, (cur, index, value))


def build_const_array(ctx: Context, index_sort: Sort, value: Expr) -> App:
    """Construct constant array mapping every ``index_sort`` key to ``value``."""
    ctx._check_sort(index_sort)
    ctx._check_expr(value)
    arr_sort = ctx.mk_array_sort(index_sort, value.sort)
    decl = ctx._intern_decl(
        DeclKind.CONST_ARRAY,
        f"(as const {arr_sort.name})",
        (value.sort,),
        arr_sort,
    )
    return ctx._intern_app(decl, (value,))
