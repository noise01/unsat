"""String and regular-expression AST builder helpers for :class:`Context`."""

from __future__ import annotations

from typing import TYPE_CHECKING

from unsat.syntax.expr import App, Const, Expr
from unsat.syntax.kinds import DeclKind
from unsat.syntax.str_eval import (
    RE_ALL,
    RE_ALLCHAR,
    RE_EMPTY,
    ReNode,
    eval_str_at,
    eval_str_from_code,
    eval_str_from_int,
    eval_str_indexof,
    eval_str_is_digit,
    eval_str_replace,
    eval_str_replace_all,
    eval_str_substr,
    eval_str_to_code,
    eval_str_to_int,
    re_comp,
    re_concat,
    re_diff,
    re_from_str,
    re_inter,
    re_loop,
    re_matches,
    re_opt,
    re_plus,
    re_power,
    re_range,
    re_star,
    re_union,
)


def expr_to_re(expr: Expr) -> ReNode | None:
    """Compile a ground ``RegLan`` expression to a canonical :data:`ReNode`."""
    memo: dict[Expr, ReNode | None] = {}
    stack: list[tuple[Expr, bool]] = [(expr, False)]
    while stack:
        node, expanded = stack.pop()
        if node in memo:
            continue
        if not isinstance(node, App) or node.decl.is_uninterpreted:
            memo[node] = None
            continue
        if not expanded and node.args:
            stack.append((node, True))
            for arg in reversed(node.args):
                if arg not in memo:
                    stack.append((arg, False))
            continue

        kind = node.decl.kind
        match kind:
            case DeclKind.STR_TO_RE:
                arg0 = node.args[0]
                if not isinstance(arg0, Const) or not arg0.is_string:
                    memo[node] = None
                else:
                    assert isinstance(arg0.value, str)
                    memo[node] = re_from_str(arg0.value)
            case DeclKind.RE_NONE:
                memo[node] = RE_EMPTY
            case DeclKind.RE_ALL:
                memo[node] = RE_ALL
            case DeclKind.RE_ALLCHAR:
                memo[node] = RE_ALLCHAR
            case DeclKind.RE_RANGE:
                lo_e, hi_e = node.args
                if (
                    isinstance(lo_e, Const)
                    and isinstance(hi_e, Const)
                    and lo_e.is_string
                    and hi_e.is_string
                ):
                    assert isinstance(lo_e.value, str)
                    assert isinstance(hi_e.value, str)
                    memo[node] = re_range(lo_e.value, hi_e.value)
                else:
                    memo[node] = None
            case DeclKind.RE_CONCAT:
                parts = [memo[a] for a in node.args]
                memo[node] = (
                    None
                    if any(p is None for p in parts)
                    else re_concat(*(p for p in parts if p is not None))
                )
            case DeclKind.RE_UNION:
                parts = [memo[a] for a in node.args]
                memo[node] = (
                    None
                    if any(p is None for p in parts)
                    else re_union(*(p for p in parts if p is not None))
                )
            case DeclKind.RE_INTER:
                parts = [memo[a] for a in node.args]
                memo[node] = (
                    None
                    if any(p is None for p in parts)
                    else re_inter(*(p for p in parts if p is not None))
                )
            case DeclKind.RE_COMP:
                sub = memo[node.args[0]]
                memo[node] = None if sub is None else re_comp(sub)
            case DeclKind.RE_DIFF:
                lhs = memo[node.args[0]]
                rhs = memo[node.args[1]]
                memo[node] = None if (lhs is None or rhs is None) else re_diff(lhs, rhs)
            case DeclKind.RE_STAR:
                sub = memo[node.args[0]]
                memo[node] = None if sub is None else re_star(sub)
            case DeclKind.RE_PLUS:
                sub = memo[node.args[0]]
                memo[node] = None if sub is None else re_plus(sub)
            case DeclKind.RE_OPT:
                sub = memo[node.args[0]]
                memo[node] = None if sub is None else re_opt(sub)
            case DeclKind.RE_POWER:
                sub = memo[node.args[0]]
                memo[node] = None if sub is None else re_power(sub, node.decl.params[0])
            case DeclKind.RE_LOOP:
                sub = memo[node.args[0]]
                lo_n, hi_n = node.decl.params
                memo[node] = None if sub is None else re_loop(sub, lo_n, hi_n)
            case _:
                memo[node] = None
    return memo[expr]


if TYPE_CHECKING:
    from unsat.syntax.context import Context


def _check_string(ctx: Context, expr: Expr) -> None:
    ctx._check_expr(expr)
    if not expr.is_string:
        msg = f"Expected String expression, got sort '{expr.sort}'"
        raise TypeError(msg)


def _check_reglan(ctx: Context, expr: Expr) -> None:
    ctx._check_expr(expr)
    if not expr.is_reglan:
        msg = f"Expected RegLan expression, got sort '{expr.sort}'"
        raise TypeError(msg)


def _const_str(expr: Expr) -> str | None:
    if isinstance(expr, Const) and expr.is_string:
        assert isinstance(expr.value, str)
        return expr.value
    return None


def _const_int(expr: Expr) -> int | None:
    if isinstance(expr, Const) and expr.is_int:
        assert isinstance(expr.value, int)
        assert not isinstance(expr.value, bool)
        return expr.value
    return None


def build_str_concat(ctx: Context, *args: Expr) -> Expr:
    """Build normalized n-ary string concatenation ``(str.++ ...)``."""
    if not args:
        msg = "str.++ requires at least one String argument"
        raise ValueError(msg)
    flat: list[Expr] = []
    for arg in args:
        _check_string(ctx, arg)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.STR_CONCAT:
            flat.extend(arg.args)
        else:
            flat.append(arg)

    merged: list[Expr] = []
    for item in flat:
        s_val = _const_str(item)
        if s_val == "":
            continue
        if s_val is not None and merged:
            prev_val = _const_str(merged[-1])
            if prev_val is not None:
                merged[-1] = ctx.mk_string_val(prev_val + s_val)
                continue
        merged.append(item)

    if not merged:
        return ctx.mk_string_val("")
    if len(merged) == 1:
        return merged[0]
    decl = ctx._intern_decl(
        DeclKind.STR_CONCAT,
        "str.++",
        (ctx.string_sort,) * len(merged),
        ctx.string_sort,
    )
    return ctx._intern_app(decl, tuple(merged))


def build_str_len(ctx: Context, arg: Expr) -> Expr:
    """Build ``(str.len arg)`` with constant folding."""
    _check_string(ctx, arg)
    s_val = _const_str(arg)
    if s_val is not None:
        return ctx.mk_int_val(len(s_val))
    decl = ctx._intern_decl(
        DeclKind.STR_LEN, "str.len", (ctx.string_sort,), ctx.int_sort
    )
    return ctx._intern_app(decl, (arg,))


def build_str_at(ctx: Context, s: Expr, idx: Expr) -> Expr:
    """Build ``(str.at s idx)`` with constant folding."""
    _check_string(ctx, s)
    ctx._check_int(idx)
    s_val = _const_str(s)
    i_val = _const_int(idx)
    if s_val is not None and i_val is not None:
        return ctx.mk_string_val(eval_str_at(s_val, i_val))
    if i_val is not None and i_val < 0:
        return ctx.mk_string_val("")
    if s_val == "":
        return ctx.mk_string_val("")
    decl = ctx._intern_decl(
        DeclKind.STR_AT, "str.at", (ctx.string_sort, ctx.int_sort), ctx.string_sort
    )
    return ctx._intern_app(decl, (s, idx))


def build_str_substr(ctx: Context, s: Expr, offset: Expr, length: Expr) -> Expr:
    """Build ``(str.substr s offset length)`` with constant folding."""
    _check_string(ctx, s)
    ctx._check_int(offset)
    ctx._check_int(length)
    s_val = _const_str(s)
    i_val = _const_int(offset)
    n_val = _const_int(length)
    if s_val is not None and i_val is not None and n_val is not None:
        return ctx.mk_string_val(eval_str_substr(s_val, i_val, n_val))
    if (i_val is not None and i_val < 0) or (n_val is not None and n_val <= 0):
        return ctx.mk_string_val("")
    if s_val == "":
        return ctx.mk_string_val("")
    decl = ctx._intern_decl(
        DeclKind.STR_SUBSTR,
        "str.substr",
        (ctx.string_sort, ctx.int_sort, ctx.int_sort),
        ctx.string_sort,
    )
    return ctx._intern_app(decl, (s, offset, length))


def build_str_indexof(ctx: Context, s: Expr, needle: Expr, offset: Expr) -> Expr:
    """Build ``(str.indexof s needle offset)`` with constant folding."""
    _check_string(ctx, s)
    _check_string(ctx, needle)
    ctx._check_int(offset)
    s_val = _const_str(s)
    t_val = _const_str(needle)
    i_val = _const_int(offset)
    if s_val is not None and t_val is not None and i_val is not None:
        return ctx.mk_int_val(eval_str_indexof(s_val, t_val, i_val))
    if i_val is not None and i_val < 0:
        return ctx.mk_int_val(-1)
    decl = ctx._intern_decl(
        DeclKind.STR_INDEXOF,
        "str.indexof",
        (ctx.string_sort, ctx.string_sort, ctx.int_sort),
        ctx.int_sort,
    )
    return ctx._intern_app(decl, (s, needle, offset))


def build_str_replace(ctx: Context, s: Expr, src: Expr, dst: Expr) -> Expr:
    """Build ``(str.replace s src dst)`` with constant folding."""
    _check_string(ctx, s)
    _check_string(ctx, src)
    _check_string(ctx, dst)
    s_val = _const_str(s)
    src_val = _const_str(src)
    dst_val = _const_str(dst)
    if s_val is not None and src_val is not None and dst_val is not None:
        return ctx.mk_string_val(eval_str_replace(s_val, src_val, dst_val))
    if src is dst:
        return s
    if src_val == "":
        return build_str_concat(ctx, dst, s)
    decl = ctx._intern_decl(
        DeclKind.STR_REPLACE,
        "str.replace",
        (ctx.string_sort, ctx.string_sort, ctx.string_sort),
        ctx.string_sort,
    )
    return ctx._intern_app(decl, (s, src, dst))


def build_str_replace_all(ctx: Context, s: Expr, src: Expr, dst: Expr) -> Expr:
    """Build ``(str.replace_all s src dst)`` with constant folding."""
    _check_string(ctx, s)
    _check_string(ctx, src)
    _check_string(ctx, dst)
    s_val = _const_str(s)
    src_val = _const_str(src)
    dst_val = _const_str(dst)
    if s_val is not None and src_val is not None and dst_val is not None:
        return ctx.mk_string_val(eval_str_replace_all(s_val, src_val, dst_val))
    if src is dst or src_val == "" or s_val == "":
        return s
    decl = ctx._intern_decl(
        DeclKind.STR_REPLACE_ALL,
        "str.replace_all",
        (ctx.string_sort, ctx.string_sort, ctx.string_sort),
        ctx.string_sort,
    )
    return ctx._intern_app(decl, (s, src, dst))


def build_str_contains(ctx: Context, s: Expr, needle: Expr) -> Expr:
    """Build ``(str.contains s needle)`` with constant folding."""
    _check_string(ctx, s)
    _check_string(ctx, needle)
    if s is needle:
        return ctx.mk_true()
    s_val = _const_str(s)
    t_val = _const_str(needle)
    if t_val == "":
        return ctx.mk_true()
    if s_val is not None and t_val is not None:
        return ctx.mk_bool_val(t_val in s_val)
    if s_val is not None and t_val is None and s_val == "":
        return ctx.mk_eq(needle, s)
    decl = ctx._intern_decl(
        DeclKind.STR_CONTAINS,
        "str.contains",
        (ctx.string_sort, ctx.string_sort),
        ctx.bool_sort,
    )
    return ctx._intern_app(decl, (s, needle))


def build_str_prefixof(ctx: Context, prefix: Expr, s: Expr) -> Expr:
    """Build ``(str.prefixof prefix s)`` with constant folding."""
    _check_string(ctx, prefix)
    _check_string(ctx, s)
    if prefix is s:
        return ctx.mk_true()
    p_val = _const_str(prefix)
    s_val = _const_str(s)
    if p_val == "":
        return ctx.mk_true()
    if p_val is not None and s_val is not None:
        return ctx.mk_bool_val(s_val.startswith(p_val))
    if s_val == "":
        return ctx.mk_eq(prefix, s)
    decl = ctx._intern_decl(
        DeclKind.STR_PREFIXOF,
        "str.prefixof",
        (ctx.string_sort, ctx.string_sort),
        ctx.bool_sort,
    )
    return ctx._intern_app(decl, (prefix, s))


def build_str_suffixof(ctx: Context, suffix: Expr, s: Expr) -> Expr:
    """Build ``(str.suffixof suffix s)`` with constant folding."""
    _check_string(ctx, suffix)
    _check_string(ctx, s)
    if suffix is s:
        return ctx.mk_true()
    suf_val = _const_str(suffix)
    s_val = _const_str(s)
    if suf_val == "":
        return ctx.mk_true()
    if suf_val is not None and s_val is not None:
        return ctx.mk_bool_val(s_val.endswith(suf_val))
    if s_val == "":
        return ctx.mk_eq(suffix, s)
    decl = ctx._intern_decl(
        DeclKind.STR_SUFFIXOF,
        "str.suffixof",
        (ctx.string_sort, ctx.string_sort),
        ctx.bool_sort,
    )
    return ctx._intern_app(decl, (suffix, s))


def build_str_cmp(ctx: Context, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
    """Build lexicographic comparison ``(str.< lhs rhs)`` or ``(str.<= lhs rhs)``."""
    _check_string(ctx, lhs)
    _check_string(ctx, rhs)
    if lhs is rhs:
        return ctx.mk_bool_val(kind is DeclKind.STR_LE)
    l_val = _const_str(lhs)
    r_val = _const_str(rhs)
    if l_val is not None and r_val is not None:
        return ctx.mk_bool_val(
            l_val < r_val if kind is DeclKind.STR_LT else l_val <= r_val
        )
    if kind is DeclKind.STR_LT and r_val == "":
        return ctx.mk_false()
    if kind is DeclKind.STR_LE and l_val == "":
        return ctx.mk_true()
    decl = ctx._intern_decl(
        kind, kind.value, (ctx.string_sort, ctx.string_sort), ctx.bool_sort
    )
    return ctx._intern_app(decl, (lhs, rhs))


def build_str_to_int(ctx: Context, s: Expr) -> Expr:
    """Build ``(str.to_int s)`` with constant folding."""
    _check_string(ctx, s)
    s_val = _const_str(s)
    if s_val is not None:
        return ctx.mk_int_val(eval_str_to_int(s_val))
    decl = ctx._intern_decl(
        DeclKind.STR_TO_INT, "str.to_int", (ctx.string_sort,), ctx.int_sort
    )
    return ctx._intern_app(decl, (s,))


def build_str_from_int(ctx: Context, n: Expr) -> Expr:
    """Build ``(str.from_int n)`` with constant folding."""
    ctx._check_int(n)
    n_val = _const_int(n)
    if n_val is not None:
        return ctx.mk_string_val(eval_str_from_int(n_val))
    decl = ctx._intern_decl(
        DeclKind.STR_FROM_INT, "str.from_int", (ctx.int_sort,), ctx.string_sort
    )
    return ctx._intern_app(decl, (n,))


def build_str_to_code(ctx: Context, s: Expr) -> Expr:
    """Build ``(str.to_code s)`` with constant folding."""
    _check_string(ctx, s)
    s_val = _const_str(s)
    if s_val is not None:
        return ctx.mk_int_val(eval_str_to_code(s_val))
    decl = ctx._intern_decl(
        DeclKind.STR_TO_CODE, "str.to_code", (ctx.string_sort,), ctx.int_sort
    )
    return ctx._intern_app(decl, (s,))


def build_str_from_code(ctx: Context, n: Expr) -> Expr:
    """Build ``(str.from_code n)`` with constant folding."""
    ctx._check_int(n)
    n_val = _const_int(n)
    if n_val is not None:
        return ctx.mk_string_val(eval_str_from_code(n_val))
    decl = ctx._intern_decl(
        DeclKind.STR_FROM_CODE, "str.from_code", (ctx.int_sort,), ctx.string_sort
    )
    return ctx._intern_app(decl, (n,))


def build_str_is_digit(ctx: Context, s: Expr) -> Expr:
    """Build ``(str.is_digit s)`` with constant folding."""
    _check_string(ctx, s)
    s_val = _const_str(s)
    if s_val is not None:
        return ctx.mk_bool_val(eval_str_is_digit(s_val))
    decl = ctx._intern_decl(
        DeclKind.STR_IS_DIGIT, "str.is_digit", (ctx.string_sort,), ctx.bool_sort
    )
    return ctx._intern_app(decl, (s,))


def build_str_in_re(ctx: Context, s: Expr, reg: Expr) -> Expr:
    """Build ``(str.in_re s reg)`` with constant folding."""
    _check_string(ctx, s)
    _check_reglan(ctx, reg)
    if isinstance(reg, App):
        if reg.decl.kind is DeclKind.RE_NONE:
            return ctx.mk_false()
        if reg.decl.kind is DeclKind.RE_ALL:
            return ctx.mk_true()
    s_val = _const_str(s)
    if s_val is not None:
        compiled = expr_to_re(reg)
        if compiled is not None:
            return ctx.mk_bool_val(re_matches(compiled, s_val))
    decl = ctx._intern_decl(
        DeclKind.STR_IN_RE,
        "str.in_re",
        (ctx.string_sort, ctx.reglan_sort),
        ctx.bool_sort,
    )
    return ctx._intern_app(decl, (s, reg))


def build_str_to_re(ctx: Context, s: Expr) -> Expr:
    """Build ``(str.to_re s)``."""
    _check_string(ctx, s)
    decl = ctx._intern_decl(
        DeclKind.STR_TO_RE, "str.to_re", (ctx.string_sort,), ctx.reglan_sort
    )
    return ctx._intern_app(decl, (s,))


def build_re_none(ctx: Context) -> Expr:
    """Build empty language ``re.none``."""
    decl = ctx._intern_decl(DeclKind.RE_NONE, "re.none", (), ctx.reglan_sort)
    return ctx._intern_app(decl, ())


def build_re_all(ctx: Context) -> Expr:
    """Build universal language ``re.all``."""
    decl = ctx._intern_decl(DeclKind.RE_ALL, "re.all", (), ctx.reglan_sort)
    return ctx._intern_app(decl, ())


def build_re_allchar(ctx: Context) -> Expr:
    """Build single-character wildcard ``re.allchar``."""
    decl = ctx._intern_decl(DeclKind.RE_ALLCHAR, "re.allchar", (), ctx.reglan_sort)
    return ctx._intern_app(decl, ())


def build_re_concat(ctx: Context, *args: Expr) -> Expr:
    """Build normalized ``(re.++ ...)``."""
    if not args:
        msg = "re.++ requires at least one RegLan argument"
        raise ValueError(msg)
    eps = build_str_to_re(ctx, ctx.mk_string_val(""))
    flat: list[Expr] = []
    for arg in args:
        _check_reglan(ctx, arg)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.RE_CONCAT:
            flat.extend(arg.args)
        else:
            flat.append(arg)

    merged: list[Expr] = []
    for item in flat:
        if isinstance(item, App) and item.decl.kind is DeclKind.RE_NONE:
            return build_re_none(ctx)
        if item is eps:
            continue
        if (
            merged
            and isinstance(item, App)
            and item.decl.kind is DeclKind.STR_TO_RE
            and isinstance(merged[-1], App)
            and merged[-1].decl.kind is DeclKind.STR_TO_RE
        ):
            s1 = _const_str(merged[-1].args[0])
            s2 = _const_str(item.args[0])
            if s1 is not None and s2 is not None:
                merged[-1] = build_str_to_re(ctx, ctx.mk_string_val(s1 + s2))
                continue
        merged.append(item)

    if not merged:
        return eps
    if len(merged) == 1:
        return merged[0]
    decl = ctx._intern_decl(
        DeclKind.RE_CONCAT, "re.++", (ctx.reglan_sort,) * len(merged), ctx.reglan_sort
    )
    return ctx._intern_app(decl, tuple(merged))


def build_re_union(ctx: Context, *args: Expr) -> Expr:
    """Build normalized ``(re.union ...)``."""
    if not args:
        msg = "re.union requires at least one RegLan argument"
        raise ValueError(msg)
    re_all = build_re_all(ctx)
    kept: list[Expr] = []
    seen: set[Expr] = set()
    for arg in args:
        _check_reglan(ctx, arg)
        items = (
            arg.args
            if isinstance(arg, App) and arg.decl.kind is DeclKind.RE_UNION
            else (arg,)
        )
        for item in items:
            if item is re_all:
                return re_all
            if isinstance(item, App) and item.decl.kind is DeclKind.RE_NONE:
                continue
            if item not in seen:
                seen.add(item)
                kept.append(item)
    if not kept:
        return build_re_none(ctx)
    if len(kept) == 1:
        return kept[0]
    decl = ctx._intern_decl(
        DeclKind.RE_UNION, "re.union", (ctx.reglan_sort,) * len(kept), ctx.reglan_sort
    )
    return ctx._intern_app(decl, tuple(kept))


def build_re_inter(ctx: Context, *args: Expr) -> Expr:
    """Build normalized ``(re.inter ...)``."""
    if not args:
        msg = "re.inter requires at least one RegLan argument"
        raise ValueError(msg)
    kept: list[Expr] = []
    seen: set[Expr] = set()
    for arg in args:
        _check_reglan(ctx, arg)
        items = (
            arg.args
            if isinstance(arg, App) and arg.decl.kind is DeclKind.RE_INTER
            else (arg,)
        )
        for item in items:
            if isinstance(item, App) and item.decl.kind is DeclKind.RE_NONE:
                return build_re_none(ctx)
            if isinstance(item, App) and item.decl.kind is DeclKind.RE_ALL:
                continue
            if item not in seen:
                seen.add(item)
                kept.append(item)
    if not kept:
        return build_re_all(ctx)
    if len(kept) == 1:
        return kept[0]
    decl = ctx._intern_decl(
        DeclKind.RE_INTER, "re.inter", (ctx.reglan_sort,) * len(kept), ctx.reglan_sort
    )
    return ctx._intern_app(decl, tuple(kept))


def build_re_star(ctx: Context, arg: Expr) -> Expr:
    """Build ``(re.* arg)``."""
    _check_reglan(ctx, arg)
    if isinstance(arg, App):
        k = arg.decl.kind
        if k is DeclKind.RE_NONE or arg is build_str_to_re(ctx, ctx.mk_string_val("")):
            return build_str_to_re(ctx, ctx.mk_string_val(""))
        if k in (DeclKind.RE_STAR, DeclKind.RE_ALL):
            return arg
    decl = ctx._intern_decl(
        DeclKind.RE_STAR, "re.*", (ctx.reglan_sort,), ctx.reglan_sort
    )
    return ctx._intern_app(decl, (arg,))


def build_re_plus(ctx: Context, arg: Expr) -> Expr:
    """Build ``(re.+ arg)``."""
    _check_reglan(ctx, arg)
    if isinstance(arg, App) and arg.decl.kind is DeclKind.RE_NONE:
        return build_re_none(ctx)
    decl = ctx._intern_decl(
        DeclKind.RE_PLUS, "re.+", (ctx.reglan_sort,), ctx.reglan_sort
    )
    return ctx._intern_app(decl, (arg,))


def build_re_opt(ctx: Context, arg: Expr) -> Expr:
    """Build ``(re.opt arg)``."""
    _check_reglan(ctx, arg)
    if isinstance(arg, App) and arg.decl.kind is DeclKind.RE_NONE:
        return build_str_to_re(ctx, ctx.mk_string_val(""))
    decl = ctx._intern_decl(
        DeclKind.RE_OPT, "re.opt", (ctx.reglan_sort,), ctx.reglan_sort
    )
    return ctx._intern_app(decl, (arg,))


def build_re_range(ctx: Context, lo: Expr, hi: Expr) -> Expr:
    """Build ``(re.range lo hi)``."""
    _check_string(ctx, lo)
    _check_string(ctx, hi)
    l_val = _const_str(lo)
    h_val = _const_str(hi)
    if (
        l_val is not None
        and h_val is not None
        and (len(l_val) != 1 or len(h_val) != 1 or ord(l_val[0]) > ord(h_val[0]))
    ):
        return build_re_none(ctx)
    decl = ctx._intern_decl(
        DeclKind.RE_RANGE,
        "re.range",
        (ctx.string_sort, ctx.string_sort),
        ctx.reglan_sort,
    )
    return ctx._intern_app(decl, (lo, hi))


def build_re_comp(ctx: Context, arg: Expr) -> Expr:
    """Build ``(re.comp arg)``."""
    _check_reglan(ctx, arg)
    if isinstance(arg, App):
        if arg.decl.kind is DeclKind.RE_NONE:
            return build_re_all(ctx)
        if arg.decl.kind is DeclKind.RE_ALL:
            return build_re_none(ctx)
        if arg.decl.kind is DeclKind.RE_COMP:
            return arg.args[0]
    decl = ctx._intern_decl(
        DeclKind.RE_COMP, "re.comp", (ctx.reglan_sort,), ctx.reglan_sort
    )
    return ctx._intern_app(decl, (arg,))


def build_re_diff(ctx: Context, lhs: Expr, rhs: Expr) -> Expr:
    """Build ``(re.diff lhs rhs)``."""
    _check_reglan(ctx, lhs)
    _check_reglan(ctx, rhs)
    if lhs is rhs:
        return build_re_none(ctx)
    if isinstance(lhs, App) and lhs.decl.kind is DeclKind.RE_NONE:
        return build_re_none(ctx)
    if isinstance(rhs, App) and rhs.decl.kind is DeclKind.RE_NONE:
        return lhs
    if isinstance(rhs, App) and rhs.decl.kind is DeclKind.RE_ALL:
        return build_re_none(ctx)
    decl = ctx._intern_decl(
        DeclKind.RE_DIFF,
        "re.diff",
        (ctx.reglan_sort, ctx.reglan_sort),
        ctx.reglan_sort,
    )
    return ctx._intern_app(decl, (lhs, rhs))


def build_re_power(ctx: Context, n: int, arg: Expr) -> Expr:
    """Build ``((_ re.^ n) arg)``."""
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        msg = f"re.^ exponent must be a non-negative int, got {n!r}"
        raise ValueError(msg)
    _check_reglan(ctx, arg)
    if n == 0:
        return build_str_to_re(ctx, ctx.mk_string_val(""))
    if n == 1:
        return arg
    if isinstance(arg, App) and arg.decl.kind is DeclKind.RE_NONE:
        return build_re_none(ctx)
    decl = ctx._intern_decl(
        DeclKind.RE_POWER,
        f"(_ re.^ {n})",
        (ctx.reglan_sort,),
        ctx.reglan_sort,
        params=(n,),
    )
    return ctx._intern_app(decl, (arg,))


def build_re_loop(ctx: Context, lo: int, hi: int, arg: Expr) -> Expr:
    """Build ``((_ re.loop lo hi) arg)``."""
    if isinstance(lo, bool) or not isinstance(lo, int) or lo < 0:
        msg = f"re.loop lower bound must be a non-negative int, got {lo!r}"
        raise ValueError(msg)
    if isinstance(hi, bool) or not isinstance(hi, int) or hi < 0:
        msg = f"re.loop upper bound must be a non-negative int, got {hi!r}"
        raise ValueError(msg)
    _check_reglan(ctx, arg)
    if hi < lo:
        return build_re_none(ctx)
    if lo == hi:
        return build_re_power(ctx, lo, arg)
    decl = ctx._intern_decl(
        DeclKind.RE_LOOP,
        f"(_ re.loop {lo} {hi})",
        (ctx.reglan_sort,),
        ctx.reglan_sort,
        params=(lo, hi),
    )
    return ctx._intern_app(decl, (arg,))
