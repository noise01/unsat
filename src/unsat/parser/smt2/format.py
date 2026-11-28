"""SMT-LIB2 model and value formatting."""

from collections.abc import Sequence
from fractions import Fraction

from unsat.model import Model, Value
from unsat.syntax import (
    Context,
    Expr,
    FuncDecl,
    Sort,
    SortKind,
    format_expr,
    format_sort,
    quote_smt2_symbol,
)


def _default_expr_for_model(model: Model, sort: Sort) -> Expr:
    chain: list[Sort] = []
    cur = sort
    while cur.kind is SortKind.ARRAY:
        chain.append(cur.index_sort)
        cur = cur.element_sort
    if cur.kind is SortKind.BOOL:
        val: Expr = model.ctx.mk_false()
    elif cur.kind is SortKind.INT:
        val = model.ctx.mk_int_val(0)
    elif cur.kind is SortKind.REAL:
        val = model.ctx.mk_real_val(0)
    elif cur.kind is SortKind.BITVEC:
        val = model.ctx.mk_bv_val(0, cur.size)
    elif cur.kind is SortKind.STRING:
        val = model.ctx.mk_string_val("")
    elif cur.kind is SortKind.REGLAN:
        val = model.ctx.mk_re_none()
    else:
        universe = model.universe(cur)
        val = universe[0] if universe else model.ctx.mk_domain_val(cur, 0)
    for idx_sort in reversed(chain):
        val = model.ctx.mk_const_array(idx_sort, val)
    return val


def _format_value_atom(ctx: Context, val: Value, sort: Sort) -> str:
    if isinstance(val, bool):
        return "true" if val else "false"
    if isinstance(val, int):
        if sort.is_bv:
            return format_expr(ctx.mk_bv_val(val, sort.size))
        return format_expr(ctx.mk_int_val(val))
    if isinstance(val, Fraction):
        return format_expr(ctx.mk_real_val(val))
    if isinstance(val, str):
        return format_expr(ctx.mk_string_val(val))
    return format_expr(val)


def format_smt2_model(
    model: Model,
    *,
    decls: Sequence[FuncDecl] | None = None,
) -> str:
    """Format ``model`` as an SMT-LIB2 ``(get-model)`` S-expression."""
    target_decls = tuple(decls) if decls is not None else (model.decls() + model.func_decls())
    if not target_decls:
        return "()"

    lines = ["("]
    for decl in target_decls:
        sym = quote_smt2_symbol(decl.name)
        range_str = format_sort(decl.range_sort)
        if decl.arity == 0:
            raw_val = model.get(decl)
            val_str = (
                _format_value_atom(model.ctx, raw_val, decl.range_sort)
                if raw_val is not None
                else format_expr(_default_expr_for_model(model, decl.range_sort))
            )
            lines.append(f"  (define-fun {sym} () {range_str} {val_str})")
            continue

        param_names = [f"x!{i}" for i in range(decl.arity)]
        params_str = " ".join(f"({p} {format_sort(sort)})" for p, sort in zip(param_names, decl.domain, strict=True))
        if model.has_func_interp(decl):
            interp = model.func_interp(decl)
            body = format_expr(interp.else_value)
            for key_args, result in reversed(interp.entries()):
                if len(key_args) == 1:
                    cond = f"(= {param_names[0]} {format_expr(key_args[0])})"
                else:
                    eqs = " ".join(f"(= {p} {format_expr(arg)})" for p, arg in zip(param_names, key_args, strict=True))
                    cond = f"(and {eqs})"
                body = f"(ite {cond} {format_expr(result)} {body})"
        else:
            body = format_expr(_default_expr_for_model(model, decl.range_sort))
        lines.append(f"  (define-fun {sym} ({params_str}) {range_str} {body})")
    lines.append(")")
    return "\n".join(lines)
