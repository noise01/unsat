from itertools import product

from unsat.model import Model
from unsat.syntax import App, Context, DeclKind, Expr, iter_subexprs
from unsat.tactics import NNFTactic, SimplifyTactic, Then, simplify, to_nnf


def _is_nnf(expr: Expr) -> bool:
    for node in iter_subexprs(expr):
        if isinstance(node, App):
            kind = node.decl.kind
            if kind is DeclKind.NOT:
                arg = node.args[0]
                if not (isinstance(arg, App) and arg.is_const_symbol):
                    return False
            elif kind not in (DeclKind.AND, DeclKind.OR) and not node.is_const_symbol:
                return False
    return True


def _truth_table(expr: Expr, vars_: list[App]) -> list[bool]:
    ctx = expr.ctx
    rows: list[bool] = []
    for bits in product((False, True), repeat=len(vars_)):
        m = Model(ctx, {v.decl: bit for v, bit in zip(vars_, bits, strict=True)})
        rows.append(m.eval_bool(expr))
    return rows


def test_simplify_and_simplify_tactic() -> None:
    ctx = Context()
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")
    r = ctx.mk_bool("r")

    assert simplify(ctx.mk_eq(p, ctx.mk_false())) is ctx.mk_not(p)
    assert simplify(ctx.mk_eq(ctx.mk_true(), q)) is q
    assert simplify(ctx.mk_distinct(p, q, r)) is ctx.mk_false()
    assert simplify(ctx.mk_distinct(p, q)) == ctx.mk_xor(p, q)
    assert simplify(ctx.mk_implies(ctx.mk_not(p), p)) is p
    assert simplify(ctx.mk_ite(p, ctx.mk_true(), q)) == ctx.mk_or(p, q)
    assert simplify(ctx.mk_ite(p, q, ctx.mk_false())) == ctx.mk_and(p, q)
    assert simplify(ctx.mk_ite(p, ctx.mk_false(), ctx.mk_true())) is ctx.mk_not(p)

    # SimplifyTactic short-circuits on false and deduplicates / drops true.
    res_sat = SimplifyTactic().apply([ctx.mk_true(), p, p])
    assert res_sat.formulas == (p,)

    res_unsat = SimplifyTactic().apply([p, ctx.mk_and(q, ctx.mk_not(q))])
    assert res_unsat.formulas == (ctx.mk_false(),)


def test_to_nnf_and_then_pipeline() -> None:
    ctx = Context()
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")
    r = ctx.mk_bool("r")
    vars_ = [p, q, r]

    formulas = [
        ctx.mk_not(ctx.mk_implies(p, q)),
        ctx.mk_xor(p, q),
        ctx.mk_eq(p, ctx.mk_not(q)),
        ctx.mk_not(ctx.mk_ite(p, q, r)),
        ctx.mk_distinct(p, q),
        ctx.mk_distinct(p, q, r),
    ]
    for f in formulas:
        nnf = to_nnf(f)
        assert _is_nnf(nnf), f"Not in NNF: {nnf}"
        assert _truth_table(nnf, vars_) == _truth_table(f, vars_)

    pipeline = Then(SimplifyTactic(), NNFTactic())
    res = pipeline.apply([ctx.mk_not(ctx.mk_implies(p, q)), ctx.mk_true()])
    assert len(res.formulas) == 1
    assert _is_nnf(res.formulas[0])
    assert _truth_table(res.formulas[0], [p, q]) == _truth_table(
        ctx.mk_and(p, ctx.mk_not(q)), [p, q]
    )


def test_to_nnf_handles_deep_expressions_without_recursion_error() -> None:
    ctx = Context()
    cur: Expr = ctx.mk_bool("x0")
    for i in range(1, 1500):
        cur = ctx.mk_implies(cur, ctx.mk_bool(f"x{i}"))
    nnf = to_nnf(cur)
    assert _is_nnf(nnf)
