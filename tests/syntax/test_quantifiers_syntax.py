import pytest

from unsat.model import FuncInterp, Model
from unsat.syntax import (
    BoundVar,
    Context,
    Quantifier,
    abstract_vars,
    format_expr,
    free_bound_var_indices,
    has_bound_vars,
    has_quantifiers,
    instantiate_quantifier,
    shift_bound_vars,
    substitute,
)


def test_quantifier_ast_debruijn_and_helpers() -> None:
    ctx = Context()
    x = ctx.mk_int("x")
    y = ctx.mk_int("y")
    z = ctx.mk_int("z")
    f = ctx.mk_decl("f", (ctx.int_sort, ctx.int_sort), ctx.int_sort)
    g = ctx.mk_decl("g", (ctx.int_sort,), ctx.int_sort)

    # Constant folding & validation
    assert ctx.mk_forall((x,), ctx.true_expr) is ctx.true_expr
    assert ctx.mk_exists((x,), ctx.false_expr) is ctx.false_expr
    with pytest.raises(ValueError, match="non-negative"):
        ctx.mk_bound_var(-1, ctx.int_sort)
    with pytest.raises(ValueError, match="Duplicate bound variable"):
        ctx.mk_forall((x, x), x > ctx.mk_int_val(0))
    with pytest.raises(TypeError, match="Expected Bool"):
        ctx.mk_forall((x,), x + ctx.mk_int_val(1))

    # Multi-variable binder assigns leftmost -> highest index, rightmost -> 0.
    q = ctx.mk_forall((x, y), ctx.mk_gt(f(x, y), z), patterns=(f(x, y),))
    assert isinstance(q, Quantifier)
    assert q.is_forall
    assert not q.is_exists
    assert q.num_vars == 2
    assert has_quantifiers(q)
    assert not has_quantifiers(f(x, y))
    assert has_bound_vars(q.body)
    assert free_bound_var_indices(q) == frozenset()
    assert free_bound_var_indices(q.body) == frozenset({0, 1})

    b0 = ctx.mk_bound_var(0, ctx.int_sort)
    b1 = ctx.mk_bound_var(1, ctx.int_sort)
    assert isinstance(b0, BoundVar)
    assert q.body is ctx.mk_gt(f(b1, b0), z)
    assert q.patterns == ((f(b1, b0),),)

    # Nested quantifiers and shadowing preserve De Bruijn scoping.
    inner = ctx.mk_exists((y,), ctx.mk_eq(f(x, y), z))
    outer = ctx.mk_forall((x,), inner)
    assert isinstance(outer, Quantifier)
    assert free_bound_var_indices(outer) == frozenset()
    assert isinstance(outer.body, Quantifier)
    assert free_bound_var_indices(outer.body) == frozenset({0})

    # Shadowing formats disambiguated binder names and skips shadowed free x.
    shadowed = ctx.mk_forall(
        (x,),
        ctx.mk_and(
            ctx.mk_gt(x, ctx.mk_int_val(0)),
            ctx.mk_exists((x,), ctx.mk_lt(x, ctx.mk_int_val(0))),
        ),
    )
    rendered_shadow = format_expr(shadowed)
    assert "x!1" in rendered_shadow
    assert "(exists ((x!1 Int)) (< x!1 0))" in rendered_shadow

    # Pattern formatting includes (! ... :pattern (...))
    rendered_pat = format_expr(q)
    assert rendered_pat == "(forall ((x Int) (y Int)) (! (> (f x y) z) :pattern ((f x y))))"

    # Capture-avoiding instantiation with open term containing BoundVar(0).
    sub_outer = instantiate_quantifier(outer, (g(b0),))
    assert isinstance(sub_outer, Quantifier)
    assert sub_outer.body is ctx.mk_eq(f(g(b1), b0), z)

    # Shift & abstract round-trip
    shifted = shift_bound_vars(b0, 2)
    assert shifted is ctx.mk_bound_var(2, ctx.int_sort)
    assert abstract_vars(ctx.mk_eq(f(x, y), y), (x, y)) is ctx.mk_eq(f(b1, b0), b0)

    # Capture-avoiding substitute skips bound occurrences inside inner quantifier.
    subst_res = substitute(
        ctx.mk_and(ctx.mk_eq(z, x), outer),
        {z: b0},
    )
    expected_subst = "(and (= (:var 0) x) (forall ((x Int)) (exists ((y Int)) (= (f x y) (:var 2)))))"
    assert format_expr(subst_res) == expected_subst


def test_model_eval_quantifiers_finite_and_open() -> None:
    ctx = Context()
    p, q = ctx.mk_bool("p"), ctx.mk_bool("q")
    s_sort = ctx.mk_uninterpreted_sort("S")
    u0, u1 = ctx.mk_domain_val(s_sort, 0), ctx.mk_domain_val(s_sort, 1)
    a, b = ctx.mk_const("a", s_sort), ctx.mk_const("b", s_sort)
    pred = ctx.mk_decl("P", (s_sort,), ctx.bool_sort)
    bv = ctx.mk_bv("bv", 2)
    i = ctx.mk_int("i")
    c = ctx.mk_int("c")

    interp_p = FuncInterp(pred, {(u0,): ctx.true_expr}, else_value=ctx.false_expr)
    model = Model(
        ctx,
        {p.decl: True, c.decl: 5, a.decl: u0, b.decl: u1},
        functions={pred: interp_p},
        universes={s_sort: (u0, u1)},
    )

    assert model.eval_bool(ctx.mk_forall((p, q), ctx.mk_eq(p, q))) is False
    assert model.eval_bool(ctx.mk_exists((p, q), ctx.mk_and(p, q))) is True
    assert model.eval_bool(ctx.mk_forall((a, b), ctx.mk_eq(a, b))) is False
    assert model.eval_bool(ctx.mk_exists((a, b), ctx.mk_distinct(a, b))) is True
    assert model.eval_bool(ctx.mk_exists((a,), pred(a))) is True
    assert model.eval_bool(ctx.mk_forall((a,), pred(a))) is False
    assert model.eval_bool(ctx.mk_forall((bv,), ctx.mk_eq(bv & ctx.mk_bv_val(3, 2), bv))) is True

    # Infinite Int quantifier leaves bound vars intact while evaluating free constants.
    open_q = ctx.mk_forall((i,), ctx.mk_gt(i, c))
    ev_q = model.eval(open_q)
    assert isinstance(ev_q, Quantifier)
    assert format_expr(ev_q) == "(forall ((i Int)) (> i 5))"
