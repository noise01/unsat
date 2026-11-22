import z3

from unsat.model import ProjectionModelConverter
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context, Quantifier, has_quantifiers
from unsat.tactics import (
    CtxSimplifyTactic,
    GaussianElimTactic,
    NNFTactic,
    PropagateBoundsTactic,
    SimplifyTactic,
    SkolemizeTactic,
    Then,
    ctx_simplify,
    gaussian_elim,
    propagate_bounds,
    skolemize,
)


def test_nnf_and_skolemize_tactics_with_projection() -> None:
    ctx = Context()
    s = ctx.mk_uninterpreted_sort("S")
    x = ctx.mk_const("x", s)
    y = ctx.mk_const("y", s)
    w = ctx.mk_const("w", s)
    p = ctx.mk_decl("P", (s,), ctx.bool_sort)
    q = ctx.mk_decl("Q", (s,), ctx.bool_sort)
    r = ctx.mk_decl("R", (s, s), ctx.bool_sort)

    # Negated ForAll turns into Exists in NNF, then Skolemizes.
    neg_fa = ctx.mk_not(ctx.mk_forall((x,), ctx.mk_implies(p(x), q(x))))
    nnf_res = NNFTactic().apply((neg_fa,))
    assert len(nnf_res.formulas) == 1
    assert isinstance(nnf_res.formulas[0], Quantifier)
    assert nnf_res.formulas[0].is_exists

    sk_res = SkolemizeTactic().apply((neg_fa,))
    assert isinstance(sk_res.converter, ProjectionModelConverter)
    assert len(sk_res.formulas) == 1
    assert not has_quantifiers(sk_res.formulas[0])

    # Nested ForAll([x, w], Exists([y], R(x, y))) depends only on x (not unused w).
    nested = ctx.mk_forall((x, w), ctx.mk_exists((y,), r(x, y)))
    sk_expr, sk_decls = skolemize(nested)
    assert len(sk_decls) == 1
    sk_fn = next(iter(sk_decls))
    assert sk_fn.domain == (s,)
    assert isinstance(sk_expr, Quantifier)
    assert sk_expr.is_forall
    assert not has_quantifiers(sk_expr.body)

    # Disjunction with ForAll prenexes cleanly without leaving nested quantifiers.
    ex = ctx.mk_exists((x,), p(x))
    fa = ctx.mk_forall((y,), q(y))
    prenexed, _ = skolemize(ctx.mk_or(ex, fa))
    assert isinstance(prenexed, Quantifier)
    assert not has_quantifiers(prenexed.body)

    # Existential BV goal solved after Skolemization hides Skolem symbols cleanly.
    a = ctx.mk_bv("a", 8)
    b = ctx.mk_bv("b", 8)
    bv_goal = ctx.mk_exists((b,), ctx.mk_eq(a + b, ctx.mk_bv_val(42, 8)))
    user_constraint = ctx.mk_eq(a, ctx.mk_bv_val(10, 8))
    goal_res = SkolemizeTactic().apply((bv_goal, user_constraint))
    solver = SMTSolver(ctx)
    solver.add(*goal_res.formulas)
    assert solver.check() is SolveResult.SAT
    projected = goal_res.converter.convert(solver.model())
    assert projected.eval_bv(a) == 10
    assert len(projected.decls()) == 1


def test_ctx_simplify_tactic() -> None:
    ctx = Context()
    p = ctx.mk_bool("p")
    x = ctx.mk_int("x")
    y = ctx.mk_int("y")
    f = ctx.mk_decl("f", (ctx.int_sort,), ctx.int_sort)

    imp = ctx.mk_implies(
        ctx.mk_and(ctx.mk_eq(x, ctx.mk_int_val(5)), p),
        ctx.mk_and(ctx.mk_ite(p, ctx.mk_eq(y, x + ctx.mk_int_val(1)), ctx.false_expr)),
    )
    simplified = ctx_simplify(imp)
    assert simplified is ctx.mk_implies(
        ctx.mk_and(ctx.mk_eq(x, ctx.mk_int_val(5)), p),
        ctx.mk_eq(y, ctx.mk_int_val(6)),
    )

    # Cross-formula propagation in CtxSimplifyTactic preserves defining facts & Z3 eqv.
    res = CtxSimplifyTactic().apply(
        (ctx.mk_eq(x, ctx.mk_int_val(3)), ctx.mk_eq(f(x), y + ctx.mk_int_val(2)))
    )
    assert res.formulas == (
        ctx.mk_eq(x, ctx.mk_int_val(3)),
        ctx.mk_eq(f(ctx.mk_int_val(3)), y + ctx.mk_int_val(2)),
    )

    # Ground truths propagate inside quantifier body without variable capture.
    z = ctx.mk_int("z")
    conj_q = ctx.mk_and(
        ctx.mk_eq(x, ctx.mk_int_val(2)),
        ctx.mk_forall((z,), ctx.mk_eq(f(z), x)),
    )
    sq = ctx_simplify(conj_q)
    zx = z3.Int("x")
    zz = z3.Int("z")
    zf = z3.Function("f", z3.IntSort(), z3.IntSort())
    zsolver = z3.Solver()
    zsolver.add(zx == 2)
    zsolver.add(z3.ForAll([zz], zf(zz) == zx) != z3.ForAll([zz], zf(zz) == 2))
    assert zsolver.check() == z3.unsat
    assert isinstance(sq.children[1], Quantifier)


def test_gaussian_elim_and_propagate_bounds_with_model_reconstruction() -> None:
    ctx = Context()
    rx, ry, rz = ctx.mk_real("rx"), ctx.mk_real("ry"), ctx.mk_real("rz")
    real_f = (
        ctx.mk_eq(rx + ctx.mk_mul(ctx.mk_real_val(2), ry), ctx.mk_real_val(5)),
        ctx.mk_eq(rx - ry, ctx.mk_real_val(2)),
        ctx.mk_eq(rz, rx + ry),
    )
    gres = gaussian_elim(real_f)
    assert not gres.formulas
    s_empty = SMTSolver(ctx)
    assert s_empty.check() is SolveResult.SAT
    reconstructed = gres.converter.convert(s_empty.model())
    for item in real_f:
        assert reconstructed.eval_bool(item) is True

    # Integer GCD contradiction (2x + 4y = 5 -> UNSAT immediately)
    ix, iy = ctx.mk_int("ix"), ctx.mk_int("iy")
    gcd_res = gaussian_elim(
        (
            ctx.mk_eq(
                ctx.mk_mul(ctx.mk_int_val(2), ix) + ctx.mk_mul(ctx.mk_int_val(4), iy),
                ctx.mk_int_val(5),
            ),
        )
    )
    assert gcd_res.formulas == (ctx.false_expr,)

    # BV & Bool & Uninterpreted defining equalities + occurs-check guard
    b1, b2 = ctx.mk_bv("b1", 8), ctx.mk_bv("b2", 8)
    uf = ctx.mk_decl("uf", (ctx.int_sort,), ctx.int_sort)
    mixed_goals = (
        ctx.mk_eq(b1, b2),
        ctx.mk_eq(b2, ctx.mk_bv_val(17, 8)),
        ctx.mk_eq(ix, uf(ix)),  # occurs-check must keep ix != infinite sub
    )
    mres = GaussianElimTactic().apply(mixed_goals)
    msolver = SMTSolver(ctx)
    msolver.add(*mres.formulas)
    assert msolver.check() is SolveResult.SAT
    mfull = mres.converter.convert(msolver.model())
    for g_item in mixed_goals:
        assert mfull.eval_bool(g_item) is True

    # PropagateBoundsTactic: Int tightening pins 2*ix > 7 /\ ix < 5 -> ix = 4
    pin_goals = (
        ctx.mk_gt(ctx.mk_mul(ctx.mk_int_val(2), ix), ctx.mk_int_val(7)),
        ctx.mk_lt(ix, ctx.mk_int_val(5)),
        ctx.mk_ge(iy, ix),
        ctx.mk_ge(iy, ctx.mk_int_val(2)),
    )
    pres = propagate_bounds(pin_goals)
    assert ctx.mk_ge(iy, ctx.mk_int_val(4)) in pres.formulas
    assert ctx.mk_ge(iy, ctx.mk_int_val(2)) not in pres.formulas

    # Composed tactic pipeline
    pipeline = Then(
        NNFTactic(),
        CtxSimplifyTactic(),
        GaussianElimTactic(),
        PropagateBoundsTactic(),
        SimplifyTactic(),
    )
    pipe_res = pipeline.apply(pin_goals)
    psolver = SMTSolver(ctx)
    psolver.add(*pipe_res.formulas)
    assert psolver.check() is SolveResult.SAT
    pmodel = pipe_res.converter.convert(psolver.model())
    for item in pin_goals:
        assert pmodel.eval_bool(item) is True
    assert pmodel.eval_int(ix) == 4
    assert pmodel.eval_int(iy) >= 4

    # Empty integer interval conflict (ix > 2 /\ ix < 3 -> false)
    assert propagate_bounds(
        (ctx.mk_gt(ix, ctx.mk_int_val(2)), ctx.mk_lt(ix, ctx.mk_int_val(3)))
    ).formulas == (ctx.false_expr,)
