from fractions import Fraction

import pytest

import unsat
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context
from unsat.tactics import simplify, to_nnf


def test_arith_dsl_overloads_and_validation() -> None:
    unsat.reset_default_context()
    x, y = unsat.Ints("x y")
    r, s = unsat.Reals("r s")
    p = unsat.Bool("p")

    expr = 2 * x - (-y) + 5
    assert expr.is_int
    real_expr = (r / 2) + Fraction(1, 3) * s - 1
    assert real_expr.is_real
    assert (+x) is x
    assert (+r) is r

    assert unsat.Sum(x, y, unsat.IntVal(1)).is_int
    assert unsat.Eq(unsat.Sum(), unsat.IntVal(0)) is unsat.default_context().mk_true()

    with pytest.raises(TypeError):
        _ = x + True
    with pytest.raises(TypeError):
        _ = x + r
    with pytest.raises(TypeError):
        _ = x / 2
    with pytest.raises(TypeError):
        _ = +p
    with pytest.raises(TypeError):
        _ = x < p
    with pytest.raises(TypeError):
        _ = bool(x < y)


def test_qf_lra_strict_ite_and_distinct() -> None:
    unsat.reset_default_context()
    x, y, z = unsat.Reals("x y z")
    p = unsat.Bool("p")

    solver = unsat.Solver()
    f1 = unsat.And(
        x > 0,
        x < Fraction(1, 500),
        unsat.Eq(y, (x + 1) / 2),
        unsat.If(p, y > 0, y < 0),
        unsat.Distinct(x, y, z),
    )
    solver.add(f1)
    assert solver.check() is unsat.SAT
    m = solver.model()
    assert m.eval_bool(f1)
    assert Fraction(0) < m.eval_real(x) < Fraction(1, 500)

    # Distinct vs disjunction of equalities -> UNSAT
    solver.reset()
    solver.add(unsat.Distinct(x, y, z), unsat.Or(unsat.Eq(x, y), unsat.Eq(y, z)))
    assert solver.check() is unsat.UNSAT


def test_qf_lia_cuts_branch_and_bound_and_mixed_lira() -> None:
    unsat.reset_default_context()
    x, y, z = unsat.Ints("x y z")

    # 1. Parity / GCD infeasibility: 2x + 2y = 5 -> UNSAT
    solver = unsat.Solver()
    solver.add(unsat.Eq(2 * x + 2 * y, unsat.IntVal(5)))
    assert solver.check() is unsat.UNSAT

    # 2. Classic fractional triangle requiring Gomory cut or B&B:
    # 2x + y >= 3, 2x - y <= 0, x + y <= 2 -> continuous (3/4, 3/2) is cut!
    # Check integer points in {x + y <= 2, 2x + y >= 3, 2x - y <= 0}:
    # From 2x + y >= 3 and x + y <= 2 => x >= 1.
    # Then 2x - y <= 0 => y >= 2x >= 2 => x + y >= 3 contradiction!
    solver.reset()
    solver.add(2 * x + y >= 3, 2 * x - y <= 0, x + y <= 2)
    assert solver.check() is unsat.UNSAT

    # 3. Unique integer solution strictly between rationals: 1 <= 2x <= 3, -3x < -2
    solver.reset()
    unique_f = unsat.And(2 * x >= 1, 2 * x <= 3, -3 * x < -2, -y < -1, y <= 2)
    solver.add(unique_f)
    assert solver.check() is unsat.SAT
    m = solver.model()
    assert m[x] == 1
    assert m[y] == 2
    assert m.eval_bool(unique_f)

    # 4. Strict & bounded 0-1 integer pigeonhole / sum mismatch
    solver.reset()
    solver.add(unsat.Eq(2 * x + 3 * y + 5 * z, unsat.IntVal(9)), x >= 1, y >= 1, z >= 1)
    assert solver.check() is unsat.UNSAT

    # 5. Mixed Int/Real (ToReal): 1.2 < to_real(x) < 2.1 -> x = 2
    solver.reset()
    r = unsat.Real("r")
    mixed = unsat.And(
        unsat.ToReal(x) > Fraction(6, 5),
        unsat.ToReal(x) < Fraction(21, 10),
        unsat.Eq(r, unsat.ToReal(x) / 2),
    )
    solver.add(mixed)
    assert solver.check() is unsat.SAT
    m_mix = solver.model()
    assert m_mix[x] == 2
    assert m_mix[r] == Fraction(1)
    assert m_mix.eval_bool(mixed)


def test_qf_uflia_and_qf_uflra_mbtc_both_directions() -> None:
    unsat.reset_default_context()
    x, y = unsat.Ints("x y")
    f = unsat.Function("f", unsat.IntSort(), unsat.IntSort())
    p_pred = unsat.Function("P", unsat.IntSort(), unsat.BoolSort())

    # LRA -> EUF MBTC: 0 <= x <= 0 and 0 <= y <= 0 force x == y -> f(x) == f(y)
    solver = unsat.Solver()
    solver.add(x >= 0, x <= 0, y >= 0, y <= 0, unsat.Not(unsat.Eq(f(x), f(y))))
    assert solver.check() is unsat.UNSAT

    # Mixed arithmetic + predicate congruence with constant numeral:
    solver.reset()
    solver.add(
        p_pred(unsat.IntVal(5)),
        unsat.Eq(2 * x, unsat.IntVal(10)),
        unsat.Not(p_pred(x)),
    )
    assert solver.check() is unsat.UNSAT

    # Compound arithmetic argument passed to UF: f(x + 1) != f(y) under x + 1 == y
    solver.reset()
    solver.add(unsat.Eq(x + 1, y), unsat.Not(unsat.Eq(f(x + 1), f(y))))
    assert solver.check() is unsat.UNSAT

    # Satisfiable QF_UFLIA with model & FuncInterp verification
    solver.reset()
    sat_f = unsat.And(
        x >= 1,
        x <= 2,
        unsat.Eq(y, x + 1),
        unsat.Eq(f(x), y),
        f(y) > 5,
        p_pred(x),
        unsat.Not(p_pred(y)),
    )
    solver.add(sat_f)
    assert solver.check() is unsat.SAT
    m = solver.model()
    assert m.eval_bool(sat_f)
    assert m.eval_int(f(y)) > 5
    assert m.has_func_interp(f)
    assert m.has_func_interp(p_pred)

    # Incremental push/pop + assumptions + unsat_core + tactics roundtrip on QF_UFLRA
    ctx = Context()
    rx, ry = ctx.mk_real("rx"), ctx.mk_real("ry")
    g = ctx.mk_decl("g", (ctx.real_sort,), ctx.real_sort)
    s2 = SMTSolver(ctx)
    s2.add(simplify(to_nnf(ctx.mk_ge(rx, ctx.mk_real_val(0)))))
    s2.push()
    a1 = ctx.mk_eq(rx, ctx.mk_real_val(1))
    a2 = ctx.mk_le(ry, ctx.mk_real_val(1))
    a3 = ctx.mk_ge(ry, ctx.mk_real_val(1))
    a4 = ctx.mk_not(ctx.mk_eq(g(rx), g(ry)))
    a_unused = ctx.mk_gt(rx, ctx.mk_real_val(0))
    assert s2.check(a1, a2, a3, a4, a_unused) is SolveResult.UNSAT
    core = s2.unsat_core()
    assert a_unused not in core
    assert set(core) <= {a1, a2, a3, a4}
    s2.pop(1)

    stats = s2.statistics()
    assert "theory_lra_pivots" in stats
    assert "theory_lia_branch_splits" in stats


def test_qf_lia_and_uflia_unbounded_regression() -> None:
    # 1. Previously diverging unbounded QF_LIA formula (idx=1679).
    ctx = Context()
    x, y, z = ctx.mk_int("x"), ctx.mk_int("y"), ctx.mk_int("z")
    b0 = ctx.mk_bool("b0")
    f0 = ctx.mk_implies(
        ctx.mk_not(
            ctx.mk_gt(
                -x + ctx.mk_int_val(-2) * z + ctx.mk_int_val(-3) * x - 4,
                ctx.mk_int_val(-3) * x - 2,
            )
        ),
        ctx.mk_or(
            b0,
            ctx.mk_lt(
                -z + 3 * z + ctx.mk_int_val(-3) * x - 3,
                y + (-z),
            ),
        ),
    )
    f1 = ctx.mk_gt(ctx.mk_int_val(3), ctx.mk_int_val(-2) * x + 3 * x + 3 * z + 2)
    f2 = b0
    s1 = SMTSolver(ctx)
    s1.add(f0, f1, f2)
    assert s1.check() is SolveResult.SAT
    m1 = s1.model()
    assert m1.eval_bool(f0)
    assert m1.eval_bool(f1)
    assert m1.eval_bool(f2)

    # 2. Previously diverging unbounded QF_UFLIA formula (idx=89).
    ctx2 = Context()
    ux, uy, uz = ctx2.mk_int("x"), ctx2.mk_int("y"), ctx2.mk_int("z")
    b1 = ctx2.mk_bool("b1")
    fn = ctx2.mk_decl("f", (ctx2.int_sort,), ctx2.int_sort)
    pred = ctx2.mk_decl("P", (ctx2.int_sort,), ctx2.bool_sort)
    fx = fn(ux)
    fxm2 = fn(ux - 2)
    ffxm2 = fn(fxm2 - 2)
    g0 = ctx2.mk_not(pred(ux))
    g1 = b1
    g2 = ctx2.mk_lt(ctx2.mk_int_val(-3) * uy - 2, ctx2.mk_int_val(-2) * ux + ux + 1)
    g3 = ctx2.mk_ite(
        ctx2.mk_and(ctx2.mk_le(ctx2.mk_int_val(-3) * uy - 1, -uz - 2), b1),
        ctx2.mk_or(b1, ctx2.mk_not(pred(fxm2))),
        ctx2.mk_or(
            ctx2.mk_gt(ctx2.mk_int_val(-3) * uy + 2, 3 * fx - 3),
            ctx2.mk_le(
                ctx2.mk_int_val(-3) * fx + (-ffxm2) + 2,
                3 * ffxm2 + ctx2.mk_int_val(-2) * uz + ctx2.mk_int_val(-2) * ffxm2 + 1,
            ),
        ),
    )
    s2 = SMTSolver(ctx2)
    s2.add(g0, g1, g2, g3)
    assert s2.check() is SolveResult.SAT
    m2 = s2.model()
    for gf in (g0, g1, g2, g3):
        assert m2.eval_bool(gf)

    # 3. Unbounded 2D wedge: 3x - 2y <= -2, -2x + 3y <= -1 -> SAT (x=-2, y=-2).
    ctx3 = Context()
    wx, wy = ctx3.mk_int("x"), ctx3.mk_int("y")
    w1 = ctx3.mk_le(3 * wx - 2 * wy, ctx3.mk_int_val(-2))
    w2 = ctx3.mk_le(ctx3.mk_int_val(-2) * wx + 3 * wy, ctx3.mk_int_val(-1))
    s3 = SMTSolver(ctx3)
    s3.add(w1, w2)
    assert s3.check() is SolveResult.SAT
    m3 = s3.model()
    assert m3.eval_bool(w1)
    assert m3.eval_bool(w2)

    # 4. Unbounded multi-row parity UNSAT cases.
    ctx4 = Context()
    px, py, pz, pw = (ctx4.mk_int(n) for n in ("x", "y", "z", "w"))
    s4 = SMTSolver(ctx4)
    s4.add(ctx4.mk_eq(px + py - 2 * pz, ctx4.mk_int_val(1)))
    s4.add(ctx4.mk_eq(px - py - 2 * pw, ctx4.mk_int_val(0)))
    assert s4.check() is SolveResult.UNSAT

    ctx5 = Context()
    qx, qy, qz = ctx5.mk_int("x"), ctx5.mk_int("y"), ctx5.mk_int("z")
    s5 = SMTSolver(ctx5)
    s5.add(ctx5.mk_eq(2 * qx + 3 * qy, ctx5.mk_int_val(1)))
    s5.add(ctx5.mk_eq(2 * qx + 3 * qy + 2 * qz, ctx5.mk_int_val(2)))
    assert s5.check() is SolveResult.UNSAT
