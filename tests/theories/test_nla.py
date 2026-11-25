"""Unit, SMT integration, and differential tests for M9 integer ops and NLA."""

from fractions import Fraction

import pytest
import z3
from hypothesis import given, settings
from hypothesis import strategies as st

import unsat
from unsat.parser import execute_smt2
from unsat.smt import SMTSolver, SolveResult
from unsat.theories.nla import isolate_real_roots


def test_sturm_univariate_root_isolation() -> None:
    # x^2 - 2 = 0 -> 2 irrational roots in (-2, -1) and (1, 2)
    r_irr = isolate_real_roots((Fraction(-2), Fraction(0), Fraction(1)))
    assert len(r_irr) == 2
    assert r_irr[0][2] is False
    assert r_irr[1][2] is False
    assert Fraction(-2) <= r_irr[0][0] < r_irr[0][1] <= Fraction(-1)
    assert Fraction(1) <= r_irr[1][0] < r_irr[1][1] <= Fraction(2)

    # x^2 - 2x + 2 = 0 -> 0 real roots
    assert isolate_real_roots((Fraction(2), Fraction(-2), Fraction(1))) == []

    # x^2 - 4 = 0 -> exact rational roots -2 and 2
    r_sq = isolate_real_roots((Fraction(-4), Fraction(0), Fraction(1)))
    assert r_sq == [
        (Fraction(-2), Fraction(-2), True),
        (Fraction(2), Fraction(2), True),
    ]

    # (x - 1)(x - 2)(x - 3) = x^3 - 6x^2 + 11x - 6
    r_cub = isolate_real_roots((Fraction(-6), Fraction(11), Fraction(-6), Fraction(1)))
    assert r_cub == [
        (Fraction(1), Fraction(1), True),
        (Fraction(2), Fraction(2), True),
        (Fraction(3), Fraction(3), True),
    ]


def test_complete_integer_operators_and_div0() -> None:
    unsat.reset_default_context()
    x, y, z = unsat.Ints("x y z")
    r = unsat.Real("r")

    # Constant folding matches SMT-LIB2 Euclidean division & floor to_int
    assert unsat.default_context().mk_idiv(
        unsat.IntVal(-7), unsat.IntVal(3)
    ) is unsat.IntVal(-3)
    assert unsat.default_context().mk_mod(
        unsat.IntVal(-7), unsat.IntVal(3)
    ) is unsat.IntVal(2)
    assert unsat.default_context().mk_idiv(
        unsat.IntVal(-7), unsat.IntVal(-3)
    ) is unsat.IntVal(3)
    assert unsat.default_context().mk_mod(
        unsat.IntVal(-7), unsat.IntVal(-3)
    ) is unsat.IntVal(2)
    assert unsat.ToInt(Fraction(-3, 2)) is unsat.IntVal(-2)
    assert unsat.IsInt(Fraction(4, 2)) is unsat.BoolVal(True)
    assert unsat.IsInt(Fraction(3, 2)) is unsat.BoolVal(False)
    assert unsat.Abs(-9) is unsat.IntVal(9)
    assert unsat.Divisible(3, 12) is unsat.BoolVal(True)
    assert unsat.Divisible(5, 12) is unsat.BoolVal(False)

    # Constant divisor Euclidean div/mod + abs + divisible + to_int/is_int
    s = unsat.Solver()
    f_sat = unsat.And(
        unsat.Eq(x, -7),
        unsat.Eq(y, x // 3),
        unsat.Eq(z, x % -3),
        unsat.Eq(abs(x), 7),
        unsat.Divisible(7, abs(x)),
        unsat.Eq(unsat.ToInt(r), -2),
        unsat.Not(unsat.IsInt(r)),
    )
    s.add(f_sat)
    assert s.check() is unsat.SAT
    m = s.model()
    assert m.eval_bool(f_sat, model_completion=True) is True
    assert m[y] == -3
    assert m[z] == 2
    assert Fraction(-2) < m[r] < Fraction(-1)

    # Variable divisor UNSAT property: mod(x, y) < abs(y) whenever y != 0
    s.reset()
    s.add(unsat.Distinct(y, 0), (x % y) >= abs(y))
    assert s.check() is unsat.UNSAT

    # Div-by-zero total uninterpreted congruence & SAT model validation
    s.reset()
    f_div0 = unsat.And(unsat.Eq(y, 0), unsat.Eq(x, 3), unsat.Eq(unsat.IDiv(x, y), 7))
    s.add(f_div0)
    assert s.check() is unsat.SAT
    assert s.model().eval_bool(f_div0, model_completion=True) is True

    s.reset()
    s.add(unsat.Eq(x, y), unsat.Distinct(unsat.IDiv(x, 0), unsat.IDiv(y, 0)))
    assert s.check() is unsat.UNSAT


def test_qf_nra_and_qf_nia_decision_and_unknown() -> None:
    unsat.reset_default_context()
    x, y = unsat.Reals("x y")

    # Rational root SAT: x^2 == 4 and x > 0 -> x = 2
    s = unsat.Solver()
    f1 = unsat.And(unsat.Eq(x**2, 4), x > 0)
    s.add(f1)
    assert s.check() is unsat.SAT
    assert s.model()[x] == Fraction(2)
    assert s.model().eval_bool(f1, model_completion=True) is True

    # Two variables bounded: x*y == 6, x + y == 5, x <= y
    s.reset()
    f2 = unsat.And(unsat.Eq(x * y, 6), unsat.Eq(x + y, 5), x <= y, x >= 1, x <= 4)
    s.add(f2)
    assert s.check() is unsat.SAT
    assert s.model().eval_bool(f2, model_completion=True) is True

    # Open interval around irrational sqrt(2): x^2 > 1 and x^2 < 3 -> SAT with rational!
    s.reset()
    f3 = unsat.And(x**2 > 1, x**2 < 3, x > 0)
    s.add(f3)
    assert s.check() is unsat.SAT
    assert s.model().eval_bool(f3, model_completion=True) is True

    # UNSAT via Sturm (no real roots): x^2 - 2x + 2 == 0
    s.reset()
    s.add(unsat.Eq(x**2 - 2 * x + 2, 0))
    assert s.check() is unsat.UNSAT

    # UNSAT via ICP sign rule: x > 0, y > 0, x*y < 0
    s.reset()
    s.add(x > 0, y > 0, x * y < 0)
    assert s.check() is unsat.UNSAT

    # Conservative UNKNOWN when only irrational real root exists: x^2 == 2
    s.reset()
    s.add(unsat.Eq(x**2, 2))
    assert s.check() is unsat.UNKNOWN

    # QF_NIA Pythagorean triple + UNSAT Diophantine + push/pop + unsat_core
    unsat.reset_default_context()
    a, b, c = unsat.Ints("a b c")
    si = unsat.Solver()
    f_pyth = unsat.And(
        unsat.Eq(a**2 + b**2, c**2), a >= 3, a <= 4, b >= 3, b <= 4, c >= 4, c <= 6
    )
    si.add(f_pyth)
    assert si.check() is unsat.SAT
    assert si.model().eval_bool(f_pyth, model_completion=True) is True

    si.reset()
    si.add(a**2 > 1, a**2 < 3)
    assert si.check() is unsat.UNSAT

    si.reset()
    a1 = unsat.Eq(a * b, 7)
    a2 = a >= 2
    a3 = b >= 2
    unused = c >= 10
    si.push()
    assert si.check(a1, a2, a3, unused) is unsat.UNSAT
    core = si.unsat_core()
    assert unused not in core
    recheck = unsat.Solver()
    recheck.add(*core)
    assert recheck.check() is unsat.UNSAT
    si.pop(1)
    assert "theory_nla_checks" in si.statistics()


def test_smt2_m9_integer_ops_and_nonlinear_logics() -> None:
    script = """
    (set-logic QF_UFNIA)
    (declare-fun x () Int)
    (declare-fun y () Int)
    (declare-fun r () Real)
    (assert (= (abs x) 6))
    (assert (< x 0))
    (assert ((_ divisible 3) x))
    (assert (= (div x 4) y))
    (assert (and (<= 1.25 r) (< r 2.0) (= (to_int r) 1) (not (is_int r))))
    (check-sat)
    (get-value (x y (mod x 4)))
    """
    outputs, stats = execute_smt2(script)
    assert outputs[0] == "sat"
    assert "((- 6))" in outputs[1] or "(- 6)" in outputs[1]
    assert "(- 2)" in outputs[1]
    assert "theory_nla_checks" in stats


@settings(max_examples=25, deadline=None)
@given(
    x_lo=st.integers(min_value=-12, max_value=8),
    x_span=st.integers(min_value=0, max_value=8),
    div_c=st.sampled_from([-5, -3, 2, 3, 5]),
    rem_target=st.integers(min_value=-1, max_value=4),
    d_mod=st.integers(min_value=2, max_value=5),
)
def test_integer_ops_differential_vs_z3(
    x_lo: int, x_span: int, div_c: int, rem_target: int, d_mod: int
) -> None:
    ctx = unsat.Context()
    x = ctx.mk_int("x")
    y = ctx.mk_int("y")
    r = ctx.mk_real("r")

    formulas = [
        ctx.mk_ge(x, ctx.mk_int_val(x_lo)),
        ctx.mk_le(x, ctx.mk_int_val(x_lo + x_span)),
        ctx.mk_eq(y, ctx.mk_idiv(x, ctx.mk_int_val(div_c))),
        ctx.mk_ge(ctx.mk_mod(x, ctx.mk_int_val(div_c)), ctx.mk_int_val(rem_target)),
        ctx.mk_divisible(d_mod, ctx.mk_abs(x)),
        ctx.mk_eq(ctx.mk_to_int(r), x),
        ctx.mk_not(ctx.mk_is_int(r)),
    ]

    us = SMTSolver(ctx)
    us.add(*formulas)
    ures = us.check()

    zx = z3.Int("x")
    zy = z3.Int("y")
    zr = z3.Real("r")
    zs = z3.Solver()
    zs.add(
        zx >= x_lo,
        zx <= x_lo + x_span,
        zy == zx / div_c,
        (zx % div_c) >= rem_target,
        (z3.Abs(zx) % d_mod) == 0,
        z3.ToInt(zr) == zx,
        z3.Not(z3.IsInt(zr)),
    )
    zver = zs.check()
    expected = SolveResult.SAT if zver == z3.sat else SolveResult.UNSAT
    if ures is not SolveResult.UNKNOWN:
        assert ures is expected
    if ures is SolveResult.SAT:
        model = us.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True


@settings(max_examples=20, deadline=None)
@given(
    lo=st.integers(min_value=-4, max_value=2),
    span=st.integers(min_value=1, max_value=4),
    prod_target=st.integers(min_value=-6, max_value=9),
    is_eq=st.booleans(),
)
def test_qf_nia_bounded_differential_vs_z3(
    lo: int, span: int, prod_target: int, is_eq: bool
) -> None:
    ctx = unsat.Context()
    x = ctx.mk_int("x")
    y = ctx.mk_int("y")
    prod = ctx.mk_mul(x, y)
    rel = (
        ctx.mk_eq(prod, ctx.mk_int_val(prod_target))
        if is_eq
        else ctx.mk_ge(prod, ctx.mk_int_val(prod_target))
    )
    formulas = [
        ctx.mk_ge(x, ctx.mk_int_val(lo)),
        ctx.mk_le(x, ctx.mk_int_val(lo + span)),
        ctx.mk_ge(y, ctx.mk_int_val(lo)),
        ctx.mk_le(y, ctx.mk_int_val(lo + span)),
        rel,
    ]
    us = SMTSolver(ctx)
    us.add(*formulas)
    ures = us.check()

    zx, zy = z3.Ints("x y")
    zs = z3.Solver()
    zs.add(
        zx >= lo,
        zx <= lo + span,
        zy >= lo,
        zy <= lo + span,
        (zx * zy == prod_target) if is_eq else (zx * zy >= prod_target),
    )
    zver = zs.check()
    expected = SolveResult.SAT if zver == z3.sat else SolveResult.UNSAT
    if ures is not SolveResult.UNKNOWN:
        assert ures is expected
    if ures is SolveResult.SAT:
        model = us.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True


def test_lra_standalone_nonlinear_flag_check() -> None:
    ctx = unsat.Context()
    r = ctx.mk_real("r")
    with pytest.raises(ValueError, match="Non-linear"):
        SMTSolver(ctx)._lra.__class__(ctx).register_atom(
            ctx.mk_gt(r * r, ctx.mk_real_val(1))
        )
