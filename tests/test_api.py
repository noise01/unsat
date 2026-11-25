import pytest

import unsat
import unsat.sat
from unsat import (
    SAT,
    UNKNOWN,
    UNSAT,
    And,
    Bool,
    Bools,
    BoolSort,
    BoolVal,
    Context,
    Distinct,
    Eq,
    If,
    Implies,
    Not,
    Or,
    Solver,
    Xor,
    reset_default_context,
    set_default_context,
)


def test_public_dsl_end_to_end() -> None:
    reset_default_context()
    assert unsat.SAT == SAT
    assert not hasattr(unsat, "main")
    assert not hasattr(unsat, "unknown")
    assert unsat.sat.SolveResult.SAT is SAT

    a, b, c = Bools("a b c")
    d = Bool("d")
    assert a.sort is BoolSort()
    assert Not(BoolVal(False)) is BoolVal(True)

    solver = Solver()
    solver.add(
        Implies(a, b),
        Xor(b, c),
        If(a, c, Eq(b, d)),
        Distinct(a, d),
        Or([a, d]),
    )
    assert solver.check() is SAT
    model = solver.model()
    assert model.eval_bool(And(solver.assertions())) is True
    assert solver.statistics()["decisions"] >= 0

    solver.push()
    solver.add(Not(a), Not(d))
    assert solver.check() is UNSAT
    solver.pop()
    assert solver.check() is SAT


def test_explicit_context_and_operator_ergonomics() -> None:
    ctx = Context()
    set_default_context(ctx)
    try:
        x, y = Bools(["x", "y"])
        assert x.ctx is ctx
        solver = Solver()
        assert solver.ctx is ctx
        solver.add((x & y) | (~x ^ y))
        assert solver.check(x, ~y) is UNSAT
        assert set(solver.unsat_core()) == {x, ~y}
        assert And() is BoolVal(True)
        assert Or() is BoolVal(False)
        assert Distinct() is BoolVal(True)

        with pytest.raises(TypeError, match="bool"):
            _ = bool(x)
    finally:
        reset_default_context()


def test_solver_resource_limits() -> None:
    ctx = Context()
    with pytest.raises(ValueError, match="timeout"):
        Solver(ctx, timeout=-0.1)
    with pytest.raises(ValueError, match="max_conflicts"):
        Solver(ctx, max_conflicts=-1)

    p = Bool("res_p", ctx=ctx)
    s = Solver(ctx)
    s.add(p)
    assert s.check(timeout=0.0) is UNKNOWN
    assert s.check() is SAT
    assert s.model().eval_bool(p) is True

    # Pigeonhole(4, 3) cannot finish within 1 conflict, but finishes when relaxed.
    php = Solver(ctx)
    grid = [[Bool(f"ph_{i}_{j}", ctx=ctx) for j in range(3)] for i in range(4)]
    for i in range(4):
        php.add(Or(*grid[i]))
    for j in range(3):
        for i1 in range(4):
            for i2 in range(i1 + 1, 4):
                php.add(Or(Not(grid[i1][j]), Not(grid[i2][j])))

    assert php.check(max_conflicts=1) is UNKNOWN
    assert php.check() is UNSAT

    default_limited = Solver(ctx, max_conflicts=1)
    default_limited.add(*php.assertions())
    assert default_limited.check() is UNKNOWN
    assert default_limited.check(max_conflicts=200) is UNSAT


def test_eq_distinct_if_literal_coercion() -> None:
    from fractions import Fraction
    from typing import Any

    ctx = Context()
    p = Bool("coerce_p", ctx=ctx)
    ix = unsat.Int("coerce_ix", ctx=ctx)
    rx = unsat.Real("coerce_rx", ctx=ctx)
    bx = unsat.BitVec("coerce_bx", 4, ctx=ctx)

    s = Solver(ctx)
    s.add(
        Eq(p, True),
        Eq(ix, 10),
        Eq(10, ix),
        Eq(rx, Fraction(3, 2)),
        Eq(Fraction(3, 2), rx),
        Eq(bx, 5),
        Eq(5, bx),
        Distinct(ix, 0, 1),
        Distinct([bx, 0, 1]),
        Eq(If(p, 1, 0), 1),
        Eq(If(p, Fraction(1, 2), 0), Fraction(1, 2)),
        Eq(If(p, bx, 3), 5),
        Eq(If(p, True, False), True),
    )
    assert s.check() is SAT
    m = s.model()
    assert m.eval_bool(p) is True
    assert m.eval_int(ix) == 10
    assert m.eval_real(rx) == Fraction(3, 2)
    assert m.eval_bv(bx) == 5

    bad_str: Any = "ab"
    bad_cond: Any = True
    for invalid in (
        lambda: Eq(1, 2),
        lambda: Eq(True, False),
        lambda: Eq(ix, True),
        lambda: Eq(True, ix),
        lambda: Distinct(1, 2),
        lambda: Distinct(ix, bad_str),
        lambda: Distinct(ix, True),
        lambda: If(p, True, 1),
        lambda: If(p, 1, False),
        lambda: If(bad_cond, 1, 0),
    ):
        with pytest.raises(TypeError, match=r".+"):
            invalid()
