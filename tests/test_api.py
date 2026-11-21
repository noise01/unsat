import pytest

import unsat
import unsat.sat
from unsat import (
    SAT,
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
