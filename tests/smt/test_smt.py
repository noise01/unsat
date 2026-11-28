import pytest

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context, Expr


def test_smt_solver_basic_connectives_and_zero_var() -> None:
    ctx = Context()
    solver = SMTSolver(ctx)
    assert solver.check() is SolveResult.SAT
    assert len(solver.model()) == 0

    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")
    r = ctx.mk_bool("r")

    formula = ctx.mk_and(
        ctx.mk_implies(p, q),
        ctx.mk_xor(q, r),
        ctx.mk_ite(p, r, ctx.mk_true()),
    )
    solver.add(formula)
    assert solver.assertions() == [formula]
    assert solver.check() is SolveResult.SAT
    model = solver.model()
    assert model.eval_bool(formula) is True
    assert not model[p] or (model[q] and model[r])


def test_smt_solver_push_pop_reset_and_unsat_core() -> None:
    ctx = Context()
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")
    r = ctx.mk_bool("r")
    s = ctx.mk_bool("s")

    solver = SMTSolver(ctx)
    solver.add(ctx.mk_implies(p, q))
    solver.add(ctx.mk_implies(q, r))

    # Incremental push/pop with false literal inside scope.
    solver.push()
    assert solver.num_scopes == 1
    solver.add(ctx.mk_false())
    assert solver.check() is SolveResult.UNSAT
    with pytest.raises(ValueError, match="SAT"):
        solver.model()
    solver.pop()
    assert solver.num_scopes == 0
    assert solver.check() is SolveResult.SAT

    # Push scope with contradiction against assumption, then pop.
    solver.push()
    solver.add(p)
    assert solver.check(ctx.mk_not(r), s) is SolveResult.UNSAT
    core = solver.unsat_core()
    assert core == [ctx.mk_not(r)]
    assert s not in core
    # Scope activation literals must never leak into assertions or core.
    assert len(solver.assertions()) == 3
    solver.pop()

    # After pop, p is retracted so check(~r, s) is SAT again.
    assert solver.check(ctx.mk_not(r), s) is SolveResult.SAT
    assert solver.unsat_core() == []
    assert solver.model().eval_bool(ctx.mk_and(ctx.mk_not(r), s)) is True

    # Both-polarity assumptions preserve both literals in core.
    assert solver.check(p, ctx.mk_not(p)) is SolveResult.UNSAT
    assert set(solver.unsat_core()) == {p, ctx.mk_not(p)}

    with pytest.raises(ValueError, match="pop"):
        solver.pop()

    solver.reset()
    assert solver.assertions() == []
    assert solver.check(p, ctx.mk_not(r)) is SolveResult.SAT


def test_smt_solver_handles_deep_xor_ite_chain_linearly() -> None:
    ctx = Context()
    vars_ = [ctx.mk_bool(f"v_{i}") for i in range(1500)]
    cur: Expr = vars_[0]
    for idx in range(1, len(vars_)):
        cur = ctx.mk_xor(cur, vars_[idx]) if idx % 2 == 0 else ctx.mk_ite(vars_[idx], cur, ctx.mk_not(cur))

    solver = SMTSolver(ctx)
    solver.add(cur)
    assert solver.check() is SolveResult.SAT
    model = solver.model()
    assert model.eval_bool(cur) is True
