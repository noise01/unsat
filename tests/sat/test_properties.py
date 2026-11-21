from itertools import product

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.sat import Lit, SATSolver, SolveResult, Var, neg_lit, pos_lit


def evaluate_cnf(clauses: list[list[Lit]], model: dict[Var, bool]) -> bool:
    """Independently check whether ``model`` satisfies every clause."""
    for clause in clauses:
        if not any(
            (not model[lit >> 1] if (lit & 1) else model[lit >> 1]) for lit in clause
        ):
            return False
    return True


def _bruteforce_sat(num_vars: int, clauses: list[list[Lit]]) -> bool:
    for bits in product((False, True), repeat=num_vars):
        assignment = dict(enumerate(bits))
        if evaluate_cnf(clauses, assignment):
            return True
    return False


def _z3_lit(z3_vars: list[z3.BoolRef], lit: Lit) -> z3.BoolRef:
    var_ref = z3_vars[lit >> 1]
    return z3.Not(var_ref) if (lit & 1) else var_ref


def _z3_solve(
    num_vars: int,
    clauses: list[list[Lit]],
    assumptions: list[Lit] | None = None,
) -> SolveResult:
    z3_vars = [z3.Bool(f"v_{i}") for i in range(num_vars)]
    solver = z3.Solver()
    for clause in clauses:
        if not clause:
            solver.add(z3.BoolVal(False))
        else:
            solver.add(z3.Or([_z3_lit(z3_vars, lit) for lit in clause]))
    z3_assumps = [_z3_lit(z3_vars, lit) for lit in (assumptions or ())]
    res = solver.check(*z3_assumps)
    if res == z3.sat:
        return SolveResult.SAT
    if res == z3.unsat:
        return SolveResult.UNSAT
    return SolveResult.UNKNOWN


@st.composite
def cnf_strategy(
    draw: st.DrawFn,
    min_vars: int,
    max_vars: int,
    max_clauses: int,
    min_clause_len: int = 0,
    max_clause_len: int = 4,
) -> tuple[int, list[list[Lit]]]:
    num_vars = draw(st.integers(min_value=min_vars, max_value=max_vars))
    num_clauses = draw(st.integers(min_value=0, max_value=max_clauses))
    lits = [fn(v) for v in range(num_vars) for fn in (pos_lit, neg_lit)]
    clause_st = st.lists(
        st.sampled_from(lits),
        min_size=min_clause_len,
        max_size=max_clause_len,
    )
    clauses = draw(st.lists(clause_st, min_size=num_clauses, max_size=num_clauses))
    return num_vars, clauses


@settings(max_examples=100, deadline=None)
@given(instance=cnf_strategy(min_vars=1, max_vars=6, max_clauses=28))
def test_matches_bruteforce_oracle_on_small_cnfs(
    instance: tuple[int, list[list[Lit]]],
) -> None:
    num_vars, clauses = instance
    expected_sat = _bruteforce_sat(num_vars, clauses)

    solver = SATSolver()
    solver.ensure_vars(num_vars)
    for clause in clauses:
        solver.add_clause(clause)

    result = solver.solve()
    if expected_sat:
        assert result is SolveResult.SAT
        assert evaluate_cnf(clauses, solver.model())
    else:
        assert result is SolveResult.UNSAT


@settings(max_examples=75, deadline=None)
@given(
    num_vars=st.integers(min_value=5, max_value=24),
    data=st.data(),
)
def test_differential_against_z3_random_3sat(
    num_vars: int, data: st.DataObject
) -> None:
    # Span under-constrained to over-constrained ratios around 4.26.
    num_clauses = data.draw(st.integers(min_value=num_vars, max_value=num_vars * 6))
    lits = [fn(v) for v in range(num_vars) for fn in (pos_lit, neg_lit)]
    clauses = data.draw(
        st.lists(
            st.lists(st.sampled_from(lits), min_size=1, max_size=3),
            min_size=num_clauses,
            max_size=num_clauses,
        )
    )

    solver = SATSolver()
    solver.ensure_vars(num_vars)
    for clause in clauses:
        solver.add_clause(clause)

    result = solver.solve()
    expected = _z3_solve(num_vars, clauses)
    assert result is expected
    if result is SolveResult.SAT:
        assert evaluate_cnf(clauses, solver.model())


@settings(max_examples=50, deadline=None)
@given(
    num_vars=st.integers(min_value=2, max_value=12),
    data=st.data(),
)
def test_incremental_clauses_and_assumptions_differential_z3(
    num_vars: int, data: st.DataObject
) -> None:
    lits = [fn(v) for v in range(num_vars) for fn in (pos_lit, neg_lit)]
    batches = data.draw(
        st.lists(
            st.tuples(
                st.lists(
                    st.lists(st.sampled_from(lits), min_size=1, max_size=3),
                    min_size=0,
                    max_size=5,
                ),
                st.lists(st.sampled_from(lits), min_size=0, max_size=5),
            ),
            min_size=1,
            max_size=6,
        )
    )

    solver = SATSolver()
    solver.ensure_vars(num_vars)
    accumulated: list[list[Lit]] = []

    for new_clauses, assumptions in batches:
        for clause in new_clauses:
            solver.add_clause(clause)
            accumulated.append(clause)

        verdict = solver.solve(assumptions)
        expected = _z3_solve(num_vars, accumulated, assumptions)
        assert verdict is expected

        if verdict is SolveResult.SAT:
            model = solver.model()
            assert evaluate_cnf(accumulated, model)
            assert evaluate_cnf([[lit] for lit in assumptions], model)
            assert solver.unsat_core() == []
        else:
            core = solver.unsat_core()
            assert set(core) <= set(assumptions)
            # Re-verify unsat core soundness independently in fresh SATSolver and Z3.
            recheck = SATSolver()
            recheck.ensure_vars(num_vars)
            for clause in accumulated:
                recheck.add_clause(clause)
            assert recheck.solve(core) is SolveResult.UNSAT
            assert _z3_solve(num_vars, accumulated, core) is SolveResult.UNSAT
