from collections.abc import Sequence
from dataclasses import dataclass, field

import pytest

from unsat.sat import (
    Lit,
    SATSolver,
    SolveResult,
    from_dimacs_lit,
    lit_sign,
    lit_var,
    neg_lit,
    negate,
    pos_lit,
    to_dimacs_lit,
)


def _pigeonhole_clauses(pigeons: int, holes: int) -> list[list[Lit]]:
    def var_id(p: int, h: int) -> int:
        return p * holes + h

    clauses: list[list[Lit]] = []
    # Every pigeon must be in at least one hole.
    for p in range(pigeons):
        clauses.append([pos_lit(var_id(p, h)) for h in range(holes)])
    # No hole can hold two pigeons.
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append([neg_lit(var_id(p1, h)), neg_lit(var_id(p2, h))])
    return clauses


def test_literal_helpers() -> None:
    assert pos_lit(0) == 0
    assert neg_lit(0) == 1
    assert pos_lit(3) == 6
    assert neg_lit(3) == 7
    assert negate(pos_lit(2)) == neg_lit(2)
    assert negate(neg_lit(2)) == pos_lit(2)
    assert lit_var(neg_lit(5)) == 5
    assert lit_sign(pos_lit(5)) is False
    assert lit_sign(neg_lit(5)) is True

    assert from_dimacs_lit(1) == pos_lit(0)
    assert from_dimacs_lit(-3) == neg_lit(2)
    assert to_dimacs_lit(pos_lit(0)) == 1
    assert to_dimacs_lit(neg_lit(2)) == -3

    for bad_fn in (
        lambda: pos_lit(-1),
        lambda: neg_lit(-1),
        lambda: negate(-1),
        lambda: lit_var(-1),
        lambda: lit_sign(-1),
        lambda: from_dimacs_lit(0),
        lambda: to_dimacs_lit(-1),
    ):
        with pytest.raises(ValueError, match=r".+"):
            bad_fn()


def test_zero_variable_sat_and_model_errors() -> None:
    solver = SATSolver()
    with pytest.raises(ValueError, match="SAT"):
        solver.model()

    assert solver.solve() is SolveResult.SAT
    assert solver.model() == {}
    assert solver.unsat_core() == []

    # Empty clause makes solver permanently UNSAT.
    assert solver.add_clause([]) is False
    assert solver.ok is False
    assert solver.solve() is SolveResult.UNSAT
    with pytest.raises(ValueError, match="SAT"):
        solver.model()
    assert solver.add_clause([pos_lit(0)]) is False


def test_input_hygiene_and_level0_propagation() -> None:
    solver = SATSolver()
    solver.ensure_vars(3)
    p = pos_lit(0)
    q = pos_lit(1)
    r = pos_lit(2)

    with pytest.raises(ValueError, match="non-negative"):
        solver.add_clause([-1])

    # Tautology and duplicate normalization.
    assert solver.add_clause([p, negate(p)]) is True
    assert solver.add_clause([p, p, q]) is True
    # Assert ~p: (p | q) + ~p forces q via level-0 BCP while r stays unassigned.
    assert solver.add_clause([negate(p)]) is True
    assert solver.value(r) is None
    assert solver.solve() is SolveResult.SAT
    model = solver.model()
    assert model[0] is False
    assert model[1] is True
    assert solver.value(p) is False
    assert solver.value(q) is True

    with pytest.raises(ValueError, match="out of range"):
        solver.value(pos_lit(99))

    # Contradicting level-0 unit assignment.
    assert solver.add_clause([negate(q)]) is False
    assert solver.ok is False
    assert solver.solve() is SolveResult.UNSAT


def test_pigeonhole_unsat_clause_db_reduction_and_restarts() -> None:
    for pigeons, holes in ((4, 3), (5, 4)):
        solver = SATSolver()
        for clause in _pigeonhole_clauses(pigeons, holes):
            assert solver.add_clause(clause)
        assert solver.solve() is SolveResult.UNSAT
        stats = solver.statistics()
        assert stats["conflicts"] > 0
        assert stats["learned_clauses"] > 0

    # Force DB reduction and restarts on PHP(6, 5) with tight thresholds.
    solver = SATSolver()
    solver._reduce_threshold = 10
    solver._reduce_inc = 10
    solver._lbd_queue_size = 5
    solver._lbd_queue = [0] * 5
    solver._restart_cooldown = 5
    solver._restart_margin = 1.0
    for clause in _pigeonhole_clauses(6, 5):
        assert solver.add_clause(clause)

    assert solver.solve() is SolveResult.UNSAT
    stats = solver.statistics()
    assert stats["deleted_clauses"] > 0
    assert stats["restarts"] > 0

    # Verify no deleted learned clauses remain in watches or bin_watches.
    for watch_list in solver._watches:
        assert all(not clause.deleted for _, clause in watch_list)
    for bin_list in solver._bin_watches:
        assert all(not clause.deleted for _, clause in bin_list)


def test_clause_minimization_shrinks_redundant_literals() -> None:
    solver = SATSolver()
    solver.ensure_vars(6)
    # Level 1: x0 -> x1 -> x2.
    # Level 2: x3 -> x4 and x3 -> x5, converging at ~x4 | ~x5 | ~x2 | ~x0.
    # 1-UIP before minimization is [~x3, ~x2, ~x0]; minimization drops ~x2.
    x0, x1, x2, x3, x4, x5 = (pos_lit(i) for i in range(6))
    solver.add_clause([negate(x0), x1])
    solver.add_clause([negate(x1), x2])
    solver.add_clause([negate(x3), x4])
    solver.add_clause([negate(x3), x5])
    solver.add_clause([negate(x4), negate(x5), negate(x2), negate(x0)])

    assert solver.solve([x0, x3]) is SolveResult.UNSAT
    assert any(set(c.literals) == {negate(x0), negate(x3)} for c in solver._learned)
    assert all(negate(x2) not in c.literals for c in solver._learned)
    assert set(solver.unsat_core()) == {x0, x3}


@pytest.mark.parametrize(
    "order",
    [
        (True, False),
        (False, True),
        (False, False, True),
        (True, False, True),
    ],
)
def test_opposite_assumptions_keep_both_polarities_in_core(
    order: tuple[bool, ...],
) -> None:
    p = pos_lit(0)
    assumptions = [p if positive else negate(p) for positive in order]
    solver = SATSolver()
    solver.ensure_vars(1)

    assert solver.solve(assumptions) is SolveResult.UNSAT
    core = solver.unsat_core()
    assert set(core) == {p, negate(p)}

    recheck = SATSolver()
    recheck.ensure_vars(1)
    assert recheck.solve(core) is SolveResult.UNSAT


def test_incremental_unsat_core_reuse_and_base_conflict() -> None:
    p, q, r, s = (pos_lit(i) for i in range(4))
    solver = SATSolver()
    solver.add_clause([negate(p), q])  # p -> q
    solver.add_clause([negate(q), r])  # q -> r

    # Assume p, ~r, and unrelated s.
    assert solver.solve([p, negate(r), s]) is SolveResult.UNSAT
    core = solver.unsat_core()
    assert set(core) == {p, negate(r)}
    assert s not in core

    # Subsequent SAT clears previous unsat core.
    assert solver.solve([p, r]) is SolveResult.SAT
    assert solver.unsat_core() == []
    assert solver.model()[0] is True
    assert solver.model()[2] is True

    # Base conflict clears previous assumption core.
    assert solver.solve([p, negate(r)]) is SolveResult.UNSAT
    assert solver.unsat_core()
    assert solver.add_clause([p]) is True
    assert solver.add_clause([negate(p)]) is False
    assert solver.solve() is SolveResult.UNSAT
    assert solver.unsat_core() == []


@dataclass
class RecordingPropagator:
    """Mock TheoryPropagator testing push/pop balance and lazy explanations."""

    rules: dict[Lit, tuple[Lit, list[Lit]]] = field(default_factory=dict)
    conflict_trigger: tuple[frozenset[Lit], list[Lit]] | None = None
    check_lemmas: list[list[Lit]] = field(default_factory=list)
    depth: int = 0
    trail: list[Lit] = field(default_factory=list)
    limits: list[int] = field(default_factory=list)
    explain_calls: list[Lit] = field(default_factory=list)
    check_calls: int = 0

    def push(self) -> None:
        self.depth += 1
        self.limits.append(len(self.trail))

    def pop(self, num_levels: int) -> None:
        self.depth -= num_levels
        assert self.depth >= 0
        target = self.limits[len(self.limits) - num_levels]
        del self.trail[target:]
        del self.limits[len(self.limits) - num_levels :]

    def on_assign(self, lit: Lit) -> None:
        self.trail.append(lit)

    def propagate(self) -> tuple[Sequence[Lit], Sequence[Lit] | None]:
        trail_set = set(self.trail)
        if self.conflict_trigger is not None:
            triggers, conflict_clause = self.conflict_trigger
            if triggers <= trail_set:
                return (), conflict_clause

        props: list[Lit] = []
        for trigger, (prop_lit, _reason) in self.rules.items():
            if trigger in trail_set and prop_lit not in trail_set:
                props.append(prop_lit)
        return props, None

    def explain_propagation(self, lit: Lit) -> Sequence[Lit]:
        self.explain_calls.append(lit)
        for _trigger, (prop_lit, reason) in self.rules.items():
            if prop_lit == lit:
                return reason
        msg = f"Unexpected explain_propagation for {lit}"
        raise AssertionError(msg)

    def check(self) -> Sequence[Sequence[Lit]]:
        self.check_calls += 1
        if self.check_lemmas:
            return [self.check_lemmas.pop(0)]
        return ()


def test_lazy_explanation_not_called_on_sat_or_unrelated_conflict() -> None:
    p, q, r = (pos_lit(i) for i in range(3))
    # Rule: p -> q (with explanation [~p, q]).
    prop = RecordingPropagator(rules={p: (q, [q, negate(p)])})
    solver = SATSolver(propagator=prop)
    solver.ensure_vars(3)

    # Under assumption [p], p triggers theory propagation of q, SAT without explain!
    assert solver.solve([p, r]) is SolveResult.SAT
    assert solver.model()[1] is True
    assert prop.explain_calls == []
    assert solver.statistics()["theory_propagations"] >= 1

    # Add conflict not involving q: [~p, ~r] + assumption [p, r].
    # Conflict happens directly on ~p | ~r without resolving q's reason.
    solver.add_clause([negate(p), negate(r)])
    assert solver.solve([p, r]) is SolveResult.UNSAT
    assert prop.explain_calls == []
    assert set(solver.unsat_core()) == {p, r}


def test_lazy_explanation_called_when_conflict_traverses_theory_lit() -> None:
    p, q, r = (pos_lit(i) for i in range(3))
    # Theory rule: p |= q (explanation clause: q | ~p).
    prop = RecordingPropagator(rules={p: (q, [q, negate(p)])})
    solver = SATSolver(propagator=prop)
    solver.ensure_vars(3)
    # SAT clause: q -> ~r, so assuming [p, r] forces q then conflicts with r.
    solver.add_clause([negate(q), negate(r)])

    assert solver.solve([p, r]) is SolveResult.UNSAT
    assert prop.explain_calls == [q]
    assert set(solver.unsat_core()) == {p, r}

    # Backtracking on next solve brings depth cleanly back to 0.
    assert solver.solve([negate(p), r]) is SolveResult.SAT
    solver._backtrack(0)
    assert prop.depth == 0


def test_theory_propagator_already_false_and_check_lemmas() -> None:
    p, q = pos_lit(0), pos_lit(1)
    # Direct false propagation: assuming ~q and p triggers p |= q when q is False.
    prop = RecordingPropagator(rules={p: (q, [q, negate(p)])})
    solver = SATSolver(propagator=prop)
    solver.ensure_vars(2)

    assert solver.solve([negate(q), p]) is SolveResult.UNSAT
    assert prop.explain_calls == [q]
    assert set(solver.unsat_core()) == {negate(q), p}

    # check() returning a blocking lemma forces solver to flip decision and succeed.
    lemma_prop = RecordingPropagator(check_lemmas=[[negate(p), negate(q)]])
    solver2 = SATSolver(propagator=lemma_prop)
    solver2.add_clause([p, q])
    assert solver2.solve() is SolveResult.SAT
    m = solver2.model()
    assert m[0] or m[1]
    assert not (m[0] and m[1])
    assert solver2.statistics()["theory_lemmas"] == 1

    # check() returning an already-satisfied lemma does not loop forever.
    sat_lemma_prop = RecordingPropagator(check_lemmas=[[p, negate(p)]])
    solver3 = SATSolver(propagator=sat_lemma_prop)
    solver3.ensure_vars(1)
    assert solver3.solve() is SolveResult.SAT
    assert sat_lemma_prop.check_calls == 1


def test_theory_unit_explanation_and_check_unit_lemma() -> None:
    p, q = pos_lit(0), pos_lit(1)
    # Unconditional unit theory explanation [q] vs assumed ~q yields core [~q].
    prop = RecordingPropagator(rules={p: (q, [q])})
    solver = SATSolver(propagator=prop)
    solver.ensure_vars(2)
    assert solver.solve([negate(q), p]) is SolveResult.UNSAT
    assert prop.explain_calls == [q]
    assert solver.unsat_core() == [negate(q)]

    # Unconditional unit theory explanation [q] vs base ~q derives global UNSAT.
    prop_base = RecordingPropagator(rules={p: (q, [q])})
    solver_base = SATSolver(propagator=prop_base)
    solver_base.add_clause([negate(q)])
    assert solver_base.solve([p]) is SolveResult.UNSAT
    assert prop_base.explain_calls == [q]
    assert solver_base.ok is False
    assert solver_base.unsat_core() == []

    # Unit lemma returned from check() forces assignment at level 0.
    unit_prop = RecordingPropagator(check_lemmas=[[p]])
    solver2 = SATSolver(propagator=unit_prop)
    solver2.ensure_vars(2)
    assert solver2.solve() is SolveResult.SAT
    assert solver2.model()[0] is True

    # Direct conflict_trigger from propagate().
    conflict_prop = RecordingPropagator(
        conflict_trigger=(frozenset({p, q}), [negate(p), negate(q)])
    )
    solver3 = SATSolver(propagator=conflict_prop)
    solver3.ensure_vars(2)
    assert solver3.solve([p, q]) is SolveResult.UNSAT
    assert set(solver3.unsat_core()) == {p, q}
    assert solver3.statistics()["theory_conflicts"] >= 1
