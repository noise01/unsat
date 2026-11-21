"""Assignment trail, decision-level tracking, and saved phases."""

from typing import Final

from unsat.sat.types import L_FALSE, L_TRUE, L_UNDEF, Clause, LBool, Lit, Var

#: Sentinel stored in ``Trail.reason`` for lazily explained theory propagations.
THEORY_REASON: Final[object] = object()

type Reason = Clause | object | None


class Trail:
    """Stores variable assignments, decision levels, saved phases, and reasons."""

    def __init__(self) -> None:
        self.assignment: list[LBool] = []
        self.lit_eval: list[LBool] = []
        self.level: list[int] = []
        self.reason: list[Reason] = []
        self.phase: list[LBool] = []
        self.stack: list[Lit] = []
        self.limits: list[int] = []

    @property
    def num_vars(self) -> int:
        """Number of variables allocated on the trail."""
        return len(self.assignment)

    @property
    def decision_level(self) -> int:
        """Current decision level (0 at the root level)."""
        return len(self.limits)

    @property
    def all_assigned(self) -> bool:
        """Whether every allocated variable currently has a truth value."""
        return len(self.stack) == len(self.assignment)

    def add_variable(self) -> Var:
        """Allocate a fresh unassigned variable and return its 0-based index."""
        var = len(self.assignment)
        self.assignment.append(L_UNDEF)
        self.lit_eval.extend((L_UNDEF, L_UNDEF))
        self.level.append(0)
        self.reason.append(None)
        self.phase.append(L_UNDEF)
        return var

    def eval_lit(self, lit: Lit) -> LBool:
        """Return ``L_TRUE``, ``L_FALSE``, or ``L_UNDEF`` for ``lit``."""
        return self.lit_eval[lit]

    def assign(self, lit: Lit, reason: Reason = None) -> None:
        """Record ``lit`` as true at the current decision level."""
        var = lit >> 1
        val = L_FALSE if (lit & 1) else L_TRUE
        self.assignment[var] = val
        self.level[var] = len(self.limits)
        self.reason[var] = reason
        self.phase[var] = val
        self.lit_eval[lit] = L_TRUE
        self.lit_eval[lit ^ 1] = L_FALSE
        self.stack.append(lit)

    def push(self) -> None:
        """Start a new decision level."""
        self.limits.append(len(self.stack))

    def backtrack(self, target_level: int) -> list[Var]:
        """Unassign all literals above ``target_level`` and return freed variables."""
        if target_level >= len(self.limits):
            return []

        limit = self.limits[target_level]
        unassigned: list[Var] = []
        while len(self.stack) > limit:
            lit = self.stack.pop()
            var = lit >> 1
            self.phase[var] = self.assignment[var]
            self.assignment[var] = L_UNDEF
            self.level[var] = 0
            self.reason[var] = None
            self.lit_eval[var << 1] = L_UNDEF
            self.lit_eval[(var << 1) | 1] = L_UNDEF
            unassigned.append(var)

        del self.limits[target_level:]
        return unassigned
