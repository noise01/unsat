"""Shared budget, statistics, and sub-solver protocols for quantifier reasoning.

Depends on: ``syntax``, ``model``.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum
from typing import Protocol

from unsat.model import Model
from unsat.syntax import Expr


@dataclass(frozen=True, slots=True)
class QuantifierBudget:
    """Resource caps for E-matching and MBQI rounds before returning ``UNKNOWN``."""

    max_rounds: int = 8
    max_matches: int = 1024
    max_instantiations: int = 1024
    max_mbqi_rounds: int = 8
    max_ematch_depth: int = 4

    def __post_init__(self) -> None:
        for field_name in (
            "max_rounds",
            "max_matches",
            "max_instantiations",
            "max_mbqi_rounds",
            "max_ematch_depth",
        ):
            val = getattr(self, field_name)
            if isinstance(val, bool) or not isinstance(val, int) or val < 0:
                msg = f"{field_name} must be a non-negative integer, got {val!r}"
                raise ValueError(msg)


@dataclass(slots=True)
class QuantifierStats:
    """Instrumentation counters collected across E-matching and MBQI."""

    ematch_rounds: int = 0
    ematch_candidates: int = 0
    ematch_instantiations: int = 0
    mbqi_rounds: int = 0
    mbqi_instantiations: int = 0
    mbqi_verified: int = 0
    budget_exhausted: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "quantifier_ematch_rounds": self.ematch_rounds,
            "quantifier_ematch_candidates": self.ematch_candidates,
            "quantifier_ematch_instantiations": self.ematch_instantiations,
            "quantifier_mbqi_rounds": self.mbqi_rounds,
            "quantifier_mbqi_instantiations": self.mbqi_instantiations,
            "quantifier_mbqi_verified": self.mbqi_verified,
            "quantifier_budget_exhausted": self.budget_exhausted,
        }


class SubSolverStatus(Enum):
    """Result returned by an injected ground sub-solver check."""

    SAT = "SAT"
    UNSAT = "UNSAT"
    UNKNOWN = "UNKNOWN"


class SubSolver(Protocol):
    """Callback protocol injected by ``smt`` so MBQI stays decoupled from ``sat``."""

    def check_formula(
        self, formulas: Sequence[Expr]
    ) -> tuple[SubSolverStatus, Model | None]:
        """Check satisfiability of ``formulas``, returning ``(status, model)``."""
