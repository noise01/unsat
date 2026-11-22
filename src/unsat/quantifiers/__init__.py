"""Quantifier instantiation and reasoning (E-matching and MBQI).

Sub-solver queries needed for MBQI use ``Protocol`` / callback interfaces
defined here and injected by ``smt`` (dependency inversion).

Depends on: ``syntax``, ``theories``, ``model``.
"""

from unsat.quantifiers.base import (
    QuantifierBudget,
    QuantifierStats,
    SubSolver,
    SubSolverStatus,
)
from unsat.quantifiers.ematch import EMatcher, EMatchResult, extract_patterns
from unsat.quantifiers.mbqi import MBQIEngine, MBQIResult

__all__ = [
    "EMatchResult",
    "EMatcher",
    "MBQIEngine",
    "MBQIResult",
    "QuantifierBudget",
    "QuantifierStats",
    "SubSolver",
    "SubSolverStatus",
    "extract_patterns",
]
