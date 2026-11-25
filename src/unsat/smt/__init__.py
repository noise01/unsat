"""CDCL(T) core orchestrator.

Bridges ``syntax`` expressions with the standalone ``sat`` solver, handles Tseitin
clausification and Model-Based Theory Combination (MBTC), coordinates ``theories``,
``tactics``, ``quantifiers``, and ``model`` construction, and injects callbacks into
lower layers (``sat`` and ``quantifiers``).

Depends on: ``syntax``, ``sat``, ``theories``, ``tactics``, ``quantifiers``, ``model``.
"""

from unsat.sat import SolveResult
from unsat.smt.solver import SMTSolver, solve_with_tactic

__all__ = ["SMTSolver", "SolveResult", "solve_with_tactic"]
