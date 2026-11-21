"""Standalone propositional CDCL SAT solver core.

Operates solely on integer variables, literals, and clauses. Must remain
completely independent of ``syntax`` and all other ``unsat`` modules. Upward
online CDCL(T) coordination uses integer-literal hook ``Protocol`` interfaces
defined here and injected by ``smt``.
"""

from unsat.sat.solver import SATSolver
from unsat.sat.types import (
    L_FALSE,
    L_TRUE,
    L_UNDEF,
    Clause,
    LBool,
    Lit,
    SATStats,
    SolveResult,
    TheoryPropagator,
    Var,
    from_dimacs_lit,
    lit_sign,
    lit_var,
    neg_lit,
    negate,
    pos_lit,
    to_dimacs_lit,
)

__all__ = [
    "L_FALSE",
    "L_TRUE",
    "L_UNDEF",
    "Clause",
    "LBool",
    "Lit",
    "SATSolver",
    "SATStats",
    "SolveResult",
    "TheoryPropagator",
    "Var",
    "from_dimacs_lit",
    "lit_sign",
    "lit_var",
    "neg_lit",
    "negate",
    "pos_lit",
    "to_dimacs_lit",
]
