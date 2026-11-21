"""Pure AST-to-AST preprocessing, simplification, and reduction tactics.

Produces transformed formulas and corresponding model converters via ``model``;
SAT clausification (Tseitin encoding to integer clauses) belongs in ``smt``.

Depends on: ``syntax``, ``model``.
"""

from unsat.tactics.base import Tactic, TacticResult, Then
from unsat.tactics.nnf import NNFTactic, to_nnf
from unsat.tactics.simplify import SimplifyTactic, simplify

__all__ = [
    "NNFTactic",
    "SimplifyTactic",
    "Tactic",
    "TacticResult",
    "Then",
    "simplify",
    "to_nnf",
]
