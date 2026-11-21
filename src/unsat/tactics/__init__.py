"""Pure AST-to-AST preprocessing, simplification, and reduction tactics.

Produces transformed formulas and corresponding model converters via ``model``;
SAT clausification (Tseitin encoding to integer clauses) belongs in ``smt``.

Depends on: ``syntax``, ``model``.
"""

from unsat.tactics.base import Tactic, TacticResult, Then
from unsat.tactics.bitblast import (
    BitBlaster,
    BitBlastTactic,
    BitVecModelConverter,
    BVSimplifyTactic,
    bitblast,
    bv_simplify,
)
from unsat.tactics.nnf import NNFTactic, to_nnf
from unsat.tactics.simplify import SimplifyTactic, simplify

__all__ = [
    "BVSimplifyTactic",
    "BitBlastTactic",
    "BitBlaster",
    "BitVecModelConverter",
    "NNFTactic",
    "SimplifyTactic",
    "Tactic",
    "TacticResult",
    "Then",
    "bitblast",
    "bv_simplify",
    "simplify",
    "to_nnf",
]
