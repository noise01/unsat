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
from unsat.tactics.ctx_simplify import CtxSimplifyTactic, ctx_simplify
from unsat.tactics.elim import (
    GaussianElimTactic,
    PropagateBoundsTactic,
    gaussian_elim,
    propagate_bounds,
)
from unsat.tactics.nnf import NNFTactic, to_nnf
from unsat.tactics.simplify import SimplifyTactic, simplify
from unsat.tactics.skolem import SkolemizeTactic, skolemize

__all__ = [
    "BVSimplifyTactic",
    "BitBlastTactic",
    "BitBlaster",
    "BitVecModelConverter",
    "CtxSimplifyTactic",
    "GaussianElimTactic",
    "NNFTactic",
    "PropagateBoundsTactic",
    "SimplifyTactic",
    "SkolemizeTactic",
    "Tactic",
    "TacticResult",
    "Then",
    "bitblast",
    "bv_simplify",
    "ctx_simplify",
    "gaussian_elim",
    "propagate_bounds",
    "simplify",
    "skolemize",
    "to_nnf",
]
