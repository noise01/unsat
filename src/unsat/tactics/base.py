"""Core tactic protocol, result container, and sequential combinator."""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Protocol

from unsat.model import CompositeModelConverter, ModelConverter
from unsat.syntax import Expr


@dataclass(frozen=True, slots=True)
class TacticResult:
    """Output formulas paired with a model-reconstruction converter."""

    formulas: tuple[Expr, ...]
    converter: ModelConverter


class Tactic(Protocol):
    """AST-to-AST preprocessing, simplification, or reduction step."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Transform ``formulas`` and return the new goal + model converter."""


class Then:
    """Applies multiple tactics sequentially from left to right."""

    def __init__(self, *tactics: Tactic) -> None:
        self._tactics = tuple(tactics)

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Run each tactic in order and compose their model converters."""
        current: tuple[Expr, ...] = tuple(formulas)
        converters: list[ModelConverter] = []
        for tactic in self._tactics:
            step = tactic.apply(current)
            current = step.formulas
            converters.append(step.converter)
        return TacticResult(current, CompositeModelConverter(converters))
