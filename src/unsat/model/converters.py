"""Model reconstruction converters for preprocessing and reduction tactics."""

from collections.abc import Iterable, Mapping, Sequence
from fractions import Fraction
from typing import Protocol

from unsat.model.eval import Model
from unsat.syntax import Const, Expr, FuncDecl


class ModelConverter(Protocol):
    """Reconstructs a user-level model from a tactic-transformed solver model."""

    def convert(self, model: Model) -> Model:
        """Transform ``model`` back to the pre-tactic vocabulary."""


class IdentityModelConverter:
    """No-op model converter returning the input model unchanged."""

    def convert(self, model: Model) -> Model:
        """Return ``model`` unchanged."""
        return model


class SubstitutionModelConverter:
    """Reconstructs eliminated symbols defined in terms of surviving expressions."""

    def __init__(self, substitutions: Mapping[FuncDecl, Expr]) -> None:
        self._substitutions: list[tuple[FuncDecl, Expr]] = []
        for decl, rhs in substitutions.items():
            if decl.ctx is not rhs.ctx:
                msg = f"Substitution for '{decl}' mixes different Contexts"
                raise ValueError(msg)
            if not decl.is_uninterpreted or decl.arity != 0:
                msg = f"Substituted key must be a 0-arity constant, got '{decl}'"
                raise ValueError(msg)
            if rhs.sort is not decl.range_sort:
                msg = f"Substitution RHS sort '{rhs.sort}' does not match declaration sort '{decl.range_sort}'"
                raise TypeError(msg)
            self._substitutions.append((decl, rhs))

    def convert(self, model: Model) -> Model:
        """Evaluate each eliminated declaration and merge it into the returned model."""
        values = dict(model.items())
        functions = {decl: model.func_interp(decl) for decl in model.func_decls()}
        universes = {sort: model.universe(sort) for sort in model.sorts()}
        for decl, rhs in self._substitutions:
            current = Model(model.ctx, values, functions=functions, universes=universes)
            val_expr = current.eval(rhs, model_completion=True)
            if isinstance(val_expr, Const):
                if decl.range_sort.is_bool:
                    values[decl] = bool(val_expr.value)
                elif decl.range_sort.is_int or decl.range_sort.is_bv:
                    assert isinstance(val_expr.value, int)
                    assert not isinstance(val_expr.value, bool)
                    values[decl] = val_expr.value
                elif decl.range_sort.is_real:
                    assert isinstance(val_expr.value, Fraction)
                    values[decl] = val_expr.value
                else:
                    values[decl] = val_expr
            else:
                values[decl] = val_expr
        return Model(model.ctx, values, functions=functions, universes=universes)


class ProjectionModelConverter:
    """Removes solver/tactic-introduced internal declarations from a model."""

    def __init__(self, hidden_decls: Iterable[FuncDecl]) -> None:
        self._hidden = frozenset(hidden_decls)

    def convert(self, model: Model) -> Model:
        """Return a copy of ``model`` with internal declarations omitted."""
        if not self._hidden:
            return model
        values = {decl: val for decl, val in model.items() if decl not in self._hidden}
        functions = {decl: model.func_interp(decl) for decl in model.func_decls() if decl not in self._hidden}
        universes = {sort: model.universe(sort) for sort in model.sorts()}
        return Model(model.ctx, values, functions=functions, universes=universes)


class CompositeModelConverter:
    """Applies a sequence of converters in reverse order to undo a tactic chain."""

    def __init__(self, converters: Sequence[ModelConverter]) -> None:
        self._converters = tuple(converters)

    def convert(self, model: Model) -> Model:
        """Apply registered converters from last to first."""
        current = model
        for converter in reversed(self._converters):
            current = converter.convert(current)
        return current
