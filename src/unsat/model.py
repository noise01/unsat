"""Model representation, formula evaluation, and model reconstruction.

Will promote to a ``model/`` subpackage as implementation grows.

Depends on: ``syntax``.
"""

from collections.abc import Mapping, Sequence
from fractions import Fraction
from typing import Protocol

from unsat.syntax import (
    App,
    Const,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Sort,
    SortKind,
    iter_subexprs,
)

type Value = bool | int | Fraction | Const


class FuncInterp:
    """Finite-table interpretation with a default fallback for a function symbol."""

    def __init__(
        self,
        decl: FuncDecl,
        entries: (
            Mapping[tuple[Const, ...], Const]
            | Sequence[tuple[tuple[Const, ...], Const]]
        ),
        else_value: Const,
    ) -> None:
        if not decl.is_uninterpreted or decl.arity < 1:
            msg = f"FuncInterp requires an arity >= 1 uninterpreted decl, got '{decl}'"
            raise ValueError(msg)
        if not isinstance(else_value, Const):
            msg = f"FuncInterp else_value must be a Const, got {type(else_value)}"
            raise TypeError(msg)
        if else_value.ctx is not decl.ctx:
            msg = "FuncInterp else_value belongs to a different Context"
            raise ValueError(msg)
        if else_value.sort is not decl.range_sort:
            msg = (
                f"FuncInterp else_value sort '{else_value.sort}' does not match "
                f"range sort '{decl.range_sort}'"
            )
            raise TypeError(msg)

        self._decl = decl
        self._else_value = else_value
        self._table: dict[tuple[Const, ...], Const] = {}

        pairs = entries.items() if isinstance(entries, Mapping) else entries
        for key, result in pairs:
            if len(key) != decl.arity:
                msg = (
                    f"FuncInterp entry for '{decl}' expects {decl.arity} args, "
                    f"got {len(key)}"
                )
                raise ValueError(msg)
            for i, (arg, expected_sort) in enumerate(
                zip(key, decl.domain, strict=True)
            ):
                if not isinstance(arg, Const):
                    msg = f"FuncInterp key argument {i} must be a Const"
                    raise TypeError(msg)
                if arg.ctx is not decl.ctx:
                    msg = f"FuncInterp key argument {i} belongs to a different Context"
                    raise ValueError(msg)
                if arg.sort is not expected_sort:
                    msg = (
                        f"FuncInterp key argument {i} sort '{arg.sort}' does not "
                        f"match '{expected_sort}'"
                    )
                    raise TypeError(msg)
            if not isinstance(result, Const):
                msg = f"FuncInterp entry result must be a Const, got {type(result)}"
                raise TypeError(msg)
            if result.ctx is not decl.ctx:
                msg = "FuncInterp entry result belongs to a different Context"
                raise ValueError(msg)
            if result.sort is not decl.range_sort:
                msg = (
                    f"FuncInterp entry result sort '{result.sort}' does not match "
                    f"range sort '{decl.range_sort}'"
                )
                raise TypeError(msg)
            self._table[tuple(key)] = result

    @property
    def decl(self) -> FuncDecl:
        """Function declaration interpreted by this table."""
        return self._decl

    @property
    def arity(self) -> int:
        """Number of arguments expected by the interpreted function."""
        return self._decl.arity

    @property
    def else_value(self) -> Const:
        """Default constant returned for argument tuples absent from the table."""
        return self._else_value

    def entries(self) -> tuple[tuple[tuple[Const, ...], Const], ...]:
        """Return explicit ``(args, value)`` table entries in insertion order."""
        return tuple(self._table.items())

    def __len__(self) -> int:
        return len(self._table)

    def __call__(self, *args: Const) -> Const:
        if len(args) != self._decl.arity:
            msg = (
                f"FuncInterp for '{self._decl}' expects {self._decl.arity} args, "
                f"got {len(args)}"
            )
            raise ValueError(msg)
        return self._table.get(args, self._else_value)

    def __repr__(self) -> str:
        items = ", ".join(
            f"({', '.join(str(a) for a in key)}) -> {val}"
            for key, val in self._table.items()
        )
        if items:
            return f"FuncInterp({self._decl.name}: {items}, else -> {self._else_value})"
        return f"FuncInterp({self._decl.name}: else -> {self._else_value})"


class Model:
    """Mapping from uninterpreted declarations to concrete values and functions."""

    def __init__(
        self,
        ctx: Context,
        values: Mapping[FuncDecl, Value] | None = None,
        *,
        functions: Mapping[FuncDecl, FuncInterp] | None = None,
        universes: Mapping[Sort, Sequence[Const]] | None = None,
    ) -> None:
        self._ctx = ctx
        self._values: dict[FuncDecl, Value] = {}
        self._functions: dict[FuncDecl, FuncInterp] = {}
        self._universes: dict[Sort, tuple[Const, ...]] = {}

        if values is not None:
            for decl, val in values.items():
                self._values[decl] = self._validate_const_entry(decl, val)

        if functions is not None:
            for decl, interp in functions.items():
                self._validate_func_entry(decl, interp)
                self._functions[decl] = interp

        if universes is not None:
            for sort, elems in universes.items():
                self._validate_universe(sort, elems)
                self._universes[sort] = tuple(elems)

    def _validate_decl(self, decl: FuncDecl) -> None:
        if decl.ctx is not self._ctx:
            msg = f"FuncDecl '{decl}' belongs to a different Context"
            raise ValueError(msg)
        if not decl.is_uninterpreted or decl.arity != 0:
            msg = f"Model entries must be 0-arity uninterpreted constants, got '{decl}'"
            raise ValueError(msg)

    def _validate_const_entry(self, decl: FuncDecl, val: Value) -> Value:
        self._validate_decl(decl)
        kind = decl.range_sort.kind
        if kind is SortKind.BOOL:
            if isinstance(val, bool):
                return val
            if isinstance(val, Const) and val.is_bool:
                if val.ctx is not self._ctx:
                    msg = f"Value '{val}' belongs to a different Context"
                    raise ValueError(msg)
                return bool(val.value)
            msg = f"Expected Bool value for '{decl}', got {val!r}"
            raise TypeError(msg)

        if kind is SortKind.INT:
            if isinstance(val, int) and not isinstance(val, bool):
                return val
            if isinstance(val, Const) and val.is_int:
                if val.ctx is not self._ctx:
                    msg = f"Value '{val}' belongs to a different Context"
                    raise ValueError(msg)
                assert isinstance(val.value, int)
                assert not isinstance(val.value, bool)
                return val.value
            msg = f"Expected Int value for '{decl}', got {val!r}"
            raise TypeError(msg)

        if kind is SortKind.REAL:
            if isinstance(val, Fraction):
                return val
            if isinstance(val, int) and not isinstance(val, bool):
                return Fraction(val)
            if isinstance(val, Const) and val.is_real:
                if val.ctx is not self._ctx:
                    msg = f"Value '{val}' belongs to a different Context"
                    raise ValueError(msg)
                assert isinstance(val.value, Fraction)
                return val.value
            msg = f"Expected Real value for '{decl}', got {val!r}"
            raise TypeError(msg)

        if not isinstance(val, Const):
            msg = f"Expected domain Const for '{decl}', got {val!r}"
            raise TypeError(msg)
        if val.ctx is not self._ctx:
            msg = f"Value '{val}' belongs to a different Context"
            raise ValueError(msg)
        if val.sort is not decl.range_sort:
            msg = (
                f"Value sort '{val.sort}' does not match declaration sort "
                f"'{decl.range_sort}'"
            )
            raise TypeError(msg)
        return val

    def _validate_func_entry(self, decl: FuncDecl, interp: FuncInterp) -> None:
        if decl.ctx is not self._ctx:
            msg = f"FuncDecl '{decl}' belongs to a different Context"
            raise ValueError(msg)
        if not decl.is_uninterpreted or decl.arity < 1:
            msg = f"Function interpretations require arity >= 1 decl, got '{decl}'"
            raise ValueError(msg)
        if interp.decl is not decl:
            msg = f"FuncInterp declaration '{interp.decl}' does not match key '{decl}'"
            raise ValueError(msg)

    def _validate_universe(self, sort: Sort, elems: Sequence[Const]) -> None:
        if sort.ctx is not self._ctx:
            msg = f"Sort '{sort}' belongs to a different Context"
            raise ValueError(msg)
        if sort.kind is not SortKind.UNINTERPRETED:
            msg = f"Universes are only stored for uninterpreted sorts, got '{sort}'"
            raise TypeError(msg)
        for elem in elems:
            if elem.ctx is not self._ctx:
                msg = f"Universe element '{elem}' belongs to a different Context"
                raise ValueError(msg)
            if elem.sort is not sort:
                msg = f"Universe element '{elem}' does not have sort '{sort}'"
                raise TypeError(msg)

    def _resolve_decl(self, key: FuncDecl | Expr) -> FuncDecl:
        if isinstance(key, FuncDecl):
            self._validate_decl(key)
            return key
        if isinstance(key, App) and key.is_const_symbol:
            if key.ctx is not self._ctx:
                msg = f"Expr '{key}' belongs to a different Context"
                raise ValueError(msg)
            return key.decl
        raise KeyError(key)

    def _default_const_for_sort(self, sort: Sort) -> Const:
        if sort.kind is SortKind.BOOL:
            return self._ctx.mk_false()
        if sort.kind is SortKind.INT:
            return self._ctx.mk_int_val(0)
        if sort.kind is SortKind.REAL:
            return self._ctx.mk_real_val(0)
        universe = self._universes.get(sort)
        if universe:
            return universe[0]
        return self._ctx.mk_domain_val(sort, 0)

    def _value_to_const(self, val: Value, sort: Sort) -> Const:
        if isinstance(val, Const):
            return val
        if sort.kind is SortKind.BOOL:
            assert isinstance(val, bool)
            return self._ctx.mk_bool_val(val)
        if sort.kind is SortKind.INT:
            assert isinstance(val, int)
            assert not isinstance(val, bool)
            return self._ctx.mk_int_val(val)
        assert sort.kind is SortKind.REAL
        assert isinstance(val, (int, Fraction))
        return self._ctx.mk_real_val(val)

    @property
    def ctx(self) -> Context:
        """AST context associated with this model."""
        return self._ctx

    def decls(self) -> tuple[FuncDecl, ...]:
        """Return 0-arity declarations interpreted by this model in insertion order."""
        return tuple(self._values)

    def func_decls(self) -> tuple[FuncDecl, ...]:
        """Return arity >= 1 function declarations interpreted by this model."""
        return tuple(self._functions)

    def sorts(self) -> tuple[Sort, ...]:
        """Return uninterpreted sorts whose finite universes are recorded here."""
        return tuple(self._universes)

    def func_interp(self, decl: FuncDecl) -> FuncInterp:
        """Return the ``FuncInterp`` recorded for ``decl``."""
        if decl.ctx is not self._ctx:
            msg = f"FuncDecl '{decl}' belongs to a different Context"
            raise ValueError(msg)
        return self._functions[decl]

    def has_func_interp(self, decl: FuncDecl) -> bool:
        """Return whether ``decl`` has a recorded function interpretation."""
        if decl.ctx is not self._ctx:
            return False
        return decl in self._functions

    def universe(self, sort: Sort) -> tuple[Const, ...]:
        """Return domain elements recorded for ``sort`` (empty if none recorded)."""
        if sort.ctx is not self._ctx:
            msg = f"Sort '{sort}' belongs to a different Context"
            raise ValueError(msg)
        return self._universes.get(sort, ())

    def items(self) -> list[tuple[FuncDecl, Value]]:
        """Return 0-arity ``(declaration, value)`` pairs stored in this model."""
        return list(self._values.items())

    def __len__(self) -> int:
        return len(self._values) + len(self._functions)

    def __contains__(self, key: object) -> bool:
        if not isinstance(key, (FuncDecl, Expr)):
            return False
        if isinstance(key, FuncDecl) and key.arity >= 1:
            return key.ctx is self._ctx and key in self._functions
        try:
            decl = self._resolve_decl(key)
        except KeyError, ValueError:
            return False
        return decl in self._values

    def __getitem__(self, key: FuncDecl | Expr) -> Value:
        decl = self._resolve_decl(key)
        return self._values[decl]

    def get(self, key: FuncDecl | Expr, default: Value | None = None) -> Value | None:
        """Return the interpreted value for ``key``, or ``default`` if absent."""
        decl = self._resolve_decl(key)
        return self._values.get(decl, default)

    def eval(self, expr: Expr, *, model_completion: bool = False) -> Expr:
        """Evaluate ``expr`` under this model, returning a simplified ``Expr``."""
        if expr.ctx is not self._ctx:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)

        memo: dict[Expr, Expr] = {}
        for node in iter_subexprs(expr):
            if isinstance(node, Const):
                memo[node] = node
                continue
            if not isinstance(node, App):
                memo[node] = node
                continue

            if node.is_const_symbol:
                if node.decl in self._values:
                    memo[node] = self._value_to_const(
                        self._values[node.decl], node.sort
                    )
                elif model_completion:
                    memo[node] = self._default_const_for_sort(node.sort)
                else:
                    memo[node] = node
                continue

            eval_args = [memo[arg] for arg in node.args]
            match node.decl.kind:
                case DeclKind.NOT:
                    memo[node] = self._ctx.mk_not(eval_args[0])
                case DeclKind.AND:
                    memo[node] = self._ctx.mk_and(*eval_args)
                case DeclKind.OR:
                    memo[node] = self._ctx.mk_or(*eval_args)
                case DeclKind.IMPLIES:
                    memo[node] = self._ctx.mk_implies(eval_args[0], eval_args[1])
                case DeclKind.XOR:
                    memo[node] = self._ctx.mk_xor(eval_args[0], eval_args[1])
                case DeclKind.EQ:
                    memo[node] = self._ctx.mk_eq(eval_args[0], eval_args[1])
                case DeclKind.DISTINCT:
                    if eval_args and eval_args[0].is_bool and len(eval_args) >= 3:
                        memo[node] = self._ctx.mk_false()
                    else:
                        memo[node] = self._ctx.mk_distinct(*eval_args)
                case DeclKind.ITE:
                    memo[node] = self._ctx.mk_ite(
                        eval_args[0], eval_args[1], eval_args[2]
                    )
                case DeclKind.NEG:
                    memo[node] = self._ctx.mk_neg(eval_args[0])
                case DeclKind.ADD:
                    memo[node] = self._ctx.mk_add(*eval_args)
                case DeclKind.SUB:
                    memo[node] = self._ctx.mk_sub(eval_args[0], eval_args[1])
                case DeclKind.MUL:
                    memo[node] = self._ctx.mk_mul(*eval_args)
                case DeclKind.DIV:
                    memo[node] = self._ctx.mk_div(eval_args[0], eval_args[1])
                case DeclKind.LT:
                    memo[node] = self._ctx.mk_lt(eval_args[0], eval_args[1])
                case DeclKind.LE:
                    memo[node] = self._ctx.mk_le(eval_args[0], eval_args[1])
                case DeclKind.GT:
                    memo[node] = self._ctx.mk_gt(eval_args[0], eval_args[1])
                case DeclKind.GE:
                    memo[node] = self._ctx.mk_ge(eval_args[0], eval_args[1])
                case DeclKind.TO_REAL:
                    memo[node] = self._ctx.mk_to_real(eval_args[0])
                case DeclKind.UNINTERPRETED:
                    const_args = tuple(
                        arg for arg in eval_args if isinstance(arg, Const)
                    )
                    if len(const_args) == len(eval_args):
                        if node.decl in self._functions:
                            memo[node] = self._functions[node.decl](*const_args)
                        elif model_completion:
                            memo[node] = self._default_const_for_sort(node.sort)
                        else:
                            memo[node] = self._ctx.mk_app(node.decl, *eval_args)
                    else:
                        memo[node] = self._ctx.mk_app(node.decl, *eval_args)

        return memo[expr]

    def eval_bool(self, expr: Expr, *, model_completion: bool = True) -> bool:
        """Evaluate Boolean expression ``expr`` to a concrete Python ``bool``."""
        if not expr.is_bool:
            msg = f"Expected Bool expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        evaluated = self.eval(expr, model_completion=model_completion)
        if not isinstance(evaluated, Const) or not isinstance(evaluated.value, bool):
            msg = (
                f"Expression '{expr}' did not reduce to a Boolean constant: {evaluated}"
            )
            raise ValueError(msg)
        return evaluated.value

    def eval_int(self, expr: Expr, *, model_completion: bool = True) -> int:
        """Evaluate ``Int`` expression ``expr`` to a concrete Python ``int``."""
        if not expr.is_int:
            msg = f"Expected Int expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        evaluated = self.eval(expr, model_completion=model_completion)
        if (
            not isinstance(evaluated, Const)
            or not isinstance(evaluated.value, int)
            or isinstance(evaluated.value, bool)
        ):
            msg = f"Expression '{expr}' did not reduce to an Int constant: {evaluated}"
            raise ValueError(msg)
        return evaluated.value

    def eval_real(self, expr: Expr, *, model_completion: bool = True) -> Fraction:
        """Evaluate ``Real`` expression ``expr`` to an exact ``Fraction``."""
        if not expr.is_real:
            msg = f"Expected Real expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        evaluated = self.eval(expr, model_completion=model_completion)
        if not isinstance(evaluated, Const) or not isinstance(
            evaluated.value, Fraction
        ):
            msg = f"Expression '{expr}' did not reduce to a Real constant: {evaluated}"
            raise ValueError(msg)
        return evaluated.value

    def __repr__(self) -> str:
        parts = [f"{decl.name}={val}" for decl, val in self._values.items()]
        parts.extend(repr(interp) for interp in self._functions.values())
        return f"Model({', '.join(parts)})"


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
            if not rhs.is_bool:
                msg = f"Substitution RHS must have Bool sort, got '{rhs.sort}'"
                raise TypeError(msg)
            self._substitutions.append((decl, rhs))

    def convert(self, model: Model) -> Model:
        """Evaluate each eliminated declaration and merge it into the returned model."""
        values = dict(model.items())
        functions = {decl: model.func_interp(decl) for decl in model.func_decls()}
        universes = {sort: model.universe(sort) for sort in model.sorts()}
        for decl, rhs in self._substitutions:
            current = Model(model.ctx, values, functions=functions, universes=universes)
            values[decl] = current.eval_bool(rhs, model_completion=True)
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


__all__ = [
    "CompositeModelConverter",
    "FuncInterp",
    "IdentityModelConverter",
    "Model",
    "ModelConverter",
    "SubstitutionModelConverter",
    "Value",
]
