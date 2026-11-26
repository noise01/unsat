"""Concrete model values, array equality helpers, and function interpretations."""

from collections.abc import Mapping, Sequence
from fractions import Fraction

from unsat.syntax import App, Const, DeclKind, Expr, FuncDecl, Sort
from unsat.syntax.context_strings import expr_to_re
from unsat.syntax.str_eval import re_diff, re_is_empty, re_union

type Value = bool | int | Fraction | str | Expr

_CONCRETE_RE_KINDS = frozenset(
    {
        DeclKind.STR_TO_RE,
        DeclKind.RE_NONE,
        DeclKind.RE_ALL,
        DeclKind.RE_ALLCHAR,
        DeclKind.RE_CONCAT,
        DeclKind.RE_UNION,
        DeclKind.RE_INTER,
        DeclKind.RE_STAR,
        DeclKind.RE_PLUS,
        DeclKind.RE_OPT,
        DeclKind.RE_RANGE,
        DeclKind.RE_COMP,
        DeclKind.RE_DIFF,
        DeclKind.RE_POWER,
        DeclKind.RE_LOOP,
    }
)


def _is_concrete_value(expr: Expr) -> bool:
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, Const):
            continue
        if isinstance(node, App) and (
            node.decl.kind in (DeclKind.CONST_ARRAY, DeclKind.STORE)
            or node.decl.kind in _CONCRETE_RE_KINDS
        ):
            stack.extend(node.args)
            continue
        return False
    return True


def _unpack_concrete_array(expr: Expr) -> tuple[Expr, list[tuple[Expr, Expr]]] | None:
    overrides: list[tuple[Expr, Expr]] = []
    cur = expr
    while isinstance(cur, App) and cur.decl.kind is DeclKind.STORE:
        overrides.append((cur.args[1], cur.args[2]))
        cur = cur.args[0]
    if isinstance(cur, App) and cur.decl.kind is DeclKind.CONST_ARRAY:
        return cur.args[0], overrides
    return None


def _concrete_values_equal(
    a: Expr,
    b: Expr,
    universes: Mapping[Sort, tuple[Const, ...]] | None = None,
) -> bool:
    if a is b:
        return True
    if a.sort is not b.sort:
        return False
    if isinstance(a, Const) and isinstance(b, Const):
        return a is b
    if a.is_reglan:
        ra = expr_to_re(a)
        rb = expr_to_re(b)
        if ra is not None and rb is not None:
            if ra == rb:
                return True
            eq = re_is_empty(re_union(re_diff(ra, rb), re_diff(rb, ra)))
            if eq is not None:
                return eq
        return False
    if not a.is_array:
        return False

    ua = _unpack_concrete_array(a)
    ub = _unpack_concrete_array(b)
    if ua is None or ub is None:
        return False
    d1, ov1 = ua
    d2, ov2 = ub

    def _lookup(default: Expr, ov: list[tuple[Expr, Expr]], key: Expr) -> Expr:
        for k, v in ov:
            if _concrete_values_equal(k, key, universes):
                return v
        return default

    unique_keys: list[Expr] = []
    for k, _ in ov1:
        if not any(_concrete_values_equal(k, prev, universes) for prev in unique_keys):
            unique_keys.append(k)
    for k, _ in ov2:
        if not any(_concrete_values_equal(k, prev, universes) for prev in unique_keys):
            unique_keys.append(k)

    idx_sort = a.sort.index_sort
    if idx_sort.is_bool:
        return all(
            _concrete_values_equal(
                _lookup(d1, ov1, probe), _lookup(d2, ov2, probe), universes
            )
            for probe in (a.ctx.false_expr, a.ctx.true_expr)
        )
    if (
        idx_sort.is_bv
        and idx_sort.size <= 8
        and len(unique_keys) >= (1 << idx_sort.size)
    ):
        width = idx_sort.size
        return all(
            _concrete_values_equal(
                _lookup(d1, ov1, a.ctx.mk_bv_val(i, width)),
                _lookup(d2, ov2, a.ctx.mk_bv_val(i, width)),
                universes,
            )
            for i in range(1 << width)
        )

    if not _concrete_values_equal(d1, d2, universes):
        return False
    return all(
        _concrete_values_equal(_lookup(d1, ov1, k), _lookup(d2, ov2, k), universes)
        for k in unique_keys
    )


class FuncInterp:
    """Finite-table interpretation with a default fallback for a function symbol."""

    def __init__(
        self,
        decl: FuncDecl,
        entries: (
            Mapping[tuple[Expr, ...], Expr] | Sequence[tuple[tuple[Expr, ...], Expr]]
        ),
        else_value: Expr,
    ) -> None:
        if not decl.is_uninterpreted or decl.arity < 1:
            msg = f"FuncInterp requires an arity >= 1 uninterpreted decl, got '{decl}'"
            raise ValueError(msg)
        if not isinstance(else_value, Expr) or not _is_concrete_value(else_value):
            msg = f"FuncInterp else_value must be concrete, got {else_value!r}"
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
        self._table: dict[tuple[Expr, ...], Expr] = {}

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
                if not isinstance(arg, Expr) or not _is_concrete_value(arg):
                    msg = f"FuncInterp key argument {i} must be concrete"
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
            if not isinstance(result, Expr) or not _is_concrete_value(result):
                msg = f"FuncInterp entry result must be concrete, got {result!r}"
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
    def else_value(self) -> Expr:
        """Default constant returned for argument tuples absent from the table."""
        return self._else_value

    def entries(self) -> tuple[tuple[tuple[Expr, ...], Expr], ...]:
        """Return explicit ``(args, value)`` table entries in insertion order."""
        return tuple(self._table.items())

    def __len__(self) -> int:
        return len(self._table)

    def __call__(self, *args: Expr) -> Expr:
        if len(args) != self._decl.arity:
            msg = (
                f"FuncInterp for '{self._decl}' expects {self._decl.arity} args, "
                f"got {len(args)}"
            )
            raise ValueError(msg)
        direct = self._table.get(args)
        if direct is not None:
            return direct
        if any(not isinstance(arg, Const) for arg in args):
            for key, result in self._table.items():
                if all(
                    _concrete_values_equal(a, k) for a, k in zip(args, key, strict=True)
                ):
                    return result
        return self._else_value

    def __repr__(self) -> str:
        items = ", ".join(
            f"({', '.join(str(a) for a in key)}) -> {val}"
            for key, val in self._table.items()
        )
        if items:
            return f"FuncInterp({self._decl.name}: {items}, else -> {self._else_value})"
        return f"FuncInterp({self._decl.name}: else -> {self._else_value})"
