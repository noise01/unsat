"""Model representation, formula evaluation, and model reconstruction.

Will promote to a ``model/`` subpackage as implementation grows.

Depends on: ``syntax``.
"""

import itertools
from collections.abc import Iterable, Mapping, Sequence
from fractions import Fraction
from typing import Protocol

from unsat.syntax import (
    App,
    BoundVar,
    Const,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
    SortKind,
    instantiate_quantifier,
    iter_subexprs,
)

type Value = bool | int | Fraction | Expr


def _is_concrete_value(expr: Expr) -> bool:
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, Const):
            continue
        if isinstance(node, App) and node.decl.kind in (
            DeclKind.CONST_ARRAY,
            DeclKind.STORE,
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

        if kind is SortKind.BITVEC:
            width = decl.range_sort.size
            if isinstance(val, int) and not isinstance(val, bool):
                if not (0 <= val < (1 << width)):
                    msg = f"BitVec value {val} out of range for {width}-bit '{decl}'"
                    raise ValueError(msg)
                return val
            if isinstance(val, Const) and val.sort is decl.range_sort:
                if val.ctx is not self._ctx:
                    msg = f"Value '{val}' belongs to a different Context"
                    raise ValueError(msg)
                assert isinstance(val.value, int)
                assert not isinstance(val.value, bool)
                return val.value
            msg = f"Expected BitVec({width}) value for '{decl}', got {val!r}"
            raise TypeError(msg)

        if kind is SortKind.ARRAY:
            if not isinstance(val, Expr) or not _is_concrete_value(val):
                msg = f"Expected concrete Array value for '{decl}', got {val!r}"
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

    def _default_value_expr(self, sort: Sort) -> Expr:
        chain: list[Sort] = []
        cur = sort
        while cur.kind is SortKind.ARRAY:
            chain.append(cur.index_sort)
            cur = cur.element_sort

        if cur.kind is SortKind.BOOL:
            val: Expr = self._ctx.mk_false()
        elif cur.kind is SortKind.INT:
            val = self._ctx.mk_int_val(0)
        elif cur.kind is SortKind.REAL:
            val = self._ctx.mk_real_val(0)
        elif cur.kind is SortKind.BITVEC:
            val = self._ctx.mk_bv_val(0, cur.size)
        else:
            universe = self._universes.get(cur)
            val = universe[0] if universe else self._ctx.mk_domain_val(cur, 0)

        for idx_sort in reversed(chain):
            val = self._ctx.mk_const_array(idx_sort, val)
        return val

    def _value_to_expr(self, val: Value, sort: Sort) -> Expr:
        if isinstance(val, Expr):
            return val
        if sort.kind is SortKind.BOOL:
            assert isinstance(val, bool)
            return self._ctx.mk_bool_val(val)
        if sort.kind is SortKind.INT:
            assert isinstance(val, int)
            assert not isinstance(val, bool)
            return self._ctx.mk_int_val(val)
        if sort.kind is SortKind.BITVEC:
            assert isinstance(val, int)
            assert not isinstance(val, bool)
            return self._ctx.mk_bv_val(val, sort.size)
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

    def _finite_domain_elements(
        self, sort: Sort, *, model_completion: bool
    ) -> tuple[Expr, ...] | None:
        kind = sort.kind
        if kind is SortKind.BOOL:
            return (self._ctx.false_expr, self._ctx.true_expr)
        if kind is SortKind.UNINTERPRETED:
            univ = self._universes.get(sort)
            if univ:
                return univ
            if model_completion:
                return (self._ctx.mk_domain_val(sort, 0),)
            return None
        if kind is SortKind.BITVEC and sort.size <= 6:
            return tuple(
                self._ctx.mk_bv_val(i, sort.size) for i in range(1 << sort.size)
            )
        return None

    def _eval_quantifier(
        self,
        node: Quantifier,
        memo: dict[Expr, Expr],
        *,
        model_completion: bool,
    ) -> Expr:
        domains: list[tuple[Expr, ...]] = []
        total = 1
        enumerable = True
        for sort in node.var_sorts:
            dom = self._finite_domain_elements(sort, model_completion=model_completion)
            if dom is None or total * len(dom) > 1024:
                enumerable = False
                break
            domains.append(dom)
            total *= len(dom)

        if enumerable:
            all_reduced = True
            for combo in itertools.product(*domains):
                inst = instantiate_quantifier(node, combo)
                ev = self.eval(inst, model_completion=model_completion)
                if node.is_forall:
                    if ev is self._ctx.false_expr:
                        return self._ctx.false_expr
                    if ev is not self._ctx.true_expr:
                        all_reduced = False
                else:
                    if ev is self._ctx.true_expr:
                        return self._ctx.true_expr
                    if ev is not self._ctx.false_expr:
                        all_reduced = False
            if all_reduced:
                return self._ctx.mk_bool_val(node.is_forall)

        new_body = memo[node.body]
        new_pats = tuple(tuple(memo[term] for term in pat) for pat in node.patterns)
        return self._ctx.mk_quantifier(
            node.is_forall,
            node.var_names,
            node.var_sorts,
            new_body,
            patterns=new_pats,
        )

    def eval(self, expr: Expr, *, model_completion: bool = False) -> Expr:
        """Evaluate ``expr`` under this model, returning a simplified ``Expr``."""
        if expr.ctx is not self._ctx:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)

        memo: dict[Expr, Expr] = {}
        for node in iter_subexprs(expr):
            if isinstance(node, (Const, BoundVar)):
                memo[node] = node
                continue
            if isinstance(node, Quantifier):
                memo[node] = self._eval_quantifier(
                    node, memo, model_completion=model_completion
                )
                continue
            if not isinstance(node, App):
                memo[node] = node
                continue

            if node.is_const_symbol:
                if node.decl in self._values:
                    memo[node] = self._value_to_expr(self._values[node.decl], node.sort)
                elif model_completion:
                    memo[node] = self._default_value_expr(node.sort)
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
                    a0, a1 = eval_args
                    if _is_concrete_value(a0) and _is_concrete_value(a1):
                        memo[node] = self._ctx.mk_bool_val(
                            _concrete_values_equal(a0, a1, self._universes)
                        )
                    else:
                        memo[node] = self._ctx.mk_eq(a0, a1)
                case DeclKind.DISTINCT:
                    if eval_args and eval_args[0].is_bool and len(eval_args) >= 3:
                        memo[node] = self._ctx.mk_false()
                    elif all(_is_concrete_value(arg) for arg in eval_args):
                        all_diff = True
                        for i in range(len(eval_args)):
                            for j in range(i + 1, len(eval_args)):
                                if _concrete_values_equal(
                                    eval_args[i], eval_args[j], self._universes
                                ):
                                    all_diff = False
                                    break
                            if not all_diff:
                                break
                        memo[node] = self._ctx.mk_bool_val(all_diff)
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
                case DeclKind.SELECT:
                    arr_e, idx_e = eval_args
                    if _is_concrete_value(arr_e) and _is_concrete_value(idx_e):
                        unpacked = _unpack_concrete_array(arr_e)
                        if unpacked is not None:
                            default_v, overrides = unpacked
                            res_v = default_v
                            for k_v, val_v in overrides:
                                if _concrete_values_equal(k_v, idx_e, self._universes):
                                    res_v = val_v
                                    break
                            memo[node] = res_v
                        else:
                            memo[node] = self._ctx.mk_select(arr_e, idx_e)
                    else:
                        memo[node] = self._ctx.mk_select(arr_e, idx_e)
                case (
                    DeclKind.BV_NOT
                    | DeclKind.BV_AND
                    | DeclKind.BV_OR
                    | DeclKind.BV_XOR
                    | DeclKind.BV_NEG
                    | DeclKind.BV_ADD
                    | DeclKind.BV_SUB
                    | DeclKind.BV_MUL
                    | DeclKind.BV_UDIV
                    | DeclKind.BV_UREM
                    | DeclKind.BV_SDIV
                    | DeclKind.BV_SREM
                    | DeclKind.BV_SMOD
                    | DeclKind.BV_SHL
                    | DeclKind.BV_LSHR
                    | DeclKind.BV_ASHR
                    | DeclKind.BV_ULT
                    | DeclKind.BV_ULE
                    | DeclKind.BV_UGT
                    | DeclKind.BV_UGE
                    | DeclKind.BV_SLT
                    | DeclKind.BV_SLE
                    | DeclKind.BV_SGT
                    | DeclKind.BV_SGE
                    | DeclKind.BV_CONCAT
                    | DeclKind.BV_EXTRACT
                    | DeclKind.BV_ZERO_EXT
                    | DeclKind.BV_SIGN_EXT
                    | DeclKind.BV_ROTATE_LEFT
                    | DeclKind.BV_ROTATE_RIGHT
                    | DeclKind.BV_REPEAT
                    | DeclKind.STORE
                    | DeclKind.CONST_ARRAY
                ):
                    memo[node] = self._ctx.mk_app(node.decl, *eval_args)
                case DeclKind.UNINTERPRETED:
                    if all(_is_concrete_value(arg) for arg in eval_args):
                        if node.decl in self._functions:
                            memo[node] = self._functions[node.decl](*eval_args)
                        elif model_completion:
                            memo[node] = self._default_value_expr(node.sort)
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

    def eval_bv(self, expr: Expr, *, model_completion: bool = True) -> int:
        """Evaluate ``BitVec`` expression ``expr`` to an unsigned Python ``int``."""
        if not expr.is_bv:
            msg = f"Expected BitVec expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        evaluated = self.eval(expr, model_completion=model_completion)
        if (
            not isinstance(evaluated, Const)
            or not isinstance(evaluated.value, int)
            or isinstance(evaluated.value, bool)
        ):
            msg = (
                f"Expression '{expr}' did not reduce to a BitVec constant: {evaluated}"
            )
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
            if rhs.sort is not decl.range_sort:
                msg = (
                    f"Substitution RHS sort '{rhs.sort}' does not match "
                    f"declaration sort '{decl.range_sort}'"
                )
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
        functions = {
            decl: model.func_interp(decl)
            for decl in model.func_decls()
            if decl not in self._hidden
        }
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


__all__ = [
    "CompositeModelConverter",
    "FuncInterp",
    "IdentityModelConverter",
    "Model",
    "ModelConverter",
    "ProjectionModelConverter",
    "SubstitutionModelConverter",
    "Value",
]
