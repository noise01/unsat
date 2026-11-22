"""Stateless hash-consed AST nodes and explicit AST context."""

import weakref
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import NoReturn

from unsat.syntax.kinds import DeclKind, SortKind


def _format_pos_fraction(frac: Fraction) -> str:
    if frac.denominator == 1:
        return f"{frac.numerator}.0"
    return f"(/ {frac.numerator}.0 {frac.denominator}.0)"


def _format_real_fraction(frac: Fraction) -> str:
    if frac < 0:
        return f"(- {_format_pos_fraction(-frac)})"
    return _format_pos_fraction(frac)


def _bv_mask(width: int) -> int:
    return (1 << width) - 1


def _bv_to_signed(val: int, width: int) -> int:
    sign_bit = 1 << (width - 1)
    return val - (1 << width) if (val & sign_bit) else val


def _bv_udiv(a: int, b: int, mask: int) -> int:
    return mask if b == 0 else a // b


def _bv_urem(a: int, b: int) -> int:
    return a if b == 0 else a % b


def _bv_sdiv(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    neg_a = (-a) & mask
    neg_b = (-b) & mask
    if not ma and not mb:
        return _bv_udiv(a, b, mask)
    if ma and not mb:
        return (-_bv_udiv(neg_a, b, mask)) & mask
    if not ma and mb:
        return (-_bv_udiv(a, neg_b, mask)) & mask
    return _bv_udiv(neg_a, neg_b, mask)


def _bv_srem(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    neg_a = (-a) & mask
    neg_b = (-b) & mask
    if not ma and not mb:
        return _bv_urem(a, b)
    if ma and not mb:
        return (-_bv_urem(neg_a, b)) & mask
    if not ma and mb:
        return _bv_urem(a, neg_b)
    return (-_bv_urem(neg_a, neg_b)) & mask


def _bv_smod(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    abs_a = (-a) & mask if ma else a
    abs_b = (-b) & mask if mb else b
    u = _bv_urem(abs_a, abs_b)
    if u == 0:
        return 0
    if not ma and not mb:
        return u
    if ma and not mb:
        return ((-u) + b) & mask
    if not ma and mb:
        return (u + b) & mask
    return (-u) & mask


@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)
class Sort:
    """Sorted type node interned within a :class:`Context`."""

    id: int
    ctx: Context
    name: str
    kind: SortKind
    bv_width: int | None = None
    array_index: Sort | None = None
    array_element: Sort | None = None

    @property
    def is_bool(self) -> bool:
        """Whether this sort is ``Bool``."""
        return self.kind is SortKind.BOOL

    @property
    def is_int(self) -> bool:
        """Whether this sort is ``Int``."""
        return self.kind is SortKind.INT

    @property
    def is_real(self) -> bool:
        """Whether this sort is ``Real``."""
        return self.kind is SortKind.REAL

    @property
    def is_arith(self) -> bool:
        """Whether this sort is ``Int`` or ``Real``."""
        return self.kind in (SortKind.INT, SortKind.REAL)

    @property
    def is_bv(self) -> bool:
        """Whether this sort is a fixed-width ``BitVec``."""
        return self.kind is SortKind.BITVEC

    @property
    def is_array(self) -> bool:
        """Whether this sort is an ``Array`` sort."""
        return self.kind is SortKind.ARRAY

    @property
    def size(self) -> int:
        """Bit width of a ``BitVec`` sort."""
        if self.kind is not SortKind.BITVEC or self.bv_width is None:
            msg = f"Expected BitVec sort, got '{self}'"
            raise TypeError(msg)
        return self.bv_width

    @property
    def index_sort(self) -> Sort:
        """Domain sort of an ``Array`` sort."""
        if self.kind is not SortKind.ARRAY or self.array_index is None:
            msg = f"Expected Array sort, got '{self}'"
            raise TypeError(msg)
        return self.array_index

    @property
    def element_sort(self) -> Sort:
        """Codomain sort of an ``Array`` sort."""
        if self.kind is not SortKind.ARRAY or self.array_element is None:
            msg = f"Expected Array sort, got '{self}'"
            raise TypeError(msg)
        return self.array_element

    def __hash__(self) -> int:
        return self.id

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)
class FuncDecl:
    """Function or constant declaration interned within a :class:`Context`."""

    id: int
    ctx: Context
    name: str
    domain: tuple[Sort, ...]
    range_sort: Sort
    kind: DeclKind
    params: tuple[int, ...] = ()

    @property
    def arity(self) -> int:
        """Number of arguments expected by this declaration."""
        return len(self.domain)

    @property
    def is_uninterpreted(self) -> bool:
        """Whether this declaration is user-defined rather than a built-in op."""
        return self.kind is DeclKind.UNINTERPRETED

    def __call__(self, *args: Expr) -> Expr:
        return self.ctx.mk_app(self, *args)

    def __hash__(self) -> int:
        return self.id

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)
class Expr:
    """Base class for immutable, hash-consed AST expressions.

    ``Expr.__eq__`` preserves structural identity (``bool``) and hashability so
    expressions work directly as ``dict`` keys and ``set`` elements.
    """

    id: int
    ctx: Context
    sort: Sort

    @property
    def is_bool(self) -> bool:
        """Whether this expression has the built-in ``Bool`` sort."""
        return self.sort.kind is SortKind.BOOL

    @property
    def is_int(self) -> bool:
        """Whether this expression has the built-in ``Int`` sort."""
        return self.sort.kind is SortKind.INT

    @property
    def is_real(self) -> bool:
        """Whether this expression has the built-in ``Real`` sort."""
        return self.sort.kind is SortKind.REAL

    @property
    def is_arith(self) -> bool:
        """Whether this expression has ``Int`` or ``Real`` sort."""
        return self.sort.kind in (SortKind.INT, SortKind.REAL)

    @property
    def is_bv(self) -> bool:
        """Whether this expression has ``BitVec`` sort."""
        return self.sort.kind is SortKind.BITVEC

    @property
    def is_array(self) -> bool:
        """Whether this expression has ``Array`` sort."""
        return self.sort.kind is SortKind.ARRAY

    @property
    def bv_size(self) -> int:
        """Bit width of this ``BitVec`` expression."""
        return self.sort.size

    @property
    def children(self) -> tuple[Expr, ...]:
        """Direct child expressions of this node."""
        return ()

    def __hash__(self) -> int:
        return self.id

    def __bool__(self) -> NoReturn:
        msg = (
            "Symbolic Expr cannot be coerced to bool; "
            "use explicit operators or Solver.check()"
        )
        raise TypeError(msg)

    def _coerce_arith(self, other: object) -> Expr | None:
        if not self.is_arith:
            return None
        if isinstance(other, Expr):
            return other
        if isinstance(other, bool):
            return None
        if isinstance(other, int):
            if self.is_int:
                return self.ctx.mk_int_val(other)
            return self.ctx.mk_real_val(other)
        if isinstance(other, Fraction):
            if self.is_real:
                return self.ctx.mk_real_val(other)
            return None
        return None

    def _coerce_bv(self, other: object) -> Expr | None:
        if not self.is_bv:
            return None
        if isinstance(other, Expr):
            return other
        if isinstance(other, bool):
            return None
        if isinstance(other, int):
            return self.ctx.mk_bv_val(other, self.sort.size)
        return None

    def __and__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_and(self, rhs)
        if not isinstance(other, Expr):
            return NotImplemented
        return self.ctx.mk_and(self, other)

    def __rand__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_and(lhs, self)
        return NotImplemented

    def __or__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_or(self, rhs)
        if not isinstance(other, Expr):
            return NotImplemented
        return self.ctx.mk_or(self, other)

    def __ror__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_or(lhs, self)
        return NotImplemented

    def __invert__(self) -> Expr:
        if self.is_bv:
            return self.ctx.mk_bv_not(self)
        return self.ctx.mk_not(self)

    def __xor__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_xor(self, rhs)
        if not isinstance(other, Expr):
            return NotImplemented
        return self.ctx.mk_xor(self, other)

    def __rxor__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_xor(lhs, self)
        return NotImplemented

    def __pos__(self) -> Expr:
        if self.is_bv:
            self.ctx._check_bv(self)
            return self
        self.ctx._check_arith(self)
        return self

    def __neg__(self) -> Expr:
        if self.is_bv:
            return self.ctx.mk_bv_neg(self)
        return self.ctx.mk_neg(self)

    def __add__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_add(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_add(self, rhs)

    def __radd__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_add(lhs, self)
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_add(lhs, self)

    def __sub__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sub(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_sub(self, rhs)

    def __rsub__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sub(lhs, self)
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_sub(lhs, self)

    def __mul__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_mul(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_mul(self, rhs)

    def __rmul__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_mul(lhs, self)
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_mul(lhs, self)

    def __truediv__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sdiv(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_div(self, rhs)

    def __rtruediv__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sdiv(lhs, self)
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_div(lhs, self)

    def __mod__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_smod(self, rhs)
        return NotImplemented

    def __rmod__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_smod(lhs, self)
        return NotImplemented

    def __lshift__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_shl(self, rhs)
        return NotImplemented

    def __rlshift__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_shl(lhs, self)
        return NotImplemented

    def __rshift__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_ashr(self, rhs)
        return NotImplemented

    def __rrshift__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_ashr(lhs, self)
        return NotImplemented

    def __lt__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_slt(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_lt(self, rhs)

    def __le__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sle(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_le(self, rhs)

    def __gt__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sgt(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_gt(self, rhs)

    def __ge__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_sge(self, rhs)
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_ge(self, rhs)


@dataclass(frozen=True, slots=True, eq=False)
class Const(Expr):
    """Constant literal expression (Bool, Int, Real, BV, or domain element)."""

    value: bool | int | Fraction

    def __str__(self) -> str:
        kind = self.sort.kind
        if kind is SortKind.BOOL:
            return "true" if self.value else "false"
        if kind is SortKind.INT:
            assert isinstance(self.value, int)
            if self.value >= 0:
                return str(self.value)
            return f"(- {-self.value})"
        if kind is SortKind.REAL:
            assert isinstance(self.value, Fraction)
            return _format_real_fraction(self.value)
        if kind is SortKind.BITVEC:
            assert isinstance(self.value, int)
            assert not isinstance(self.value, bool)
            w = self.sort.size
            if w % 4 == 0:
                return f"#x{self.value:0{w // 4}x}"
            return f"#b{self.value:0{w}b}"
        return f"{self.sort.name}!val!{self.value}"


@dataclass(frozen=True, slots=True, eq=False)
class App(Expr):
    """Function, operator, or 0-arity symbolic constant application."""

    decl: FuncDecl
    args: tuple[Expr, ...]

    @property
    def children(self) -> tuple[Expr, ...]:
        """Direct argument expressions of this application."""
        return self.args

    @property
    def is_const_symbol(self) -> bool:
        """Whether this node is a 0-arity uninterpreted symbol."""
        return self.decl.is_uninterpreted and not self.args

    @property
    def name(self) -> str:
        """Declaration name for this application."""
        return self.decl.name

    def __str__(self) -> str:
        if not self.args:
            return self.decl.name
        args_str = " ".join(str(arg) for arg in self.args)
        return f"({self.decl.name} {args_str})"


@dataclass(frozen=True, slots=True, eq=False)
class BoundVar(Expr):
    """De Bruijn indexed bound variable inside a :class:`Quantifier`."""

    index: int

    def __str__(self) -> str:
        return f"(:var {self.index})"


@dataclass(frozen=True, slots=True, eq=False)
class Quantifier(Expr):
    """Universally (``forall``) or existentially (``exists``) quantified formula."""

    is_forall: bool
    var_names: tuple[str, ...]
    var_sorts: tuple[Sort, ...]
    body: Expr
    patterns: tuple[tuple[Expr, ...], ...] = ()

    @property
    def is_exists(self) -> bool:
        """Whether this quantifier is an existential (``exists``) binder."""
        return not self.is_forall

    @property
    def num_vars(self) -> int:
        """Number of variables bound by this quantifier."""
        return len(self.var_sorts)

    @property
    def children(self) -> tuple[Expr, ...]:
        """Body followed by all pattern terms referenced by this quantifier."""
        return (self.body, *(term for pat in self.patterns for term in pat))

    def __str__(self) -> str:
        kw = "ForAll" if self.is_forall else "Exists"
        binders = ", ".join(
            f"{name}: {sort}"
            for name, sort in zip(self.var_names, self.var_sorts, strict=True)
        )
        if not self.patterns:
            return f"{kw}([{binders}], {self.body})"
        pats = ", ".join(
            f"({', '.join(str(t) for t in pat)})" if len(pat) > 1 else str(pat[0])
            for pat in self.patterns
        )
        return f"{kw}([{binders}], {self.body}, patterns=[{pats}])"


def _abstract_vars_impl(
    ctx: Context,
    expr: Expr,
    vars_to_bind: Sequence[App],
) -> Expr:
    if not vars_to_bind:
        return expr
    k = len(vars_to_bind)
    slot_map: dict[Expr, int] = {v: k - 1 - i for i, v in enumerate(vars_to_bind)}
    memo: dict[tuple[Expr, int], Expr] = {}
    stack: list[tuple[Expr, int, bool]] = [(expr, 0, False)]

    while stack:
        node, depth, expanded = stack.pop()
        key = (node, depth)
        if key in memo:
            continue
        if isinstance(node, Const):
            memo[key] = node
            continue
        if isinstance(node, BoundVar):
            memo[key] = (
                node
                if node.index < depth
                else ctx.mk_bound_var(node.index + k, node.sort)
            )
            continue
        if isinstance(node, App):
            slot = slot_map.get(node)
            if slot is not None:
                memo[key] = ctx.mk_bound_var(depth + slot, node.sort)
                continue
            if not node.args:
                memo[key] = node
                continue
            if not expanded:
                stack.append((node, depth, True))
                for arg in reversed(node.args):
                    if (arg, depth) not in memo:
                        stack.append((arg, depth, False))
                continue
            new_args = [memo[(arg, depth)] for arg in node.args]
            if all(n is o for n, o in zip(new_args, node.args, strict=True)):
                memo[key] = node
            else:
                memo[key] = ctx.mk_app(node.decl, *new_args)
            continue
        if isinstance(node, Quantifier):
            cdepth = depth + node.num_vars
            if not expanded:
                stack.append((node, depth, True))
                for pat in reversed(node.patterns):
                    for term in reversed(pat):
                        if (term, cdepth) not in memo:
                            stack.append((term, cdepth, False))
                if (node.body, cdepth) not in memo:
                    stack.append((node.body, cdepth, False))
                continue
            new_body = memo[(node.body, cdepth)]
            new_pats = tuple(
                tuple(memo[(term, cdepth)] for term in pat) for pat in node.patterns
            )
            if new_body is node.body and new_pats == node.patterns:
                memo[key] = node
            else:
                memo[key] = ctx.mk_quantifier(
                    node.is_forall,
                    node.var_names,
                    node.var_sorts,
                    new_body,
                    patterns=new_pats,
                )
            continue
        memo[key] = node

    return memo[(expr, 0)]


def _is_not_of(candidate: Expr, target: Expr) -> bool:
    return (
        isinstance(candidate, App)
        and candidate.decl.kind is DeclKind.NOT
        and candidate.args[0] is target
    )


class Context:
    """Explicit AST arena managing hash-consed sorts, declarations, and terms."""

    def __init__(self) -> None:
        self._next_id = 0
        self._sorts: weakref.WeakValueDictionary[tuple[object, ...], Sort] = (
            weakref.WeakValueDictionary()
        )
        self._decls: weakref.WeakValueDictionary[
            tuple[DeclKind, str, tuple[Sort, ...], Sort, tuple[int, ...]],
            FuncDecl,
        ] = weakref.WeakValueDictionary()
        self._exprs: weakref.WeakValueDictionary[tuple[object, ...], Expr] = (
            weakref.WeakValueDictionary()
        )
        self._bound_vars: weakref.WeakValueDictionary[tuple[int, int], BoundVar] = (
            weakref.WeakValueDictionary()
        )
        self._quantifiers: weakref.WeakValueDictionary[
            tuple[
                bool,
                tuple[str, ...],
                tuple[int, ...],
                int,
                tuple[tuple[int, ...], ...],
            ],
            Quantifier,
        ] = weakref.WeakValueDictionary()

        # Keep strong references to built-in sorts & Boolean singletons.
        self.bool_sort = self._intern_sort(SortKind.BOOL, "Bool")
        self.int_sort = self._intern_sort(SortKind.INT, "Int")
        self.real_sort = self._intern_sort(SortKind.REAL, "Real")
        self.true_expr = self._intern_const(True, self.bool_sort)
        self.false_expr = self._intern_const(False, self.bool_sort)

    def _alloc_id(self) -> int:
        node_id = self._next_id
        self._next_id += 1
        return node_id

    def _intern_sort(
        self,
        kind: SortKind,
        name: str,
        *,
        bv_width: int | None = None,
        array_index: Sort | None = None,
        array_element: Sort | None = None,
    ) -> Sort:
        if kind is SortKind.BITVEC:
            key: tuple[object, ...] = (kind, bv_width)
        elif kind is SortKind.ARRAY:
            assert array_index is not None
            assert array_element is not None
            key = (kind, array_index.id, array_element.id)
        else:
            key = (kind, name)
        existing = self._sorts.get(key)
        if existing is not None:
            return existing
        sort = Sort(
            self._alloc_id(),
            self,
            name,
            kind,
            bv_width=bv_width,
            array_index=array_index,
            array_element=array_element,
        )
        self._sorts[key] = sort
        return sort

    def _intern_decl(
        self,
        kind: DeclKind,
        name: str,
        domain: tuple[Sort, ...],
        range_sort: Sort,
        params: tuple[int, ...] = (),
    ) -> FuncDecl:
        key = (kind, name, domain, range_sort, params)
        existing = self._decls.get(key)
        if existing is not None:
            return existing
        decl = FuncDecl(
            self._alloc_id(), self, name, domain, range_sort, kind, params=params
        )
        self._decls[key] = decl
        return decl

    def _intern_const(self, value: bool | int | Fraction, sort: Sort) -> Const:
        key: tuple[object, ...] = (Const, sort.id, type(value), value)
        existing = self._exprs.get(key)
        if existing is not None:
            assert isinstance(existing, Const)
            return existing
        expr = Const(self._alloc_id(), self, sort, value)
        self._exprs[key] = expr
        return expr

    def _intern_app(self, decl: FuncDecl, args: tuple[Expr, ...]) -> App:
        key: tuple[object, ...] = (App, decl.id, *(arg.id for arg in args))
        existing = self._exprs.get(key)
        if existing is not None:
            assert isinstance(existing, App)
            return existing
        expr = App(self._alloc_id(), self, decl.range_sort, decl, args)
        self._exprs[key] = expr
        return expr

    def _check_sort(self, sort: Sort) -> None:
        if sort.ctx is not self:
            msg = f"Sort '{sort}' belongs to a different Context"
            raise ValueError(msg)

    def _check_expr(self, expr: Expr) -> None:
        if expr.ctx is not self:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)

    def _check_bool(self, expr: Expr) -> None:
        self._check_expr(expr)
        if not expr.is_bool:
            msg = f"Expected Bool expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _check_int(self, expr: Expr) -> None:
        self._check_expr(expr)
        if not expr.is_int:
            msg = f"Expected Int expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _check_real(self, expr: Expr) -> None:
        self._check_expr(expr)
        if not expr.is_real:
            msg = f"Expected Real expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _check_arith(self, expr: Expr) -> Sort:
        self._check_expr(expr)
        if not expr.is_arith:
            msg = f"Expected Int or Real expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        return expr.sort

    def _check_bv(self, expr: Expr) -> int:
        self._check_expr(expr)
        if not expr.is_bv:
            msg = f"Expected BitVec expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        return expr.sort.size

    def _check_bv_pair(self, lhs: Expr, rhs: Expr, op_name: str) -> int:
        width = self._check_bv(lhs)
        self._check_expr(rhs)
        if lhs.sort is not rhs.sort:
            msg = f"Sort mismatch in {op_name}: '{lhs.sort}' vs '{rhs.sort}'"
            raise TypeError(msg)
        return width

    def _check_array(self, expr: Expr) -> Sort:
        self._check_expr(expr)
        if not expr.is_array:
            msg = f"Expected Array expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        return expr.sort

    def mk_bool_sort(self) -> Sort:
        """Return this context's canonical ``Bool`` sort."""
        return self.bool_sort

    def mk_int_sort(self) -> Sort:
        """Return this context's canonical ``Int`` sort."""
        return self.int_sort

    def mk_real_sort(self) -> Sort:
        """Return this context's canonical ``Real`` sort."""
        return self.real_sort

    def mk_bv_sort(self, width: int) -> Sort:
        """Create or retrieve the fixed-width ``(_ BitVec width)`` sort."""
        if isinstance(width, bool) or not isinstance(width, int) or width < 1:
            msg = f"BitVec width must be a positive int, got {width!r}"
            raise ValueError(msg)
        return self._intern_sort(SortKind.BITVEC, f"(_ BitVec {width})", bv_width=width)

    def mk_array_sort(self, index_sort: Sort, element_sort: Sort) -> Sort:
        """Create or retrieve ``(Array index_sort element_sort)``."""
        self._check_sort(index_sort)
        self._check_sort(element_sort)
        return self._intern_sort(
            SortKind.ARRAY,
            f"(Array {index_sort.name} {element_sort.name})",
            array_index=index_sort,
            array_element=element_sort,
        )

    def mk_uninterpreted_sort(self, name: str) -> Sort:
        """Create or retrieve a hash-consed uninterpreted sort."""
        if not name:
            msg = "Sort name cannot be empty"
            raise ValueError(msg)
        return self._intern_sort(SortKind.UNINTERPRETED, name)

    def mk_domain_val(self, sort: Sort, index: int) -> Const:
        """Create or retrieve a distinct domain-element constant for ``sort``."""
        self._check_sort(sort)
        if sort.kind is not SortKind.UNINTERPRETED:
            msg = f"Expected uninterpreted sort for domain value, got '{sort}'"
            raise TypeError(msg)
        if isinstance(index, bool) or index < 0:
            msg = f"Domain value index must be a non-negative int, got {index!r}"
            raise ValueError(msg)
        return self._intern_const(index, sort)

    def mk_int_val(self, value: int) -> Const:
        """Create or retrieve a hash-consed integer literal constant."""
        if isinstance(value, bool) or not isinstance(value, int):
            msg = f"Int constant value must be int, got {type(value).__name__}"
            raise TypeError(msg)
        return self._intern_const(value, self.int_sort)

    def mk_real_val(self, value: int | Fraction | str) -> Const:
        """Create or retrieve a hash-consed exact rational ``Real`` constant."""
        if isinstance(value, bool):
            msg = "Real constant value cannot be bool"
            raise TypeError(msg)
        if not isinstance(value, (int, Fraction, str)):
            msg = (
                "Real constant value must be int, Fraction, or str, got "
                f"{type(value).__name__}"
            )
            raise TypeError(msg)
        frac = Fraction(value)
        return self._intern_const(frac, self.real_sort)

    def mk_bv_val(self, value: int, width: int) -> Const:
        """Create or retrieve a hash-consed ``width``-bit ``BitVec`` constant."""
        if isinstance(value, bool) or not isinstance(value, int):
            msg = f"BitVec constant value must be int, got {type(value).__name__}"
            raise TypeError(msg)
        sort = self.mk_bv_sort(width)
        return self._intern_const(value & _bv_mask(width), sort)

    def mk_true(self) -> Const:
        """Return this context's canonical ``true`` literal."""
        return self.true_expr

    def mk_false(self) -> Const:
        """Return this context's canonical ``false`` literal."""
        return self.false_expr

    def mk_bool_val(self, value: bool) -> Const:
        """Return this context's canonical Boolean constant for ``value``."""
        return self.true_expr if value else self.false_expr

    def mk_decl(
        self,
        name: str,
        domain: Sequence[Sort],
        range_sort: Sort,
        *,
        kind: DeclKind = DeclKind.UNINTERPRETED,
    ) -> FuncDecl:
        """Create or retrieve a hash-consed function declaration."""
        if not name:
            msg = "Declaration name cannot be empty"
            raise ValueError(msg)
        for sort in domain:
            self._check_sort(sort)
        self._check_sort(range_sort)
        return self._intern_decl(kind, name, tuple(domain), range_sort)

    def mk_const(self, name: str, sort: Sort) -> App:
        """Create or retrieve a 0-arity symbolic constant of ``sort``."""
        self._check_sort(sort)
        decl = self.mk_decl(name, (), sort, kind=DeclKind.UNINTERPRETED)
        return self._intern_app(decl, ())

    def mk_bool(self, name: str) -> App:
        """Create or retrieve a 0-arity Boolean symbolic constant."""
        return self.mk_const(name, self.bool_sort)

    def mk_int(self, name: str) -> App:
        """Create or retrieve a 0-arity integer symbolic constant."""
        return self.mk_const(name, self.int_sort)

    def mk_real(self, name: str) -> App:
        """Create or retrieve a 0-arity real symbolic constant."""
        return self.mk_const(name, self.real_sort)

    def mk_bv(self, name: str, width: int) -> App:
        """Create or retrieve a 0-arity ``width``-bit bit-vector constant."""
        return self.mk_const(name, self.mk_bv_sort(width))

    def mk_array(self, name: str, index_sort: Sort, element_sort: Sort) -> App:
        """Create or retrieve a 0-arity array symbolic constant."""
        return self.mk_const(name, self.mk_array_sort(index_sort, element_sort))

    def mk_app(self, decl: FuncDecl, *args: Expr) -> Expr:
        """Apply ``decl`` to ``args``, validating sorts and normalizing built-ins."""
        if decl.ctx is not self:
            msg = f"FuncDecl '{decl}' belongs to a different Context"
            raise ValueError(msg)
        if len(args) != decl.arity:
            msg = f"Arity mismatch for '{decl}': expected {decl.arity}, got {len(args)}"
            raise ValueError(msg)
        for i, (arg, expected_sort) in enumerate(zip(args, decl.domain, strict=True)):
            self._check_expr(arg)
            if arg.sort is not expected_sort:
                msg = (
                    f"Sort mismatch in argument {i} of '{decl}': "
                    f"expected '{expected_sort}', got '{arg.sort}'"
                )
                raise TypeError(msg)

        match decl.kind:
            case DeclKind.NOT:
                return self.mk_not(args[0])
            case DeclKind.AND:
                return self.mk_and(*args)
            case DeclKind.OR:
                return self.mk_or(*args)
            case DeclKind.IMPLIES:
                return self.mk_implies(args[0], args[1])
            case DeclKind.XOR:
                return self.mk_xor(args[0], args[1])
            case DeclKind.EQ:
                return self.mk_eq(args[0], args[1])
            case DeclKind.DISTINCT:
                return self.mk_distinct(*args)
            case DeclKind.ITE:
                return self.mk_ite(args[0], args[1], args[2])
            case DeclKind.NEG:
                return self.mk_neg(args[0])
            case DeclKind.ADD:
                return self.mk_add(*args)
            case DeclKind.SUB:
                return self.mk_sub(args[0], args[1])
            case DeclKind.MUL:
                return self.mk_mul(*args)
            case DeclKind.DIV:
                return self.mk_div(args[0], args[1])
            case DeclKind.LT:
                return self.mk_lt(args[0], args[1])
            case DeclKind.LE:
                return self.mk_le(args[0], args[1])
            case DeclKind.GT:
                return self.mk_gt(args[0], args[1])
            case DeclKind.GE:
                return self.mk_ge(args[0], args[1])
            case DeclKind.TO_REAL:
                return self.mk_to_real(args[0])
            case DeclKind.BV_NOT:
                return self.mk_bv_not(args[0])
            case DeclKind.BV_AND:
                return self.mk_bv_and(*args)
            case DeclKind.BV_OR:
                return self.mk_bv_or(*args)
            case DeclKind.BV_XOR:
                return self.mk_bv_xor(*args)
            case DeclKind.BV_NEG:
                return self.mk_bv_neg(args[0])
            case DeclKind.BV_ADD:
                return self.mk_bv_add(*args)
            case DeclKind.BV_SUB:
                return self.mk_bv_sub(args[0], args[1])
            case DeclKind.BV_MUL:
                return self.mk_bv_mul(*args)
            case DeclKind.BV_UDIV:
                return self.mk_bv_udiv(args[0], args[1])
            case DeclKind.BV_UREM:
                return self.mk_bv_urem(args[0], args[1])
            case DeclKind.BV_SDIV:
                return self.mk_bv_sdiv(args[0], args[1])
            case DeclKind.BV_SREM:
                return self.mk_bv_srem(args[0], args[1])
            case DeclKind.BV_SMOD:
                return self.mk_bv_smod(args[0], args[1])
            case DeclKind.BV_SHL:
                return self.mk_bv_shl(args[0], args[1])
            case DeclKind.BV_LSHR:
                return self.mk_bv_lshr(args[0], args[1])
            case DeclKind.BV_ASHR:
                return self.mk_bv_ashr(args[0], args[1])
            case DeclKind.BV_ULT:
                return self.mk_bv_ult(args[0], args[1])
            case DeclKind.BV_ULE:
                return self.mk_bv_ule(args[0], args[1])
            case DeclKind.BV_UGT:
                return self.mk_bv_ugt(args[0], args[1])
            case DeclKind.BV_UGE:
                return self.mk_bv_uge(args[0], args[1])
            case DeclKind.BV_SLT:
                return self.mk_bv_slt(args[0], args[1])
            case DeclKind.BV_SLE:
                return self.mk_bv_sle(args[0], args[1])
            case DeclKind.BV_SGT:
                return self.mk_bv_sgt(args[0], args[1])
            case DeclKind.BV_SGE:
                return self.mk_bv_sge(args[0], args[1])
            case DeclKind.BV_CONCAT:
                return self.mk_concat(*args)
            case DeclKind.BV_EXTRACT:
                return self.mk_extract(decl.params[0], decl.params[1], args[0])
            case DeclKind.BV_ZERO_EXT:
                return self.mk_zero_ext(decl.params[0], args[0])
            case DeclKind.BV_SIGN_EXT:
                return self.mk_sign_ext(decl.params[0], args[0])
            case DeclKind.BV_ROTATE_LEFT:
                return self.mk_rotate_left(decl.params[0], args[0])
            case DeclKind.BV_ROTATE_RIGHT:
                return self.mk_rotate_right(decl.params[0], args[0])
            case DeclKind.BV_REPEAT:
                return self.mk_repeat(decl.params[0], args[0])
            case DeclKind.SELECT:
                return self.mk_select(args[0], args[1])
            case DeclKind.STORE:
                return self.mk_store(args[0], args[1], args[2])
            case DeclKind.CONST_ARRAY:
                return self.mk_const_array(decl.range_sort.index_sort, args[0])
            case DeclKind.UNINTERPRETED:
                return self._intern_app(decl, tuple(args))

    def mk_not(self, arg: Expr) -> Expr:
        """Build a normalized logical negation."""
        self._check_bool(arg)
        if isinstance(arg, Const):
            return self.mk_bool_val(not arg.value)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.NOT:
            return arg.args[0]
        decl = self._intern_decl(DeclKind.NOT, "not", (self.bool_sort,), self.bool_sort)
        return self._intern_app(decl, (arg,))

    def mk_and(self, *args: Expr) -> Expr:
        """Build a normalized logical conjunction."""
        flattened: list[Expr] = []
        for arg in args:
            self._check_bool(arg)
            if isinstance(arg, App) and arg.decl.kind is DeclKind.AND:
                flattened.extend(arg.args)
            else:
                flattened.append(arg)

        if any(arg is self.false_expr for arg in flattened):
            return self.false_expr

        unique = list(
            dict.fromkeys(arg for arg in flattened if arg is not self.true_expr)
        )
        unique_set = set(unique)
        for item in unique:
            if (
                isinstance(item, App)
                and item.decl.kind is DeclKind.NOT
                and item.args[0] in unique_set
            ):
                return self.false_expr

        if not unique:
            return self.true_expr
        if len(unique) == 1:
            return unique[0]

        decl = self._intern_decl(
            DeclKind.AND,
            "and",
            (self.bool_sort,) * len(unique),
            self.bool_sort,
        )
        return self._intern_app(decl, tuple(unique))

    def mk_or(self, *args: Expr) -> Expr:
        """Build a normalized logical disjunction."""
        flattened: list[Expr] = []
        for arg in args:
            self._check_bool(arg)
            if isinstance(arg, App) and arg.decl.kind is DeclKind.OR:
                flattened.extend(arg.args)
            else:
                flattened.append(arg)

        if any(arg is self.true_expr for arg in flattened):
            return self.true_expr

        unique = list(
            dict.fromkeys(arg for arg in flattened if arg is not self.false_expr)
        )
        unique_set = set(unique)
        for item in unique:
            if (
                isinstance(item, App)
                and item.decl.kind is DeclKind.NOT
                and item.args[0] in unique_set
            ):
                return self.true_expr

        if not unique:
            return self.false_expr
        if len(unique) == 1:
            return unique[0]

        decl = self._intern_decl(
            DeclKind.OR,
            "or",
            (self.bool_sort,) * len(unique),
            self.bool_sort,
        )
        return self._intern_app(decl, tuple(unique))

    def mk_implies(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized logical implication ``lhs => rhs``."""
        self._check_bool(lhs)
        self._check_bool(rhs)
        if lhs is self.false_expr or rhs is self.true_expr or lhs is rhs:
            return self.true_expr
        if lhs is self.true_expr:
            return rhs
        if rhs is self.false_expr:
            return self.mk_not(lhs)
        decl = self._intern_decl(
            DeclKind.IMPLIES,
            "=>",
            (self.bool_sort, self.bool_sort),
            self.bool_sort,
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_xor(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized exclusive-OR expression."""
        self._check_bool(lhs)
        self._check_bool(rhs)
        if lhs is rhs:
            return self.false_expr
        if _is_not_of(lhs, rhs) or _is_not_of(rhs, lhs):
            return self.true_expr
        if lhs is self.false_expr:
            return rhs
        if rhs is self.false_expr:
            return lhs
        if lhs is self.true_expr:
            return self.mk_not(rhs)
        if rhs is self.true_expr:
            return self.mk_not(lhs)
        decl = self._intern_decl(
            DeclKind.XOR,
            "xor",
            (self.bool_sort, self.bool_sort),
            self.bool_sort,
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_eq(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized equality expression ``lhs = rhs``."""
        self._check_expr(lhs)
        self._check_expr(rhs)
        if lhs.sort is not rhs.sort:
            msg = f"Sort mismatch in Eq: cannot compare '{lhs.sort}' and '{rhs.sort}'"
            raise TypeError(msg)
        if lhs is rhs:
            return self.true_expr
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            return self.mk_bool_val(lhs.value == rhs.value)
        if _is_not_of(lhs, rhs) or _is_not_of(rhs, lhs):
            return self.false_expr
        decl = self._intern_decl(
            DeclKind.EQ,
            "=",
            (lhs.sort, rhs.sort),
            self.bool_sort,
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_distinct(self, *args: Expr) -> Expr:
        """Build a normalized pairwise-distinct constraint."""
        if not args:
            return self.true_expr
        first_sort = args[0].sort
        for i, arg in enumerate(args):
            self._check_expr(arg)
            if arg.sort is not first_sort:
                msg = (
                    f"Sort mismatch in argument {i} of Distinct: "
                    f"expected '{first_sort}', got '{arg.sort}'"
                )
                raise TypeError(msg)
        if len(args) == 1:
            return self.true_expr
        if len(set(args)) < len(args):
            return self.false_expr
        if all(isinstance(arg, Const) for arg in args):
            return self.true_expr

        decl = self._intern_decl(
            DeclKind.DISTINCT,
            "distinct",
            (first_sort,) * len(args),
            self.bool_sort,
        )
        return self._intern_app(decl, tuple(args))

    def mk_ite(self, cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr:
        """Build a normalized if-then-else expression."""
        self._check_bool(cond)
        self._check_expr(then_branch)
        self._check_expr(else_branch)
        if then_branch.sort is not else_branch.sort:
            msg = (
                f"Sort mismatch in Ite branches: "
                f"'{then_branch.sort}' vs '{else_branch.sort}'"
            )
            raise TypeError(msg)
        if cond is self.true_expr:
            return then_branch
        if cond is self.false_expr:
            return else_branch
        if then_branch is else_branch:
            return then_branch
        branch_sort = then_branch.sort
        decl = self._intern_decl(
            DeclKind.ITE,
            "ite",
            (self.bool_sort, branch_sort, branch_sort),
            branch_sort,
        )
        return self._intern_app(decl, (cond, then_branch, else_branch))

    def _mk_arith_const(self, sort: Sort, val: int | Fraction) -> Const:
        if sort.is_int:
            assert isinstance(val, int)
            assert not isinstance(val, bool)
            return self.mk_int_val(val)
        return self.mk_real_val(val)

    def _check_arith_pair(self, lhs: Expr, rhs: Expr, op_name: str) -> Sort:
        sort = self._check_arith(lhs)
        self._check_expr(rhs)
        if lhs.sort is not rhs.sort:
            msg = f"Sort mismatch in {op_name}: '{lhs.sort}' vs '{rhs.sort}'"
            raise TypeError(msg)
        return sort

    def mk_to_real(self, arg: Expr) -> Expr:
        """Convert an ``Int`` expression to ``Real`` via ``to_real``."""
        self._check_int(arg)
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return self.mk_real_val(arg.value)
        decl = self._intern_decl(
            DeclKind.TO_REAL, "to_real", (self.int_sort,), self.real_sort
        )
        return self._intern_app(decl, (arg,))

    def mk_neg(self, arg: Expr) -> Expr:
        """Build a normalized arithmetic negation."""
        sort = self._check_arith(arg)
        if isinstance(arg, Const):
            if sort.is_int:
                assert isinstance(arg.value, int)
                assert not isinstance(arg.value, bool)
                return self.mk_int_val(-arg.value)
            assert isinstance(arg.value, Fraction)
            return self.mk_real_val(-arg.value)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.NEG:
            return arg.args[0]
        decl = self._intern_decl(DeclKind.NEG, "-", (sort,), sort)
        return self._intern_app(decl, (arg,))

    def mk_add(self, *args: Expr) -> Expr:
        """Build a normalized n-ary arithmetic sum."""
        if not args:
            msg = "mk_add requires at least one argument"
            raise ValueError(msg)
        sort = self._check_arith(args[0])
        const_sum: int | Fraction = 0 if sort.is_int else Fraction(0)
        non_const: list[Expr] = []

        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in Add: expected '{sort}', got '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.ADD:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert not isinstance(item.value, bool)
                if sort.is_int:
                    assert isinstance(item.value, int)
                    assert isinstance(const_sum, int)
                    const_sum += item.value
                else:
                    assert isinstance(item.value, Fraction)
                    assert isinstance(const_sum, Fraction)
                    const_sum += item.value
            else:
                non_const.append(item)

        if not non_const:
            return self._mk_arith_const(sort, const_sum)
        if const_sum != 0:
            non_const.append(self._mk_arith_const(sort, const_sum))
        if len(non_const) == 1:
            return non_const[0]

        decl = self._intern_decl(DeclKind.ADD, "+", (sort,) * len(non_const), sort)
        return self._intern_app(decl, tuple(non_const))

    def mk_sub(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized arithmetic difference ``lhs - rhs``."""
        sort = self._check_arith_pair(lhs, rhs, "Sub")
        if lhs is rhs:
            return self._mk_arith_const(sort, 0 if sort.is_int else Fraction(0))
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            assert not isinstance(lhs.value, bool)
            assert not isinstance(rhs.value, bool)
            if sort.is_int:
                assert isinstance(lhs.value, int)
                assert isinstance(rhs.value, int)
                return self.mk_int_val(lhs.value - rhs.value)
            assert isinstance(lhs.value, Fraction)
            assert isinstance(rhs.value, Fraction)
            return self.mk_real_val(lhs.value - rhs.value)
        if isinstance(rhs, Const) and rhs.value == 0:
            return lhs
        if isinstance(lhs, Const) and lhs.value == 0:
            return self.mk_neg(rhs)
        decl = self._intern_decl(DeclKind.SUB, "-", (sort, sort), sort)
        return self._intern_app(decl, (lhs, rhs))

    def mk_mul(self, *args: Expr) -> Expr:
        """Build a normalized arithmetic product."""
        if not args:
            msg = "mk_mul requires at least one argument"
            raise ValueError(msg)
        sort = self._check_arith(args[0])
        const_prod: int | Fraction = 1 if sort.is_int else Fraction(1)
        non_const: list[Expr] = []

        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in Mul: expected '{sort}', got '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.MUL:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert not isinstance(item.value, bool)
                if sort.is_int:
                    assert isinstance(item.value, int)
                    assert isinstance(const_prod, int)
                    const_prod *= item.value
                else:
                    assert isinstance(item.value, Fraction)
                    assert isinstance(const_prod, Fraction)
                    const_prod *= item.value
            else:
                non_const.append(item)

        if const_prod == 0:
            return self._mk_arith_const(sort, 0 if sort.is_int else Fraction(0))
        if not non_const:
            return self._mk_arith_const(sort, const_prod)
        if const_prod == -1 and len(non_const) == 1:
            return self.mk_neg(non_const[0])
        if const_prod == 1:
            if len(non_const) == 1:
                return non_const[0]
            factors = tuple(non_const)
        else:
            factors = (self._mk_arith_const(sort, const_prod), *non_const)

        decl = self._intern_decl(DeclKind.MUL, "*", (sort,) * len(factors), sort)
        return self._intern_app(decl, factors)

    def mk_div(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized ``Real`` division ``lhs / rhs``."""
        self._check_real(lhs)
        self._check_real(rhs)
        if isinstance(rhs, Const):
            assert isinstance(rhs.value, Fraction)
            if rhs.value == 1:
                return lhs
            if rhs.value == -1:
                return self.mk_neg(lhs)
            if isinstance(lhs, Const) and rhs.value != 0:
                assert isinstance(lhs.value, Fraction)
                return self.mk_real_val(lhs.value / rhs.value)
        decl = self._intern_decl(
            DeclKind.DIV, "/", (self.real_sort, self.real_sort), self.real_sort
        )
        return self._intern_app(decl, (lhs, rhs))

    def _mk_arith_cmp(self, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
        sort = self._check_arith_pair(lhs, rhs, kind.value)
        if lhs is rhs:
            return self.mk_bool_val(kind in (DeclKind.LE, DeclKind.GE))
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            assert not isinstance(lhs.value, bool)
            assert not isinstance(rhs.value, bool)
            if sort.is_int:
                assert isinstance(lhs.value, int)
                assert isinstance(rhs.value, int)
                lv, rv = lhs.value, rhs.value
                res = (
                    lv < rv
                    if kind is DeclKind.LT
                    else lv <= rv
                    if kind is DeclKind.LE
                    else lv > rv
                    if kind is DeclKind.GT
                    else lv >= rv
                )
            else:
                assert isinstance(lhs.value, Fraction)
                assert isinstance(rhs.value, Fraction)
                lf, rf = lhs.value, rhs.value
                res = (
                    lf < rf
                    if kind is DeclKind.LT
                    else lf <= rf
                    if kind is DeclKind.LE
                    else lf > rf
                    if kind is DeclKind.GT
                    else lf >= rf
                )
            return self.mk_bool_val(res)

        decl = self._intern_decl(kind, kind.value, (sort, sort), self.bool_sort)
        return self._intern_app(decl, (lhs, rhs))

    def mk_lt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized strict less-than inequality ``lhs < rhs``."""
        return self._mk_arith_cmp(DeclKind.LT, lhs, rhs)

    def mk_le(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized less-than-or-equal inequality ``lhs <= rhs``."""
        return self._mk_arith_cmp(DeclKind.LE, lhs, rhs)

    def mk_gt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized strict greater-than inequality ``lhs > rhs``."""
        return self._mk_arith_cmp(DeclKind.GT, lhs, rhs)

    def mk_ge(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized greater-than-or-equal inequality ``lhs >= rhs``."""
        return self._mk_arith_cmp(DeclKind.GE, lhs, rhs)

    # ------------------------------------------------------------------
    # Bit-vector constructors
    # ------------------------------------------------------------------

    def mk_bv_not(self, arg: Expr) -> Expr:
        """Build bitwise negation ``(bvnot arg)``."""
        width = self._check_bv(arg)
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return self.mk_bv_val((~arg.value) & _bv_mask(width), width)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.BV_NOT:
            return arg.args[0]
        decl = self._intern_decl(DeclKind.BV_NOT, "bvnot", (arg.sort,), arg.sort)
        return self._intern_app(decl, (arg,))

    def mk_bv_neg(self, arg: Expr) -> Expr:
        """Build two's-complement negation ``(bvneg arg)``."""
        width = self._check_bv(arg)
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return self.mk_bv_val((-arg.value) & _bv_mask(width), width)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.BV_NEG:
            return arg.args[0]
        decl = self._intern_decl(DeclKind.BV_NEG, "bvneg", (arg.sort,), arg.sort)
        return self._intern_app(decl, (arg,))

    def mk_bv_and(self, *args: Expr) -> Expr:
        """Build bitwise conjunction ``(bvand ...)``."""
        if not args:
            msg = "mk_bv_and requires at least one argument"
            raise ValueError(msg)
        width = self._check_bv(args[0])
        sort = args[0].sort
        mask = _bv_mask(width)
        const_bits = mask
        non_const: list[Expr] = []
        seen: set[Expr] = set()
        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in bvand: '{sort}' vs '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.BV_AND:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert isinstance(item.value, int)
                assert not isinstance(item.value, bool)
                const_bits &= item.value
            elif item not in seen:
                seen.add(item)
                non_const.append(item)
        if const_bits == 0 or not non_const:
            return self.mk_bv_val(const_bits, width)
        terms = (
            tuple(non_const)
            if const_bits == mask
            else (*non_const, self.mk_bv_val(const_bits, width))
        )
        if len(terms) == 1:
            return terms[0]
        decl = self._intern_decl(DeclKind.BV_AND, "bvand", (sort,) * len(terms), sort)
        return self._intern_app(decl, terms)

    def mk_bv_or(self, *args: Expr) -> Expr:
        """Build bitwise disjunction ``(bvor ...)``."""
        if not args:
            msg = "mk_bv_or requires at least one argument"
            raise ValueError(msg)
        width = self._check_bv(args[0])
        sort = args[0].sort
        mask = _bv_mask(width)
        const_bits = 0
        non_const: list[Expr] = []
        seen: set[Expr] = set()
        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in bvor: '{sort}' vs '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.BV_OR:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert isinstance(item.value, int)
                assert not isinstance(item.value, bool)
                const_bits |= item.value
            elif item not in seen:
                seen.add(item)
                non_const.append(item)
        if const_bits == mask or not non_const:
            return self.mk_bv_val(const_bits, width)
        terms = (
            tuple(non_const)
            if const_bits == 0
            else (*non_const, self.mk_bv_val(const_bits, width))
        )
        if len(terms) == 1:
            return terms[0]
        decl = self._intern_decl(DeclKind.BV_OR, "bvor", (sort,) * len(terms), sort)
        return self._intern_app(decl, terms)

    def mk_bv_xor(self, *args: Expr) -> Expr:
        """Build bitwise exclusive-OR ``(bvxor ...)``."""
        if not args:
            msg = "mk_bv_xor requires at least one argument"
            raise ValueError(msg)
        width = self._check_bv(args[0])
        sort = args[0].sort
        const_bits = 0
        counts: dict[Expr, int] = {}
        order: list[Expr] = []
        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in bvxor: '{sort}' vs '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.BV_XOR:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert isinstance(item.value, int)
                assert not isinstance(item.value, bool)
                const_bits ^= item.value
            else:
                if item not in counts:
                    order.append(item)
                    counts[item] = 1
                else:
                    counts[item] += 1
        kept = [item for item in order if counts[item] % 2 == 1]
        if not kept:
            return self.mk_bv_val(const_bits, width)
        terms = (
            tuple(kept)
            if const_bits == 0
            else (*kept, self.mk_bv_val(const_bits, width))
        )
        if len(terms) == 1:
            return terms[0]
        decl = self._intern_decl(DeclKind.BV_XOR, "bvxor", (sort,) * len(terms), sort)
        return self._intern_app(decl, terms)

    def mk_bv_add(self, *args: Expr) -> Expr:
        """Build modular bit-vector addition ``(bvadd ...)``."""
        if not args:
            msg = "mk_bv_add requires at least one argument"
            raise ValueError(msg)
        width = self._check_bv(args[0])
        sort = args[0].sort
        mask = _bv_mask(width)
        const_sum = 0
        non_const: list[Expr] = []
        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in bvadd: '{sort}' vs '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.BV_ADD:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert isinstance(item.value, int)
                assert not isinstance(item.value, bool)
                const_sum = (const_sum + item.value) & mask
            else:
                non_const.append(item)
        if not non_const:
            return self.mk_bv_val(const_sum, width)
        if const_sum != 0:
            non_const.append(self.mk_bv_val(const_sum, width))
        if len(non_const) == 1:
            return non_const[0]
        decl = self._intern_decl(
            DeclKind.BV_ADD, "bvadd", (sort,) * len(non_const), sort
        )
        return self._intern_app(decl, tuple(non_const))

    def mk_bv_sub(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build modular bit-vector subtraction ``(bvsub lhs rhs)``."""
        width = self._check_bv_pair(lhs, rhs, "bvsub")
        if lhs is rhs:
            return self.mk_bv_val(0, width)
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            assert isinstance(lhs.value, int)
            assert isinstance(rhs.value, int)
            assert not isinstance(lhs.value, bool)
            assert not isinstance(rhs.value, bool)
            return self.mk_bv_val(lhs.value - rhs.value, width)
        if isinstance(rhs, Const) and rhs.value == 0:
            return lhs
        decl = self._intern_decl(
            DeclKind.BV_SUB, "bvsub", (lhs.sort, rhs.sort), lhs.sort
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_bv_mul(self, *args: Expr) -> Expr:
        """Build modular bit-vector multiplication ``(bvmul ...)``."""
        if not args:
            msg = "mk_bv_mul requires at least one argument"
            raise ValueError(msg)
        width = self._check_bv(args[0])
        sort = args[0].sort
        mask = _bv_mask(width)
        const_prod = 1
        non_const: list[Expr] = []
        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_expr(item)
            if item.sort is not sort:
                msg = f"Sort mismatch in bvmul: '{sort}' vs '{item.sort}'"
                raise TypeError(msg)
            if isinstance(item, App) and item.decl.kind is DeclKind.BV_MUL:
                stack.extend(reversed(item.args))
            elif isinstance(item, Const):
                assert isinstance(item.value, int)
                assert not isinstance(item.value, bool)
                const_prod = (const_prod * item.value) & mask
            else:
                non_const.append(item)
        if const_prod == 0 or not non_const:
            return self.mk_bv_val(const_prod, width)
        if const_prod == mask and len(non_const) == 1:
            return self.mk_bv_neg(non_const[0])
        if const_prod == 1:
            if len(non_const) == 1:
                return non_const[0]
            factors = tuple(non_const)
        else:
            factors = (self.mk_bv_val(const_prod, width), *non_const)
        decl = self._intern_decl(DeclKind.BV_MUL, "bvmul", (sort,) * len(factors), sort)
        return self._intern_app(decl, factors)

    def _mk_bv_bin(self, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
        width = self._check_bv_pair(lhs, rhs, kind.value)
        mask = _bv_mask(width)
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            assert isinstance(lhs.value, int)
            assert isinstance(rhs.value, int)
            assert not isinstance(lhs.value, bool)
            assert not isinstance(rhs.value, bool)
            a, b = lhs.value, rhs.value
            match kind:
                case DeclKind.BV_UDIV:
                    return self.mk_bv_val(_bv_udiv(a, b, mask), width)
                case DeclKind.BV_UREM:
                    return self.mk_bv_val(_bv_urem(a, b), width)
                case DeclKind.BV_SDIV:
                    return self.mk_bv_val(_bv_sdiv(a, b, width, mask), width)
                case DeclKind.BV_SREM:
                    return self.mk_bv_val(_bv_srem(a, b, width, mask), width)
                case DeclKind.BV_SMOD:
                    return self.mk_bv_val(_bv_smod(a, b, width, mask), width)
                case DeclKind.BV_SHL:
                    return self.mk_bv_val(0 if b >= width else (a << b) & mask, width)
                case DeclKind.BV_LSHR:
                    return self.mk_bv_val(0 if b >= width else a >> b, width)
                case DeclKind.BV_ASHR:
                    sign_bit = 1 << (width - 1)
                    if b >= width:
                        return self.mk_bv_val(mask if (a & sign_bit) else 0, width)
                    return self.mk_bv_val(_bv_to_signed(a, width) >> b, width)
                case _:
                    pass
        decl = self._intern_decl(kind, kind.value, (lhs.sort, rhs.sort), lhs.sort)
        return self._intern_app(decl, (lhs, rhs))

    def mk_bv_udiv(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned bit-vector division ``(bvudiv lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_UDIV, lhs, rhs)

    def mk_bv_urem(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned bit-vector remainder ``(bvurem lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_UREM, lhs, rhs)

    def mk_bv_sdiv(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed two's-complement division ``(bvsdiv lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_SDIV, lhs, rhs)

    def mk_bv_srem(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed truncation remainder ``(bvsrem lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_SREM, lhs, rhs)

    def mk_bv_smod(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed floor-divisor modulo ``(bvsmod lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_SMOD, lhs, rhs)

    def mk_bv_shl(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build logical left shift ``(bvshl lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_SHL, lhs, rhs)

    def mk_bv_lshr(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build logical right shift ``(bvlshr lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_LSHR, lhs, rhs)

    def mk_bv_ashr(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build arithmetic right shift ``(bvashr lhs rhs)``."""
        return self._mk_bv_bin(DeclKind.BV_ASHR, lhs, rhs)

    def _mk_bv_cmp(self, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
        width = self._check_bv_pair(lhs, rhs, kind.value)
        if lhs is rhs:
            return self.mk_bool_val(
                kind
                in (DeclKind.BV_ULE, DeclKind.BV_UGE, DeclKind.BV_SLE, DeclKind.BV_SGE)
            )
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            assert isinstance(lhs.value, int)
            assert isinstance(rhs.value, int)
            assert not isinstance(lhs.value, bool)
            assert not isinstance(rhs.value, bool)
            a, b = lhs.value, rhs.value
            sa, sb = _bv_to_signed(a, width), _bv_to_signed(b, width)
            match kind:
                case DeclKind.BV_ULT:
                    res = a < b
                case DeclKind.BV_ULE:
                    res = a <= b
                case DeclKind.BV_UGT:
                    res = a > b
                case DeclKind.BV_UGE:
                    res = a >= b
                case DeclKind.BV_SLT:
                    res = sa < sb
                case DeclKind.BV_SLE:
                    res = sa <= sb
                case DeclKind.BV_SGT:
                    res = sa > sb
                case DeclKind.BV_SGE:
                    res = sa >= sb
                case _:
                    res = False
            return self.mk_bool_val(res)
        decl = self._intern_decl(kind, kind.value, (lhs.sort, rhs.sort), self.bool_sort)
        return self._intern_app(decl, (lhs, rhs))

    def mk_bv_ult(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned less-than comparison ``(bvult lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_ULT, lhs, rhs)

    def mk_bv_ule(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned less-or-equal comparison ``(bvule lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_ULE, lhs, rhs)

    def mk_bv_ugt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned greater-than comparison ``(bvugt lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_UGT, lhs, rhs)

    def mk_bv_uge(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned greater-or-equal comparison ``(bvuge lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_UGE, lhs, rhs)

    def mk_bv_slt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed less-than comparison ``(bvslt lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_SLT, lhs, rhs)

    def mk_bv_sle(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed less-or-equal comparison ``(bvsle lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_SLE, lhs, rhs)

    def mk_bv_sgt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed greater-than comparison ``(bvsgt lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_SGT, lhs, rhs)

    def mk_bv_sge(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed greater-or-equal comparison ``(bvsge lhs rhs)``."""
        return self._mk_bv_cmp(DeclKind.BV_SGE, lhs, rhs)

    def mk_concat(self, *args: Expr) -> Expr:
        """Concatenate bit-vectors from most-significant to least-significant."""
        if not args:
            msg = "mk_concat requires at least one BitVec argument"
            raise ValueError(msg)
        flat: list[Expr] = []
        stack: list[Expr] = list(reversed(args))
        while stack:
            item = stack.pop()
            self._check_bv(item)
            if isinstance(item, App) and item.decl.kind is DeclKind.BV_CONCAT:
                stack.extend(reversed(item.args))
            else:
                flat.append(item)

        merged: list[Expr] = []
        for item in flat:
            if merged and isinstance(merged[-1], Const) and isinstance(item, Const):
                prev = merged[-1]
                assert isinstance(prev.value, int)
                assert isinstance(item.value, int)
                assert not isinstance(prev.value, bool)
                assert not isinstance(item.value, bool)
                w_item = item.sort.size
                merged[-1] = self.mk_bv_val(
                    (prev.value << w_item) | item.value, prev.sort.size + w_item
                )
            else:
                merged.append(item)

        if len(merged) == 1:
            return merged[0]
        total_width = sum(part.sort.size for part in merged)
        range_sort = self.mk_bv_sort(total_width)
        domain = tuple(part.sort for part in merged)
        decl = self._intern_decl(DeclKind.BV_CONCAT, "concat", domain, range_sort)
        return self._intern_app(decl, tuple(merged))

    def mk_extract(self, high: int, low: int, arg: Expr) -> Expr:
        """Extract bits ``[high:low]`` (inclusive, 0 = LSB) from ``arg``."""
        width = self._check_bv(arg)
        if (
            isinstance(high, bool)
            or isinstance(low, bool)
            or not isinstance(high, int)
            or not isinstance(low, int)
        ):
            msg = "Extract bounds must be int"
            raise TypeError(msg)
        if low < 0 or high < low or high >= width:
            msg = f"Invalid extract bounds [{high}:{low}] for {width}-bit vector"
            raise ValueError(msg)
        if low == 0 and high == width - 1:
            return arg
        out_width = high - low + 1
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return self.mk_bv_val((arg.value >> low) & _bv_mask(out_width), out_width)
        out_sort = self.mk_bv_sort(out_width)
        decl = self._intern_decl(
            DeclKind.BV_EXTRACT,
            f"(_ extract {high} {low})",
            (arg.sort,),
            out_sort,
            params=(high, low),
        )
        return self._intern_app(decl, (arg,))

    def mk_zero_ext(self, n: int, arg: Expr) -> Expr:
        """Zero-extend bit-vector ``arg`` by ``n`` high-order zero bits."""
        width = self._check_bv(arg)
        if isinstance(n, bool) or not isinstance(n, int) or n < 0:
            msg = f"zero_extend width must be a non-negative int, got {n!r}"
            raise ValueError(msg)
        if n == 0:
            return arg
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return self.mk_bv_val(arg.value, width + n)
        out_sort = self.mk_bv_sort(width + n)
        decl = self._intern_decl(
            DeclKind.BV_ZERO_EXT,
            f"(_ zero_extend {n})",
            (arg.sort,),
            out_sort,
            params=(n,),
        )
        return self._intern_app(decl, (arg,))

    def mk_sign_ext(self, n: int, arg: Expr) -> Expr:
        """Sign-extend bit-vector ``arg`` by ``n`` high-order copies of its MSB."""
        width = self._check_bv(arg)
        if isinstance(n, bool) or not isinstance(n, int) or n < 0:
            msg = f"sign_extend width must be a non-negative int, got {n!r}"
            raise ValueError(msg)
        if n == 0:
            return arg
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            return self.mk_bv_val(_bv_to_signed(arg.value, width), width + n)
        out_sort = self.mk_bv_sort(width + n)
        decl = self._intern_decl(
            DeclKind.BV_SIGN_EXT,
            f"(_ sign_extend {n})",
            (arg.sort,),
            out_sort,
            params=(n,),
        )
        return self._intern_app(decl, (arg,))

    def mk_rotate_left(self, n: int, arg: Expr) -> Expr:
        """Rotate bit-vector ``arg`` left by ``n`` bits."""
        width = self._check_bv(arg)
        if isinstance(n, bool) or not isinstance(n, int) or n < 0:
            msg = f"rotate_left distance must be a non-negative int, got {n!r}"
            raise ValueError(msg)
        shift = n % width
        if shift == 0:
            return arg
        mask = _bv_mask(width)
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            val = arg.value
            rot = ((val << shift) | (val >> (width - shift))) & mask
            return self.mk_bv_val(rot, width)
        decl = self._intern_decl(
            DeclKind.BV_ROTATE_LEFT,
            f"(_ rotate_left {shift})",
            (arg.sort,),
            arg.sort,
            params=(shift,),
        )
        return self._intern_app(decl, (arg,))

    def mk_rotate_right(self, n: int, arg: Expr) -> Expr:
        """Rotate bit-vector ``arg`` right by ``n`` bits."""
        width = self._check_bv(arg)
        if isinstance(n, bool) or not isinstance(n, int) or n < 0:
            msg = f"rotate_right distance must be a non-negative int, got {n!r}"
            raise ValueError(msg)
        shift = n % width
        if shift == 0:
            return arg
        mask = _bv_mask(width)
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            val = arg.value
            rot = ((val >> shift) | (val << (width - shift))) & mask
            return self.mk_bv_val(rot, width)
        decl = self._intern_decl(
            DeclKind.BV_ROTATE_RIGHT,
            f"(_ rotate_right {shift})",
            (arg.sort,),
            arg.sort,
            params=(shift,),
        )
        return self._intern_app(decl, (arg,))

    def mk_repeat(self, n: int, arg: Expr) -> Expr:
        """Concatenate ``n >= 1`` copies of bit-vector ``arg``."""
        width = self._check_bv(arg)
        if isinstance(n, bool) or not isinstance(n, int) or n < 1:
            msg = f"repeat count must be a positive int, got {n!r}"
            raise ValueError(msg)
        if n == 1:
            return arg
        if isinstance(arg, Const):
            assert isinstance(arg.value, int)
            assert not isinstance(arg.value, bool)
            acc = 0
            for _ in range(n):
                acc = (acc << width) | arg.value
            return self.mk_bv_val(acc, width * n)
        out_sort = self.mk_bv_sort(width * n)
        decl = self._intern_decl(
            DeclKind.BV_REPEAT,
            f"(_ repeat {n})",
            (arg.sort,),
            out_sort,
            params=(n,),
        )
        return self._intern_app(decl, (arg,))

    # ------------------------------------------------------------------
    # Array constructors
    # ------------------------------------------------------------------

    def mk_select(self, array: Expr, index: Expr) -> Expr:
        """Read element at ``index`` from ``array``."""
        arr_sort = self._check_array(array)
        self._check_expr(index)
        if index.sort is not arr_sort.index_sort:
            msg = (
                f"Sort mismatch in Array select index: "
                f"expected '{arr_sort.index_sort}', got '{index.sort}'"
            )
            raise TypeError(msg)

        cur = array
        while isinstance(cur, App):
            if cur.decl.kind is DeclKind.CONST_ARRAY:
                return cur.args[0]
            if cur.decl.kind is DeclKind.STORE:
                base, st_idx, st_val = cur.args
                if st_idx is index:
                    return st_val
                if isinstance(st_idx, Const) and isinstance(index, Const):
                    cur = base
                    continue
                break
            break

        decl = self._intern_decl(
            DeclKind.SELECT,
            "select",
            (arr_sort, arr_sort.index_sort),
            arr_sort.element_sort,
        )
        return self._intern_app(decl, (cur, index))

    def mk_store(self, array: Expr, index: Expr, value: Expr) -> Expr:
        """Write ``value`` at ``index`` in ``array``, returning a new array."""
        arr_sort = self._check_array(array)
        self._check_expr(index)
        self._check_expr(value)
        if index.sort is not arr_sort.index_sort:
            msg = (
                f"Sort mismatch in Array store index: "
                f"expected '{arr_sort.index_sort}', got '{index.sort}'"
            )
            raise TypeError(msg)
        if value.sort is not arr_sort.element_sort:
            msg = (
                f"Sort mismatch in Array store value: "
                f"expected '{arr_sort.element_sort}', got '{value.sort}'"
            )
            raise TypeError(msg)

        cur = array
        if (
            isinstance(cur, App)
            and cur.decl.kind is DeclKind.CONST_ARRAY
            and cur.args[0] is value
        ):
            return cur
        while (
            isinstance(cur, App)
            and cur.decl.kind is DeclKind.STORE
            and cur.args[1] is index
        ):
            cur = cur.args[0]
        if (
            isinstance(cur, App)
            and cur.decl.kind is DeclKind.CONST_ARRAY
            and cur.args[0] is value
        ):
            return cur

        decl = self._intern_decl(
            DeclKind.STORE,
            "store",
            (arr_sort, arr_sort.index_sort, arr_sort.element_sort),
            arr_sort,
        )
        return self._intern_app(decl, (cur, index, value))

    def mk_const_array(self, index_sort: Sort, value: Expr) -> App:
        """Construct constant array mapping every ``index_sort`` key to ``value``."""
        self._check_sort(index_sort)
        self._check_expr(value)
        arr_sort = self.mk_array_sort(index_sort, value.sort)
        decl = self._intern_decl(
            DeclKind.CONST_ARRAY,
            f"(as const {arr_sort.name})",
            (value.sort,),
            arr_sort,
        )
        return self._intern_app(decl, (value,))

    # ------------------------------------------------------------------
    # Quantifier constructors
    # ------------------------------------------------------------------

    def mk_bound_var(self, index: int, sort: Sort) -> BoundVar:
        """Create or retrieve a hash-consed De Bruijn bound variable."""
        if isinstance(index, bool) or not isinstance(index, int) or index < 0:
            msg = f"BoundVar index must be a non-negative int, got {index!r}"
            raise ValueError(msg)
        self._check_sort(sort)
        key = (index, sort.id)
        existing = self._bound_vars.get(key)
        if existing is not None:
            return existing
        bvar = BoundVar(self._alloc_id(), self, sort, index)
        self._bound_vars[key] = bvar
        return bvar

    def mk_quantifier(
        self,
        is_forall: bool,
        var_names: Sequence[str],
        var_sorts: Sequence[Sort],
        body: Expr,
        *,
        patterns: Sequence[Sequence[Expr]] = (),
    ) -> Expr:
        """Create or retrieve a hash-consed quantifier with explicit De Bruijn body."""
        if not var_sorts:
            msg = "Quantifier must bind at least one variable"
            raise ValueError(msg)
        if len(var_names) != len(var_sorts):
            msg = (
                f"Quantifier name/sort count mismatch: "
                f"{len(var_names)} names vs {len(var_sorts)} sorts"
            )
            raise ValueError(msg)
        for name in var_names:
            if not name:
                msg = "Bound variable name cannot be empty"
                raise ValueError(msg)
        for sort in var_sorts:
            self._check_sort(sort)
        self._check_bool(body)

        norm_patterns: list[tuple[Expr, ...]] = []
        for pat in patterns:
            if not pat:
                msg = "Quantifier pattern cannot be empty"
                raise ValueError(msg)
            for term in pat:
                self._check_expr(term)
            norm_patterns.append(tuple(pat))

        if isinstance(body, Const):
            return body

        names_t = tuple(var_names)
        sorts_t = tuple(var_sorts)
        pats_t = tuple(norm_patterns)
        key = (
            is_forall,
            names_t,
            tuple(sort.id for sort in sorts_t),
            body.id,
            tuple(tuple(term.id for term in pat) for pat in pats_t),
        )
        existing = self._quantifiers.get(key)
        if existing is not None:
            return existing
        quant = Quantifier(
            self._alloc_id(),
            self,
            self.bool_sort,
            is_forall,
            names_t,
            sorts_t,
            body,
            pats_t,
        )
        self._quantifiers[key] = quant
        return quant

    def _mk_binder(
        self,
        is_forall: bool,
        bound_vars: Sequence[Expr],
        body: Expr,
        patterns: Sequence[Expr | Sequence[Expr]] = (),
    ) -> Expr:
        if not bound_vars:
            msg = "Quantifier must bind at least one variable"
            raise ValueError(msg)
        seen_decls: set[FuncDecl] = set()
        bound_apps: list[App] = []
        var_names: list[str] = []
        var_sorts: list[Sort] = []
        for var in bound_vars:
            self._check_expr(var)
            if not isinstance(var, App) or not var.is_const_symbol:
                msg = (
                    f"Bound quantifier variable must be a 0-arity constant, got '{var}'"
                )
                raise TypeError(msg)
            if var.decl in seen_decls:
                msg = f"Duplicate bound variable '{var.name}' in quantifier binder"
                raise ValueError(msg)
            seen_decls.add(var.decl)
            bound_apps.append(var)
            var_names.append(var.name)
            var_sorts.append(var.sort)

        self._check_bool(body)
        norm_pats: list[tuple[Expr, ...]] = []
        for item in patterns:
            if isinstance(item, Expr):
                self._check_expr(item)
                norm_pats.append((item,))
            else:
                if not item:
                    msg = "Quantifier pattern cannot be empty"
                    raise ValueError(msg)
                for term in item:
                    self._check_expr(term)
                norm_pats.append(tuple(item))

        if isinstance(body, Const):
            return body

        abs_body = _abstract_vars_impl(self, body, bound_apps)
        abs_pats = tuple(
            tuple(_abstract_vars_impl(self, term, bound_apps) for term in pat)
            for pat in norm_pats
        )
        return self.mk_quantifier(
            is_forall, var_names, var_sorts, abs_body, patterns=abs_pats
        )

    def mk_forall(
        self,
        bound_vars: Sequence[Expr],
        body: Expr,
        *,
        patterns: Sequence[Expr | Sequence[Expr]] = (),
    ) -> Expr:
        """Bind ``bound_vars`` universally across ``body`` and optional ``patterns``."""
        return self._mk_binder(True, bound_vars, body, patterns)

    def mk_exists(
        self,
        bound_vars: Sequence[Expr],
        body: Expr,
        *,
        patterns: Sequence[Expr | Sequence[Expr]] = (),
    ) -> Expr:
        """Bind ``bound_vars`` existentially across ``body`` and ``patterns``."""
        return self._mk_binder(False, bound_vars, body, patterns)
