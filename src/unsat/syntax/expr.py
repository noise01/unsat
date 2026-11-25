"""Hash-consed AST node definitions (Sort, FuncDecl, Expr, Const, App, Quantifier)."""

import sys
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING, NoReturn

from unsat.syntax.bv_eval import _format_real_fraction
from unsat.syntax.kinds import DeclKind, SortKind

if TYPE_CHECKING:
    from unsat.syntax.context import Context


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

    def __floordiv__(self, other: object) -> Expr:
        if not self.is_int:
            return NotImplemented
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_idiv(self, rhs)

    def __rfloordiv__(self, other: object) -> Expr:
        if not self.is_int:
            return NotImplemented
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_idiv(lhs, self)

    def __mod__(self, other: object) -> Expr:
        if self.is_bv:
            rhs = self._coerce_bv(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_bv_smod(self, rhs)
        if self.is_int:
            rhs = self._coerce_arith(other)
            if rhs is None:
                return NotImplemented
            return self.ctx.mk_mod(self, rhs)
        return NotImplemented

    def __rmod__(self, other: object) -> Expr:
        if self.is_bv:
            lhs = self._coerce_bv(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_bv_smod(lhs, self)
        if self.is_int:
            lhs = self._coerce_arith(other)
            if lhs is None:
                return NotImplemented
            return self.ctx.mk_mod(lhs, self)
        return NotImplemented

    def __abs__(self) -> Expr:
        if self.is_int:
            return self.ctx.mk_abs(self)
        msg = f"bad operand type for abs(): '{self.sort}'"
        raise TypeError(msg)

    def __pow__(self, other: object) -> Expr:
        if not self.is_arith:
            return NotImplemented
        if isinstance(other, bool) or not isinstance(other, int):
            return NotImplemented
        if other < 0:
            msg = (
                f"Negative exponent is not supported on arithmetic expressions: {other}"
            )
            raise ValueError(msg)
        if other == 0:
            return self.ctx.mk_int_val(1) if self.is_int else self.ctx.mk_real_val(1)
        if other == 1:
            return self
        return self.ctx.mk_mul(*(self,) * other)

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


if "unsat.syntax.context" not in sys.modules:
    from unsat.syntax.context import Context
