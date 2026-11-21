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


@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)
class Sort:
    """Sorted type node interned within a :class:`Context`."""

    id: int
    ctx: Context
    name: str
    kind: SortKind

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

    def __and__(self, other: object) -> Expr:
        if not isinstance(other, Expr):
            return NotImplemented
        return self.ctx.mk_and(self, other)

    def __or__(self, other: object) -> Expr:
        if not isinstance(other, Expr):
            return NotImplemented
        return self.ctx.mk_or(self, other)

    def __invert__(self) -> Expr:
        return self.ctx.mk_not(self)

    def __xor__(self, other: object) -> Expr:
        if not isinstance(other, Expr):
            return NotImplemented
        return self.ctx.mk_xor(self, other)

    def __pos__(self) -> Expr:
        self.ctx._check_arith(self)
        return self

    def __neg__(self) -> Expr:
        return self.ctx.mk_neg(self)

    def __add__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_add(self, rhs)

    def __radd__(self, other: object) -> Expr:
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_add(lhs, self)

    def __sub__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_sub(self, rhs)

    def __rsub__(self, other: object) -> Expr:
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_sub(lhs, self)

    def __mul__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_mul(self, rhs)

    def __rmul__(self, other: object) -> Expr:
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_mul(lhs, self)

    def __truediv__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_div(self, rhs)

    def __rtruediv__(self, other: object) -> Expr:
        lhs = self._coerce_arith(other)
        if lhs is None:
            return NotImplemented
        return self.ctx.mk_div(lhs, self)

    def __lt__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_lt(self, rhs)

    def __le__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_le(self, rhs)

    def __gt__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_gt(self, rhs)

    def __ge__(self, other: object) -> Expr:
        rhs = self._coerce_arith(other)
        if rhs is None:
            return NotImplemented
        return self.ctx.mk_ge(self, rhs)


@dataclass(frozen=True, slots=True, eq=False)
class Const(Expr):
    """Constant literal expression (Bool, Int, Real, or finite-domain element)."""

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
        self._sorts: weakref.WeakValueDictionary[tuple[SortKind, str], Sort] = (
            weakref.WeakValueDictionary()
        )
        self._decls: weakref.WeakValueDictionary[
            tuple[DeclKind, str, tuple[Sort, ...], Sort], FuncDecl
        ] = weakref.WeakValueDictionary()
        self._exprs: weakref.WeakValueDictionary[tuple[object, ...], Expr] = (
            weakref.WeakValueDictionary()
        )

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

    def _intern_sort(self, kind: SortKind, name: str) -> Sort:
        key = (kind, name)
        existing = self._sorts.get(key)
        if existing is not None:
            return existing
        sort = Sort(self._alloc_id(), self, name, kind)
        self._sorts[key] = sort
        return sort

    def _intern_decl(
        self,
        kind: DeclKind,
        name: str,
        domain: tuple[Sort, ...],
        range_sort: Sort,
    ) -> FuncDecl:
        key = (kind, name, domain, range_sort)
        existing = self._decls.get(key)
        if existing is not None:
            return existing
        decl = FuncDecl(self._alloc_id(), self, name, domain, range_sort, kind)
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

    def mk_bool_sort(self) -> Sort:
        """Return this context's canonical ``Bool`` sort."""
        return self.bool_sort

    def mk_int_sort(self) -> Sort:
        """Return this context's canonical ``Int`` sort."""
        return self.int_sort

    def mk_real_sort(self) -> Sort:
        """Return this context's canonical ``Real`` sort."""
        return self.real_sort

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
