"""Thin user-facing Z3Py-style Python DSL and builder layer.

Provides default-context management, syntactic sugar, and the ``Solver`` facade
directly over ``syntax`` objects without duplicating an AST wrapper hierarchy.

Depends on: ``syntax``, ``smt``, ``model``.
"""

from collections.abc import Sequence
from fractions import Fraction

from unsat.model import FuncInterp, Model
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, BoundVar, Const, Context, Expr, FuncDecl, Quantifier, Sort

_default_ctx = Context()

SAT = SolveResult.SAT
UNSAT = SolveResult.UNSAT
UNKNOWN = SolveResult.UNKNOWN


def default_context() -> Context:
    """Return the active default AST :class:`Context`."""
    return _default_ctx


def set_default_context(ctx: Context) -> None:
    """Set the active default AST :class:`Context`."""
    global _default_ctx
    _default_ctx = ctx


def reset_default_context() -> Context:
    """Replace the default AST :class:`Context` with a fresh instance."""
    global _default_ctx
    _default_ctx = Context()
    return _default_ctx


def _resolve_ctx(ctx: Context | None) -> Context:
    return _default_ctx if ctx is None else ctx


def _flatten_expr_args(
    args: tuple[Expr | Sequence[Expr], ...],
) -> tuple[Expr, ...]:
    if (
        len(args) == 1
        and isinstance(args[0], Sequence)
        and not isinstance(args[0], Expr)
    ):
        return tuple(args[0])
    flat: list[Expr] = []
    for item in args:
        if isinstance(item, Expr):
            flat.append(item)
        else:
            flat.extend(item)
    return tuple(flat)


def _bv_coerce_pair(a: Expr | int, b: Expr | int, op_name: str) -> tuple[Expr, Expr]:
    if isinstance(a, Expr) and isinstance(b, Expr):
        return a, b
    if (
        isinstance(a, Expr)
        and a.is_bv
        and isinstance(b, int)
        and not isinstance(b, bool)
    ):
        return a, a.ctx.mk_bv_val(b, a.bv_size)
    if (
        isinstance(b, Expr)
        and b.is_bv
        and isinstance(a, int)
        and not isinstance(a, bool)
    ):
        return b.ctx.mk_bv_val(a, b.bv_size), b
    msg = f"{op_name} requires BitVec expressions"
    raise TypeError(msg)


def _coerce_arg_for_sort(sort: Sort, value: Expr | bool | int | Fraction) -> Expr:
    if isinstance(value, Expr):
        return value
    if sort.is_bool and isinstance(value, bool):
        return sort.ctx.mk_bool_val(value)
    if sort.is_int and isinstance(value, int) and not isinstance(value, bool):
        return sort.ctx.mk_int_val(value)
    if (
        sort.is_real
        and not isinstance(value, bool)
        and isinstance(value, (int, Fraction))
    ):
        return sort.ctx.mk_real_val(value)
    if sort.is_bv and isinstance(value, int) and not isinstance(value, bool):
        return sort.ctx.mk_bv_val(value, sort.size)
    msg = f"Cannot coerce value {value!r} to sort '{sort}'"
    raise TypeError(msg)


def BoolSort(ctx: Context | None = None) -> Sort:
    """Return the ``Bool`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_bool_sort()


def IntSort(ctx: Context | None = None) -> Sort:
    """Return the ``Int`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_int_sort()


def RealSort(ctx: Context | None = None) -> Sort:
    """Return the ``Real`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_real_sort()


def BitVecSort(size: int, ctx: Context | None = None) -> Sort:
    """Return the fixed-width ``(_ BitVec size)`` sort."""
    return _resolve_ctx(ctx).mk_bv_sort(size)


def ArraySort(domain: Sort, range_sort: Sort) -> Sort:
    """Return the ``(Array domain range_sort)`` sort."""
    if domain.ctx is not range_sort.ctx:
        msg = "ArraySort domain and range belong to different Contexts"
        raise ValueError(msg)
    return domain.ctx.mk_array_sort(domain, range_sort)


def DeclareSort(name: str, ctx: Context | None = None) -> Sort:
    """Declare or retrieve an uninterpreted sort named ``name``."""
    return _resolve_ctx(ctx).mk_uninterpreted_sort(name)


def Bool(name: str, ctx: Context | None = None) -> App:
    """Create a Boolean symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_bool(name)


def Bools(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple Boolean symbolic constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_bool(name) for name in name_list]


def Int(name: str, ctx: Context | None = None) -> App:
    """Create an ``Int`` symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_int(name)


def Ints(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple ``Int`` symbolic constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_int(name) for name in name_list]


def Real(name: str, ctx: Context | None = None) -> App:
    """Create a ``Real`` symbolic constant named ``name``."""
    return _resolve_ctx(ctx).mk_real(name)


def Reals(names: str | Sequence[str], ctx: Context | None = None) -> list[App]:
    """Create multiple ``Real`` symbolic constants from whitespace-separated names."""
    resolved = _resolve_ctx(ctx)
    name_list = names.split() if isinstance(names, str) else list(names)
    return [resolved.mk_real(name) for name in name_list]


def BitVec(name: str, bv: int | Sort, ctx: Context | None = None) -> App:
    """Create a fixed-width ``BitVec`` symbolic constant named ``name``."""
    if isinstance(bv, Sort):
        if not bv.is_bv:
            msg = f"Expected BitVec sort, got '{bv}'"
            raise TypeError(msg)
        return bv.ctx.mk_const(name, bv)
    return _resolve_ctx(ctx).mk_bv(name, bv)


def BitVecs(
    names: str | Sequence[str], bv: int | Sort, ctx: Context | None = None
) -> list[App]:
    """Create multiple ``BitVec`` constants from whitespace-separated names."""
    name_list = names.split() if isinstance(names, str) else list(names)
    return [BitVec(name, bv, ctx) for name in name_list]


def Array(name: str, index_sort: Sort, element_sort: Sort) -> App:
    """Create an ``Array`` symbolic constant over ``index_sort -> element_sort``."""
    if index_sort.ctx is not element_sort.ctx:
        msg = "Array index and element sorts belong to different Contexts"
        raise ValueError(msg)
    return index_sort.ctx.mk_array(name, index_sort, element_sort)


def Constant(name: str, sort: Sort) -> App:
    """Create a 0-arity symbolic constant named ``name`` of ``sort``."""
    return sort.ctx.mk_const(name, sort)


def Constants(names: str | Sequence[str], sort: Sort) -> list[App]:
    """Create multiple 0-arity constants of ``sort`` from names."""
    name_list = names.split() if isinstance(names, str) else list(names)
    return [sort.ctx.mk_const(name, sort) for name in name_list]


def Function(name: str, *sorts: Sort) -> FuncDecl:
    """Declare an uninterpreted function ``name`` over ``sorts[:-1] -> sorts[-1]``."""
    if not sorts:
        msg = "Function requires at least a range sort"
        raise ValueError(msg)
    range_sort = sorts[-1]
    domain = sorts[:-1]
    return range_sort.ctx.mk_decl(name, domain, range_sort)


def BoolVal(value: bool, ctx: Context | None = None) -> Const:
    """Create a Boolean literal constant ``true`` or ``false``."""
    return _resolve_ctx(ctx).mk_bool_val(value)


def IntVal(value: int, ctx: Context | None = None) -> Const:
    """Create an exact integer literal constant."""
    return _resolve_ctx(ctx).mk_int_val(value)


def RealVal(value: int | Fraction | str, ctx: Context | None = None) -> Const:
    """Create an exact rational ``Real`` literal constant."""
    return _resolve_ctx(ctx).mk_real_val(value)


def BitVecVal(val: int, bv: int | Sort, ctx: Context | None = None) -> Const:
    """Create a fixed-width ``BitVec`` constant literal."""
    if isinstance(bv, Sort):
        if not bv.is_bv:
            msg = f"Expected BitVec sort, got '{bv}'"
            raise TypeError(msg)
        return bv.ctx.mk_bv_val(val, bv.size)
    return _resolve_ctx(ctx).mk_bv_val(val, bv)


def ToReal(expr: Expr) -> Expr:
    """Convert an ``Int`` expression to ``Real``."""
    return expr.ctx.mk_to_real(expr)


def UDiv(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector division ``bvudiv(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "UDiv")
    return lhs.ctx.mk_bv_udiv(lhs, rhs)


def URem(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector remainder ``bvurem(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "URem")
    return lhs.ctx.mk_bv_urem(lhs, rhs)


def SDiv(a: Expr | int, b: Expr | int) -> Expr:
    """Signed bit-vector division ``bvsdiv(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "SDiv")
    return lhs.ctx.mk_bv_sdiv(lhs, rhs)


def SRem(a: Expr | int, b: Expr | int) -> Expr:
    """Signed bit-vector remainder ``bvsrem(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "SRem")
    return lhs.ctx.mk_bv_srem(lhs, rhs)


def SMod(a: Expr | int, b: Expr | int) -> Expr:
    """Signed bit-vector modulo ``bvsmod(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "SMod")
    return lhs.ctx.mk_bv_smod(lhs, rhs)


def LShR(a: Expr | int, b: Expr | int) -> Expr:
    """Logical right shift ``bvlshr(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "LShR")
    return lhs.ctx.mk_bv_lshr(lhs, rhs)


def ULT(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector less-than ``bvult(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "ULT")
    return lhs.ctx.mk_bv_ult(lhs, rhs)


def ULE(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector less-or-equal ``bvule(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "ULE")
    return lhs.ctx.mk_bv_ule(lhs, rhs)


def UGT(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector greater-than ``bvugt(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "UGT")
    return lhs.ctx.mk_bv_ugt(lhs, rhs)


def UGE(a: Expr | int, b: Expr | int) -> Expr:
    """Unsigned bit-vector greater-or-equal ``bvuge(a, b)``."""
    lhs, rhs = _bv_coerce_pair(a, b, "UGE")
    return lhs.ctx.mk_bv_uge(lhs, rhs)


def Concat(*args: Expr | Sequence[Expr]) -> Expr:
    """Concatenate bit-vectors from most-significant to least-significant."""
    flat = _flatten_expr_args(args)
    if not flat:
        msg = "Concat requires at least one BitVec expression"
        raise ValueError(msg)
    return flat[0].ctx.mk_concat(*flat)


def Extract(high: int, low: int, a: Expr) -> Expr:
    """Extract bit slice ``a[high:low]`` (inclusive, 0 = LSB)."""
    return a.ctx.mk_extract(high, low, a)


def ZeroExt(n: int, a: Expr) -> Expr:
    """Zero-extend bit-vector ``a`` by ``n`` bits."""
    return a.ctx.mk_zero_ext(n, a)


def SignExt(n: int, a: Expr) -> Expr:
    """Sign-extend bit-vector ``a`` by ``n`` bits."""
    return a.ctx.mk_sign_ext(n, a)


def RotateLeft(a: Expr, n: int) -> Expr:
    """Rotate bit-vector ``a`` left by ``n`` bits."""
    return a.ctx.mk_rotate_left(n, a)


def RotateRight(a: Expr, n: int) -> Expr:
    """Rotate bit-vector ``a`` right by ``n`` bits."""
    return a.ctx.mk_rotate_right(n, a)


def Repeat(n: int, a: Expr) -> Expr:
    """Concatenate ``n`` copies of bit-vector ``a``."""
    return a.ctx.mk_repeat(n, a)


def Select(array: Expr, index: Expr | bool | int | Fraction) -> Expr:
    """Read the element at ``index`` in ``array``."""
    if not array.is_array:
        msg = f"Expected Array expression in Select, got '{array.sort}'"
        raise TypeError(msg)
    idx_expr = _coerce_arg_for_sort(array.sort.index_sort, index)
    return array.ctx.mk_select(array, idx_expr)


def Store(
    array: Expr,
    index: Expr | bool | int | Fraction,
    value: Expr | bool | int | Fraction,
) -> Expr:
    """Store ``value`` at ``index`` in ``array``, returning the updated array."""
    if not array.is_array:
        msg = f"Expected Array expression in Store, got '{array.sort}'"
        raise TypeError(msg)
    idx_expr = _coerce_arg_for_sort(array.sort.index_sort, index)
    val_expr = _coerce_arg_for_sort(array.sort.element_sort, value)
    return array.ctx.mk_store(array, idx_expr, val_expr)


def K(domain: Sort, value: Expr | bool | int | Fraction) -> App:
    """Construct a constant array mapping every key in ``domain`` to ``value``."""
    if isinstance(value, Expr):
        return domain.ctx.mk_const_array(domain, value)
    if isinstance(value, bool):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_bool_val(value))
    if isinstance(value, int):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_int_val(value))
    if isinstance(value, Fraction):
        return domain.ctx.mk_const_array(domain, domain.ctx.mk_real_val(value))
    msg = f"Unsupported constant array value: {value!r}"
    raise TypeError(msg)


def Sum(*args: Expr | Sequence[Expr]) -> Expr:
    """Build an n-ary arithmetic sum over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_int_val(0)
    return flat[0].ctx.mk_add(*flat)


def And(*args: Expr | Sequence[Expr]) -> Expr:
    """Build a logical conjunction over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_true()
    return flat[0].ctx.mk_and(*flat)


def Or(*args: Expr | Sequence[Expr]) -> Expr:
    """Build a logical disjunction over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_false()
    return flat[0].ctx.mk_or(*flat)


def Not(arg: Expr) -> Expr:
    """Build the logical negation of ``arg``."""
    return arg.ctx.mk_not(arg)


def Implies(lhs: Expr, rhs: Expr) -> Expr:
    """Build the logical implication ``lhs => rhs``."""
    return lhs.ctx.mk_implies(lhs, rhs)


def Xor(lhs: Expr, rhs: Expr) -> Expr:
    """Build the logical exclusive-OR ``lhs xor rhs``."""
    return lhs.ctx.mk_xor(lhs, rhs)


def Eq(lhs: Expr, rhs: Expr) -> Expr:
    """Build the formula-level equality ``lhs = rhs``."""
    return lhs.ctx.mk_eq(lhs, rhs)


def Distinct(*args: Expr | Sequence[Expr]) -> Expr:
    """Build a pairwise-distinct constraint over ``args``."""
    flat = _flatten_expr_args(args)
    if not flat:
        return _default_ctx.mk_true()
    return flat[0].ctx.mk_distinct(*flat)


def If(cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr:
    """Build an if-then-else expression ``ite(cond, then_branch, else_branch)``."""
    return cond.ctx.mk_ite(cond, then_branch, else_branch)


def ForAll(
    vs: Expr | Sequence[Expr],
    body: Expr,
    *,
    patterns: Sequence[Expr | Sequence[Expr]] = (),
) -> Expr:
    """Build a universally quantified formula ``ForAll(vs, body)``."""
    bound = (vs,) if isinstance(vs, Expr) else tuple(vs)
    if not bound:
        return _default_ctx.mk_forall(bound, body, patterns=patterns)
    return bound[0].ctx.mk_forall(bound, body, patterns=patterns)


def Exists(
    vs: Expr | Sequence[Expr],
    body: Expr,
    *,
    patterns: Sequence[Expr | Sequence[Expr]] = (),
) -> Expr:
    """Build an existentially quantified formula ``Exists(vs, body)``."""
    bound = (vs,) if isinstance(vs, Expr) else tuple(vs)
    if not bound:
        return _default_ctx.mk_exists(bound, body, patterns=patterns)
    return bound[0].ctx.mk_exists(bound, body, patterns=patterns)


def MultiPattern(*terms: Expr) -> tuple[Expr, ...]:
    """Group multiple trigger expressions into one multi-pattern tuple."""
    if not terms:
        msg = "MultiPattern requires at least one trigger expression"
        raise ValueError(msg)
    ctx = terms[0].ctx
    for term in terms[1:]:
        if term.ctx is not ctx:
            msg = f"Expr '{term}' belongs to a different Context"
            raise ValueError(msg)
    return tuple(terms)


class Solver:
    """User-facing incremental SMT solver facade."""

    def __init__(
        self,
        ctx: Context | None = None,
        *,
        max_quantifier_rounds: int | None = None,
        max_quantifier_matches: int | None = None,
        timeout: float | None = None,
        max_conflicts: int | None = None,
    ) -> None:
        self._solver = SMTSolver(
            _resolve_ctx(ctx),
            max_quantifier_rounds=max_quantifier_rounds,
            max_quantifier_matches=max_quantifier_matches,
            timeout=timeout,
            max_conflicts=max_conflicts,
        )

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._solver.ctx

    def add(self, *formulas: Expr) -> None:
        """Assert one or more formulas into the current scope."""
        self._solver.add(*formulas)

    def check(
        self,
        *assumptions: Expr,
        timeout: float | None = None,
        max_conflicts: int | None = None,
    ) -> SolveResult:
        """Check satisfiability under optional assumption formulas."""
        return self._solver.check(
            *assumptions, timeout=timeout, max_conflicts=max_conflicts
        )

    def model(self) -> Model:
        """Return a satisfying :class:`Model` from the latest ``check()``."""
        return self._solver.model()

    def unsat_core(self) -> list[Expr]:
        """Return the assumption subset responsible for the last ``UNSAT``."""
        return self._solver.unsat_core()

    def push(self) -> None:
        """Push a new incremental assertion scope."""
        self._solver.push()

    def pop(self, levels: int = 1) -> None:
        """Pop ``levels`` incremental assertion scopes."""
        self._solver.pop(levels)

    def reset(self) -> None:
        """Reset all asserted formulas and scopes."""
        self._solver.reset()

    def assertions(self) -> list[Expr]:
        """Return all active asserted formulas."""
        return self._solver.assertions()

    def statistics(self) -> dict[str, int]:
        """Return solver search counters."""
        stats = self._solver.statistics()
        return {key: val for key, val in stats.items() if isinstance(val, int)}


__all__ = [
    "SAT",
    "UGE",
    "UGT",
    "ULE",
    "ULT",
    "UNKNOWN",
    "UNSAT",
    "And",
    "App",
    "Array",
    "ArraySort",
    "BitVec",
    "BitVecSort",
    "BitVecVal",
    "BitVecs",
    "Bool",
    "BoolSort",
    "BoolVal",
    "Bools",
    "BoundVar",
    "Concat",
    "Const",
    "Constant",
    "Constants",
    "Context",
    "DeclareSort",
    "Distinct",
    "Eq",
    "Exists",
    "Expr",
    "Extract",
    "ForAll",
    "FuncDecl",
    "FuncInterp",
    "Function",
    "If",
    "Implies",
    "Int",
    "IntSort",
    "IntVal",
    "Ints",
    "K",
    "LShR",
    "Model",
    "MultiPattern",
    "Not",
    "Or",
    "Quantifier",
    "Real",
    "RealSort",
    "RealVal",
    "Reals",
    "Repeat",
    "RotateLeft",
    "RotateRight",
    "SDiv",
    "SMod",
    "SRem",
    "Select",
    "SignExt",
    "SolveResult",
    "Solver",
    "Sort",
    "Store",
    "Sum",
    "ToReal",
    "UDiv",
    "URem",
    "Xor",
    "ZeroExt",
    "default_context",
    "reset_default_context",
    "set_default_context",
]
