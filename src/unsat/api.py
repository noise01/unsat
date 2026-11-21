"""Thin user-facing Z3Py-style Python DSL and builder layer.

Provides default-context management, syntactic sugar, and the ``Solver`` facade
directly over ``syntax`` objects without duplicating an AST wrapper hierarchy.

Depends on: ``syntax``, ``smt``, ``model``.
"""

from collections.abc import Sequence
from fractions import Fraction

from unsat.model import FuncInterp, Model
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, Const, Context, Expr, FuncDecl, Sort

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


def BoolSort(ctx: Context | None = None) -> Sort:
    """Return the ``Bool`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_bool_sort()


def IntSort(ctx: Context | None = None) -> Sort:
    """Return the ``Int`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_int_sort()


def RealSort(ctx: Context | None = None) -> Sort:
    """Return the ``Real`` sort in ``ctx`` (or the default context)."""
    return _resolve_ctx(ctx).mk_real_sort()


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


def ToReal(expr: Expr) -> Expr:
    """Convert an ``Int`` expression to ``Real``."""
    return expr.ctx.mk_to_real(expr)


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


class Solver:
    """User-facing incremental SMT solver facade."""

    def __init__(self, ctx: Context | None = None) -> None:
        self._solver = SMTSolver(_resolve_ctx(ctx))

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._solver.ctx

    def add(self, *formulas: Expr) -> None:
        """Assert one or more formulas into the current scope."""
        self._solver.add(*formulas)

    def check(self, *assumptions: Expr) -> SolveResult:
        """Check satisfiability under optional assumption formulas."""
        return self._solver.check(*assumptions)

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
    "UNKNOWN",
    "UNSAT",
    "And",
    "App",
    "Bool",
    "BoolSort",
    "BoolVal",
    "Bools",
    "Const",
    "Constant",
    "Constants",
    "Context",
    "DeclareSort",
    "Distinct",
    "Eq",
    "Expr",
    "FuncDecl",
    "FuncInterp",
    "Function",
    "If",
    "Implies",
    "Int",
    "IntSort",
    "IntVal",
    "Ints",
    "Model",
    "Not",
    "Or",
    "Real",
    "RealSort",
    "RealVal",
    "Reals",
    "SolveResult",
    "Solver",
    "Sort",
    "Sum",
    "ToReal",
    "Xor",
    "default_context",
    "reset_default_context",
    "set_default_context",
]
