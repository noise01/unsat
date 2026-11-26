from collections.abc import Sequence
from typing import Any, Literal

from unsat_legacy.ast.context import AND_DECL, NOT_DECL, OR_DECL, global_ctx
from unsat_legacy.ast.expr import Expr, FuncDecl
from unsat_legacy.ast.sorts import BOOL_SORT, INT_SORT, Sort
from unsat_legacy.engine import SMTEngine
from unsat_legacy.errors import SortMismatchError


class Solver:
    def __init__(self, callbacks: dict[str, Any] | None = None) -> None:
        self.callbacks = callbacks or {}

        self.engine = SMTEngine(callbacks=self.callbacks)

    def add(self, formula: Expr) -> None:
        self.engine.add_formula(formula)

    def check(
        self,
        *assumptions: Expr,
        max_rounds: int | None = None,
        max_matches: int | None = None,
    ) -> Literal["SAT", "UNSAT", "UNKNOWN"]:
        return self.engine.check(
            list(assumptions), max_rounds=max_rounds, max_matches=max_matches
        )

    def unsat_core(self) -> list[Expr]:
        return self.engine.get_unsat_core()

    def push(self) -> None:
        self.engine.push()

    def pop(self, num_levels: int = 1) -> None:
        self.engine.pop(num_levels)

    def model(self) -> dict[Expr, int]:
        return self.engine.get_model()

    def statistics(self) -> dict[str, int]:
        return self.engine.get_stats()


def Bool(name: str) -> Expr:
    return global_ctx.mk_var(name, BOOL_SORT)


def Int(name: str) -> Expr:
    return global_ctx.mk_var(name, INT_SORT)


def BoolVal(*, val: bool) -> Expr:
    return global_ctx.mk_const(val, BOOL_SORT)


def And(*args: Expr) -> Expr:
    return global_ctx.mk_app(AND_DECL, *args)


def Or(*args: Expr) -> Expr:
    return global_ctx.mk_app(OR_DECL, *args)


def Not(arg: Expr) -> Expr:
    return global_ctx.mk_app(NOT_DECL, arg)


def Implies(p: Expr, q: Expr) -> Expr:
    return Or(Not(p), q)


def Eq(a: Expr, b: Expr) -> Expr:
    if a.sort != b.sort:
        msg = f"Sort mismatch in Eq: cannot compare '{a.sort}' and '{b.sort}'"
        raise SortMismatchError(msg)

    eq_decl = FuncDecl("Eq", (a.sort, b.sort), BOOL_SORT)
    return global_ctx.mk_app(eq_decl, a, b)


def Function(name: str, *sorts: Sort) -> FuncDecl:
    *domain, range_sort = sorts
    domain_sort = tuple(domain)

    return FuncDecl(name, domain_sort, range_sort)


def BoundVar(name: str, sort: Sort) -> Expr:
    return global_ctx.mk_bound_var(name, sort)


def MultiPattern(*exprs: Expr) -> Expr:
    return global_ctx.mk_pattern(*exprs)


def ForAll(
    bound_vars: Sequence[Expr], body: Expr, patterns: Sequence[Expr] | None = None
) -> Expr:
    pats = tuple(patterns) if patterns else ()
    return global_ctx.mk_quantifier(
        is_forall=True, bound_vars=tuple(bound_vars), body=body, patterns=pats
    )


def Exists(
    bound_vars: Sequence[Expr], body: Expr, patterns: Sequence[Expr] | None = None
) -> Expr:
    pats = tuple(patterns) if patterns else ()
    return global_ctx.mk_quantifier(
        is_forall=False, bound_vars=tuple(bound_vars), body=body, patterns=pats
    )
