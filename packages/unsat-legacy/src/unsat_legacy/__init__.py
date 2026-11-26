"""A self-contained SMT engine, and the public facade for it.

Satisfiability modulo theories with assumption-based solving and unsat cores, an
equality (EUF) theory, quantifier instantiation by E-matching under explicit
budgets, and a TPTP front end. Preserved as a standalone archived solver package.

A check answers three ways -- ``"SAT"``, ``"UNSAT"``, or ``"UNKNOWN"`` when a
budget ran out. The third is a real answer rather than a failure: deliberation is
*anytime*, so a matching loop that could run unbounded is cut and reported as
undetermined instead of hanging. ``"UNSAT"`` stays sound however the search was
cut short, because a contradiction derived from the ground clauses does not
depend on instantiation having finished.

Correctness is asserted differentially against Z3 rather than by this package's
own tests alone; those tests are dev-only and are not shipped.

External callers should import from ``unsat_legacy`` directly rather than reaching
into submodules. Modules *inside* this package keep their deep imports to avoid
import cycles (``parsers.tptp`` depends on ``api``).
"""

from unsat_legacy.api import (
    And,
    Bool,
    BoolVal,
    BoundVar,
    Eq,
    Exists,
    ForAll,
    Function,
    Implies,
    Int,
    MultiPattern,
    Not,
    Or,
    Solver,
)
from unsat_legacy.ast.context import global_ctx
from unsat_legacy.ast.expr import App, Const, Expr, FuncDecl, Pattern, Quantifier, Var
from unsat_legacy.ast.expr import BoundVar as BoundVarExpr
from unsat_legacy.ast.sorts import BOOL_SORT, INT_SORT, Sort, USort
from unsat_legacy.parsers import parse_fof, to_tptp_expr

__all__ = [
    "BOOL_SORT",
    "INT_SORT",
    "And",
    "App",
    "Bool",
    "BoolVal",
    "BoundVar",
    "BoundVarExpr",
    "Const",
    "Eq",
    "Exists",
    "Expr",
    "ForAll",
    "FuncDecl",
    "Function",
    "Implies",
    "Int",
    "MultiPattern",
    "Not",
    "Or",
    "Pattern",
    "Quantifier",
    "Solver",
    "Sort",
    "USort",
    "Var",
    "global_ctx",
    "parse_fof",
    "to_tptp_expr",
]
