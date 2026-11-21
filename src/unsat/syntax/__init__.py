"""Abstract syntax for sorts, declarations, terms, formulas, and contexts.

Stateless/explicit-context AST layer at the bottom of the solver; must not
depend on any other ``unsat`` module.
"""

from unsat.syntax.core import App, Const, Context, Expr, FuncDecl, Sort
from unsat.syntax.kinds import DeclKind, SortKind
from unsat.syntax.walk import (
    collect_const_decls,
    collect_func_decls,
    format_expr,
    format_sort,
    iter_subexprs,
    quote_smt2_symbol,
)

__all__ = [
    "App",
    "Const",
    "Context",
    "DeclKind",
    "Expr",
    "FuncDecl",
    "Sort",
    "SortKind",
    "collect_const_decls",
    "collect_func_decls",
    "format_expr",
    "format_sort",
    "iter_subexprs",
    "quote_smt2_symbol",
]
