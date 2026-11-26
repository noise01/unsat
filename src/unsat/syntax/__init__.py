"""Abstract syntax for sorts, declarations, terms, formulas, and contexts.

Stateless/explicit-context AST layer at the bottom of the solver; must not
depend on any other ``unsat`` module.
"""

from unsat.syntax.context import Context
from unsat.syntax.expr import (
    App,
    BoundVar,
    Const,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
)
from unsat.syntax.kinds import DeclKind, SortKind
from unsat.syntax.str_eval import (
    MAX_CHAR_CODE,
    format_smt2_string,
    unescape_smt2_string,
    validate_smt2_string,
)
from unsat.syntax.walk import (
    abstract_vars,
    collect_const_decls,
    collect_func_decls,
    format_expr,
    format_sort,
    free_bound_var_indices,
    has_bound_vars,
    has_quantifiers,
    instantiate_quantifier,
    iter_subexprs,
    quote_smt2_symbol,
    shift_bound_vars,
    substitute,
)

__all__ = [
    "MAX_CHAR_CODE",
    "App",
    "BoundVar",
    "Const",
    "Context",
    "DeclKind",
    "Expr",
    "FuncDecl",
    "Quantifier",
    "Sort",
    "SortKind",
    "abstract_vars",
    "collect_const_decls",
    "collect_func_decls",
    "format_expr",
    "format_smt2_string",
    "format_sort",
    "free_bound_var_indices",
    "has_bound_vars",
    "has_quantifiers",
    "instantiate_quantifier",
    "iter_subexprs",
    "quote_smt2_symbol",
    "shift_bound_vars",
    "substitute",
    "unescape_smt2_string",
    "validate_smt2_string",
]
