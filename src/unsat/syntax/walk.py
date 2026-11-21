"""Iterative AST traversal, declaration collection, and SMT-LIB2 formatting."""

from collections.abc import Iterator

from unsat.syntax.core import App, Const, Expr, FuncDecl
from unsat.syntax.kinds import DeclKind, SortKind

_SIMPLE_SYMBOL_PUNCTUATION = frozenset("~!@$%^&*_-+=<>.?/")
_RESERVED_WORDS = frozenset(
    {
        "!",
        "_",
        "and",
        "as",
        "assert",
        "check-sat",
        "check-sat-assuming",
        "declare-const",
        "declare-fun",
        "define-fun",
        "distinct",
        "exists",
        "exit",
        "false",
        "forall",
        "get-model",
        "get-value",
        "ite",
        "let",
        "not",
        "or",
        "par",
        "pop",
        "push",
        "reset",
        "reset-assertions",
        "set-info",
        "set-logic",
        "set-option",
        "true",
        "xor",
    }
)
_BUILTIN_SMT2_NAMES: dict[DeclKind, str] = {
    DeclKind.NOT: "not",
    DeclKind.AND: "and",
    DeclKind.OR: "or",
    DeclKind.IMPLIES: "=>",
    DeclKind.XOR: "xor",
    DeclKind.EQ: "=",
    DeclKind.DISTINCT: "distinct",
    DeclKind.ITE: "ite",
    DeclKind.NEG: "-",
    DeclKind.ADD: "+",
    DeclKind.SUB: "-",
    DeclKind.MUL: "*",
    DeclKind.DIV: "/",
    DeclKind.LT: "<",
    DeclKind.LE: "<=",
    DeclKind.GT: ">",
    DeclKind.GE: ">=",
    DeclKind.TO_REAL: "to_real",
}


def iter_subexprs(expr: Expr) -> Iterator[Expr]:
    """Yield every unique reachable subexpression in iterative post-order."""
    visited: set[Expr] = set()
    stack: list[tuple[Expr, bool]] = [(expr, False)]
    while stack:
        node, expanded = stack.pop()
        if node in visited:
            continue
        if expanded:
            visited.add(node)
            yield node
            continue
        stack.append((node, True))
        for child in reversed(node.children):
            if child not in visited:
                stack.append((child, False))


def collect_const_decls(expr: Expr) -> list[FuncDecl]:
    """Return unique 0-arity uninterpreted declarations appearing in ``expr``."""
    decls: list[FuncDecl] = []
    seen: set[FuncDecl] = set()
    for node in iter_subexprs(expr):
        if isinstance(node, App) and node.is_const_symbol and node.decl not in seen:
            seen.add(node.decl)
            decls.append(node.decl)
    return decls


def collect_func_decls(expr: Expr) -> list[FuncDecl]:
    """Return all unique uninterpreted declarations appearing in ``expr``."""
    decls: list[FuncDecl] = []
    seen: set[FuncDecl] = set()
    for node in iter_subexprs(expr):
        if (
            isinstance(node, App)
            and node.decl.is_uninterpreted
            and node.decl not in seen
        ):
            seen.add(node.decl)
            decls.append(node.decl)
    return decls


def quote_smt2_symbol(name: str) -> str:
    """Format ``name`` as an SMT-LIB2 simple or pipe-quoted symbol."""
    if not name:
        msg = "SMT-LIB2 symbol name cannot be empty"
        raise ValueError(msg)
    if "|" in name or "\\" in name:
        msg = f"Symbol name {name!r} contains illegal SMT-LIB2 quote character"
        raise ValueError(msg)

    is_simple = (
        not name[0].isascii() or not name[0].isdigit()
    ) and name not in _RESERVED_WORDS
    if is_simple:
        is_simple = all(
            ch.isascii() and (ch.isalnum() or ch in _SIMPLE_SYMBOL_PUNCTUATION)
            for ch in name
        )
    return name if is_simple else f"|{name}|"


def format_expr(expr: Expr) -> str:
    """Render ``expr`` iteratively as an SMT-LIB2 S-expression string."""
    rendered: dict[Expr, str] = {}
    for node in iter_subexprs(expr):
        if isinstance(node, Const):
            if node.sort.kind is SortKind.UNINTERPRETED:
                rendered[node] = quote_smt2_symbol(f"{node.sort.name}!val!{node.value}")
            else:
                rendered[node] = str(node)
        elif isinstance(node, App):
            if node.decl.kind is DeclKind.UNINTERPRETED:
                head = quote_smt2_symbol(node.decl.name)
            else:
                head = _BUILTIN_SMT2_NAMES[node.decl.kind]
            if not node.args:
                rendered[node] = head
            else:
                args_str = " ".join(rendered[arg] for arg in node.args)
                rendered[node] = f"({head} {args_str})"
        else:
            rendered[node] = str(node)
    return rendered[expr]
