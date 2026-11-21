"""Iterative AST traversal, declaration collection, and SMT-LIB2 formatting."""

from collections.abc import Iterator

from unsat.syntax.core import App, Const, Expr, FuncDecl, Sort
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
    DeclKind.BV_NOT: "bvnot",
    DeclKind.BV_AND: "bvand",
    DeclKind.BV_OR: "bvor",
    DeclKind.BV_XOR: "bvxor",
    DeclKind.BV_NEG: "bvneg",
    DeclKind.BV_ADD: "bvadd",
    DeclKind.BV_SUB: "bvsub",
    DeclKind.BV_MUL: "bvmul",
    DeclKind.BV_UDIV: "bvudiv",
    DeclKind.BV_UREM: "bvurem",
    DeclKind.BV_SDIV: "bvsdiv",
    DeclKind.BV_SREM: "bvsrem",
    DeclKind.BV_SMOD: "bvsmod",
    DeclKind.BV_SHL: "bvshl",
    DeclKind.BV_LSHR: "bvlshr",
    DeclKind.BV_ASHR: "bvashr",
    DeclKind.BV_ULT: "bvult",
    DeclKind.BV_ULE: "bvule",
    DeclKind.BV_UGT: "bvugt",
    DeclKind.BV_UGE: "bvuge",
    DeclKind.BV_SLT: "bvslt",
    DeclKind.BV_SLE: "bvsle",
    DeclKind.BV_SGT: "bvsgt",
    DeclKind.BV_SGE: "bvsge",
    DeclKind.BV_CONCAT: "concat",
    DeclKind.SELECT: "select",
    DeclKind.STORE: "store",
}


def format_sort(sort: Sort) -> str:
    """Render ``sort`` iteratively as an SMT-LIB2 sort expression."""
    if sort.kind is SortKind.BOOL:
        return "Bool"
    if sort.kind is SortKind.INT:
        return "Int"
    if sort.kind is SortKind.REAL:
        return "Real"
    if sort.kind is SortKind.BITVEC:
        return f"(_ BitVec {sort.size})"
    if sort.kind is SortKind.ARRAY:
        return (
            f"(Array {format_sort(sort.index_sort)} {format_sort(sort.element_sort)})"
        )
    return quote_smt2_symbol(sort.name)


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
            kind = node.decl.kind
            if kind is DeclKind.UNINTERPRETED:
                head = quote_smt2_symbol(node.decl.name)
            elif kind is DeclKind.CONST_ARRAY:
                head = f"(as const {format_sort(node.decl.range_sort)})"
            elif kind is DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                head = f"(_ extract {hi} {lo})"
            elif kind in (
                DeclKind.BV_ZERO_EXT,
                DeclKind.BV_SIGN_EXT,
                DeclKind.BV_ROTATE_LEFT,
                DeclKind.BV_ROTATE_RIGHT,
                DeclKind.BV_REPEAT,
            ):
                head = f"(_ {kind.value} {node.decl.params[0]})"
            else:
                head = _BUILTIN_SMT2_NAMES[kind]
            if not node.args:
                rendered[node] = head
            else:
                args_str = " ".join(rendered[arg] for arg in node.args)
                rendered[node] = f"({head} {args_str})"
        else:
            rendered[node] = str(node)
    return rendered[expr]
