"""Iterative AST traversal, declaration collection, and SMT-LIB2 formatting."""

from collections.abc import Iterator, Mapping, Sequence

from unsat.syntax.expr import (
    App,
    BoundVar,
    Const,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
    _abstract_vars_impl,
)
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
        "declare-sort",
        "define-fun",
        "define-sort",
        "distinct",
        "echo",
        "exists",
        "exit",
        "false",
        "forall",
        "get-assertions",
        "get-model",
        "get-unsat-core",
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
    DeclKind.IDIV: "div",
    DeclKind.MOD: "mod",
    DeclKind.ABS: "abs",
    DeclKind.LT: "<",
    DeclKind.LE: "<=",
    DeclKind.GT: ">",
    DeclKind.GE: ">=",
    DeclKind.TO_REAL: "to_real",
    DeclKind.TO_INT: "to_int",
    DeclKind.IS_INT: "is_int",
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


def _extend_binder_env(
    env: tuple[str, ...], var_names: tuple[str, ...]
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    used = set(env)
    cur_env = list(env)
    disambiguated: list[str] = []
    for name in var_names:
        out_name = f"{name}!{len(cur_env)}" if name in used else name
        used.add(out_name)
        cur_env.append(out_name)
        disambiguated.append(out_name)
    return tuple(cur_env), tuple(disambiguated)


def format_expr(expr: Expr) -> str:
    """Render ``expr`` iteratively as an SMT-LIB2 S-expression string."""
    rendered: dict[tuple[Expr, tuple[str, ...]], str] = {}
    stack: list[tuple[Expr, tuple[str, ...], bool]] = [(expr, (), False)]

    while stack:
        node, env, expanded = stack.pop()
        key = (node, env)
        if key in rendered:
            continue

        if isinstance(node, Const):
            if node.sort.kind is SortKind.UNINTERPRETED:
                rendered[key] = quote_smt2_symbol(f"{node.sort.name}!val!{node.value}")
            else:
                rendered[key] = str(node)
            continue

        if isinstance(node, BoundVar):
            if node.index < len(env):
                rendered[key] = quote_smt2_symbol(env[-1 - node.index])
            else:
                rendered[key] = f"(:var {node.index})"
            continue

        if isinstance(node, Quantifier):
            child_env, display_names = _extend_binder_env(env, node.var_names)
            if not expanded:
                stack.append((node, env, True))
                for pat in reversed(node.patterns):
                    for term in reversed(pat):
                        if (term, child_env) not in rendered:
                            stack.append((term, child_env, False))
                if (node.body, child_env) not in rendered:
                    stack.append((node.body, child_env, False))
                continue
            kw = "forall" if node.is_forall else "exists"
            binders = " ".join(
                f"({quote_smt2_symbol(name)} {format_sort(sort)})"
                for name, sort in zip(display_names, node.var_sorts, strict=True)
            )
            body_str = rendered[(node.body, child_env)]
            if node.patterns:
                pats_str = " ".join(
                    f":pattern ({' '.join(rendered[(t, child_env)] for t in pat)})"
                    for pat in node.patterns
                )
                body_str = f"(! {body_str} {pats_str})"
            rendered[key] = f"({kw} ({binders}) {body_str})"
            continue

        if isinstance(node, App):
            if not expanded and node.args:
                stack.append((node, env, True))
                for arg in reversed(node.args):
                    if (arg, env) not in rendered:
                        stack.append((arg, env, False))
                continue
            kind = node.decl.kind
            if kind is DeclKind.UNINTERPRETED:
                head = quote_smt2_symbol(node.decl.name)
            elif kind is DeclKind.CONST_ARRAY:
                head = f"(as const {format_sort(node.decl.range_sort)})"
            elif kind is DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                head = f"(_ extract {hi} {lo})"
            elif kind in (
                DeclKind.DIVISIBLE,
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
                rendered[key] = head
            else:
                args_str = " ".join(rendered[(arg, env)] for arg in node.args)
                rendered[key] = f"({head} {args_str})"
            continue

        rendered[key] = str(node)

    return rendered[(expr, ())]


def has_quantifiers(expr: Expr) -> bool:
    """Return whether any :class:`Quantifier` node is reachable in ``expr``."""
    visited: set[Expr] = set()
    stack: list[Expr] = [expr]
    while stack:
        node = stack.pop()
        if node in visited:
            continue
        visited.add(node)
        if isinstance(node, Quantifier):
            return True
        stack.extend(node.children)
    return False


def has_bound_vars(expr: Expr) -> bool:
    """Return whether any :class:`BoundVar` node is reachable in ``expr``."""
    visited: set[Expr] = set()
    stack: list[Expr] = [expr]
    while stack:
        node = stack.pop()
        if node in visited:
            continue
        visited.add(node)
        if isinstance(node, BoundVar):
            return True
        stack.extend(node.children)
    return False


def free_bound_var_indices(expr: Expr) -> frozenset[int]:
    """Return all De Bruijn bound-variable indices free at the root of ``expr``."""
    free: set[int] = set()
    visited: set[tuple[Expr, int]] = set()
    stack: list[tuple[Expr, int]] = [(expr, 0)]
    while stack:
        node, depth = stack.pop()
        key = (node, depth)
        if key in visited:
            continue
        visited.add(key)
        if isinstance(node, BoundVar):
            if node.index >= depth:
                free.add(node.index - depth)
            continue
        if isinstance(node, Quantifier):
            cdepth = depth + node.num_vars
            for child in node.children:
                if (child, cdepth) not in visited:
                    stack.append((child, cdepth))
            continue
        for child in node.children:
            if (child, depth) not in visited:
                stack.append((child, depth))
    return frozenset(free)


def shift_bound_vars(expr: Expr, delta: int, cutoff: int = 0) -> Expr:
    """Shift free :class:`BoundVar` indices ``>= cutoff`` by ``delta``."""
    if delta == 0:
        return expr
    ctx = expr.ctx
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
            if node.index < depth + cutoff:
                memo[key] = node
            else:
                new_idx = node.index + delta
                if new_idx < depth:
                    msg = (
                        f"Shifting BoundVar({node.index}) by {delta} at depth "
                        f"{depth} yields negative relative index"
                    )
                    raise ValueError(msg)
                memo[key] = ctx.mk_bound_var(new_idx, node.sort)
            continue
        if isinstance(node, App):
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


def abstract_vars(expr: Expr, vars_to_bind: Sequence[App]) -> Expr:
    """Replace 0-arity ``vars_to_bind`` with De Bruijn indices for binder scope."""
    ctx = expr.ctx
    seen_decls: set[FuncDecl] = set()
    for var in vars_to_bind:
        if var.ctx is not ctx:
            msg = f"Variable '{var}' belongs to a different Context"
            raise ValueError(msg)
        if not isinstance(var, App) or not var.is_const_symbol:
            msg = f"Expected 0-arity constant symbol, got '{var}'"
            raise TypeError(msg)
        if var.decl in seen_decls:
            msg = f"Duplicate variable '{var.name}' in abstract_vars"
            raise ValueError(msg)
        seen_decls.add(var.decl)
    return _abstract_vars_impl(ctx, expr, vars_to_bind)


def instantiate_quantifier(quantifier: Quantifier, args: Sequence[Expr]) -> Expr:
    """Instantiate ``quantifier.body`` with concrete/symbolic terms ``args``."""
    ctx = quantifier.ctx
    k = quantifier.num_vars
    if len(args) != k:
        msg = f"Quantifier instantiation arity mismatch: expected {k}, got {len(args)}"
        raise ValueError(msg)
    for i, (arg, expected_sort) in enumerate(
        zip(args, quantifier.var_sorts, strict=True)
    ):
        if arg.ctx is not ctx:
            msg = f"Instantiation argument {i} belongs to a different Context"
            raise ValueError(msg)
        if arg.sort is not expected_sort:
            msg = (
                f"Sort mismatch in quantifier argument {i}: "
                f"expected '{expected_sort}', got '{arg.sort}'"
            )
            raise TypeError(msg)

    memo: dict[tuple[Expr, int], Expr] = {}
    stack: list[tuple[Expr, int, bool]] = [(quantifier.body, 0, False)]

    while stack:
        node, depth, expanded = stack.pop()
        key = (node, depth)
        if key in memo:
            continue
        if isinstance(node, Const):
            memo[key] = node
            continue
        if isinstance(node, BoundVar):
            if node.index < depth:
                memo[key] = node
            elif node.index < depth + k:
                slot = node.index - depth
                arg_pos = k - 1 - slot
                memo[key] = shift_bound_vars(args[arg_pos], depth)
            else:
                memo[key] = ctx.mk_bound_var(node.index - k, node.sort)
            continue
        if isinstance(node, App):
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

    return memo[(quantifier.body, 0)]


def substitute(expr: Expr, mapping: Mapping[Expr, Expr]) -> Expr:
    """Simultaneously substitute subexpressions in ``mapping``, capture-avoiding."""
    if not mapping:
        return expr
    ctx = expr.ctx
    clean_map: dict[Expr, tuple[Expr, bool]] = {}
    for target, replacement in mapping.items():
        if target.ctx is not ctx or replacement.ctx is not ctx:
            msg = "Substitute key/value belongs to a different Context"
            raise ValueError(msg)
        if target.sort is not replacement.sort:
            msg = (
                f"Sort mismatch in substitute: '{target.sort}' vs '{replacement.sort}'"
            )
            raise TypeError(msg)
        clean_map[target] = (replacement, not free_bound_var_indices(target))

    memo: dict[tuple[Expr, int], Expr] = {}
    stack: list[tuple[Expr, int, bool]] = [(expr, 0, False)]

    while stack:
        node, depth, expanded = stack.pop()
        key = (node, depth)
        if key in memo:
            continue

        if isinstance(node, BoundVar):
            if depth == 0:
                entry = clean_map.get(node)
                memo[key] = entry[0] if entry is not None else node
            else:
                memo[key] = node
            continue

        entry = clean_map.get(node)
        if entry is not None and (depth == 0 or entry[1]):
            memo[key] = shift_bound_vars(entry[0], depth)
            continue

        if isinstance(node, Const):
            memo[key] = node
            continue

        if isinstance(node, App):
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
