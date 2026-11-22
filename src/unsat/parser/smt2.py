"""SMT-LIB2 lexer, S-expression parser, formatter, and command runner."""

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from unsat.model import Model, Value
from unsat.sat import SolveResult
from unsat.smt import SMTSolver
from unsat.syntax import (
    App,
    Const,
    Context,
    Expr,
    FuncDecl,
    Sort,
    SortKind,
    abstract_vars,
    format_expr,
    format_sort,
    quote_smt2_symbol,
)

type SExpr = _Atom | tuple[SExpr, ...]

_SIMPLE_SYMBOL_CHARS = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~!@$%^&*_-+=<>.?/"
)
_HEX_CHARS = frozenset("0123456789abcdefABCDEF")


@dataclass(frozen=True, slots=True)
class _Symbol:
    name: str
    quoted: bool
    line: int
    col: int


@dataclass(frozen=True, slots=True)
class _Keyword:
    name: str
    line: int
    col: int


@dataclass(frozen=True, slots=True)
class _StringLit:
    value: str
    line: int
    col: int


@dataclass(frozen=True, slots=True)
class _BVLiteral:
    value: int
    width: int
    line: int
    col: int


type _Atom = _Symbol | _Keyword | _StringLit | _BVLiteral


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    value: str
    line: int
    col: int


def tokenize_smt2(text: str) -> list[_Token]:
    """Tokenize SMT-LIB2 source text into tokens."""
    text = text.removeprefix("\ufeff")
    tokens: list[_Token] = []
    n = len(text)
    i = 0
    line = 1
    col = 1

    while i < n:
        ch = text[i]
        if ch in " \t\r":
            i += 1
            col += 1
            continue
        if ch == "\n":
            i += 1
            line += 1
            col = 1
            continue
        if ch == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch == "(":
            tokens.append(_Token("LPAREN", "(", line, col))
            i += 1
            col += 1
            continue
        if ch == ")":
            tokens.append(_Token("RPAREN", ")", line, col))
            i += 1
            col += 1
            continue
        if ch == "|":
            start_line, start_col = line, col
            i += 1
            col += 1
            chars: list[str] = []
            while i < n and text[i] != "|":
                if text[i] == "\\":
                    msg = f"Line {line}, col {col}: '\\' is not allowed inside '|...|'"
                    raise ValueError(msg)
                if text[i] == "\n":
                    line += 1
                    col = 1
                else:
                    col += 1
                chars.append(text[i])
                i += 1
            if i >= n:
                msg = (
                    f"Line {start_line}, col {start_col}: "
                    "unterminated quoted symbol '|...|'"
                )
                raise ValueError(msg)
            i += 1
            col += 1
            tokens.append(_Token("QSYMBOL", "".join(chars), start_line, start_col))
            continue
        if ch == '"':
            start_line, start_col = line, col
            i += 1
            col += 1
            chars = []
            while i < n:
                cur = text[i]
                if cur == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        chars.append('"')
                        i += 2
                        col += 2
                        continue
                    i += 1
                    col += 1
                    break
                if cur == "\n":
                    line += 1
                    col = 1
                else:
                    col += 1
                chars.append(cur)
                i += 1
            else:
                msg = f"Line {start_line}, col {start_col}: unterminated string literal"
                raise ValueError(msg)
            tokens.append(_Token("STRING", "".join(chars), start_line, start_col))
            continue
        if ch == ":":
            start_col = col
            i += 1
            col += 1
            start = i
            while i < n and text[i] in _SIMPLE_SYMBOL_CHARS:
                i += 1
                col += 1
            if i == start:
                msg = f"Line {line}, col {start_col}: empty keyword ':'"
                raise ValueError(msg)
            tokens.append(_Token("KEYWORD", text[start:i], line, start_col))
            continue
        if ch == "#":
            start_col = col
            if i + 1 < n and text[i + 1] == "b":
                i += 2
                col += 2
                start = i
                while i < n and text[i] in ("0", "1"):
                    i += 1
                    col += 1
                if i == start:
                    msg = f"Line {line}, col {start_col}: empty binary '#b' literal"
                    raise ValueError(msg)
                tokens.append(_Token("BVBIN", text[start:i], line, start_col))
                continue
            if i + 1 < n and text[i + 1] == "x":
                i += 2
                col += 2
                start = i
                while i < n and text[i] in _HEX_CHARS:
                    i += 1
                    col += 1
                if i == start:
                    msg = f"Line {line}, col {start_col}: empty hex '#x' literal"
                    raise ValueError(msg)
                tokens.append(_Token("BVHEX", text[start:i], line, start_col))
                continue
            msg = f"Line {line}, col {col}: unexpected '#' literal"
            raise ValueError(msg)
        if ch in _SIMPLE_SYMBOL_CHARS:
            start_col = col
            start = i
            while i < n and text[i] in _SIMPLE_SYMBOL_CHARS:
                i += 1
                col += 1
            tokens.append(_Token("SYMBOL", text[start:i], line, start_col))
            continue

        msg = f"Line {line}, col {col}: unexpected character {ch!r}"
        raise ValueError(msg)

    return tokens


def _parse_sexprs(tokens: Sequence[_Token]) -> list[SExpr]:
    top: list[SExpr] = []
    stack: list[tuple[list[SExpr], int, int]] = []

    for tok in tokens:
        if tok.kind == "LPAREN":
            stack.append(([], tok.line, tok.col))
            continue
        if tok.kind == "RPAREN":
            if not stack:
                msg = f"Line {tok.line}, col {tok.col}: unexpected ')'"
                raise ValueError(msg)
            items, _, _ = stack.pop()
            node: SExpr = tuple(items)
            if stack:
                stack[-1][0].append(node)
            else:
                top.append(node)
            continue

        if tok.kind == "SYMBOL":
            atom: SExpr = _Symbol(tok.value, False, tok.line, tok.col)
        elif tok.kind == "QSYMBOL":
            atom = _Symbol(tok.value, True, tok.line, tok.col)
        elif tok.kind == "KEYWORD":
            atom = _Keyword(tok.value, tok.line, tok.col)
        elif tok.kind == "BVBIN":
            atom = _BVLiteral(int(tok.value, 2), len(tok.value), tok.line, tok.col)
        elif tok.kind == "BVHEX":
            atom = _BVLiteral(int(tok.value, 16), 4 * len(tok.value), tok.line, tok.col)
        else:
            atom = _StringLit(tok.value, tok.line, tok.col)

        if stack:
            stack[-1][0].append(atom)
        else:
            top.append(atom)

    if stack:
        _, open_line, open_col = stack[-1]
        msg = f"Line {open_line}, col {open_col}: unclosed '('"
        raise ValueError(msg)

    return top


_SUPPORTED_LOGICS = frozenset(
    {
        "QF_BOOL",
        "QF_UF",
        "QF_LRA",
        "QF_LIA",
        "QF_UFLRA",
        "QF_UFLIA",
        "QF_LIRA",
        "QF_BV",
        "QF_UFBV",
        "QF_AX",
        "QF_ABV",
        "QF_AUFBV",
        "QF_ALIA",
        "QF_ALRA",
        "QF_AUFLIA",
        "QF_AUFLRA",
        "QF_AUFLIRA",
        "UF",
        "LIA",
        "LRA",
        "LIRA",
        "UFLIA",
        "UFLRA",
        "UFLIRA",
        "BV",
        "UFBV",
        "AX",
        "ABV",
        "AUFBV",
        "ALIA",
        "ALRA",
        "AUFLIA",
        "AUFLRA",
        "AUFLIRA",
        "ALL",
    }
)


def _is_decimal_token(name: str) -> bool:
    parts = name.split(".")
    return len(parts) == 2 and parts[0].isdigit() and parts[1].isdigit()


def _default_expr_for_model(model: Model, sort: Sort) -> Expr:
    chain: list[Sort] = []
    cur = sort
    while cur.kind is SortKind.ARRAY:
        chain.append(cur.index_sort)
        cur = cur.element_sort
    if cur.kind is SortKind.BOOL:
        val: Expr = model.ctx.mk_false()
    elif cur.kind is SortKind.INT:
        val = model.ctx.mk_int_val(0)
    elif cur.kind is SortKind.REAL:
        val = model.ctx.mk_real_val(0)
    elif cur.kind is SortKind.BITVEC:
        val = model.ctx.mk_bv_val(0, cur.size)
    else:
        universe = model.universe(cur)
        val = universe[0] if universe else model.ctx.mk_domain_val(cur, 0)
    for idx_sort in reversed(chain):
        val = model.ctx.mk_const_array(idx_sort, val)
    return val


def _format_value_atom(ctx: Context, val: Value, sort: Sort) -> str:
    if isinstance(val, bool):
        return "true" if val else "false"
    if isinstance(val, int):
        if sort.is_bv:
            return format_expr(ctx.mk_bv_val(val, sort.size))
        return format_expr(ctx.mk_int_val(val))
    if isinstance(val, Fraction):
        return format_expr(ctx.mk_real_val(val))
    return format_expr(val)


def format_smt2_model(
    model: Model,
    *,
    decls: Sequence[FuncDecl] | None = None,
) -> str:
    """Format ``model`` as an SMT-LIB2 ``(get-model)`` S-expression."""
    target_decls = (
        tuple(decls) if decls is not None else (model.decls() + model.func_decls())
    )
    if not target_decls:
        return "()"

    lines = ["("]
    for decl in target_decls:
        sym = quote_smt2_symbol(decl.name)
        range_str = format_sort(decl.range_sort)
        if decl.arity == 0:
            raw_val = model.get(decl)
            val_str = (
                _format_value_atom(model.ctx, raw_val, decl.range_sort)
                if raw_val is not None
                else format_expr(_default_expr_for_model(model, decl.range_sort))
            )
            lines.append(f"  (define-fun {sym} () {range_str} {val_str})")
            continue

        param_names = [f"x!{i}" for i in range(decl.arity)]
        params_str = " ".join(
            f"({p} {format_sort(sort)})"
            for p, sort in zip(param_names, decl.domain, strict=True)
        )
        if model.has_func_interp(decl):
            interp = model.func_interp(decl)
            body = format_expr(interp.else_value)
            for key_args, result in reversed(interp.entries()):
                if len(key_args) == 1:
                    cond = f"(= {param_names[0]} {format_expr(key_args[0])})"
                else:
                    eqs = " ".join(
                        f"(= {p} {format_expr(arg)})"
                        for p, arg in zip(param_names, key_args, strict=True)
                    )
                    cond = f"(and {eqs})"
                body = f"(ite {cond} {format_expr(result)} {body})"
        else:
            body = format_expr(_default_expr_for_model(model, decl.range_sort))
        lines.append(f"  (define-fun {sym} ({params_str}) {range_str} {body})")
    lines.append(")")
    return "\n".join(lines)


class SMT2Runner:
    """Stateful SMT-LIB2 command executor for core & combined SMT logics."""

    def __init__(self) -> None:
        self.ctx = Context()
        self.solver = SMTSolver(self.ctx)
        self._sorts_stack: list[dict[str, Sort]] = [{}]
        self._decls_stack: list[dict[str, FuncDecl]] = [{}]
        self._defs_stack: list[dict[str, Expr]] = [{}]
        self._declared_order: list[list[FuncDecl]] = [[]]
        self._logic: str | None = None
        self._qvar_seq = 0

    def declared_decls(self) -> list[FuncDecl]:
        """Return currently active declarations in declaration order."""
        return [decl for scope in self._declared_order for decl in scope]

    def execute(self, text: str) -> list[str]:
        """Execute all SMT-LIB2 commands in ``text`` and return output lines."""
        tokens = tokenize_smt2(text)
        commands = _parse_sexprs(tokens)
        outputs: list[str] = []
        for cmd in commands:
            done, reply = self._run_command(cmd)
            if reply is not None:
                outputs.append(reply)
            if done:
                break
        return outputs

    def statistics(self) -> dict[str, int]:
        """Return underlying solver statistics."""
        return self.solver.statistics()

    def _lookup_sort(self, name: str) -> Sort | None:
        for scope in reversed(self._sorts_stack):
            if name in scope:
                return scope[name]
        return None

    def _lookup_decl(self, name: str) -> FuncDecl | None:
        for scope in reversed(self._decls_stack):
            if name in scope:
                return scope[name]
        return None

    def _lookup_def(self, name: str) -> Expr | None:
        for scope in reversed(self._defs_stack):
            if name in scope:
                return scope[name]
        return None

    def _expect_symbol(self, sexpr: SExpr, context_desc: str) -> _Symbol:
        if not isinstance(sexpr, _Symbol):
            msg = f"Expected symbol in {context_desc}, got {sexpr!r}"
            raise ValueError(msg)
        return sexpr

    def _resolve_sort(self, sexpr: SExpr, context_desc: str) -> Sort:
        if isinstance(sexpr, tuple) and sexpr:
            head = self._expect_symbol(sexpr[0], context_desc)
            if not head.quoted and head.name == "_" and len(sexpr) == 3:
                tag = self._expect_symbol(sexpr[1], context_desc)
                if not tag.quoted and tag.name == "BitVec":
                    width = self._parse_nonneg_int(sexpr[2], context_desc)
                    return self.ctx.mk_bv_sort(width)
            if not head.quoted and head.name == "Array" and len(sexpr) == 3:
                idx_sort = self._resolve_sort(sexpr[1], context_desc)
                elem_sort = self._resolve_sort(sexpr[2], context_desc)
                return self.ctx.mk_array_sort(idx_sort, elem_sort)
            msg = f"Invalid compound sort {sexpr!r} in {context_desc}"
            raise ValueError(msg)

        sym = self._expect_symbol(sexpr, context_desc)
        if not sym.quoted:
            if sym.name == "Bool":
                return self.ctx.bool_sort
            if sym.name == "Int":
                return self.ctx.int_sort
            if sym.name == "Real":
                return self.ctx.real_sort
        found = self._lookup_sort(sym.name)
        if found is None:
            msg = f"Unknown sort {sym.name!r} in {context_desc}"
            raise ValueError(msg)
        return found

    def _parse_nonneg_int(self, sexpr: SExpr, context_desc: str) -> int:
        sym = self._expect_symbol(sexpr, context_desc)
        if sym.quoted or not sym.name.isdigit():
            msg = f"Expected non-negative integer in {context_desc}, got {sym.name!r}"
            raise ValueError(msg)
        return int(sym.name)

    def _run_command(self, cmd: SExpr) -> tuple[bool, str | None]:
        if not isinstance(cmd, tuple) or not cmd:
            msg = f"Expected command S-expression list, got {cmd!r}"
            raise ValueError(msg)
        head = self._expect_symbol(cmd[0], "command name")
        if head.quoted:
            msg = f"Unknown quoted command {head.name!r}"
            raise ValueError(msg)
        name = head.name
        args = cmd[1:]

        match name:
            case "set-logic":
                if len(args) != 1:
                    msg = "set-logic expects exactly 1 argument"
                    raise ValueError(msg)
                logic = self._expect_symbol(args[0], "set-logic").name
                if logic not in _SUPPORTED_LOGICS:
                    msg = (
                        f"Unsupported logic {logic!r}; supported logics are: "
                        f"{', '.join(sorted(_SUPPORTED_LOGICS))}"
                    )
                    raise ValueError(msg)
                self._logic = logic
                return False, None
            case "set-option" | "set-info":
                return False, None
            case "declare-sort":
                if len(args) != 2:
                    msg = "declare-sort expects <symbol> <numeral>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "declare-sort")
                arity = self._parse_nonneg_int(args[1], "declare-sort")
                if arity != 0:
                    msg = (
                        f"Parameterized sort '{sym.name}' (arity {arity}) is not "
                        "supported"
                    )
                    raise ValueError(msg)
                if not sym.quoted and sym.name in ("Bool", "Int", "Real"):
                    msg = f"Cannot redeclare built-in sort '{sym.name}'"
                    raise ValueError(msg)
                if sym.name in self._sorts_stack[-1]:
                    msg = f"Sort {sym.name!r} already declared in current scope"
                    raise ValueError(msg)
                self._sorts_stack[-1][sym.name] = self.ctx.mk_uninterpreted_sort(
                    sym.name
                )
                return False, None
            case "declare-const":
                if len(args) != 2:
                    msg = "declare-const expects <symbol> <sort>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "declare-const")
                sort = self._resolve_sort(args[1], "declare-const")
                self._register_decl(sym.name, (), sort)
                return False, None
            case "declare-fun":
                if len(args) != 3:
                    msg = "declare-fun expects <symbol> (<sort>*) <sort>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "declare-fun")
                if not isinstance(args[1], tuple):
                    msg = "declare-fun domain must be a sort list"
                    raise ValueError(msg)
                domain = tuple(
                    self._resolve_sort(sort_sexpr, "declare-fun domain")
                    for sort_sexpr in args[1]
                )
                range_sort = self._resolve_sort(args[2], "declare-fun range")
                self._register_decl(sym.name, domain, range_sort)
                return False, None
            case "define-fun":
                if len(args) != 4:
                    msg = "define-fun expects <symbol> (<sorted-var>*) <sort> <term>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "define-fun")
                if not isinstance(args[1], tuple):
                    msg = "define-fun parameter list must be a list"
                    raise ValueError(msg)
                if args[1]:
                    msg = "Parameterized define-fun is not supported yet"
                    raise ValueError(msg)
                expected_sort = self._resolve_sort(args[2], "define-fun")
                if (
                    sym.name in self._decls_stack[-1]
                    or sym.name in self._defs_stack[-1]
                ):
                    msg = f"Symbol {sym.name!r} already defined in current scope"
                    raise ValueError(msg)
                body = self._parse_term(args[3], {})
                if body.sort is not expected_sort:
                    msg = (
                        f"define-fun '{sym.name}' body sort '{body.sort}' does not "
                        f"match declared sort '{expected_sort}'"
                    )
                    raise TypeError(msg)
                self._defs_stack[-1][sym.name] = body
                return False, None
            case "assert":
                if len(args) != 1:
                    msg = "assert expects exactly 1 formula"
                    raise ValueError(msg)
                self.solver.add(self._parse_term(args[0], {}))
                return False, None
            case "check-sat":
                if args:
                    msg = "check-sat takes no arguments"
                    raise ValueError(msg)
                return False, self._format_verdict(self.solver.check())
            case "check-sat-assuming":
                if len(args) != 1 or not isinstance(args[0], tuple):
                    msg = "check-sat-assuming expects a list of assumptions"
                    raise ValueError(msg)
                assumps = [self._parse_term(item, {}) for item in args[0]]
                return False, self._format_verdict(self.solver.check(*assumps))
            case "get-model":
                if args:
                    msg = "get-model takes no arguments"
                    raise ValueError(msg)
                return False, format_smt2_model(
                    self.solver.model(), decls=self.declared_decls()
                )
            case "get-value":
                if len(args) != 1 or not isinstance(args[0], tuple) or not args[0]:
                    msg = "get-value expects a non-empty list of terms"
                    raise ValueError(msg)
                model = self.solver.model()
                pairs = []
                for item in args[0]:
                    term = self._parse_term(item, {})
                    val = model.eval(term, model_completion=True)
                    pairs.append(f"({format_expr(term)} {format_expr(val)})")
                return False, "(" + " ".join(pairs) + ")"
            case "push":
                levels = 1 if not args else self._parse_nonneg_int(args[0], "push")
                if len(args) > 1:
                    msg = "push accepts at most 1 argument"
                    raise ValueError(msg)
                for _ in range(levels):
                    self.solver.push()
                    self._sorts_stack.append({})
                    self._decls_stack.append({})
                    self._defs_stack.append({})
                    self._declared_order.append([])
                return False, None
            case "pop":
                levels = 1 if not args else self._parse_nonneg_int(args[0], "pop")
                if len(args) > 1:
                    msg = "pop accepts at most 1 argument"
                    raise ValueError(msg)
                self.solver.pop(levels)
                for _ in range(levels):
                    self._sorts_stack.pop()
                    self._decls_stack.pop()
                    self._defs_stack.pop()
                    self._declared_order.pop()
                return False, None
            case "reset":
                if args:
                    msg = "reset takes no arguments"
                    raise ValueError(msg)
                self.ctx = Context()
                self.solver = SMTSolver(self.ctx)
                self._sorts_stack = [{}]
                self._decls_stack = [{}]
                self._defs_stack = [{}]
                self._declared_order = [[]]
                self._logic = None
                return False, None
            case "reset-assertions":
                if args:
                    msg = "reset-assertions takes no arguments"
                    raise ValueError(msg)
                self.solver.reset()
                self._sorts_stack = [self._sorts_stack[0]]
                self._decls_stack = [self._decls_stack[0]]
                self._defs_stack = [self._defs_stack[0]]
                self._declared_order = [self._declared_order[0]]
                return False, None
            case "exit":
                if args:
                    msg = "exit takes no arguments"
                    raise ValueError(msg)
                return True, None
            case _:
                msg = f"Unsupported SMT-LIB2 command: {name!r}"
                raise ValueError(msg)

    def _register_decl(
        self,
        name: str,
        domain: tuple[Sort, ...],
        range_sort: Sort,
    ) -> FuncDecl:
        if name in self._decls_stack[-1] or name in self._defs_stack[-1]:
            msg = f"Symbol {name!r} already declared in current scope"
            raise ValueError(msg)
        decl = self.ctx.mk_decl(name, domain, range_sort)
        self._decls_stack[-1][name] = decl
        self._declared_order[-1].append(decl)
        return decl

    def _format_verdict(self, verdict: SolveResult) -> str:
        if verdict is SolveResult.SAT:
            return "sat"
        if verdict is SolveResult.UNSAT:
            return "unsat"
        return "unknown"

    def _coerce_call_args(self, parsed: list[Expr], decl: FuncDecl) -> list[Expr]:
        if len(parsed) != decl.arity:
            return parsed
        return [
            self.ctx.mk_to_real(arg)
            if isinstance(arg, Const) and arg.is_int and exp.is_real
            else arg
            for arg, exp in zip(parsed, decl.domain, strict=True)
        ]

    def _coerce_int_literals_for_real(self, exprs: list[Expr]) -> list[Expr]:
        if not any(item.is_real for item in exprs):
            return exprs
        return [
            self.ctx.mk_to_real(item)
            if isinstance(item, Const) and item.is_int
            else item
            for item in exprs
        ]

    def _parse_term(self, sexpr: SExpr, local_env: dict[str, Expr]) -> Expr:
        if isinstance(sexpr, _BVLiteral):
            return self.ctx.mk_bv_val(sexpr.value, sexpr.width)

        if isinstance(sexpr, _Symbol):
            if not sexpr.quoted:
                if sexpr.name == "true":
                    return self.ctx.mk_true()
                if sexpr.name == "false":
                    return self.ctx.mk_false()
                if sexpr.name.isdigit():
                    if self._logic in (
                        "QF_LRA",
                        "QF_UFLRA",
                        "QF_ALRA",
                        "QF_AUFLRA",
                        "LRA",
                        "UFLRA",
                        "ALRA",
                        "AUFLRA",
                    ):
                        return self.ctx.mk_real_val(sexpr.name)
                    return self.ctx.mk_int_val(int(sexpr.name))
                if _is_decimal_token(sexpr.name):
                    return self.ctx.mk_real_val(sexpr.name)
            if sexpr.name in local_env:
                return local_env[sexpr.name]
            defined = self._lookup_def(sexpr.name)
            if defined is not None:
                return defined
            decl = self._lookup_decl(sexpr.name)
            if decl is not None:
                if decl.arity != 0:
                    msg = (
                        f"Line {sexpr.line}, col {sexpr.col}: function {sexpr.name!r} "
                        f"of arity {decl.arity} requires arguments"
                    )
                    raise ValueError(msg)
                return decl()
            msg = (
                f"Line {sexpr.line}, col {sexpr.col}: "
                f"undeclared identifier {sexpr.name!r}"
            )
            raise ValueError(msg)

        if not isinstance(sexpr, tuple) or not sexpr:
            msg = f"Invalid SMT-LIB2 term: {sexpr!r}"
            raise ValueError(msg)

        if isinstance(sexpr[0], tuple):
            return self._parse_compound_head_term(sexpr[0], sexpr[1:], local_env)

        head = self._expect_symbol(sexpr[0], "term operator")
        args = sexpr[1:]

        if head.quoted:
            decl = self._lookup_decl(head.name)
            if decl is not None:
                parsed = [self._parse_term(arg, local_env) for arg in args]
                return decl(*self._coerce_call_args(parsed, decl))
            msg = (
                f"Line {head.line}, col {head.col}: "
                f"unknown function application {head.name!r}"
            )
            raise ValueError(msg)

        op = head.name
        if op == "_":
            if len(args) == 2:
                bv_sym = self._expect_symbol(args[0], "indexed bitvector")
                if (
                    not bv_sym.quoted
                    and bv_sym.name.startswith("bv")
                    and bv_sym.name[2:].isdigit()
                ):
                    bv_val = int(bv_sym.name[2:])
                    bv_width = self._parse_nonneg_int(args[1], "(_ bv...)")
                    return self.ctx.mk_bv_val(bv_val, bv_width)
            msg = f"Unsupported indexed identifier: {sexpr!r}"
            raise ValueError(msg)
        if op == "!":
            if len(args) < 3 or len(args) % 2 == 0:
                msg = "Attribute term '(! <term> :kw <val> ...)' is malformed"
                raise ValueError(msg)
            for idx in range(1, len(args), 2):
                if not isinstance(args[idx], _Keyword):
                    msg = f"Expected attribute keyword in '!', got {args[idx]!r}"
                    raise ValueError(msg)
            return self._parse_term(args[0], local_env)

        if op == "let":
            if len(args) != 2 or not isinstance(args[0], tuple):
                msg = "let expects ((<var> <term>)*) <term>"
                raise ValueError(msg)
            bound: dict[str, Expr] = {}
            for binding in args[0]:
                if not isinstance(binding, tuple) or len(binding) != 2:
                    msg = f"Malformed let binding {binding!r}"
                    raise ValueError(msg)
                var_sym = self._expect_symbol(binding[0], "let binding variable")
                if var_sym.name in bound:
                    msg = f"Duplicate variable {var_sym.name!r} in let"
                    raise ValueError(msg)
                bound[var_sym.name] = self._parse_term(binding[1], local_env)
            merged_env = {**local_env, **bound}
            return self._parse_term(args[1], merged_env)

        if op in ("forall", "exists"):
            if len(args) != 2 or not isinstance(args[0], tuple) or not args[0]:
                msg = f"{op} expects ((<var> <sort>)+) <term>"
                raise ValueError(msg)
            q_bound: dict[str, Expr] = {}
            var_names: list[str] = []
            var_sorts: list[Sort] = []
            placeholders: list[App] = []
            for binding in args[0]:
                if not isinstance(binding, tuple) or len(binding) != 2:
                    msg = f"Malformed {op} binder {binding!r}"
                    raise ValueError(msg)
                var_sym = self._expect_symbol(binding[0], f"{op} binder variable")
                if var_sym.name in q_bound:
                    msg = f"Duplicate bound variable {var_sym.name!r} in {op}"
                    raise ValueError(msg)
                sort = self._resolve_sort(binding[1], f"{op} binder sort")
                while True:
                    self._qvar_seq += 1
                    ph_name = f"__smt2_qvar!{self._qvar_seq}"
                    if self._lookup_decl(ph_name) is None:
                        break
                placeholder = self.ctx.mk_const(ph_name, sort)
                q_bound[var_sym.name] = placeholder
                var_names.append(var_sym.name)
                var_sorts.append(sort)
                placeholders.append(placeholder)

            body_sexpr: SExpr = args[1]
            raw_patterns: list[tuple[SExpr, ...]] = []
            while (
                isinstance(body_sexpr, tuple)
                and body_sexpr
                and isinstance(body_sexpr[0], _Symbol)
                and not body_sexpr[0].quoted
                and body_sexpr[0].name == "!"
            ):
                ann_args = body_sexpr[1:]
                if len(ann_args) < 3 or len(ann_args) % 2 == 0:
                    msg = "Attribute term '(! <term> :kw <val> ...)' is malformed"
                    raise ValueError(msg)
                for idx in range(1, len(ann_args), 2):
                    kw = ann_args[idx]
                    if not isinstance(kw, _Keyword):
                        msg = f"Expected attribute keyword in '!', got {kw!r}"
                        raise ValueError(msg)
                    if kw.name == ":pattern":
                        pat_val = ann_args[idx + 1]
                        if not isinstance(pat_val, tuple) or not pat_val:
                            msg = "Expected non-empty term list after :pattern"
                            raise ValueError(msg)
                        raw_patterns.append(pat_val)
                body_sexpr = ann_args[0]

            merged_env = {**local_env, **q_bound}
            raw_body = self._parse_term(body_sexpr, merged_env)
            abs_body = abstract_vars(raw_body, placeholders)
            abs_patterns = tuple(
                tuple(
                    abstract_vars(self._parse_term(t, merged_env), placeholders)
                    for t in pat
                )
                for pat in raw_patterns
            )
            return self.ctx.mk_quantifier(
                op == "forall",
                var_names,
                var_sorts,
                abs_body,
                patterns=abs_patterns,
            )

        parsed = [self._parse_term(arg, local_env) for arg in args]
        match op:
            case "not":
                if len(parsed) != 1:
                    msg = "'not' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_not(parsed[0])
            case "and":
                if not parsed:
                    msg = "'and' expects at least 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_and(*parsed)
            case "or":
                if not parsed:
                    msg = "'or' expects at least 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_or(*parsed)
            case "=>":
                if len(parsed) < 2:
                    msg = "'=>' expects at least 2 arguments"
                    raise ValueError(msg)
                acc = parsed[-1]
                for item in reversed(parsed[:-1]):
                    acc = self.ctx.mk_implies(item, acc)
                return acc
            case "xor":
                if len(parsed) < 2:
                    msg = "'xor' expects at least 2 arguments"
                    raise ValueError(msg)
                acc = parsed[0]
                for item in parsed[1:]:
                    acc = self.ctx.mk_xor(acc, item)
                return acc
            case "=":
                if len(parsed) < 2:
                    msg = "'=' expects at least 2 arguments"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                if len(coerced) == 2:
                    return self.ctx.mk_eq(coerced[0], coerced[1])
                return self.ctx.mk_and(
                    *(
                        self.ctx.mk_eq(coerced[i], coerced[i + 1])
                        for i in range(len(coerced) - 1)
                    )
                )
            case "distinct":
                if len(parsed) < 2:
                    msg = "'distinct' expects at least 2 arguments"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                return self.ctx.mk_distinct(*coerced)
            case "ite":
                if len(parsed) != 3:
                    msg = "'ite' expects 3 arguments"
                    raise ValueError(msg)
                branches = self._coerce_int_literals_for_real([parsed[1], parsed[2]])
                return self.ctx.mk_ite(parsed[0], branches[0], branches[1])
            case "+":
                if not parsed:
                    msg = "'+' expects at least 1 argument"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                return coerced[0] if len(coerced) == 1 else self.ctx.mk_add(*coerced)
            case "-":
                if not parsed:
                    msg = "'-' expects at least 1 argument"
                    raise ValueError(msg)
                if len(parsed) == 1:
                    return self.ctx.mk_neg(parsed[0])
                coerced = self._coerce_int_literals_for_real(parsed)
                acc = coerced[0]
                for item in coerced[1:]:
                    acc = self.ctx.mk_sub(acc, item)
                return acc
            case "*":
                if not parsed:
                    msg = "'*' expects at least 1 argument"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                return coerced[0] if len(coerced) == 1 else self.ctx.mk_mul(*coerced)
            case "/":
                if len(parsed) < 2:
                    msg = "'/' expects at least 2 arguments"
                    raise ValueError(msg)
                real_args = [
                    self.ctx.mk_to_real(item)
                    if isinstance(item, Const) and item.is_int
                    else item
                    for item in parsed
                ]
                acc = real_args[0]
                for item in real_args[1:]:
                    acc = self.ctx.mk_div(acc, item)
                return acc
            case "<" | "<=" | ">" | ">=":
                if len(parsed) < 2:
                    msg = f"'{op}' expects at least 2 arguments"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                mk_cmp = (
                    self.ctx.mk_lt
                    if op == "<"
                    else self.ctx.mk_le
                    if op == "<="
                    else self.ctx.mk_gt
                    if op == ">"
                    else self.ctx.mk_ge
                )
                if len(coerced) == 2:
                    return mk_cmp(coerced[0], coerced[1])
                return self.ctx.mk_and(
                    *(
                        mk_cmp(coerced[i], coerced[i + 1])
                        for i in range(len(coerced) - 1)
                    )
                )
            case "to_real":
                if len(parsed) != 1:
                    msg = "'to_real' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_to_real(parsed[0])
            case "bvnot":
                if len(parsed) != 1:
                    msg = "'bvnot' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(parsed[0])
            case "bvneg":
                if len(parsed) != 1:
                    msg = "'bvneg' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_bv_neg(parsed[0])
            case "bvand":
                if len(parsed) < 2:
                    msg = "'bvand' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_and(*parsed)
            case "bvor":
                if len(parsed) < 2:
                    msg = "'bvor' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_or(*parsed)
            case "bvxor":
                if len(parsed) < 2:
                    msg = "'bvxor' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_xor(*parsed)
            case "bvnand":
                if len(parsed) != 2:
                    msg = "'bvnand' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(self.ctx.mk_bv_and(parsed[0], parsed[1]))
            case "bvnor":
                if len(parsed) != 2:
                    msg = "'bvnor' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(self.ctx.mk_bv_or(parsed[0], parsed[1]))
            case "bvxnor":
                if len(parsed) != 2:
                    msg = "'bvxnor' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(self.ctx.mk_bv_xor(parsed[0], parsed[1]))
            case "bvcomp":
                if len(parsed) != 2:
                    msg = "'bvcomp' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_ite(
                    self.ctx.mk_eq(parsed[0], parsed[1]),
                    self.ctx.mk_bv_val(1, 1),
                    self.ctx.mk_bv_val(0, 1),
                )
            case "bvadd":
                if len(parsed) < 2:
                    msg = "'bvadd' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_add(*parsed)
            case "bvsub":
                if len(parsed) != 2:
                    msg = "'bvsub' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sub(parsed[0], parsed[1])
            case "bvmul":
                if len(parsed) < 2:
                    msg = "'bvmul' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_mul(*parsed)
            case "bvudiv":
                if len(parsed) != 2:
                    msg = "'bvudiv' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_udiv(parsed[0], parsed[1])
            case "bvurem":
                if len(parsed) != 2:
                    msg = "'bvurem' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_urem(parsed[0], parsed[1])
            case "bvsdiv":
                if len(parsed) != 2:
                    msg = "'bvsdiv' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sdiv(parsed[0], parsed[1])
            case "bvsrem":
                if len(parsed) != 2:
                    msg = "'bvsrem' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_srem(parsed[0], parsed[1])
            case "bvsmod":
                if len(parsed) != 2:
                    msg = "'bvsmod' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_smod(parsed[0], parsed[1])
            case "bvshl":
                if len(parsed) != 2:
                    msg = "'bvshl' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_shl(parsed[0], parsed[1])
            case "bvlshr":
                if len(parsed) != 2:
                    msg = "'bvlshr' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_lshr(parsed[0], parsed[1])
            case "bvashr":
                if len(parsed) != 2:
                    msg = "'bvashr' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ashr(parsed[0], parsed[1])
            case "bvult":
                if len(parsed) != 2:
                    msg = "'bvult' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ult(parsed[0], parsed[1])
            case "bvule":
                if len(parsed) != 2:
                    msg = "'bvule' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ule(parsed[0], parsed[1])
            case "bvugt":
                if len(parsed) != 2:
                    msg = "'bvugt' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ugt(parsed[0], parsed[1])
            case "bvuge":
                if len(parsed) != 2:
                    msg = "'bvuge' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_uge(parsed[0], parsed[1])
            case "bvslt":
                if len(parsed) != 2:
                    msg = "'bvslt' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_slt(parsed[0], parsed[1])
            case "bvsle":
                if len(parsed) != 2:
                    msg = "'bvsle' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sle(parsed[0], parsed[1])
            case "bvsgt":
                if len(parsed) != 2:
                    msg = "'bvsgt' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sgt(parsed[0], parsed[1])
            case "bvsge":
                if len(parsed) != 2:
                    msg = "'bvsge' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sge(parsed[0], parsed[1])
            case "concat":
                if len(parsed) < 2:
                    msg = "'concat' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_concat(*parsed)
            case "select":
                if len(parsed) != 2:
                    msg = "'select' expects 2 arguments"
                    raise ValueError(msg)
                arr, idx = parsed
                if (
                    arr.is_array
                    and arr.sort.index_sort.is_real
                    and isinstance(idx, Const)
                    and idx.is_int
                ):
                    idx = self.ctx.mk_to_real(idx)
                return self.ctx.mk_select(arr, idx)
            case "store":
                if len(parsed) != 3:
                    msg = "'store' expects 3 arguments"
                    raise ValueError(msg)
                arr, idx, val = parsed
                if arr.is_array:
                    if (
                        arr.sort.index_sort.is_real
                        and isinstance(idx, Const)
                        and idx.is_int
                    ):
                        idx = self.ctx.mk_to_real(idx)
                    if (
                        arr.sort.element_sort.is_real
                        and isinstance(val, Const)
                        and val.is_int
                    ):
                        val = self.ctx.mk_to_real(val)
                return self.ctx.mk_store(arr, idx, val)
            case _:
                decl = self._lookup_decl(op)
                if decl is not None:
                    return decl(*self._coerce_call_args(parsed, decl))
                msg = (
                    f"Line {head.line}, col {head.col}: "
                    f"unsupported operator or undeclared function {op!r}"
                )
                raise ValueError(msg)

    def _parse_compound_head_term(
        self,
        head_tuple: tuple[SExpr, ...],
        args: tuple[SExpr, ...],
        local_env: dict[str, Expr],
    ) -> Expr:
        if not head_tuple:
            msg = f"Invalid empty operator head in {head_tuple!r}"
            raise ValueError(msg)
        tag = self._expect_symbol(head_tuple[0], "compound operator")
        if not tag.quoted and tag.name == "as":
            if len(head_tuple) != 3 or len(args) != 1:
                msg = f"Malformed constant array application: ({head_tuple!r} ...)"
                raise ValueError(msg)
            const_sym = self._expect_symbol(head_tuple[1], "as const")
            if const_sym.quoted or const_sym.name != "const":
                msg = f"Unsupported qualified identifier '(as {const_sym.name} ...)'"
                raise ValueError(msg)
            sort = self._resolve_sort(head_tuple[2], "(as const <Sort>)")
            if not sort.is_array:
                msg = f"Expected Array sort in '(as const ...)', got '{sort}'"
                raise TypeError(msg)
            val = self._parse_term(args[0], local_env)
            if sort.element_sort.is_real and isinstance(val, Const) and val.is_int:
                val = self.ctx.mk_to_real(val)
            return self.ctx.mk_const_array(sort.index_sort, val)

        if not tag.quoted and tag.name == "_":
            if len(head_tuple) < 3 or len(args) != 1:
                msg = f"Unsupported indexed operator application: {head_tuple!r}"
                raise ValueError(msg)
            op_sym = self._expect_symbol(head_tuple[1], "indexed BV operator")
            if op_sym.quoted:
                msg = f"Unsupported quoted indexed operator {op_sym.name!r}"
                raise ValueError(msg)
            arg = self._parse_term(args[0], local_env)
            op_name = op_sym.name
            if op_name == "extract":
                if len(head_tuple) != 4:
                    msg = "'(_ extract hi lo)' expects 2 indices"
                    raise ValueError(msg)
                hi = self._parse_nonneg_int(head_tuple[2], "extract high")
                lo = self._parse_nonneg_int(head_tuple[3], "extract low")
                return self.ctx.mk_extract(hi, lo, arg)
            if len(head_tuple) != 3:
                msg = f"'(_ {op_name} n)' expects 1 index"
                raise ValueError(msg)
            param = self._parse_nonneg_int(head_tuple[2], op_name)
            match op_name:
                case "zero_extend":
                    return self.ctx.mk_zero_ext(param, arg)
                case "sign_extend":
                    return self.ctx.mk_sign_ext(param, arg)
                case "rotate_left":
                    return self.ctx.mk_rotate_left(param, arg)
                case "rotate_right":
                    return self.ctx.mk_rotate_right(param, arg)
                case "repeat":
                    return self.ctx.mk_repeat(param, arg)
                case _:
                    msg = f"Unsupported indexed operator '(_ {op_name} ...)'"
                    raise ValueError(msg)

        msg = f"Unsupported compound operator head: {head_tuple!r}"
        raise ValueError(msg)


def execute_smt2(text: str) -> tuple[list[str], dict[str, int]]:
    """Execute SMT-LIB2 script text and return outputs paired with solver stats."""
    runner = SMT2Runner()
    outputs = runner.execute(text)
    return outputs, runner.statistics()


def execute_smt2_file(path: str | Path) -> tuple[list[str], dict[str, int]]:
    """Read and execute a UTF-8 SMT-LIB2 file, returning outputs and stats."""
    text = Path(path).read_text(encoding="utf-8-sig")
    return execute_smt2(text)


def run_smt2(text: str) -> list[str]:
    """Execute SMT-LIB2 script text and return emitted response strings."""
    outputs, _ = execute_smt2(text)
    return outputs


def run_smt2_file(path: str | Path) -> list[str]:
    """Read and execute a UTF-8 SMT-LIB2 file and return emitted response strings."""
    outputs, _ = execute_smt2_file(path)
    return outputs
