"""Zero-dependency TPTP FOF parser, formatter, and solving helpers.

Depends on: ``syntax``, ``smt``, ``sat``.
"""

from dataclasses import dataclass
from pathlib import Path

from unsat.sat import SolveResult
from unsat.smt import SMTSolver
from unsat.syntax import (
    App,
    BoundVar,
    Const,
    Context,
    DeclKind,
    Expr,
    Quantifier,
    Sort,
)


class TPTPParseError(ValueError):
    """Error raised when TPTP FOF input is malformed."""

    def __init__(self, message: str, *, line: int = 1, column: int = 1) -> None:
        self.line = line
        self.column = column
        super().__init__(f"TPTP parse error at line {line}, column {column}: {message}")


@dataclass(frozen=True, slots=True)
class FofStatement:
    """Parsed TPTP ``fof(name, role, formula).`` annotated statement."""

    name: str
    role: str
    formula: Expr


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    value: str
    line: int
    column: int


_SINGLE_CHAR_TOKENS: dict[str, str] = {
    "(": "LPAREN",
    ")": "RPAREN",
    "[": "LBRACK",
    "]": "RBRACK",
    ",": "COMMA",
    ".": "DOT",
    ":": "COLON",
    "|": "OR",
    "&": "AND",
    "~": "NOT",
    "!": "FORALL",
    "?": "EXISTS",
    "=": "EQ",
}


def _is_word_cont(ch: str) -> bool:
    return ch.isascii() and (ch.isalnum() or ch == "_")


def _tokenize_tptp(text: str) -> list[_Token]:
    text = text.removeprefix("\ufeff")
    tokens: list[_Token] = []
    n = len(text)
    i = 0
    line = 1
    col = 1

    while i < n:
        ch = text[i]
        if ch == "\n":
            i += 1
            line += 1
            col = 1
            continue
        if ch.isspace():
            i += 1
            col += 1
            continue

        if ch == "%":
            while i < n and text[i] != "\n":
                i += 1
            continue

        if ch == "/" and i + 1 < n and text[i + 1] == "*":
            start_line, start_col = line, col
            i += 2
            col += 2
            closed = False
            while i < n:
                if text[i] == "*" and i + 1 < n and text[i + 1] == "/":
                    i += 2
                    col += 2
                    closed = True
                    break
                if text[i] == "\n":
                    i += 1
                    line += 1
                    col = 1
                else:
                    i += 1
                    col += 1
            if not closed:
                msg = "unterminated block comment"
                raise TPTPParseError(msg, line=start_line, column=start_col)
            continue

        if text.startswith("<=>", i):
            tokens.append(_Token("IFF", "<=>", line, col))
            i += 3
            col += 3
            continue

        if text.startswith("=>", i):
            tokens.append(_Token("IMPLIES", "=>", line, col))
            i += 2
            col += 2
            continue

        if text.startswith("!=", i):
            tokens.append(_Token("NEQ", "!=", line, col))
            i += 2
            col += 2
            continue

        single = _SINGLE_CHAR_TOKENS.get(ch)
        if single is not None:
            tokens.append(_Token(single, ch, line, col))
            i += 1
            col += 1
            continue

        if ch == "$":
            start_col = col
            j = i + 1
            while j < n and _is_word_cont(text[j]):
                j += 1
            word = text[i:j]
            if word == "$true":
                tokens.append(_Token("TRUE", word, line, start_col))
            elif word == "$false":
                tokens.append(_Token("FALSE", word, line, start_col))
            else:
                msg = f"unsupported TPTP system constant {word!r}"
                raise TPTPParseError(msg, line=line, column=start_col)
            col += j - i
            i = j
            continue

        if ch.isascii() and ch.isalpha():
            start_col = col
            j = i + 1
            while j < n and _is_word_cont(text[j]):
                j += 1
            word = text[i:j]
            kind = "LOWER_WORD" if ch.islower() else "UPPER_WORD"
            tokens.append(_Token(kind, word, line, start_col))
            col += j - i
            i = j
            continue

        if ch.isascii() and ch.isdigit():
            start_col = col
            j = i + 1
            while j < n and text[j].isascii() and text[j].isdigit():
                j += 1
            tokens.append(_Token("NUMBER", text[i:j], line, start_col))
            col += j - i
            i = j
            continue

        msg = f"unexpected character {ch!r}"
        raise TPTPParseError(msg, line=line, column=col)

    tokens.append(_Token("EOF", "", line, col))
    return tokens


class _TPTPParser:
    def __init__(
        self,
        tokens: list[_Token],
        ctx: Context,
        u_sort: Sort,
    ) -> None:
        self._tokens = tokens
        self._pos = 0
        self._ctx = ctx
        self._u_sort = u_sort

    def _peek(self) -> _Token:
        return self._tokens[self._pos]

    def _advance(self) -> _Token:
        tok = self._tokens[self._pos]
        self._pos += 1
        return tok

    def _expect(self, kind: str, *, expected: str | None = None) -> _Token:
        tok = self._peek()
        if tok.kind != kind:
            desc = expected or kind
            found = "end of input" if tok.kind == "EOF" else repr(tok.value)
            msg = f"expected {desc}, got {found}"
            raise TPTPParseError(msg, line=tok.line, column=tok.column)
        self._pos += 1
        return tok

    def parse_all(self) -> list[FofStatement]:
        statements: list[FofStatement] = []
        while self._peek().kind != "EOF":
            statements.append(self.parse_statement())
        return statements

    def parse_single_statement(self) -> FofStatement:
        tok = self._peek()
        if tok.kind == "EOF":
            msg = "expected TPTP fof statement, got empty input"
            raise TPTPParseError(msg, line=tok.line, column=tok.column)
        stmt = self.parse_statement()
        trailing = self._peek()
        if trailing.kind != "EOF":
            msg = f"unexpected trailing token {trailing.value!r} after fof statement"
            raise TPTPParseError(msg, line=trailing.line, column=trailing.column)
        return stmt

    def parse_statement(self) -> FofStatement:
        head = self._expect("LOWER_WORD", expected="'fof'")
        if head.value != "fof":
            msg = f"expected 'fof' annotated formula, got {head.value!r}"
            raise TPTPParseError(msg, line=head.line, column=head.column)
        self._expect("LPAREN", expected="'('")
        name_tok = self._peek()
        if name_tok.kind in ("LOWER_WORD", "NUMBER"):
            self._advance()
        else:
            found = "end of input" if name_tok.kind == "EOF" else repr(name_tok.value)
            msg = f"expected formula name, got {found}"
            raise TPTPParseError(msg, line=name_tok.line, column=name_tok.column)
        self._expect("COMMA", expected="','")
        role_tok = self._expect("LOWER_WORD", expected="formula role")
        self._expect("COMMA", expected="','")
        formula = self._parse_formula()
        self._expect("RPAREN", expected="')'")
        self._expect("DOT", expected="'.'")
        return FofStatement(name=name_tok.value, role=role_tok.value, formula=formula)

    def _parse_formula(self) -> Expr:
        lhs = self._parse_or()
        tok = self._peek()
        if tok.kind == "IMPLIES":
            self._advance()
            rhs = self._parse_formula()
            return self._ctx.mk_implies(lhs, rhs)
        if tok.kind == "IFF":
            self._advance()
            rhs = self._parse_or()
            return self._ctx.mk_eq(lhs, rhs)
        return lhs

    def _parse_or(self) -> Expr:
        operands = [self._parse_and()]
        while self._peek().kind == "OR":
            self._advance()
            operands.append(self._parse_and())
        if len(operands) == 1:
            return operands[0]
        return self._ctx.mk_or(*operands)

    def _parse_and(self) -> Expr:
        operands = [self._parse_unary()]
        while self._peek().kind == "AND":
            self._advance()
            operands.append(self._parse_unary())
        if len(operands) == 1:
            return operands[0]
        return self._ctx.mk_and(*operands)

    def _parse_unary(self) -> Expr:
        tok = self._peek()
        if tok.kind == "NOT":
            self._advance()
            return self._ctx.mk_not(self._parse_unary())
        if tok.kind in ("FORALL", "EXISTS"):
            self._advance()
            self._expect("LBRACK", expected="'['")
            var_names: list[str] = []
            seen: set[str] = set()
            while True:
                vtok = self._expect("UPPER_WORD", expected="quantified variable")
                if vtok.value in seen:
                    msg = f"duplicate bound variable {vtok.value!r} in quantifier"
                    raise TPTPParseError(msg, line=vtok.line, column=vtok.column)
                seen.add(vtok.value)
                var_names.append(vtok.value)
                if self._peek().kind != "COMMA":
                    break
                self._advance()
            self._expect("RBRACK", expected="']'")
            self._expect("COLON", expected="':'")
            body = self._parse_unary()
            var_exprs = [self._ctx.mk_const(name, self._u_sort) for name in var_names]
            if tok.kind == "FORALL":
                return self._ctx.mk_forall(var_exprs, body)
            return self._ctx.mk_exists(var_exprs, body)
        if tok.kind == "LPAREN":
            self._advance()
            inner = self._parse_formula()
            self._expect("RPAREN", expected="')'")
            return inner
        return self._parse_atomic()

    def _parse_atomic(self) -> Expr:
        tok = self._peek()
        if tok.kind == "TRUE":
            self._advance()
            return self._ctx.mk_true()
        if tok.kind == "FALSE":
            self._advance()
            return self._ctx.mk_false()
        if tok.kind == "UPPER_WORD":
            self._advance()
            lhs = self._ctx.mk_const(tok.value, self._u_sort)
            op = self._peek()
            if op.kind not in ("EQ", "NEQ"):
                msg = f"unexpected variable {tok.value!r} in formula position"
                raise TPTPParseError(msg, line=tok.line, column=tok.column)
            self._advance()
            rhs = self._parse_term()
            eq = self._ctx.mk_eq(lhs, rhs)
            return eq if op.kind == "EQ" else self._ctx.mk_not(eq)
        if tok.kind == "LOWER_WORD":
            functor, args = self._parse_plain_term()
            op = self._peek()
            if op.kind in ("EQ", "NEQ"):
                lhs = self._mk_term_app(functor, args)
                self._advance()
                rhs = self._parse_term()
                eq = self._ctx.mk_eq(lhs, rhs)
                return eq if op.kind == "EQ" else self._ctx.mk_not(eq)
            decl = self._ctx.mk_decl(
                functor, tuple(arg.sort for arg in args), self._ctx.bool_sort
            )
            return self._ctx.mk_app(decl, *args)
        found = "end of input" if tok.kind == "EOF" else repr(tok.value)
        msg = f"expected atomic formula, got {found}"
        raise TPTPParseError(msg, line=tok.line, column=tok.column)

    def _parse_plain_term(self) -> tuple[str, tuple[Expr, ...]]:
        head = self._expect("LOWER_WORD", expected="functor")
        if self._peek().kind != "LPAREN":
            return head.value, ()
        self._advance()
        args = [self._parse_term()]
        while self._peek().kind == "COMMA":
            self._advance()
            args.append(self._parse_term())
        self._expect("RPAREN", expected="')'")
        return head.value, tuple(args)

    def _parse_term(self) -> Expr:
        tok = self._peek()
        if tok.kind == "UPPER_WORD":
            self._advance()
            return self._ctx.mk_const(tok.value, self._u_sort)
        if tok.kind == "LOWER_WORD":
            functor, args = self._parse_plain_term()
            return self._mk_term_app(functor, args)
        found = "end of input" if tok.kind == "EOF" else repr(tok.value)
        msg = f"expected term, got {found}"
        raise TPTPParseError(msg, line=tok.line, column=tok.column)

    def _mk_term_app(self, functor: str, args: tuple[Expr, ...]) -> Expr:
        decl = self._ctx.mk_decl(functor, tuple(arg.sort for arg in args), self._u_sort)
        return self._ctx.mk_app(decl, *args)


def parse_fof(
    text: str,
    ctx: Context | None = None,
    *,
    sort_name: str = "U",
) -> tuple[str, str, Expr]:
    """Parse one TPTP ``fof(name, role, formula).`` statement.

    Returns ``(name, role, formula)``.
    """
    if not isinstance(text, str):
        msg = "expected TPTP fof statement as a string"
        raise TPTPParseError(msg)
    if not sort_name:
        msg = "sort_name cannot be empty"
        raise ValueError(msg)
    target_ctx = Context() if ctx is None else ctx
    u_sort = target_ctx.mk_uninterpreted_sort(sort_name)
    tokens = _tokenize_tptp(text)
    stmt = _TPTPParser(tokens, target_ctx, u_sort).parse_single_statement()
    return stmt.name, stmt.role, stmt.formula


def parse_tptp(
    text: str,
    ctx: Context | None = None,
    *,
    sort_name: str = "U",
) -> list[FofStatement]:
    """Parse zero or more TPTP ``fof(...)`` statements."""
    if not isinstance(text, str):
        msg = "expected TPTP script as a string"
        raise TPTPParseError(msg)
    if not sort_name:
        msg = "sort_name cannot be empty"
        raise ValueError(msg)
    target_ctx = Context() if ctx is None else ctx
    u_sort = target_ctx.mk_uninterpreted_sort(sort_name)
    tokens = _tokenize_tptp(text)
    return _TPTPParser(tokens, target_ctx, u_sort).parse_all()


def parse_tptp_file(
    path: str | Path,
    ctx: Context | None = None,
    *,
    sort_name: str = "U",
) -> list[FofStatement]:
    """Read and parse a TPTP FOF file from ``path``."""
    text = Path(path).read_text(encoding="utf-8-sig")
    return parse_tptp(text, ctx=ctx, sort_name=sort_name)


def _format_tptp_node(expr: Expr, bound_names: tuple[str, ...]) -> str:
    if isinstance(expr, Const):
        if expr.is_bool:
            return "$true" if expr.value else "$false"
        return str(expr.value)
    if isinstance(expr, BoundVar):
        if 0 <= expr.index < len(bound_names):
            return bound_names[-1 - expr.index]
        return f"V{expr.index}"
    if isinstance(expr, Quantifier):
        quant = "!" if expr.is_forall else "?"
        vars_str = ", ".join(expr.var_names)
        body_str = _format_tptp_node(expr.body, bound_names + expr.var_names)
        return f"({quant} [{vars_str}] : {body_str})"
    if isinstance(expr, App):
        kind = expr.decl.kind
        if kind is DeclKind.AND:
            inner = " & ".join(_format_tptp_node(arg, bound_names) for arg in expr.args)
            return f"({inner})"
        if kind is DeclKind.OR:
            inner = " | ".join(_format_tptp_node(arg, bound_names) for arg in expr.args)
            return f"({inner})"
        if kind is DeclKind.IMPLIES:
            lhs = _format_tptp_node(expr.args[0], bound_names)
            rhs = _format_tptp_node(expr.args[1], bound_names)
            return f"({lhs} => {rhs})"
        if kind is DeclKind.NOT:
            return f"~{_format_tptp_node(expr.args[0], bound_names)}"
        if kind is DeclKind.EQ:
            lhs = _format_tptp_node(expr.args[0], bound_names)
            rhs = _format_tptp_node(expr.args[1], bound_names)
            op = "<=>" if expr.args[0].is_bool else "="
            return f"({lhs} {op} {rhs})"
        if kind is DeclKind.DISTINCT:
            if len(expr.args) == 2:
                lhs = _format_tptp_node(expr.args[0], bound_names)
                rhs = _format_tptp_node(expr.args[1], bound_names)
                return f"({lhs} != {rhs})"
            pairs = [
                f"({_format_tptp_node(expr.args[i], bound_names)} != "
                f"{_format_tptp_node(expr.args[j], bound_names)})"
                for i in range(len(expr.args))
                for j in range(i + 1, len(expr.args))
            ]
            return f"({' & '.join(pairs)})"
        if kind is DeclKind.UNINTERPRETED:
            if not expr.args:
                return expr.decl.name
            args_str = ", ".join(
                _format_tptp_node(arg, bound_names) for arg in expr.args
            )
            return f"{expr.decl.name}({args_str})"
        msg = f"Unsupported operator for TPTP FOF formatting: '{expr.decl.name}'"
        raise ValueError(msg)
    msg = f"Unsupported expression node for TPTP FOF formatting: {type(expr).__name__}"
    raise TypeError(msg)


def to_tptp_expr(expr: Expr) -> str:
    """Serialize a FOF :class:`Expr` body without an enclosing ``fof(...)`` wrapper."""
    return _format_tptp_node(expr, ())


def format_fof(name: str, role: str, expr: Expr) -> str:
    """Serialize ``expr`` as a complete ``fof(name, role, formula).`` statement."""
    return f"fof({name}, {role}, {to_tptp_expr(expr)})."


def solve_tptp(
    text: str,
    *,
    timeout: float | None = None,
    max_conflicts: int | None = None,
    max_quantifier_rounds: int | None = None,
    max_quantifier_matches: int | None = None,
) -> tuple[SolveResult, dict[str, int]]:
    """Parse and solve a TPTP FOF script (refuting any ``conjecture`` role)."""
    ctx = Context()
    stmts = parse_tptp(text, ctx=ctx)
    solver = SMTSolver(
        ctx,
        timeout=timeout,
        max_conflicts=max_conflicts,
        max_quantifier_rounds=max_quantifier_rounds,
        max_quantifier_matches=max_quantifier_matches,
    )
    for stmt in stmts:
        if stmt.role == "conjecture":
            solver.add(ctx.mk_not(stmt.formula))
        else:
            solver.add(stmt.formula)
    verdict = solver.check()
    return verdict, solver.statistics()


__all__ = [
    "FofStatement",
    "TPTPParseError",
    "format_fof",
    "parse_fof",
    "parse_tptp",
    "parse_tptp_file",
    "solve_tptp",
    "to_tptp_expr",
]
