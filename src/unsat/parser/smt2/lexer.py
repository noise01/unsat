"""SMT-LIB2 lexer and S-expression parser."""

from collections.abc import Sequence
from dataclasses import dataclass

type SExpr = _Atom | tuple[SExpr, ...]

_SIMPLE_SYMBOL_CHARS = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~!@$%^&*_-+=<>.?/")
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
                msg = f"Line {start_line}, col {start_col}: unterminated quoted symbol '|...|'"
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
