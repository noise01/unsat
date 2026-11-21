"""Structural sort and declaration kind enumerations."""

from enum import StrEnum


class SortKind(StrEnum):
    """Built-in and user-declared sort categories."""

    BOOL = "Bool"
    INT = "Int"
    REAL = "Real"
    UNINTERPRETED = "Uninterpreted"


class DeclKind(StrEnum):
    """Structural operator kinds distinguishing built-ins from user symbols."""

    UNINTERPRETED = "uninterpreted"
    NOT = "not"
    AND = "and"
    OR = "or"
    IMPLIES = "implies"
    XOR = "xor"
    EQ = "="
    DISTINCT = "distinct"
    ITE = "ite"
    NEG = "neg"
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"
    LT = "<"
    LE = "<="
    GT = ">"
    GE = ">="
    TO_REAL = "to_real"
