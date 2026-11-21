"""Core types, literal encodings, statistics, and theory-hook protocols."""

from collections.abc import Sequence
from dataclasses import dataclass
from enum import StrEnum
from typing import Protocol, TypedDict

type Var = int
type Lit = int
type LBool = int

L_FALSE: LBool = -1
L_UNDEF: LBool = 0
L_TRUE: LBool = 1


def pos_lit(var: Var) -> Lit:
    """Return the positive literal for 0-indexed variable ``var``."""
    if var < 0:
        msg = f"Variable index must be non-negative, got {var}"
        raise ValueError(msg)
    return var << 1


def neg_lit(var: Var) -> Lit:
    """Return the negative literal for 0-indexed variable ``var``."""
    if var < 0:
        msg = f"Variable index must be non-negative, got {var}"
        raise ValueError(msg)
    return (var << 1) | 1


def negate(lit: Lit) -> Lit:
    """Return the logical negation of ``lit``."""
    if lit < 0:
        msg = f"Literal must be non-negative, got {lit}"
        raise ValueError(msg)
    return lit ^ 1


def lit_var(lit: Lit) -> Var:
    """Return the 0-indexed variable of ``lit``."""
    if lit < 0:
        msg = f"Literal must be non-negative, got {lit}"
        raise ValueError(msg)
    return lit >> 1


def lit_sign(lit: Lit) -> bool:
    """Return ``True`` when ``lit`` is negated and ``False`` when positive."""
    if lit < 0:
        msg = f"Literal must be non-negative, got {lit}"
        raise ValueError(msg)
    return bool(lit & 1)


def from_dimacs_lit(dimacs_lit: int) -> Lit:
    """Convert a signed 1-based DIMACS literal to an internal ``Lit``."""
    if dimacs_lit == 0:
        msg = "DIMACS literal cannot be 0"
        raise ValueError(msg)
    if dimacs_lit > 0:
        return pos_lit(dimacs_lit - 1)
    return neg_lit(-dimacs_lit - 1)


def to_dimacs_lit(lit: Lit) -> int:
    """Convert an internal ``Lit`` to a signed 1-based DIMACS literal."""
    if lit < 0:
        msg = f"Literal must be non-negative, got {lit}"
        raise ValueError(msg)
    var_1based = (lit >> 1) + 1
    return -var_1based if (lit & 1) else var_1based


class SolveResult(StrEnum):
    """Result of a satisfiability check."""

    SAT = "SAT"
    UNSAT = "UNSAT"
    UNKNOWN = "UNKNOWN"


@dataclass(slots=True)
class Clause:
    """Disjunction of literals stored in the SAT clause database."""

    literals: list[Lit]
    learned: bool = False
    lbd: int = 0
    activity: float = 0.0
    deleted: bool = False

    def __str__(self) -> str:
        return f"Clause({self.literals})"


class SATStats(TypedDict):
    """Counters recorded during SAT search."""

    conflicts: int
    decisions: int
    propagations: int
    restarts: int
    learned_clauses: int
    deleted_clauses: int
    theory_propagations: int
    theory_conflicts: int
    theory_lemmas: int


class TheoryPropagator(Protocol):
    """Integer-literal callback hook for online CDCL(T) theory integration."""

    def push(self) -> None:
        """Start a new decision level."""

    def pop(self, num_levels: int) -> None:
        """Backtrack ``num_levels`` decision levels."""

    def on_assign(self, lit: Lit) -> None:
        """Notify the theory that ``lit`` became true on the trail."""

    def propagate(self) -> tuple[Sequence[Lit], Sequence[Lit] | None]:
        """Run incremental theory propagation after SAT BCP reaches a fixed point.

        Returns ``(propagated_lits, conflict_clause)``. Each propagated literal
        must be entailed by the current trail. ``conflict_clause``, when not
        ``None``, is a falsified disjunction of literals explaining a conflict.
        """

    def explain_propagation(self, lit: Lit) -> Sequence[Lit]:
        """Lazily explain why ``lit`` was theory-propagated.

        Returns a valid clause containing ``lit`` where every other literal is
        currently false on the trail and was assigned before ``lit``.
        """

    def check(self) -> Sequence[Sequence[Lit]]:
        """Run a final full-assignment check, returning zero or more lemma clauses."""
