"""Base types, statistics, and protocol for background theory solvers.

Depends on: ``syntax``, ``model``.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Protocol

from unsat.model import Model
from unsat.syntax import Expr


@dataclass(frozen=True, slots=True)
class TheoryLit:
    """Signed theory literal consisting of an atomic expression and polarity."""

    atom: Expr
    sign: bool = True

    def negated(self) -> TheoryLit:
        """Return this theory literal with inverted polarity."""
        return TheoryLit(self.atom, not self.sign)


@dataclass(slots=True)
class EUFStats:
    """Instrumentation counters collected by an ``EUFSolver``."""

    merges: int = 0
    congruences: int = 0
    propagations: int = 0
    conflicts: int = 0
    explanations: int = 0
    checks: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "theory_merges": self.merges,
            "theory_congruences": self.congruences,
            "theory_euf_propagations": self.propagations,
            "theory_euf_conflicts": self.conflicts,
            "theory_explanations": self.explanations,
            "theory_checks": self.checks,
        }


@dataclass(slots=True)
class LRAStats:
    """Instrumentation counters collected by an ``LRASolver``."""

    pivots: int = 0
    bound_updates: int = 0
    propagations: int = 0
    conflicts: int = 0
    checks: int = 0
    gomory_cuts: int = 0
    branch_splits: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "theory_lra_pivots": self.pivots,
            "theory_lra_bound_updates": self.bound_updates,
            "theory_lra_propagations": self.propagations,
            "theory_lra_conflicts": self.conflicts,
            "theory_lra_checks": self.checks,
            "theory_lia_gomory_cuts": self.gomory_cuts,
            "theory_lia_branch_splits": self.branch_splits,
        }


@dataclass(slots=True)
class ArrayStats:
    """Instrumentation counters collected by an ``ArraySolver``."""

    row1_lemmas: int = 0
    row2_lemmas: int = 0
    const_lemmas: int = 0
    ext_lemmas: int = 0
    checks: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "theory_array_row1_lemmas": self.row1_lemmas,
            "theory_array_row2_lemmas": self.row2_lemmas,
            "theory_array_const_lemmas": self.const_lemmas,
            "theory_array_ext_lemmas": self.ext_lemmas,
            "theory_array_checks": self.checks,
        }


@dataclass(slots=True)
class BVStats:
    """Instrumentation counters collected by a :class:`BVSolver`."""

    propagations: int = 0
    conflicts: int = 0
    checks: int = 0
    word_models: int = 0
    blasted_atoms: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "theory_bv_propagations": self.propagations,
            "theory_bv_conflicts": self.conflicts,
            "theory_bv_checks": self.checks,
            "theory_bv_word_models": self.word_models,
            "theory_bv_blasted_atoms": self.blasted_atoms,
        }


@dataclass(slots=True)
class NLAStats:
    """Instrumentation counters collected by an :class:`NLASolver`."""

    checks: int = 0
    zero_lemmas: int = 0
    sign_lemmas: int = 0
    tangent_lemmas: int = 0
    icp_conflicts: int = 0
    sturm_lemmas: int = 0
    branch_splits: int = 0
    unknowns: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "theory_nla_checks": self.checks,
            "theory_nla_zero_lemmas": self.zero_lemmas,
            "theory_nla_sign_lemmas": self.sign_lemmas,
            "theory_nla_tangent_lemmas": self.tangent_lemmas,
            "theory_nla_icp_conflicts": self.icp_conflicts,
            "theory_nla_sturm_lemmas": self.sturm_lemmas,
            "theory_nla_branch_splits": self.branch_splits,
            "theory_nla_unknowns": self.unknowns,
        }


@dataclass(slots=True)
class StringStats:
    """Instrumentation counters collected by a :class:`StringSolver`."""

    checks: int = 0
    word_splits: int = 0
    length_lemmas: int = 0
    regex_lemmas: int = 0
    ext_lemmas: int = 0
    unknowns: int = 0

    def to_dict(self) -> dict[str, int]:
        """Return counters as a plain dictionary."""
        return {
            "theory_str_checks": self.checks,
            "theory_str_word_splits": self.word_splits,
            "theory_str_length_lemmas": self.length_lemmas,
            "theory_str_regex_lemmas": self.regex_lemmas,
            "theory_str_ext_lemmas": self.ext_lemmas,
            "theory_str_unknowns": self.unknowns,
        }


class TheorySolver(Protocol):
    """Protocol implemented by incremental congruence / background theory solvers."""

    def push(self) -> None:
        """Save the current assertion state onto the backtracking stack."""

    def pop(self, num_levels: int = 1) -> None:
        """Restore the assertion state by popping ``num_levels`` frames."""

    def register_term(self, term: Expr) -> None:
        """Register ``term`` and its uninterpreted subterms with the theory solver."""

    def register_eq(self, atom: Expr) -> None:
        """Register an equality atom ``lhs = rhs`` for propagation and checks."""

    def register_bool_term(self, term: Expr) -> None:
        """Register a Boolean-sorted term (e.g., predicate app) for propagation."""

    def assert_atom(self, atom: Expr, polarity: bool) -> None:
        """Assert ``atom`` with truth value ``polarity`` at the current level."""

    def propagate(
        self,
    ) -> tuple[Sequence[tuple[Expr, bool]], Sequence[TheoryLit] | None]:
        """Process pending assertions, returning ``(propagations, conflict)``."""

    def explain_propagation(self, atom: Expr, polarity: bool) -> Sequence[TheoryLit]:
        """Return asserted ``TheoryLit`` reasons entailing ``(atom, polarity)``."""

    def explain_conflict(self) -> Sequence[TheoryLit]:
        """Return asserted ``TheoryLit`` reasons for the current theory conflict."""

    def check(self) -> Sequence[Sequence[TheoryLit]]:
        """Perform a final consistency check, returning any blocking lemmas."""

    def build_model(self) -> Model:
        """Construct a finite-domain ``Model`` for the current satisfiable state."""
