"""Standalone exception hierarchy for ``unsat_legacy``."""


class LegacySolverError(Exception):
    """Base for every error raised by ``unsat_legacy``."""


class RuleSyntaxError(LegacySolverError, ValueError):
    """A rule, axiom, or formula string that could not be parsed."""


class SortMismatchError(LegacySolverError, TypeError):
    """A term used where a term of another sort was required."""


class ArityMismatchError(LegacySolverError, ValueError):
    """A function or predicate applied to the wrong number of arguments."""


class SolverStateError(LegacySolverError, RuntimeError):
    """The engine was asked for something its current state cannot give."""


class InternalError(LegacySolverError, RuntimeError):
    """An internal solver invariant did not hold."""


__all__ = [
    "ArityMismatchError",
    "InternalError",
    "LegacySolverError",
    "RuleSyntaxError",
    "SolverStateError",
    "SortMismatchError",
]
