"""DIMACS CNF parser, solver helper, and result formatter."""

import math
import time
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from unsat.sat import (
    Lit,
    SATSolver,
    SATStats,
    SolveResult,
    Var,
    from_dimacs_lit,
)


@dataclass(frozen=True, slots=True)
class DimacsCNF:
    """Parsed DIMACS CNF instance."""

    num_vars: int
    declared_clauses: int
    clauses: tuple[tuple[Lit, ...], ...]


def parse_dimacs(text: str) -> DimacsCNF:
    """Parse DIMACS CNF text into a :class:`DimacsCNF`."""
    text = text.removeprefix("\ufeff")
    num_vars: int | None = None
    declared_clauses = 0
    clauses: list[tuple[Lit, ...]] = []
    current_clause: list[Lit] = []

    for line_no, raw_line in enumerate(text.splitlines(), start=1):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        if stripped.startswith("%"):
            break
        if stripped.startswith("p"):
            if num_vars is not None:
                msg = f"Line {line_no}: duplicate problem header"
                raise ValueError(msg)
            parts = stripped.split()
            if len(parts) != 4 or parts[1] != "cnf":
                msg = f"Line {line_no}: invalid DIMACS header {stripped!r}"
                raise ValueError(msg)
            try:
                parsed_vars = int(parts[2])
                parsed_clauses = int(parts[3])
            except ValueError as exc:
                msg = f"Line {line_no}: non-integer counts in header {stripped!r}"
                raise ValueError(msg) from exc
            if parsed_vars < 0 or parsed_clauses < 0:
                msg = f"Line {line_no}: negative counts in header {stripped!r}"
                raise ValueError(msg)
            num_vars = parsed_vars
            declared_clauses = parsed_clauses
            continue

        if num_vars is None:
            msg = f"Line {line_no}: clause data before 'p cnf' header"
            raise ValueError(msg)

        for token in stripped.split():
            try:
                val = int(token)
            except ValueError as exc:
                msg = f"Line {line_no}: invalid integer token {token!r}"
                raise ValueError(msg) from exc

            if val == 0:
                clauses.append(tuple(current_clause))
                current_clause.clear()
                continue

            if abs(val) > num_vars:
                msg = f"Line {line_no}: literal {val} exceeds declared num_vars={num_vars}"
                raise ValueError(msg)
            current_clause.append(from_dimacs_lit(val))

    if num_vars is None:
        msg = "Missing 'p cnf <num_vars> <num_clauses>' header"
        raise ValueError(msg)
    if current_clause:
        msg = "Unterminated trailing clause (missing '0')"
        raise ValueError(msg)

    return DimacsCNF(
        num_vars=num_vars,
        declared_clauses=declared_clauses,
        clauses=tuple(clauses),
    )


def parse_dimacs_file(path: str | Path) -> DimacsCNF:
    """Read and parse a UTF-8 DIMACS CNF file from ``path``."""
    text = Path(path).read_text(encoding="utf-8-sig")
    return parse_dimacs(text)


def solve_dimacs(
    cnf: DimacsCNF,
    *,
    timeout: float | None = None,
    max_conflicts: int | None = None,
) -> tuple[SolveResult, dict[Var, bool] | None, SATStats]:
    """Solve a parsed :class:`DimacsCNF` with :class:`SATSolver`."""
    if timeout is not None and (math.isnan(timeout) or timeout < 0):
        msg = f"timeout must be non-negative, got {timeout}"
        raise ValueError(msg)
    if max_conflicts is not None and max_conflicts < 0:
        msg = f"max_conflicts must be non-negative, got {max_conflicts}"
        raise ValueError(msg)
    solver = SATSolver()
    solver.ensure_vars(cnf.num_vars)
    for clause in cnf.clauses:
        solver.add_clause(clause)
    deadline = None if timeout is None else time.monotonic() + timeout
    result = solver.solve(max_conflicts=max_conflicts, deadline=deadline)
    model = solver.model() if result is SolveResult.SAT else None
    return result, model, solver.statistics()


def format_dimacs_result(
    result: SolveResult,
    model: Mapping[Var, bool] | None = None,
    num_vars: int = 0,
) -> str:
    """Format a SAT result (and model when satisfiable) in DIMACS output format."""
    if result is SolveResult.UNSAT:
        return "s UNSATISFIABLE"
    if result is SolveResult.UNKNOWN:
        return "s UNKNOWN"

    if model is None and num_vars > 0:
        msg = "A model is required to format a SATISFIABLE result with variables"
        raise ValueError(msg)

    assignments = model or {}
    tokens = [str(var + 1 if assignments.get(var, False) else -(var + 1)) for var in range(num_vars)]
    tokens.append("0")
    return "s SATISFIABLE\nv " + " ".join(tokens)
