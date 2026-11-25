"""Curated benchmark suite runner for ``unsat``."""

from __future__ import annotations

import argparse
import importlib
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from unsat.parser import execute_smt2, parse_dimacs, solve_dimacs
from unsat.sat import SolveResult

_ROOT = Path(__file__).resolve().parent
_DIMACS_STATUS_RE = re.compile(
    r"^c\s+status:\s*(sat|unsat|unknown)\b", re.IGNORECASE | re.MULTILINE
)
_SMT2_STATUS_RE = re.compile(
    r"\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)", re.IGNORECASE
)


@dataclass(frozen=True, slots=True)
class BenchmarkResult:
    """Execution record for a single benchmark file."""

    rel_path: str
    group: str
    expected: str
    verdict: str
    elapsed_ms: float
    conflicts: int
    z3_verdict: str | None = None

    @property
    def ok(self) -> bool:
        if self.verdict != self.expected:
            return False
        return self.z3_verdict is None or self.z3_verdict == self.verdict


def _extract_expected_status(path: Path, text: str) -> str:
    pattern = _DIMACS_STATUS_RE if path.suffix == ".cnf" else _SMT2_STATUS_RE
    match = pattern.search(text)
    if match is None:
        return "unknown"
    return match.group(1).lower()


def _group_name(path: Path) -> str:
    rel = path.relative_to(_ROOT)
    if rel.parts[0] == "dimacs":
        return "dimacs"
    if len(rel.parts) >= 3 and rel.parts[0] == "smt2":
        return rel.parts[1]
    return rel.parts[0]


def _discover_benchmarks(logic: str | None, pattern: str | None) -> list[Path]:
    files = sorted([*_ROOT.rglob("*.cnf"), *_ROOT.rglob("*.smt2")])
    selected: list[Path] = []
    for path in files:
        group = _group_name(path)
        if logic is not None and group.lower() != logic.lower():
            continue
        rel = path.relative_to(_ROOT).as_posix()
        if pattern is not None and pattern.lower() not in rel.lower():
            continue
        selected.append(path)
    return selected


def _strip_script_commands_for_z3(text: str) -> str:
    drop_prefixes = (
        "(check-sat",
        "(get-unsat-core",
        "(get-model",
        "(get-assertions",
        "(get-value",
        "(echo",
        "(exit",
    )
    kept_lines: list[str] = []
    for line in text.splitlines():
        if line.strip().startswith(drop_prefixes):
            continue
        kept_lines.append(line)
    return "\n".join(kept_lines) + "\n"


def _run_z3_check(path: Path, text: str, timeout: float, z3_mod: Any) -> str:
    solver = z3_mod.Solver()
    solver.set("timeout", max(1, int(timeout * 1000)))
    if path.suffix == ".cnf":
        cnf = parse_dimacs(text)
        vars_map = [z3_mod.Bool(f"v_{i + 1}") for i in range(cnf.num_vars)]
        for clause in cnf.clauses:
            solver.add(
                z3_mod.Or(
                    *(
                        vars_map[lit >> 1]
                        if (lit & 1) == 0
                        else z3_mod.Not(vars_map[lit >> 1])
                        for lit in clause
                    )
                )
            )
    else:
        solver.from_string(_strip_script_commands_for_z3(text))
    z3_res = solver.check()
    if z3_res == z3_mod.sat:
        return "sat"
    if z3_res == z3_mod.unsat:
        return "unsat"
    return "unknown"


def _run_benchmark(path: Path, timeout: float, z3_mod: Any | None) -> BenchmarkResult:
    text = path.read_text(encoding="utf-8-sig")
    expected = _extract_expected_status(path, text)
    t0 = time.perf_counter()
    if path.suffix == ".cnf":
        cnf = parse_dimacs(text)
        res, _, stats = solve_dimacs(cnf, timeout=timeout)
        verdict = (
            "sat"
            if res is SolveResult.SAT
            else "unsat"
            if res is SolveResult.UNSAT
            else "unknown"
        )
    else:
        outputs, stats = execute_smt2(text, timeout=timeout)
        verdict = next(
            (line for line in outputs if line in ("sat", "unsat", "unknown")),
            "unknown",
        )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    conflicts = int(stats.get("conflicts", 0))
    z3_verdict = (
        _run_z3_check(path, text, timeout, z3_mod) if z3_mod is not None else None
    )
    return BenchmarkResult(
        rel_path=path.relative_to(_ROOT).as_posix(),
        group=_group_name(path),
        expected=expected,
        verdict=verdict,
        elapsed_ms=elapsed_ms,
        conflicts=conflicts,
        z3_verdict=z3_verdict,
    )


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI parser for ``benchmarks/run.py``."""
    parser = argparse.ArgumentParser(
        description="Run the curated unsat benchmark suite."
    )
    parser.add_argument(
        "--logic",
        help="Filter by benchmark group/logic (e.g. dimacs, qf_bv, qf_aufbv, uf).",
    )
    parser.add_argument(
        "--pattern",
        help="Substring filter against benchmark relative paths.",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=10.0,
        help="Per-benchmark solver timeout in seconds (default: 10.0).",
    )
    parser.add_argument(
        "--z3",
        action="store_true",
        help="Cross-check verdicts against z3-solver when available.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit with code 1 if any benchmark fails its expected/Z3 verdict.",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    """Execute selected benchmarks and print a timing/verdict summary table."""
    args = build_parser().parse_args(argv)
    z3_mod: Any | None = None
    if args.z3:
        try:
            z3_mod = importlib.import_module("z3")
        except ImportError as exc:
            print(f"error: --z3 requires z3-solver installed: {exc}", file=sys.stderr)
            return 1

    paths = _discover_benchmarks(args.logic, args.pattern)
    if not paths:
        print("No matching benchmark files found.", file=sys.stderr)
        return 1 if args.check else 0

    results = [_run_benchmark(path, args.timeout, z3_mod) for path in paths]

    header = (
        f"{'Benchmark':<46} {'Group':<14} {'Exp':<7} {'Got':<7} {'Time ms':>8} "
        f"{'Confl':>6}"
    )
    if args.z3:
        header += f" {'Z3':<7}"
    header += " Status"
    print(header)
    print("-" * len(header))

    total_ms = 0.0
    failures = 0
    for rec in results:
        total_ms += rec.elapsed_ms
        status = "PASS" if rec.ok else "FAIL"
        if not rec.ok:
            failures += 1
        row = (
            f"{rec.rel_path:<46} {rec.group:<14} {rec.expected:<7} "
            f"{rec.verdict:<7} {rec.elapsed_ms:8.2f} {rec.conflicts:6d}"
        )
        if args.z3:
            row += f" {rec.z3_verdict or '-':<7}"
        row += f" {status}"
        print(row)

    print(
        f"\nRan {len(results)} benchmarks in {total_ms:.2f} ms "
        f"({len(results) - failures} passed, {failures} failed)."
    )
    if args.check and failures > 0:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
