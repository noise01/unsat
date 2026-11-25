"""Curated benchmark suite runner with profiling and baseline telemetry."""

from __future__ import annotations

import argparse
import cProfile
import importlib
import io
import json
import pstats
import re
import sys
import time
import tracemalloc
from dataclasses import asdict, dataclass
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
    propagations: int = 0
    decisions: int = 0
    pivots: int = 0
    merges: int = 0
    alloc_count: int = 0
    peak_kib: float = 0.0
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
    parts = rel.parts[1:] if rel.parts[0] == "scale" else rel.parts
    if parts[0] == "dimacs":
        return "dimacs"
    if len(parts) >= 3 and parts[0] == "smt2":
        return parts[1]
    return parts[0]


def _discover_benchmarks(
    suite: str, logic: str | None, pattern: str | None
) -> list[Path]:
    files = sorted([*_ROOT.rglob("*.cnf"), *_ROOT.rglob("*.smt2")])
    selected: list[Path] = []
    for path in files:
        rel_parts = path.relative_to(_ROOT).parts
        is_scale = rel_parts[0] == "scale"
        if suite == "core" and is_scale:
            continue
        if suite == "scale" and not is_scale:
            continue
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


def _run_benchmark(
    path: Path,
    timeout: float,
    z3_mod: Any | None,
    *,
    measure_alloc: bool,
    profiler: cProfile.Profile | None,
) -> BenchmarkResult:
    text = path.read_text(encoding="utf-8-sig")
    expected = _extract_expected_status(path, text)

    if measure_alloc:
        tracemalloc.clear_traces()
        tracemalloc.reset_peak()

    t0 = time.perf_counter()
    if profiler is not None:
        profiler.enable()
    try:
        if path.suffix == ".cnf":
            cnf = parse_dimacs(text)
            res, _, sat_stats = solve_dimacs(cnf, timeout=timeout)
            stats: dict[str, int] = {
                k: v for k, v in sat_stats.items() if isinstance(v, int)
            }
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
    finally:
        if profiler is not None:
            profiler.disable()
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    alloc_count = 0
    peak_kib = 0.0
    if measure_alloc:
        _, peak_bytes = tracemalloc.get_traced_memory()
        snap = tracemalloc.take_snapshot()
        alloc_count = sum(stat.count for stat in snap.statistics("filename"))
        peak_kib = peak_bytes / 1024.0

    z3_verdict = (
        _run_z3_check(path, text, timeout, z3_mod) if z3_mod is not None else None
    )
    return BenchmarkResult(
        rel_path=path.relative_to(_ROOT).as_posix(),
        group=_group_name(path),
        expected=expected,
        verdict=verdict,
        elapsed_ms=elapsed_ms,
        conflicts=int(stats.get("conflicts", 0)),
        propagations=int(stats.get("propagations", 0)),
        decisions=int(stats.get("decisions", 0)),
        pivots=int(stats.get("pivots", 0)),
        merges=int(stats.get("merges", 0)),
        alloc_count=alloc_count,
        peak_kib=peak_kib,
        z3_verdict=z3_verdict,
    )


def _save_baseline(path: Path, suite: str, results: list[BenchmarkResult]) -> None:
    payload = {
        "suite": suite,
        "total_ms": sum(rec.elapsed_ms for rec in results),
        "total_conflicts": sum(rec.conflicts for rec in results),
        "total_alloc_count": sum(rec.alloc_count for rec in results),
        "max_peak_kib": max((rec.peak_kib for rec in results), default=0.0),
        "benchmarks": {
            rec.rel_path: {
                k: v
                for k, v in asdict(rec).items()
                if k not in ("rel_path", "z3_verdict")
            }
            for rec in results
        },
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _print_comparison(baseline_path: Path, results: list[BenchmarkResult]) -> None:
    raw = json.loads(baseline_path.read_text(encoding="utf-8"))
    base_map: dict[str, dict[str, Any]] = raw.get("benchmarks", {})

    header = (
        f"\n{'Benchmark':<48} {'Base ms':>9} {'Curr ms':>9} {'Speedup':>8} "
        f"{'Base KiB':>9} {'Curr KiB':>9}"
    )
    print(header)
    print("-" * len(header.lstrip("\n")))

    base_total = 0.0
    curr_total = 0.0
    for rec in results:
        b = base_map.get(rec.rel_path)
        if b is None:
            continue
        b_ms = float(b["elapsed_ms"])
        base_total += b_ms
        curr_total += rec.elapsed_ms
        speedup = (b_ms / rec.elapsed_ms) if rec.elapsed_ms > 0 else float("inf")
        b_kib = float(b.get("peak_kib", 0.0))
        print(
            f"{rec.rel_path:<48} {b_ms:9.2f} {rec.elapsed_ms:9.2f} {speedup:7.2f}x "
            f"{b_kib:9.1f} {rec.peak_kib:9.1f}"
        )

    if curr_total > 0 and base_total > 0:
        print(
            f"\nMatched total: {base_total:.2f} ms -> {curr_total:.2f} ms "
            f"({base_total / curr_total:.2f}x)"
        )


def _print_profile(profiler: cProfile.Profile, top_n: int) -> None:
    print(f"\nTop {top_n} functions (cumulative time):")
    cum_buf = io.StringIO()
    pstats.Stats(profiler, stream=cum_buf).sort_stats("cumtime").print_stats(top_n)
    print(cum_buf.getvalue().rstrip())

    print(f"\nTop {top_n} functions (internal/tottime):")
    tot_buf = io.StringIO()
    pstats.Stats(profiler, stream=tot_buf).sort_stats("tottime").print_stats(top_n)
    print(tot_buf.getvalue().rstrip())


def build_parser() -> argparse.ArgumentParser:
    """Build the CLI parser for ``benchmarks/run.py``."""
    parser = argparse.ArgumentParser(
        description="Run the curated unsat benchmark suite."
    )
    parser.add_argument(
        "--suite",
        choices=("core", "scale", "all"),
        default="core",
        help="Benchmark corpus selection (default: core).",
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
    parser.add_argument(
        "--profile",
        action="store_true",
        help="Collect cProfile timings across selected benchmarks.",
    )
    parser.add_argument(
        "--profile-top",
        type=int,
        default=20,
        help="Number of cProfile rows to display (default: 20).",
    )
    parser.add_argument(
        "--alloc",
        action="store_true",
        help="Measure tracemalloc allocation counts and peak KiB per benchmark.",
    )
    parser.add_argument(
        "--save-baseline",
        type=Path,
        help="Save JSON benchmark metrics to this path.",
    )
    parser.add_argument(
        "--compare",
        type=Path,
        help="Compare current timings/allocations against a saved JSON baseline.",
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

    paths = _discover_benchmarks(args.suite, args.logic, args.pattern)
    if not paths:
        print("No matching benchmark files found.", file=sys.stderr)
        return 1 if args.check else 0

    profiler = cProfile.Profile() if args.profile else None
    if args.alloc:
        tracemalloc.start()
    try:
        results = [
            _run_benchmark(
                path,
                args.timeout,
                z3_mod,
                measure_alloc=args.alloc,
                profiler=profiler,
            )
            for path in paths
        ]
    finally:
        if args.alloc:
            tracemalloc.stop()

    header = (
        f"{'Benchmark':<48} {'Group':<14} {'Exp':<7} {'Got':<7} {'Time ms':>8} "
        f"{'Confl':>6}"
    )
    if args.alloc:
        header += f" {'PeakKiB':>8} {'Blocks':>8}"
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
            f"{rec.rel_path:<48} {rec.group:<14} {rec.expected:<7} "
            f"{rec.verdict:<7} {rec.elapsed_ms:8.2f} {rec.conflicts:6d}"
        )
        if args.alloc:
            row += f" {rec.peak_kib:8.1f} {rec.alloc_count:8d}"
        if args.z3:
            row += f" {rec.z3_verdict or '-':<7}"
        row += f" {status}"
        print(row)

    print(
        f"\nRan {len(results)} benchmarks in {total_ms:.2f} ms "
        f"({len(results) - failures} passed, {failures} failed)."
    )

    if args.save_baseline is not None:
        _save_baseline(args.save_baseline, args.suite, results)
    if args.compare is not None:
        _print_comparison(args.compare, results)
    if profiler is not None:
        _print_profile(profiler, args.profile_top)

    if args.check and failures > 0:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
