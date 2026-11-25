"""Smoke and regression checks across the curated ``benchmarks/`` suite."""

import re
from pathlib import Path

import pytest

from unsat.parser import execute_smt2, parse_dimacs, solve_dimacs
from unsat.sat import SolveResult

_BENCH_ROOT = Path(__file__).resolve().parent.parent / "benchmarks"
_ALL_BENCHMARKS = sorted([*_BENCH_ROOT.rglob("*.cnf"), *_BENCH_ROOT.rglob("*.smt2")])
_DIMACS_STATUS_RE = re.compile(
    r"^c\s+status:\s*(sat|unsat)\b", re.IGNORECASE | re.MULTILINE
)
_SMT2_STATUS_RE = re.compile(r"\(set-info\s+:status\s+(sat|unsat)\s*\)", re.IGNORECASE)


def test_benchmark_inventory_covers_dimacs_and_smt2_logics() -> None:
    core_dimacs = [
        p for p in _ALL_BENCHMARKS if p.relative_to(_BENCH_ROOT).parts[0] == "dimacs"
    ]
    assert core_dimacs
    smt2_groups = {
        p.relative_to(_BENCH_ROOT).parts[1]
        for p in _ALL_BENCHMARKS
        if p.relative_to(_BENCH_ROOT).parts[0] == "smt2" and p.suffix == ".smt2"
    }
    assert {
        "qf_bool",
        "qf_uf",
        "qf_lra",
        "qf_lia",
        "qf_nra",
        "qf_nia",
        "qf_uflia",
        "qf_bv",
        "qf_ufbv",
        "qf_ax",
        "qf_aufbv",
        "qf_auflia",
        "uf",
        "lia",
        "smt2_features",
    } <= smt2_groups
    scale_paths = [
        p for p in _ALL_BENCHMARKS if p.relative_to(_BENCH_ROOT).parts[0] == "scale"
    ]
    assert any(p.suffix == ".cnf" for p in scale_paths)
    assert any(p.suffix == ".smt2" for p in scale_paths)


@pytest.mark.parametrize(
    "bench_path",
    _ALL_BENCHMARKS,
    ids=lambda path: path.relative_to(_BENCH_ROOT).as_posix(),
)
def test_curated_benchmark_matches_expected_status(bench_path: Path) -> None:
    text = bench_path.read_text(encoding="utf-8-sig")

    if bench_path.suffix == ".cnf":
        match = _DIMACS_STATUS_RE.search(text)
        assert match is not None
        expected = match.group(1).lower()
        cnf = parse_dimacs(text)
        res, model, _ = solve_dimacs(cnf, timeout=10.0)
        actual = "sat" if res is SolveResult.SAT else "unsat"
        assert actual == expected
        if expected == "sat":
            assert model is not None
            for clause in cnf.clauses:
                assert any(model[lit >> 1] is ((lit & 1) == 0) for lit in clause)
        return

    match = _SMT2_STATUS_RE.search(text)
    assert match is not None
    expected = match.group(1).lower()
    outputs, _ = execute_smt2(text, timeout=10.0)
    verdict = next(
        (line for line in outputs if line in ("sat", "unsat", "unknown")),
        None,
    )
    assert verdict == expected

    if bench_path.name == "unsat_core_named_macros.smt2":
        assert len(outputs) == 2
        assert "row1_clash" in outputs[1]
        assert "unrelated" not in outputs[1]
