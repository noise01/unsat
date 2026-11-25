import subprocess
import sys
import sysconfig
from importlib.metadata import version
from pathlib import Path

SAT_CNF = "p cnf 2 2\n1 2 0\n-1 2 0\n"
UNSAT_CNF = "p cnf 1 2\n1 0\n-1 0\n"
SAT_SMT2 = """
(set-logic QF_BOOL)
(declare-const p Bool)
(declare-const q Bool)
(assert (and p (=> p q)))
(check-sat)
(get-model)
"""
UNSAT_SMT2 = """
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
"""


def _cli_command() -> Path:
    return Path(sysconfig.get_path("scripts")) / "unsat"


def test_unsat_no_args_prints_help() -> None:
    result = subprocess.run(
        [_cli_command()],
        check=True,
        capture_output=True,
        text=True,
    )
    assert "usage: unsat" in result.stdout


def test_unsat_version_flag() -> None:
    result = subprocess.run(
        [_cli_command(), "--version"],
        check=True,
        capture_output=True,
        text=True,
    )
    assert result.stdout.strip() == f"unsat {version('unsat')}"


def test_unsat_solves_sat_and_unsat_files(tmp_path: Path) -> None:
    sat_file = tmp_path / "sat.cnf"
    sat_file.write_text(SAT_CNF, encoding="utf-8")
    unsat_file = tmp_path / "unsat.cnf"
    unsat_file.write_text(UNSAT_CNF, encoding="utf-8")

    sat_res = subprocess.run(
        [_cli_command(), str(sat_file)],
        check=True,
        capture_output=True,
        text=True,
    )
    lines = sat_res.stdout.strip().splitlines()
    assert lines[0] == "s SATISFIABLE"
    assert lines[1].startswith("v ")
    assert lines[1].endswith(" 2 0")

    unsat_res = subprocess.run(
        [sys.executable, "-m", "unsat", str(unsat_file)],
        check=True,
        capture_output=True,
        text=True,
    )
    assert unsat_res.stdout.strip() == "s UNSATISFIABLE"


def test_unsat_solves_smt2_files_and_stdin(tmp_path: Path) -> None:
    sat_smt = tmp_path / "sat.smt2"
    sat_smt.write_text(SAT_SMT2, encoding="utf-8")
    unsat_smt = tmp_path / "unsat.smt2"
    unsat_smt.write_text(UNSAT_SMT2, encoding="utf-8")

    sat_res = subprocess.run(
        [_cli_command(), str(sat_smt)],
        check=True,
        capture_output=True,
        text=True,
    )
    assert "sat" in sat_res.stdout
    assert "(define-fun p () Bool true)" in sat_res.stdout
    assert "(define-fun q () Bool true)" in sat_res.stdout

    unsat_res = subprocess.run(
        [sys.executable, "-m", "unsat", str(unsat_smt)],
        check=True,
        capture_output=True,
        text=True,
    )
    assert unsat_res.stdout.strip() == "unsat"

    stdin_res = subprocess.run(
        [_cli_command(), "-", "--stats"],
        input=SAT_SMT2,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "; conflicts:" in stdin_res.stdout
    assert "sat" in stdin_res.stdout

    explicit_res = subprocess.run(
        [_cli_command(), "-", "--format", "smt2"],
        input="(assert true)\n(check-sat)\n",
        check=True,
        capture_output=True,
        text=True,
    )
    assert explicit_res.stdout.strip() == "sat"


def test_unsat_stdin_and_stats_flag() -> None:
    result = subprocess.run(
        [_cli_command(), "-", "--stats"],
        input=SAT_CNF,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "c conflicts:" in result.stdout
    assert "s SATISFIABLE" in result.stdout


def test_unsat_error_returns_nonzero(tmp_path: Path) -> None:
    missing = subprocess.run(
        [_cli_command(), str(tmp_path / "missing.cnf")],
        check=False,
        capture_output=True,
        text=True,
    )
    assert missing.returncode == 1
    assert "error:" in missing.stderr

    bad_file = tmp_path / "bad.cnf"
    bad_file.write_text("not dimacs\n", encoding="utf-8")
    invalid = subprocess.run(
        [_cli_command(), str(bad_file)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert invalid.returncode == 1
    assert "error:" in invalid.stderr

    bad_smt = tmp_path / "bad.smt2"
    bad_smt.write_text("(assert undeclared)\n", encoding="utf-8")
    invalid_smt = subprocess.run(
        [_cli_command(), str(bad_smt)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert invalid_smt.returncode == 1
    assert "error:" in invalid_smt.stderr


def test_unsat_resource_limit_flags() -> None:
    # PHP(4, 3) in DIMACS exceeds 1 conflict.
    lines = ["p cnf 12 22"]
    for i in range(4):
        lines.append(" ".join(str(i * 3 + j + 1) for j in range(3)) + " 0")
    for j in range(3):
        for i1 in range(4):
            for i2 in range(i1 + 1, 4):
                lines.append(f"-{i1 * 3 + j + 1} -{i2 * 3 + j + 1} 0")
    php_cnf = "\n".join(lines) + "\n"

    dimacs_limited = subprocess.run(
        [_cli_command(), "-", "--format", "dimacs", "--max-conflicts", "1"],
        input=php_cnf,
        check=True,
        capture_output=True,
        text=True,
    )
    assert dimacs_limited.stdout.strip() == "s UNKNOWN"

    smt_timeout = subprocess.run(
        [_cli_command(), "-", "--format", "smt2", "--timeout", "0"],
        input="(declare-const p Bool)\n(assert p)\n(check-sat)\n",
        check=True,
        capture_output=True,
        text=True,
    )
    assert smt_timeout.stdout.strip() == "unknown"

    smt_quant_budget = subprocess.run(
        [
            _cli_command(),
            "-",
            "--format",
            "smt2",
            "--max-quantifier-rounds",
            "0",
            "--max-quantifier-matches",
            "4",
        ],
        input=(
            "(set-logic UF)\n"
            "(declare-fun P (Int) Bool)\n"
            "(assert (forall ((x Int)) (! (P x) :pattern ((P x)))))\n"
            "(check-sat)\n"
            "(reset)\n"
            "(set-logic UF)\n"
            "(declare-fun Q (Int) Bool)\n"
            "(assert (forall ((x Int)) (! (Q x) :pattern ((Q x)))))\n"
            "(check-sat)\n"
        ),
        check=True,
        capture_output=True,
        text=True,
    )
    assert smt_quant_budget.stdout.strip().splitlines() == ["unknown", "unknown"]

    bad_timeout = subprocess.run(
        [_cli_command(), "-", "--format", "dimacs", "--timeout", "-1"],
        input=SAT_CNF,
        check=False,
        capture_output=True,
        text=True,
    )
    assert bad_timeout.returncode == 1
    assert "error:" in bad_timeout.stderr
