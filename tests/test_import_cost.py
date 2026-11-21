"""Verify lightweight entry points avoid importing CLI/parser/test-only modules."""

import subprocess
import sys

import pytest

LIGHTWEIGHT_MODULES = [
    "unsat",
    "unsat.sat",
    "unsat.syntax",
    "unsat.smt",
]
FORBIDDEN_EAGER_IMPORTS = ("unsat.cli", "unsat.parser", "argparse", "z3")


def _run_fresh(script: str) -> str:
    result = subprocess.run(
        [sys.executable, "-c", script],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    return result.stdout.strip()


@pytest.mark.parametrize("module", LIGHTWEIGHT_MODULES)
def test_importing_core_module_avoids_cli_parser_and_z3(module: str) -> None:
    script = (
        f"import sys, {module}; "
        f"forbidden = {FORBIDDEN_EAGER_IMPORTS!r}; "
        "loaded = [m for m in forbidden if m in sys.modules]; "
        "print(','.join(loaded))"
    )
    loaded = _run_fresh(script)
    assert loaded == "", f"importing {module} unexpectedly loaded: {loaded}"


def test_cli_import_control_loads_parser_and_argparse() -> None:
    script = (
        "import sys, unsat.cli; "
        "print('unsat.parser' in sys.modules and 'argparse' in sys.modules)"
    )
    assert _run_fresh(script) == "True"
