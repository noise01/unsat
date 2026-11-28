import json
import os
import subprocess
import sys
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path

import pytest

CONFIG = Path(__file__).resolve().parents[1] / "pyproject.toml"

# Direct dependencies from the architecture's module responsibilities table.
ALLOWED: dict[str, tuple[str, ...]] = {
    "unsat": ("api",),
    "__main__": ("cli",),
    "cli": ("parser", "smt", "sat"),
    "parser": ("syntax", "sat", "smt", "model"),
    "api": ("syntax", "smt", "model"),
    "smt": ("syntax", "sat", "theories", "tactics", "quantifiers", "model"),
    "quantifiers": ("syntax", "theories", "model"),
    "theories": ("syntax", "model"),
    "tactics": ("syntax", "model"),
    "model": ("syntax",),
    "syntax": (),
    "sat": (),
}
MODULES = (
    "unsat",
    "__main__",
    "cli",
    "parser",
    "api",
    "smt",
    "quantifiers",
    "theories",
    "tactics",
    "model",
    "syntax",
    "sat",
)
SUBPACKAGES = (
    "syntax",
    "sat",
    "theories",
    "tactics",
    "quantifiers",
    "parser",
    "smt",
    "model",
)
CHILD_MODULES = (
    "syntax.expr",
    "sat.cdcl",
    "theories.euf",
    "tactics.simplify",
    "quantifiers.ematch",
    "parser.reader",
    "smt.solver",
    "model.eval",
)

SUBMODULE_FORBIDDEN_CASES = [
    ("parser.reader", "api"),
    ("parser.reader", "theories"),
    ("unsat", "parser.reader"),
    ("theories.euf", "sat"),
    ("theories.euf", "tactics"),
    ("tactics.simplify", "theories"),
    ("quantifiers.ematch", "tactics"),
    ("quantifiers.ematch", "sat"),
    ("syntax.expr", "sat"),
    ("sat.cdcl", "syntax"),
    ("model.eval", "sat"),
    ("smt.solver", "api"),
]

WORKER_SCRIPT = """
import importlib
import io
import json
import os
import sys

from importlinter import configuration
from importlinter.application import output, use_cases

config_path = sys.argv[1]
real_stdout = sys.stdout
sys.stdout = io.StringIO()

configuration.configure()
output.console.width = 1000
output.console.no_color = True
assert "unsat" not in sys.modules

original_cwd = os.getcwd()
for line in sys.stdin:
    cwd = json.loads(line)["cwd"]
    os.chdir(cwd)
    sys.path.insert(0, cwd)
    importlib.invalidate_caches()
    try:
        with output.console.capture() as capture:
            passed = use_cases.lint_imports(
                config_filename=config_path,
                cache_dir=None,
                no_logo=True,
            )
    finally:
        sys.path.pop(0)
        os.chdir(original_cwd)
    payload = json.dumps({"passed": bool(passed), "output": capture.get()})
    real_stdout.write(payload + "\\n")
    real_stdout.flush()
"""


@dataclass(frozen=True)
class LintResult:
    passed: bool
    output: str


class LintWorker:
    def __init__(self, config: Path) -> None:
        env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
        env["PYTHONIOENCODING"] = "utf-8"
        self._proc = subprocess.Popen(
            [sys.executable, "-c", WORKER_SCRIPT, str(config)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            encoding="utf-8",
            env=env,
        )

    def check(self, package: Path) -> LintResult:
        assert self._proc.stdin is not None
        assert self._proc.stdout is not None
        self._proc.stdin.write(json.dumps({"cwd": str(package.parent)}) + "\n")
        self._proc.stdin.flush()
        response = self._proc.stdout.readline()
        if not response:
            msg = f"import-linter worker exited unexpectedly ({self._proc.poll()})"
            raise RuntimeError(msg)
        payload = json.loads(response)
        return LintResult(passed=payload["passed"], output=payload["output"])

    def close(self) -> None:
        if self._proc.stdin is not None:
            self._proc.stdin.close()
        try:
            returncode = self._proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self._proc.kill()
            self._proc.wait()
            raise
        assert returncode == 0, f"import-linter worker failed with exit code {returncode}"


def module_path(package: Path, name: str) -> Path:
    if name == "unsat":
        return package / "__init__.py"
    if name in SUBPACKAGES:
        return package / name / "__init__.py"
    return package.joinpath(*name.split(".")).with_suffix(".py")


def full_module_name(name: str) -> str:
    return "unsat" if name == "unsat" else f"unsat.{name}"


@pytest.fixture(scope="module")
def lint_worker() -> Iterator[LintWorker]:
    worker = LintWorker(CONFIG)
    try:
        yield worker
    finally:
        worker.close()


@pytest.fixture
def package(tmp_path: Path) -> Path:
    # Isolate each import graph while exercising the same configuration as CI.
    pkg = tmp_path / "unsat"
    pkg.mkdir()
    for subpkg in SUBPACKAGES:
        (pkg / subpkg).mkdir()
    for name in (*MODULES, *CHILD_MODULES):
        module_path(pkg, name).touch()
    return pkg


@pytest.mark.parametrize(
    ("source", "target"),
    [
        (source, target)
        for source, allowed in ALLOWED.items()
        for target in MODULES
        if target != source and target not in allowed
    ]
    + SUBMODULE_FORBIDDEN_CASES,
)
def test_forbidden_direct_import(lint_worker: LintWorker, package: Path, source: str, target: str) -> None:
    imported = full_module_name(target)
    importer = full_module_name(source)
    module_path(package, source).write_text(f"import {imported}\n", encoding="utf-8")

    result = lint_worker.check(package)

    assert not result.passed, result.output
    assert f"{importer} -> {imported} (" in result.output, result.output


def test_unregistered_top_level_module(lint_worker: LintWorker, package: Path) -> None:
    (package / "errors.py").touch()

    result = lint_worker.check(package)

    assert not result.passed, result.output
    assert "- unsat.errors" in result.output.splitlines(), result.output


def test_all_allowed_dependencies_pass(lint_worker: LintWorker, package: Path) -> None:
    allowed_with_submodules: dict[str, tuple[str, ...]] = {
        **ALLOWED,
        "parser.reader": ("model",),
        "theories.euf": ("syntax.expr",),
        "tactics.simplify": ("model",),
        "quantifiers.ematch": ("theories.euf",),
        "smt.solver": ("theories.euf", "tactics.simplify", "quantifiers.ematch"),
        "model.eval": ("syntax.expr",),
    }
    for source, targets in allowed_with_submodules.items():
        if targets:
            module_path(package, source).write_text(
                "".join(f"import {full_module_name(target)}\n" for target in targets),
                encoding="utf-8",
            )

    result = lint_worker.check(package)

    assert result.passed, result.output
