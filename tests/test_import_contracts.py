import os
import subprocess
import sysconfig
from pathlib import Path

import pytest

CONFIG = Path(__file__).resolve().parents[1] / "pyproject.toml"
LINT_IMPORTS = Path(sysconfig.get_path("scripts")) / "lint-imports"

# Direct dependencies from the architecture's module responsibilities table.
ALLOWED = {
    "unsat": ("api",),
    "__main__": ("cli", "parser", "smt", "sat"),
    "api": ("syntax", "smt", "model"),
    "parser": ("syntax", "sat", "smt", "api"),
    "cli": ("parser", "smt", "sat"),
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


def module_path(package: Path, name: str) -> Path:
    if name == "unsat":
        return package / "__init__.py"
    if name == "parser":
        return package / "parser" / "__init__.py"
    return package.joinpath(*name.split(".")).with_suffix(".py")


@pytest.fixture
def package(tmp_path: Path) -> Path:
    # Isolate each import graph while exercising the same configuration as CI.
    pkg = tmp_path / "unsat"
    pkg.mkdir()
    (pkg / "parser").mkdir()
    for name in (*MODULES, "parser.reader"):
        module_path(pkg, name).touch()
    return pkg


def lint_imports(package: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [LINT_IMPORTS, "--config", CONFIG, "--no-cache"],
        check=False,
        cwd=package.parent,
        env={
            **os.environ,
            "PYTHONPATH": str(package.parent),
            "PYTHONIOENCODING": "utf-8",
        },
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        encoding="utf-8",
    )


@pytest.mark.parametrize(
    ("source", "target"),
    [
        (source, target)
        for source, allowed in ALLOWED.items()
        for target in MODULES
        if target != source and target not in allowed
    ]
    + [("parser.reader", "model"), ("unsat", "parser.reader")],
)
def test_forbidden_direct_import(package: Path, source: str, target: str):
    imported = "unsat" if target == "unsat" else f"unsat.{target}"
    importer = "unsat" if source == "unsat" else f"unsat.{source}"
    module_path(package, source).write_text(f"import {imported}\n", encoding="utf-8")

    result = lint_imports(package)

    assert result.returncode == 1, result.stdout
    assert f"{importer} -> {imported} (" in result.stdout, result.stdout


def test_unregistered_top_level_module(package: Path):
    (package / "errors.py").touch()

    result = lint_imports(package)

    assert result.returncode == 1, result.stdout
    assert "- unsat.errors" in result.stdout.splitlines(), result.stdout


def test_allowed_indirect_imports(package: Path):
    # Includes api -> smt -> sat, parser -> api -> model and cli -> parser -> api.
    dependencies = {
        **ALLOWED,
        "smt": ("sat", "theories", "tactics", "quantifiers", "model", "syntax"),
    }
    for source, targets in dependencies.items():
        module_path(package, source).write_text(
            "".join(f"import unsat.{target}\n" for target in targets), encoding="utf-8"
        )

    result = lint_imports(package)

    assert result.returncode == 0, result.stdout
