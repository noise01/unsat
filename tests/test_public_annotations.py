"""Verify PEP 649 type annotations resolve cleanly on all exported symbols."""

import importlib
import inspect
import typing
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


def _modules_with_exports() -> list[str]:
    pkg_root = ROOT / "src" / "unsat"
    modules: list[str] = []
    for py_path in sorted(pkg_root.rglob("*.py")):
        rel_parts = py_path.relative_to(pkg_root).parts
        if any(part.startswith("_") and part != "__init__.py" for part in rel_parts):
            continue
        if rel_parts == ("__init__.py",):
            dotted = "unsat"
        elif rel_parts[-1] == "__init__.py":
            dotted = "unsat." + ".".join(rel_parts[:-1])
        else:
            dotted = "unsat." + ".".join((*rel_parts[:-1], py_path.stem))
        mod = importlib.import_module(dotted)
        if getattr(mod, "__all__", None):
            modules.append(dotted)
    return modules


EXPORTING_MODULES = _modules_with_exports()


def _check_module_annotations(module_name: str) -> list[str]:
    module = importlib.import_module(module_name)
    failures: list[str] = []
    for name in module.__all__:
        obj = getattr(module, name)
        targets: list[tuple[str, object]] = []
        if inspect.isfunction(obj):
            targets.append((f"{module_name}.{name}", obj))
        elif inspect.isclass(obj):
            targets.append((f"{module_name}.{name}", obj))
            for attr_name, attr in obj.__dict__.items():
                if attr_name.startswith("_"):
                    continue
                if inspect.isfunction(attr):
                    targets.append((f"{module_name}.{name}.{attr_name}", attr))
                elif isinstance(attr, property) and attr.fget is not None:
                    targets.append((f"{module_name}.{name}.{attr_name}", attr.fget))
        for qualname, target in targets:
            try:
                typing.get_type_hints(target)
            except Exception as exc:
                failures.append(f"{qualname}: {type(exc).__name__}: {exc}")
    return failures


@pytest.mark.parametrize("module_name", EXPORTING_MODULES)
def test_exported_annotations_resolve_at_runtime(module_name: str) -> None:
    failures = _check_module_annotations(module_name)
    assert not failures, "\n".join(failures)


def test_expected_m2_modules_are_covered() -> None:
    expected = {
        "unsat",
        "unsat.api",
        "unsat.model",
        "unsat.parser",
        "unsat.sat",
        "unsat.smt",
        "unsat.syntax",
        "unsat.tactics",
        "unsat.theories",
    }
    assert expected <= set(EXPORTING_MODULES)


def test_type_checking_only_annotation_is_detected() -> None:
    namespace: dict[str, object] = {}
    exec(
        "from typing import TYPE_CHECKING\n"
        "if TYPE_CHECKING:\n"
        "    from collections.abc import Sequence\n"
        "def f(xs: 'Sequence[int]') -> int:\n"
        "    return len(xs)\n",
        namespace,
    )
    with pytest.raises(NameError, match="Sequence"):
        typing.get_type_hints(namespace["f"])
