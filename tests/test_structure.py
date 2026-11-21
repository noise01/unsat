import importlib

import pytest

import unsat

EXPECTED_MODULES = [
    "unsat.syntax",
    "unsat.sat",
    "unsat.theories",
    "unsat.tactics",
    "unsat.quantifiers",
    "unsat.parser",
    "unsat.smt",
    "unsat.model",
    "unsat.api",
    "unsat.cli",
]


def test_public_entry_point():
    assert isinstance(unsat.__all__, list)
    assert not hasattr(unsat, "main")


@pytest.mark.parametrize("module_name", EXPECTED_MODULES)
def test_submodule_importable(module_name: str):
    module = importlib.import_module(module_name)
    assert module.__name__ == module_name
