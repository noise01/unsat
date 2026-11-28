# Verification & Soundness Strategy

This document summarizes the verification and code-quality invariants enforced across `unsat`.

## Dependency & Packaging Policy

- **Zero runtime dependencies**: The shipped `unsat` package keeps zero runtime dependencies; `z3-solver` is strictly a dev-only verification dependency and must never be imported inside `src/unsat/`.
- **Clean import graph**: [`pyproject.toml`](../../pyproject.toml) (`[tool.importlinter]`) and [`tests/test_import_contracts.py`](../../tests/test_import_contracts.py) enforce the strict acyclic DAG documented in [Module Responsibilities & Dependency DAG](../architecture/dependencies.md).

## Multi-Layered Verification

- **Z3 differential testing**: Render backend-neutral generated formulas and terms into both `unsat` and `z3` and assert verdict agreement across SAT, EUF, arithmetic, BV, arrays, quantifiers, tactics, and combined fragments (treating unexpected `UNKNOWN` on complete fragments as failures).
- **Reference brute-force oracles**: Exhaustive truth-table and small-domain reference oracles validate propositional and finite-domain semantics.
- **Hypothesis property-based fuzzing**: Property suites cover AST construction, tactics (`solve_with_tactic`), incremental solving, `push`/`pop` scope retraction, both-polarity assumption `unsat_core` soundness, reused-vs-fresh solver equivalence, SMT-LIB2 round-trips, and mock `TheoryPropagator` interactions.
- **Independent model evaluation**: Every `SAT` verdict checks `model.eval(formula)` / `model.eval_bool(formula, model_completion=True) is True` against the original asserted formulas (before tactic rewriting).
- **`unsat_core` soundness**: Extracted cores are re-verified as `UNSAT` on their own (and scoped `:named` SMT-LIB2 indicators remain hidden from `get-model`).
- **Curated benchmark & CLI regression suites**: End-to-end verification across [`benchmarks/`](../../benchmarks/) via `uv run python benchmarks/run.py --check` and [`tests/test_benchmarks.py`](../../tests/test_benchmarks.py), plus CLI smoke checks.

## Package & Type Safety Invariants

- **PEP 649 runtime annotation resolution**: [`tests/test_public_annotations.py`](../../tests/test_public_annotations.py) runs `typing.get_type_hints()` at runtime on all exported functions, classes, and public methods in every module with non-empty `__all__`. Exported signatures must not depend on `TYPE_CHECKING`-only imports.
- **Lightweight import isolation**: [`tests/test_import_cost.py`](../../tests/test_import_cost.py) verifies that importing core modules (`unsat`, `unsat.sat`, `unsat.syntax`, `unsat.smt`) does not eagerly load parser/CLI/test dependencies (`unsat.cli`, `unsat.parser`, `argparse`, `z3`).
- **CI release safety**: [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) runs lint (`ruff`), formatting, type checking (`ty`), `import-linter`, markdown linting (`rumdl`), `pytest tests`, `benchmarks/run.py --check`, and isolated wheel smoke tests; [`.github/workflows/release.yml`](../../.github/workflows/release.yml) gates Trusted Publishing (OIDC) behind `ci`, `check-tag`, and `build` smoke checks before uploading and creating a GitHub Release.
