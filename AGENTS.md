# AGENTS.md

Engineering guide for coding agents working in `unsat` (pure Python 3.14+ SMT solver with zero runtime dependencies).

## Repository Layout

- `src/unsat/`: Active solver package (see [docs/architecture/layout.md](docs/architecture/layout.md))
  - `syntax/`: Hash-consed AST (`Context`, `Sort`, `FuncDecl`, `Expr`, `Quantifier`)
  - `sat/`: Standalone propositional CDCL SAT solver (`SATSolver`)
  - `model/`: `Model`, recursive evaluator, and `ModelConverter`
  - `theories/`: `EUF`, `LRA`, `LIA`, `NLA`, `BV`, `Arrays`, and `Strings` theory solvers
  - `tactics/`: Pure AST-to-AST preprocessing tactics (`SimplifyTactic`, `NNFTactic`, `BitBlastTactic`, `SkolemizeTactic`, `CtxSimplifyTactic`, `GaussianElimTactic`, `PropagateBoundsTactic`)
  - `quantifiers/`: `EMatcher` and `MBQI` engines (`QuantifierBudget`)
  - `smt/`: CDCL(T) orchestrator (`SMTSolver`, `solve_with_tactic`)
  - `parser/`: `DIMACS` and `SMT-LIB2` (`lexer`, `format`, `SMT2Runner`) frontends
  - `api.py` / `cli.py` / `__init__.py` / `__main__.py`: Python DSL facade and CLI entry point
- `packages/unsat-legacy/`: Reserved `uv` workspace member for archived legacy implementations (keep isolated from `src/unsat/`)
- `tests/`: Mirrors `src/unsat/` plus contract/property/benchmark suites
- `benchmarks/`: Curated DIMACS & SMT-LIB2 suite and `benchmarks/run.py`
- `docs/architecture/`: Module layout and dependency DAG contracts
- `docs/designs/`: Core solver design, verification strategy, and M1–M10 roadmap

## Verification Commands

Run all checks after code or doc edits (`uv sync --locked --all-extras --dev` first if dependencies changed):

```bash
uv run ruff check .
uv run ruff format --check .
uv run ty check
uv run lint-imports
uv run rumdl check .
uv run pytest tests
uv run python benchmarks/run.py --check
```

Do not leave a `dist/` build directory checked into or lingering in the repository root; pass `--out-dir` outside the repo when testing `uv build` locally.

## Critical Architectural Invariants

1. **Strict Import DAG**: Must satisfy all 9 `[tool.importlinter]` contracts in [`pyproject.toml`](pyproject.toml) and [`tests/test_import_contracts.py`](tests/test_import_contracts.py):
   - `unsat.syntax` and `unsat.sat` have zero internal dependencies (`sat` must never import `syntax`).
   - `unsat.api` must not import `unsat.sat`, `unsat.quantifiers`, `unsat.theories`, or `unsat.tactics` (directly or indirectly) — preprocessing+solving belongs in `unsat.smt.solve_with_tactic`.
   - `unsat.quantifiers` must not import `unsat.tactics` or `unsat.sat`.
   - Adding a new top-level module under `src/unsat/` requires updating `[tool.importlinter]` and [`tests/test_import_contracts.py`](tests/test_import_contracts.py).
2. **Import Isolation & Zero Runtime Deps**: `pyproject.toml` keeps `dependencies = []`. Never import `z3` inside `src/unsat/`; keep `import unsat`, `unsat.sat`, `unsat.syntax`, and `unsat.smt` free of `cli`, `parser`, and `argparse` (`tests/test_import_cost.py`).
3. **PEP 649 Public Type Annotations**: Any type annotation on exported symbols in module `__all__` must resolve at runtime via `typing.get_type_hints()` (`tests/test_public_annotations.py`). Avoid `TYPE_CHECKING`-only imports for exported signatures.
4. **AST Identity vs. Formula Equality**: `Expr.__eq__` checks object identity (`self is other`), and `Expr.__bool__` raises `TypeError`. Build formula equality with `Eq(a, b)` / `ctx.mk_eq(a, b)` and `Distinct(...)`.

## Testing & Soundness Rules

- Every new theory/tactic/SMT feature must verify:
  - Differential agreement against `z3` (never claim `SAT` when Z3 says `UNSAT`, nor `UNSAT` when Z3 says `SAT`).
  - Independent model evaluation (`model.eval_bool(f, model_completion=True) is True`) on every `SAT` result.
  - Core minimality / satisfiability of extracted `unsat_core()` subsets.
- When editing workflows in [`.github/workflows/`](.github/workflows/), pin third-party Actions to full commit SHAs and validate any `uv build` wheel in an `--isolated --no-project` environment.
