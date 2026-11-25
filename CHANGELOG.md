# Changelog

All notable changes to `unsat` are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Automatic Python scalar coercion (`bool`, `int`, `Fraction`) in `Eq`, `Distinct`, and `If` builders in [`unsat.api`](src/unsat/api.py).
- Reserved [`packages/unsat-legacy/`](packages/unsat-legacy/README.md) `uv` workspace package slot for future archived/legacy solver implementations.
- Repository [`AGENTS.md`](AGENTS.md) and restructured architecture/design documentation under [`docs/architecture/`](docs/architecture/README.md) and [`docs/designs/`](docs/designs/README.md).
- Automated GitHub Release creation job in [`publish.yml`](.github/workflows/publish.yml) gated on PyPI publish success.
- Isolated wheel smoke testing (`import unsat`, `py.typed`, `Solver`, `unsat --version`, stdin SMT-LIB2), `benchmarks/run.py --check` in CI, full commit SHA Action pinning, concurrency guards, and [`.github/dependabot.yml`](.github/dependabot.yml).

## [0.1.0] - 2026-11-25

### Added

- Standalone incremental CDCL SAT solver (`unsat.sat`) with two-watched literals, binary watch lists, 1-UIP learning with recursive minimization, EVSIDS branching, Glucose LBD restarts/reduction, assumption-based `unsat_core()`, lazy `TheoryPropagator` hooks, and `max_conflicts`/`deadline` budgets.
- Immutable `WeakValueDictionary` hash-consed AST (`unsat.syntax`), Z3Py-style Python DSL (`unsat.api`), and `Model` / `FuncInterp` evaluator with `ModelConverter` reconstruction (`unsat.model`).
- Online CDCL(T) theory solvers (`unsat.theories`): `EUF` congruence closure with proof-forest explanations, exact rational `LRA` Simplex with infinitesimals, `LIA` branch-and-bound + Gomory cuts, and lazy Read-over-Write / extensional `Arrays`.
- Quantifier reasoning (`unsat.quantifiers`) with E-matching and `MBQI` under `QuantifierBudget` limits, plus AST preprocessing tactics (`SimplifyTactic`, `NNFTactic`, `BitBlastTactic`, `SkolemizeTactic`, `CtxSimplifyTactic`, `GaussianElimTactic`, `PropagateBoundsTactic`) and `solve_with_tactic` (`unsat.smt`).
- DIMACS CNF and SMT-LIB2 parser/runner/CLI (`unsat`) supporting core logics (`QF_BOOL` through `ALL`), parameterized `define-fun`, `define-sort` with cycle checks, `:named` + `get-unsat-core`, `get-assertions`, `echo`, and `--timeout` / `--max-conflicts` / quantifier budget flags.
- Curated DIMACS & SMT-LIB2 [`benchmarks/`](benchmarks/run.py) suite, Hypothesis differential test suites against `z3-solver`, and strict `import-linter` / PEP 649 annotation / import-isolation checks.
