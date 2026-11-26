# unsat

A Z3-inspired SMT solver written in pure Python 3.14+ with zero runtime dependencies.

`unsat` pairs a standalone CDCL SAT core with online CDCL(T) theory solvers (`EUF`, `LRA`, `LIA`, `NLA` for `QF_NRA`/`QF_NIA`, lazy word-level `BV` with on-demand bit-blasting, `Arrays`, and `Strings`/`RegLan` for `QF_S`/`QF_SLIA`), Model-Based Theory Combination (`MBTC`), E-matching and MBQI quantifier instantiation, AST preprocessing tactics, a Z3Py-style Python DSL, and an SMT-LIB2 / DIMACS CLI.

## Features

- **CDCL SAT solver (`unsat.sat`)**: Two-watched literals (dedicated binary watches + blocker literals), 1-UIP conflict learning with recursive minimization, EVSIDS, phase saving, Glucose LBD restarts and DB reduction, incremental assumptions, assumption-based `unsat_core()`, lazy theory explanation hooks, and resource budgets (`max_conflicts`, `deadline`).
- **Theories & Combination (`unsat.theories`, `unsat.smt`)**:
  - **EUF**: Congruence closure with signature table, copy-free trail-undo log, and proof forest minimal conflict explanations.
  - **LRA / LIA / NLA**: Exact rational `fractions.Fraction` Simplex with infinitesimals (`a + b * delta`), branch-and-bound, Gomory cuts, nonlinear `QF_NRA`/`QF_NIA` solving (interval constraint propagation, Sturm real-root isolation, linearization lemmas), and complete Euclidean integer operators (`div`, `mod`, `abs`, `to_int`, `is_int`, `(_ divisible n)`).
  - **Bit-Vectors**: Word-level `BVDomain` propagation (`BVSolver`) with on-demand `BitBlaster` escalation and explicit `BitBlastTactic` / `ModelConverter` support.
  - **Arrays**: Lazy Read-over-Write (`select` / `store`), constant arrays (`const`), and extensionality lemmas.
  - **Strings & Regular Expressions**: `String` / `RegLan` sorts, full SMT-LIB2 2.6 string and regex operators (`\u{...}` / `\uXXXX` escapes up to `0x2FFFF`), Brzozowski derivative regex analysis, word-equation alignment and Nielsen splitting, and concrete `str` model synthesis.
  - **MBTC**: Model-Based Theory Combination across EUF, arithmetic, bit-vectors, arrays, and strings.
- **Quantifiers (`unsat.quantifiers`)**: E-matching with pattern tables and Model-Based Quantifier Instantiation (`MBQI`) bounded by configurable round/match/conflict/timeout budgets.
- **Tactics (`unsat.tactics`)**: Composable AST preprocessing (`SimplifyTactic`, `NNFTactic`, `BitBlastTactic`, `SkolemizeTactic`, `CtxSimplifyTactic`, `GaussianElimTactic`, `PropagateBoundsTactic`) with `ModelConverter` reconstruction via `solve_with_tactic`.
- **Frontends (`unsat.api`, `unsat.parser`, `unsat.cli`)**: Python DSL (`Solver`, `Int`, `Real`, `BitVec`, `Array`, `String`, `RegLan`, `Bool`, `Function`, `ForAll`, `Exists`), DIMACS CNF parser/formatter, zero-dependency TPTP FOF parser/formatter (`parse_fof`, `to_tptp_expr`, `solve_tptp`), and interactive SMT-LIB2 command runner.

## Supported SMT-LIB2 Logics & Commands

- **Logics**: `QF_BOOL`, `QF_UF`, `QF_LRA`, `QF_LIA`, `QF_UFLRA`, `QF_UFLIA`, `QF_LIRA`, `QF_NRA`, `QF_NIA`, `QF_NIRA`, `QF_UFNRA`, `QF_UFNIA`, `QF_UFNIRA`, `QF_BV`, `QF_UFBV`, `QF_AX`, `QF_ABV`, `QF_AUFBV`, `QF_ALIA`, `QF_ALRA`, `QF_ANRA`, `QF_ANIA`, `QF_AUFLIA`, `QF_AUFLRA`, `QF_AUFLIRA`, `QF_AUFNRA`, `QF_AUFNIA`, `QF_AUFNIRA`, `QF_S`, `QF_SLIA`, `QF_SNIA`, `QF_UFS`, `QF_UFSLIA`, `QF_AS`, `QF_AUFSLIA`, `UF`, `LIA`, `LRA`, `LIRA`, `NRA`, `NIA`, `NIRA`, `UFLIA`, `UFLRA`, `UFLIRA`, `UFNRA`, `UFNIA`, `UFNIRA`, `BV`, `UFBV`, `AX`, `ABV`, `AUFBV`, `ALIA`, `ALRA`, `AUFLIA`, `AUFLRA`, `AUFLIRA`, `AUFNRA`, `AUFNIA`, `AUFNIRA`, `S`, `SLIA`, `SNIA`, `UFS`, `UFSLIA`, `AS`, `AUFSLIA`, `ALL`.
- **Commands**: `set-logic`, `set-option`, `set-info`, `declare-sort`, `define-sort`, `declare-const`, `declare-fun`, `define-fun`, `assert` (with top-level `:named`), `check-sat`, `check-sat-assuming`, `get-model`, `get-value`, `get-unsat-core`, `get-assertions`, `push`, `pop`, `reset`, `reset-assertions`, `echo`, `exit`.

## Installation

Requires Python 3.14 or newer.

```bash
uv add unsat
# or
pip install unsat
```

For local development (includes `pytest`, `hypothesis`, `z3-solver` for differential tests, `ruff`, `ty`, `import-linter`, and `rumdl`):

```bash
uv sync --locked --all-extras --dev
```

## Quick Start

### Python DSL

```python
from unsat import Eq, Int, SAT, Solver

x, y = Int("x"), Int("y")
solver = Solver(timeout=5.0, max_conflicts=10_000)
solver.add(Eq(x + y, 10), x > y, y >= 2)

if solver.check() is SAT:
    model = solver.model()
    print(model.eval_int(x), model.eval_int(y))
```

### Preprocessing Tactics

```python
from unsat import Context
from unsat.smt import SolveResult, solve_with_tactic
from unsat.tactics import (
    CtxSimplifyTactic,
    GaussianElimTactic,
    PropagateBoundsTactic,
    SimplifyTactic,
    Then,
)

ctx = Context()
x, y = ctx.mk_int("x"), ctx.mk_int("y")
pipeline = Then(
    CtxSimplifyTactic(),
    GaussianElimTactic(),
    PropagateBoundsTactic(),
    SimplifyTactic(),
)
verdict, model = solve_with_tactic([ctx.mk_eq(x, y + 3), y >= 4, x <= 10], pipeline)
assert verdict is SolveResult.SAT and model is not None
```

### Command Line Interface

```bash
unsat problem.smt2
unsat problem.cnf --stats --timeout 5.0 --max-conflicts 5000
python -m unsat - --format smt2 < script.smt2
```

Available CLI options include `--format {auto,dimacs,smt2,tptp}`, `--stats`, `--timeout`, `--max-conflicts`, `--max-quantifier-rounds`, `--max-quantifier-matches`, and `--version`.

## Development & Benchmarks

```bash
uv run ruff check .
uv run ruff format --check .
uv run ty check
uv run lint-imports
uv run rumdl check .
uv run pytest tests
uv run python benchmarks/run.py --check
uv run python benchmarks/run.py --z3 --check
```

## Documentation

- [Architecture & Module Layout](docs/architecture/README.md)
- [Design & Roadmap](docs/designs/README.md)
- [Changelog](CHANGELOG.md)

## License

Licensed under the [Apache License 2.0](LICENSE).
