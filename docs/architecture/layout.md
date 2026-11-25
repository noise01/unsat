# Directory Layout & Design Conventions

This document describes the repository layout and module organization conventions for `unsat`. See [Module Responsibilities & Dependency DAG](dependencies.md) for allowed internal imports and enforcement contracts.

## Repository Layout

```text
.
├── AGENTS.md                        # Repository guide and engineering invariants for agents
├── CHANGELOG.md                     # Versioned release notes (Keep a Changelog format)
├── pyproject.toml                   # Active `unsat` package config, uv workspace, lint/import contracts
├── benchmarks/                      # Curated DIMACS & SMT-LIB2 benchmark suite + runner
│   ├── run.py
│   ├── dimacs/
│   └── smt2/
├── docs/
│   ├── architecture/                # Repository layout and dependency DAG documentation
│   └── designs/                     # Core solver designs, verification strategy, and roadmap
├── packages/
│   └── unsat-legacy/                # Reserved workspace slot for archived legacy implementations
├── src/unsat/
│   ├── __init__.py                  # Public API façade (`__all__` re-exports from api.py; no CLI main)
│   ├── __main__.py                  # `python -m unsat` entry point delegating exclusively to cli.main
│   ├── py.typed                     # PEP 561 typed package marker
│   ├── api.py                       # Thin Z3Py-style Python DSL / builder layer
│   ├── cli.py                       # CLI entry point (`unsat = "unsat.cli:main"`)
│   ├── syntax/
│   │   ├── __init__.py              # Public syntax exports
│   │   ├── kinds.py                 # SortKind / DeclKind enums
│   │   ├── bv_eval.py               # Pure bit-vector concrete evaluation helpers
│   │   ├── expr.py                  # Immutable hash-consed Sort, FuncDecl, Expr, Quantifier nodes
│   │   ├── context_arith.py         # Arithmetic builder helpers mixed into Context
│   │   ├── context_bv.py            # Bit-vector builder helpers mixed into Context
│   │   ├── context.py               # WeakValueDictionary-backed AST Context
│   │   └── walk.py                  # Iterative traversal, substitution, de Bruijn, SMT-LIB2 formatting
│   ├── sat/
│   │   ├── __init__.py              # Standalone SAT exports
│   │   ├── types.py                 # Lit, Var, Clause, SolveResult, TheoryPropagator protocol
│   │   ├── heap.py                  # EVSIDS variable activity heap
│   │   ├── trail.py                 # Assignment trail and decision levels
│   │   └── solver.py                # CDCL SAT solver core with restarts, LBD reduction, budgets
│   ├── model/
│   │   ├── __init__.py              # Model exports
│   │   ├── values.py                # Concrete values and FuncInterp tables
│   │   ├── eval.py                  # Model container and recursive formula evaluator
│   │   └── converters.py            # ModelConverter implementations for tactic reconstruction
│   ├── theories/
│   │   ├── __init__.py              # Theory solver exports
│   │   ├── base.py                  # TheorySolver interface
│   │   ├── euf.py                   # Congruence closure with signature table & proof forest
│   │   ├── lra.py                   # Exact rational Simplex with infinitesimals
│   │   ├── lia.py                   # Branch-and-bound and Gomory cuts over LRA
│   │   └── arrays.py                # Lazy Read-over-Write and extensionality solver
│   ├── tactics/
│   │   ├── __init__.py              # Tactic exports
│   │   ├── base.py                  # Tactic, TacticResult, Then combinator
│   │   ├── simplify.py              # Algebraic / Boolean AST normalization tactic
│   │   ├── nnf.py                   # Negation normal form conversion
│   │   ├── bitblast.py              # Eager BV simplification and CNF bit-blasting
│   │   ├── skolem.py                # Existential Skolemization with ProjectionModelConverter
│   │   ├── ctx_simplify.py          # Contextual unit simplification
│   │   └── elim.py                  # Gaussian elimination and bound propagation tactics
│   ├── quantifiers/
│   │   ├── __init__.py              # Quantifier exports
│   │   ├── base.py                  # QuantifierBudget, QuantifierStats, SubSolver protocol
│   │   ├── ematch.py                # E-matching over the EUF E-graph
│   │   └── mbqi.py                  # Model-Based Quantifier Instantiation
│   ├── smt/
│   │   ├── __init__.py              # CDCL(T) exports (`SMTSolver`, `SolveResult`, `solve_with_tactic`)
│   │   ├── propagator.py            # Combined EUF / LRA / Array / shared-BV TheoryPropagator
│   │   ├── encoder.py               # Incremental Plaisted-Greenbaum Tseitin encoder
│   │   └── solver.py                # SMTSolver, MBTC loop, quantifier orchestration, solve_with_tactic
│   └── parser/
│       ├── __init__.py              # Parser and runner exports
│       ├── dimacs.py                # DIMACS CNF parser, solver helper, formatter
│       └── smt2/
│           ├── __init__.py          # SMT-LIB2 parser/runner exports
│           ├── lexer.py             # Lexer and S-expression parser
│           ├── format.py            # SMT-LIB2 model formatter
│           └── runner.py            # Stateful SMT2Runner and script helpers
└── tests/                           # Mirrors src/unsat/ + property tests, contracts, and benchmark tests
```

Tests under `tests/` mirror `src/unsat/` cleanly (for example, `tests/sat/`, `tests/syntax/`, `tests/theories/`, `tests/smt/`, `tests/tactics/`, `tests/quantifiers/`, `tests/model/`, `tests/parser/`) alongside cross-cutting contract tests (`test_import_contracts.py`, `test_import_cost.py`, `test_public_annotations.py`, `test_structure.py`, `test_benchmarks.py`).

## Design Conventions

- **Hybrid granularity**: Subsystems are organized as subpackages (`syntax/`, `sat/`, `model/`, `theories/`, `tactics/`, `quantifiers/`, `smt/`, `parser/`), promoting single files to multi-file subpackages cleanly without breaking package imports. Shared exceptions (`errors.py`) are introduced only when exceptions need to be shared across multiple top-level packages (and must be registered in [`pyproject.toml`](../../pyproject.toml) import-linter contracts and [`tests/test_import_contracts.py`](../../tests/test_import_contracts.py)).
- **Naming rules**:
  - Singular for single cohesive subsystems: `syntax`, `sat`, `parser`, `smt`, `model`.
  - Plural for collections of pluggable implementations: `theories`, `tactics`, `quantifiers`.
  - `syntax/` is used instead of `ast/` to reflect mathematical-logic terminology and avoid confusion with Python's standard-library `ast` module.
- **Thin DSL layer (`api.py`)**: `api.py` provides user-facing builders, syntactic sugar, and default-context management directly over `syntax` objects (avoiding a redundant wrapper AST hierarchy) so `syntax` stays stateless and pure.
- **Public visibility**: Subpackages do not use a leading underscore (`unsat.sat`, `unsat.theories`, etc.), making standalone SAT usage and external theory/tactic extensions straightforward. `unsat/__init__.py` curates the everyday user-facing API via `__all__` by re-exporting from `unsat.api`.
- **CLI separation**: CLI concerns live in `unsat.cli` and `unsat.__main__` (`unsat = "unsat.cli:main"`), with `__main__` delegating exclusively to `cli`, keeping `import unsat` free of CLI parsing overhead.
- **Legacy archive slot (`packages/unsat-legacy/`)**: Isolated `uv` workspace member reserved for archived legacy implementations and differential reference comparisons, independent from the shipped `unsat` distribution.
