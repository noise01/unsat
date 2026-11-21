# Architecture

`unsat` is a Z3-inspired SMT solver written in Python. The codebase adopts Z3's high-level conceptual separation while following Pythonic packaging and dependency conventions.

## Directory Layout

```text
src/unsat/
├── __init__.py          # Public API façade (__all__ re-exports from api.py; no CLI main)
├── __main__.py          # `python -m unsat` entry point delegating to cli.main
├── py.typed             # PEP 561 typed package marker
├── api.py               # User-facing Z3Py-style Python DSL
├── cli.py               # CLI entry point (`unsat = "unsat.cli:main"`)
├── smt.py               # CDCL(T) orchestrator (promotes to smt/ when it grows)
├── model.py             # Model representation & evaluation (promotes to model/ when it grows)
├── syntax/
│   └── __init__.py      # Sorts, declarations, terms, formulas, and contexts
├── sat/
│   └── __init__.py      # Standalone propositional CDCL SAT solver core
├── theories/
│   └── __init__.py      # Theory solver implementations (EUF, LRA, LIA, BV, Arrays, ...)
├── tactics/
│   └── __init__.py      # Formula preprocessing, simplification, and reduction tactics
├── quantifiers/
│   └── __init__.py      # Quantifier reasoning (E-matching, MBQI, ...)
└── parser/
    └── __init__.py      # Input format parsers (SMT-LIB2, DIMACS, ...)
```

Tests under `tests/` mirror `src/unsat/` incrementally as modules are implemented (for example, `tests/sat/`, `tests/syntax/`, `tests/theories/`) without pre-creating empty test directories.

## Design Conventions

- **Hybrid granularity**: Multi-module domains (`syntax/`, `sat/`, `theories/`, `tactics/`, `quantifiers/`, `parser/`) start as subpackages with only `__init__.py`; internal module files are added as each subsystem is built. Single-file entry modules (`api.py`, `cli.py`, `smt.py`, `model.py`) promote seamlessly to packages (`smt/`, `model/`, etc.) without breaking imports when they outgrow one file. Shared exceptions (`errors.py`) are introduced only when exceptions need to be shared across multiple modules.
- **Naming rules**:
  - Singular for single cohesive subsystems: `syntax`, `sat`, `parser`, `smt`, `model`.
  - Plural for collections of pluggable implementations: `theories`, `tactics`, `quantifiers`.
  - `syntax/` is used instead of `ast/` to reflect mathematical-logic terminology and avoid confusion with Python's standard-library `ast` module.
- **Public visibility**: Subpackages do not use a leading underscore (`unsat.sat`, `unsat.theories`, etc.), making standalone SAT usage and external theory/tactic extensions straightforward, while `unsat/__init__.py` curates the everyday user-facing API via `__all__`.
- **CLI separation**: CLI concerns live in `unsat.cli` and `unsat.__main__` (`unsat = "unsat.cli:main"`), keeping `import unsat` free of CLI parsing overhead.

## Module Responsibilities

| Module | Role | Allowed Internal Dependencies |
| --- | --- | --- |
| `unsat.syntax` | Sorts, function declarations, AST/terms, formulas, and AST context | None |
| `unsat.sat` | Pure propositional CDCL SAT core (integer variables, literals, clauses) | None |
| `unsat.model` | Model representation, formula evaluation, and model reconstruction | `syntax` |
| `unsat.theories` | Theory solvers (EUF, LRA, LIA, BV, Arrays, etc.) | `syntax`, `model` |
| `unsat.tactics` | Formula simplification, Tseitin/CNF conversion, bit-blasting, etc. | `syntax`, `model` |
| `unsat.quantifiers` | Quantifier instantiation and reasoning (E-matching, MBQI) | `syntax`, `theories`, `model` |
| `unsat.smt` | CDCL(T) orchestrator bridging `syntax` and `sat`, push/pop, theory combination | `syntax`, `sat`, `theories`, `tactics`, `quantifiers`, `model` |
| `unsat.api` | Z3Py-style Python DSL (`Solver`, `Int`, `Bool`, `And`, ...) | `syntax`, `smt`, `model` |
| `unsat.parser` | SMT-LIB2, DIMACS, and command execution frontends | `syntax`, `sat`, `smt`, `api` |
| `unsat.cli` | Command-line executable | `parser`, `smt`, `sat` |
| `unsat.__main__` | Delegates `python -m unsat` to the CLI | `cli`, `parser`, `smt`, `sat` |
| `unsat.__init__` | Curated public exports (`__all__`) | `api` |

## Dependency DAG & Invariants

```text
               cli / __main__
                /     |     \
               ▼      |      ▼
            parser    |     sat  (standalone; zero internal deps)
             /  \     |      ▲
            ▼    ▼    ▼      │
           api ─► smt ───────┘
            │    / │ \
            │   │  │  └──────┐
            │   │  ▼         ▼
            │   │ quantifiers tactics
            │   │  │           │
            │   ▼  ▼           │
            │ theories         │
            │     \            │
            │      ▼           │
            └─────►   model  ◄─┘
                        │
                        ▼
                      syntax     (bottom layer; zero internal deps)
```

*(Note: higher layers may also import `syntax` and `model` directly as listed in the table above; transitive edges are omitted from the diagram for readability.)*

Key architectural invariants:

1. **Strict Acyclic Dependencies**: Imports must follow the DAG above strictly downward; circular imports across subsystems are forbidden.
2. **Bottom-Layer `syntax/`**: `unsat.syntax` has zero internal dependencies on any other `unsat` module.
3. **Standalone `sat/`**: `unsat.sat` has zero internal dependencies and **must never import `unsat.syntax`**. `unsat.smt` mediates between `syntax` expressions and `sat` integer literals.
