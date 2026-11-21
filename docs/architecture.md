# Architecture

`unsat` is a Z3-inspired SMT solver written in Python. The codebase adopts Z3's high-level conceptual separation while following Pythonic packaging and dependency conventions.

## Directory Layout

```text
src/unsat/
├── __init__.py          # Public API façade (__all__ re-exports from api.py; no CLI main)
├── __main__.py          # `python -m unsat` entry point delegating exclusively to cli.main
├── py.typed             # PEP 561 typed package marker
├── api.py               # Thin user-facing Z3Py-style Python DSL / builder layer (no duplicate AST wrappers)
├── cli.py               # CLI entry point (`unsat = "unsat.cli:main"`)
├── smt.py               # CDCL(T) orchestrator & Tseitin clausification (promotes to smt/ when it grows)
├── model.py             # Model representation, evaluation & reconstruction (promotes to model/ when it grows)
├── syntax/
│   └── __init__.py      # Stateless sorts, declarations, terms, formulas, and explicit contexts
├── sat/
│   └── __init__.py      # Standalone propositional CDCL SAT solver core
├── theories/
│   └── __init__.py      # Theory solver implementations (EUF, LRA, LIA, BV, Arrays, ...)
├── tactics/
│   └── __init__.py      # Pure AST-to-AST preprocessing, simplification, and reduction tactics
├── quantifiers/
│   └── __init__.py      # Quantifier reasoning (E-matching, MBQI, ...)
└── parser/
    └── __init__.py      # Input/output parsers, formatters, and command runners (SMT-LIB2, DIMACS, ...)
```

Tests under `tests/` mirror `src/unsat/` incrementally as modules are implemented (for example, `tests/sat/`, `tests/syntax/`, `tests/theories/`) without pre-creating empty test directories.

## Design Conventions

- **Hybrid granularity**: Multi-module domains (`syntax/`, `sat/`, `theories/`, `tactics/`, `quantifiers/`, `parser/`) start as subpackages with only `__init__.py`; internal module files are added as each subsystem is built. Single-file entry modules (`api.py`, `cli.py`, `smt.py`, `model.py`) promote seamlessly to packages (`smt/`, `model/`, etc.) without breaking imports when they outgrow one file. Shared exceptions (`errors.py`) are introduced only when exceptions need to be shared across multiple modules.
- **Naming rules**:
  - Singular for single cohesive subsystems: `syntax`, `sat`, `parser`, `smt`, `model`.
  - Plural for collections of pluggable implementations: `theories`, `tactics`, `quantifiers`.
  - `syntax/` is used instead of `ast/` to reflect mathematical-logic terminology and avoid confusion with Python's standard-library `ast` module.
- **Thin DSL layer (`api.py`)**: `api.py` provides user-facing builders, syntactic sugar, and default-context management directly over `syntax` objects (avoiding a redundant wrapper AST hierarchy) so `syntax` stays stateless and pure.
- **Public visibility**: Subpackages do not use a leading underscore (`unsat.sat`, `unsat.theories`, etc.), making standalone SAT usage and external theory/tactic extensions straightforward. `unsat/__init__.py` curates the everyday user-facing API via `__all__`, starting with straightforward top-level re-exports from `unsat.api`; it can later adopt PEP 562 (`__getattr__`) lazy re-exports without breaking public API compatibility if startup or import isolation warrants it.
- **CLI separation**: CLI concerns live in `unsat.cli` and `unsat.__main__` (`unsat = "unsat.cli:main"`), with `__main__` delegating exclusively to `cli`, keeping `import unsat` free of CLI parsing overhead.

## Module Responsibilities

| Module | Role | Allowed Internal Dependencies |
| --- | --- | --- |
| `unsat.syntax` | Stateless sorts, function declarations, AST/terms, formulas, and explicit AST contexts | None |
| `unsat.sat` | Pure propositional CDCL SAT core (integer variables, literals, clauses, and theory-hook protocols) | None |
| `unsat.model` | Model representation, formula evaluation, and model reconstruction (`ModelConverter`) | `syntax` |
| `unsat.theories` | Theory solver implementations (EUF, LRA, LIA, BV, Arrays, etc.) | `syntax`, `model` |
| `unsat.tactics` | Pure AST-to-AST preprocessing, simplification, reduction tactics, and model converters (excludes SAT clausification) | `syntax`, `model` |
| `unsat.quantifiers` | Quantifier instantiation and reasoning (E-matching, MBQI via injected sub-solver protocols) | `syntax`, `theories`, `model` |
| `unsat.smt` | CDCL(T) orchestrator bridging `syntax` and `sat`, Tseitin clausification, push/pop, theory combination, and callback injection | `syntax`, `sat`, `theories`, `tactics`, `quantifiers`, `model` |
| `unsat.api` | Thin Z3Py-style Python DSL builders, syntactic sugar, and default context (`Solver`, `Int`, `Bool`, `And`, ...) without duplicate AST wrappers | `syntax`, `smt`, `model` |
| `unsat.parser` | SMT-LIB2 and DIMACS parsers, formatters, and command execution frontends | `syntax`, `sat`, `smt`, `model` |
| `unsat.cli` | Command-line executable | `parser`, `smt`, `sat` |
| `unsat.__main__` | Delegates `python -m unsat` exclusively to `cli` | `cli` |
| `unsat.__init__` | Curated public exports (`__all__`) | `api` |

## Dependency DAG & Invariants

```text
          __main__
             │
             ▼
            cli                               __init__
         /   │   \                               │
        ▼    ▼    ▼                              ▼
     parser─►sat◄─smt ◄──────────────────────── api
      │  └───────►│  \   \                      │
      │          /    ▼   ▼                     │
      │         │  quantifiers  tactics         │
      │         │     │           │             │
      │         ▼     ▼           │             │
      │        theories           │             │
      │            \              │             │
      │             ▼             ▼             │
      └────────────►    model    ◄──────────────┘
                          │
                          ▼
                        syntax  (bottom layer; zero internal deps)
```

*(Note: higher layers may also import `syntax` and `model` directly as listed in the table above; transitive edges are omitted from the diagram for readability, and `sat` is standalone with zero internal dependencies.)*

Key architectural invariants:

1. **Strict Acyclic Dependencies**: Imports must follow the DAG above strictly downward; circular imports across subsystems are forbidden.
2. **Bottom-Layer `syntax/`**: `unsat.syntax` has zero internal dependencies on any other `unsat` module.
3. **Standalone `sat/`**: `unsat.sat` has zero internal dependencies and **must never import `unsat.syntax`**. `unsat.smt` mediates between `syntax` expressions and `sat` integer literals.
4. **Dependency Inversion for Upward Coordination**: Lower layers (`sat`, `quantifiers`, etc.) never import `smt`. When upward coordination is needed (such as online CDCL(T) theory propagation hooks in `sat` or MBQI sub-solver queries in `quantifiers`), the lower layer defines an abstract `Protocol`/callback interface and `smt` injects the concrete implementation.
5. **`tactics` vs. `smt` Boundary**: `unsat.tactics` performs pure AST-to-AST transformations (and produces model converters via `model`). Encoding Boolean ASTs into integer SAT clauses (Tseitin clausification) lives in `unsat.smt` together with the AST-to-SAT variable mapping.
