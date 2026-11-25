# Module Responsibilities & Dependency DAG

This document defines the package boundary contracts enforced automatically by `lint-imports` (configured in [`pyproject.toml`](../../pyproject.toml)) and [`tests/test_import_contracts.py`](../../tests/test_import_contracts.py). See [Directory Layout & Design Conventions](layout.md) for the file tree.

## Module Responsibilities

| Module | Role | Allowed Internal Dependencies |
| --- | --- | --- |
| `unsat.syntax` | Stateless sorts, function declarations, AST/terms, formulas, and explicit AST contexts | None |
| `unsat.sat` | Pure propositional CDCL SAT core (integer variables, literals, clauses, and theory-hook protocols) | None |
| `unsat.model` | Model representation, formula evaluation, and model reconstruction (`ModelConverter`) | `syntax` |
| `unsat.theories` | Theory solver implementations (`EUF`, `LRA`, `LIA`, `Arrays`, and future solvers) | `syntax`, `model` |
| `unsat.tactics` | Pure AST-to-AST preprocessing, simplification, reduction tactics, and model converters (excludes SAT clausification) | `syntax`, `model` |
| `unsat.quantifiers` | Quantifier instantiation and reasoning (`E-matching`, `MBQI` via injected sub-solver protocols) | `syntax`, `theories`, `model` |
| `unsat.smt` | CDCL(T) orchestrator bridging `syntax` and `sat`, Tseitin clausification, push/pop, theory combination, callback injection, and `solve_with_tactic` | `syntax`, `sat`, `theories`, `tactics`, `quantifiers`, `model` |
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
5. **`tactics` vs. `smt` Boundary**: `unsat.tactics` performs pure AST-to-AST transformations (and produces `ModelConverter` objects via `model`). Encoding Boolean ASTs into integer SAT clauses (Tseitin clausification) and running tactics end-to-end (`solve_with_tactic`) live in `unsat.smt`.
