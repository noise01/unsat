# Architecture

`unsat` is a Z3-inspired SMT solver written in Python. The codebase adopts Z3's high-level conceptual separation while following Pythonic packaging and dependency conventions.

## Directory Layout

```text
src/unsat/
├── __init__.py          # Public API façade (__all__ re-exports from api.py; no CLI main)
├── __main__.py          # `python -m unsat` entry point delegating exclusively to cli.main
├── py.typed             # PEP 561 typed package marker
├── api.py               # Thin user-facing Z3Py-style Python DSL / builder layer
├── cli.py               # CLI entry point (`unsat = "unsat.cli:main"`)
├── syntax/
│   ├── __init__.py      # Public syntax exports
│   ├── kinds.py         # SortKind / DeclKind enums
│   ├── bv_eval.py       # Pure bit-vector concrete evaluation helpers
│   ├── expr.py          # Immutable hash-consed Sort, FuncDecl, Expr, Quantifier nodes
│   ├── context_arith.py # Arithmetic builder helpers mixed into Context
│   ├── context_bv.py    # Bit-vector builder helpers mixed into Context
│   ├── context.py       # WeakValueDictionary-backed AST Context
│   └── walk.py          # Iterative traversal, substitution, de Bruijn, SMT-LIB2 formatting
├── sat/
│   ├── __init__.py      # Standalone SAT exports
│   ├── types.py         # Lit, Var, Clause, SolveResult, TheoryPropagator protocol
│   ├── heap.py          # EVSIDS variable activity heap
│   ├── trail.py         # Assignment trail and decision levels
│   └── solver.py        # CDCL SAT solver core with restarts, LBD reduction, budgets
├── model/
│   ├── __init__.py      # Model exports
│   ├── values.py        # Concrete values and FuncInterp tables
│   ├── eval.py          # Model container and recursive formula evaluator
│   └── converters.py    # ModelConverter implementations for tactic reconstruction
├── theories/
│   ├── __init__.py      # Theory solver exports
│   ├── base.py          # TheorySolver interface
│   ├── euf.py           # Congruence closure with signature table & proof forest
│   ├── lra.py           # Exact rational Simplex with infinitesimals
│   ├── lia.py           # Branch-and-bound and Gomory cuts over LRA
│   └── arrays.py        # Lazy Read-over-Write and extensionality solver
├── tactics/
│   ├── __init__.py      # Tactic exports
│   ├── base.py          # Tactic, TacticResult, Then combinator
│   ├── simplify.py      # Algebraic / Boolean AST normalization tactic
│   ├── nnf.py           # Negation normal form conversion
│   ├── bitblast.py      # Eager BV simplification and CNF bit-blasting
│   ├── skolem.py        # Existential Skolemization with ProjectionModelConverter
│   ├── ctx_simplify.py  # Contextual unit simplification
│   └── elim.py          # Gaussian elimination and bound propagation tactics
├── quantifiers/
│   ├── __init__.py      # Quantifier exports
│   ├── base.py          # QuantifierBudget, QuantifierStats, SubSolver protocol
│   ├── ematch.py        # E-matching over the EUF E-graph
│   └── mbqi.py          # Model-Based Quantifier Instantiation
├── smt/
│   ├── __init__.py      # CDCL(T) exports (`SMTSolver`, `SolveResult`, `solve_with_tactic`)
│   ├── propagator.py    # Combined EUF / LRA / Array / shared-BV TheoryPropagator
│   ├── encoder.py       # Incremental Plaisted-Greenbaum Tseitin encoder
│   └── solver.py        # SMTSolver, MBTC loop, quantifier orchestration, solve_with_tactic
└── parser/
    ├── __init__.py      # Parser and runner exports
    ├── dimacs.py        # DIMACS CNF parser, solver helper, formatter
    └── smt2/
        ├── __init__.py  # SMT-LIB2 parser/runner exports
        ├── lexer.py     # Lexer and S-expression parser
        ├── format.py    # SMT-LIB2 model formatter
        └── runner.py    # Stateful SMT2Runner and script helpers
```

Tests under `tests/` mirror `src/unsat/` incrementally as modules are implemented (for example, `tests/sat/`, `tests/syntax/`, `tests/theories/`) without pre-creating empty test directories.

## Design Conventions

- **Hybrid granularity**: Subsystems are organized as subpackages (`syntax/`, `sat/`, `model/`, `theories/`, `tactics/`, `quantifiers/`, `smt/`, `parser/`), promoting single files to multi-file subpackages cleanly without breaking package imports. Shared exceptions (`errors.py`) are introduced only when exceptions need to be shared across multiple top-level packages.
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
5. **`tactics` vs. `smt` Boundary**: `unsat.tactics` performs pure AST-to-AST transformations (and produces model converters via `model`). Encoding Boolean ASTs into integer SAT clauses (Tseitin clausification) lives in `unsat.smt` together with the AST-to-SAT variable mapping.
