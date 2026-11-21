# Design & Roadmap

This document records the core design decisions, supported logics, verification strategy, and phased implementation roadmap for `unsat`. See [Architecture & Module Layout](architecture.md) for package structure and dependency contracts.

## Project Positioning

- **Goal**: A pure Python 3.14 (`requires-python = ">=3.14"`) Z3-inspired SMT solver balancing a practical, production-style CDCL(T) architecture with algorithmic clarity and extensibility, targeting reliable solving on small-to-medium instances.
- **Target scope**: Five core theories (`EUF`, `LRA`, `LIA`, `BV`, `Arrays`), multi-theory combination via Model-Based Theory Combination (`MBTC`), and basic quantifier reasoning (`E-matching` and `MBQI`).
- **Frontends**: The Python DSL (`unsat.api`) and text format frontends (`DIMACS` followed by `SMT-LIB2` in `unsat.parser`) evolve in parallel. `unsat.api` aims for Z3Py-like ergonomics while prioritizing Pythonic clarity and static type safety (`ty`) over strict 100% Z3Py API compatibility.

## Core Design Decisions

### SAT Core (`unsat.sat`)

- **Representation and hot path**: Encode literals as signed integers `Lit = (var << 1) | sign` (`lit ^ 1` negation, `lit >> 1` variable) with direct `lit_eval[lit]` indexing. Use dedicated binary-clause watch lists (`bin_watches`) and blocker-literal watch lists (`watches`) for clauses of length 3+.
- **Full incremental CDCL**: Two-watched literals (2WL), 1-UIP conflict analysis with recursive learned-clause minimization, EVSIDS variable decision heuristic, phase saving, Luby/Glucose restarts, LBD-based learned-clause database reduction that cleans deleted clauses from both `watches` and `bin_watches`, incremental `add_clause`, `solve(assumptions=...)`, and assumption-based `unsat_core()`.
- **Top-level state and input hygiene**: Normalize duplicate literals and drop tautologies in `add_clause`, track top-level consistency cleanly via an explicit `ok` state, and distinguish a valid 0-variable `SAT` model (`{}`) from `UNSAT` (no model available).
- **Online CDCL(T) hooks with true lazy explanation from M1**: `unsat.sat` defines an optional integer-literal `TheoryPropagator` `Protocol` (defaulting to `None` for standalone SAT) covering theory propagation, conflict reporting, **lazy explanation** clauses requested only when conflict analysis traverses a theory-propagated literal (safely handling unit explanations and theory conflicts without eager watcher attachment on every propagation), and backtrack notifications. Building this hook surface upfront avoids rewriting the SAT loop when theories arrive in M3.

### AST & Python DSL (`unsat.syntax`, `unsat.api`)

- **Explicit `Context` with weakref hash-consing**: `unsat.syntax` manages `Sort`, `FuncDecl`, and `Expr` nodes inside an explicit `Context` via `WeakValueDictionary` (using `@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)` nodes), assigning sequential integer IDs and storing an explicit reference to the owning `Context`. Nodes are strictly immutable post-construction—`unsat.syntax` holds no global state, and `unsat.api` manages a convenient default context.
- **Structural operator dispatch and lightweight normalization**: Identify built-in operators and symbols via a `DeclKind` / `ExprKind` `Enum` rather than string-name comparisons (preventing collisions with user-defined uninterpreted symbols), paired with lightweight normalizing constructors (`And`/`Or` flattening, deduplication, identity/absorbing constants, and double-negation elimination).
- **No duplicate AST wrapper hierarchy**: `unsat.api` is a thin builder/sugar layer that constructs and returns `syntax` objects directly rather than wrapping them in a second AST class hierarchy.
- **Equality, hashing, and operators**: `Expr.__eq__` and `Expr.__ne__` preserve standard Python structural identity (`bool`, `self is other`), and `Expr` remains hashable (keyed by its hash-consed ID) so `dict[Expr, T]`, `set[Expr]`, and static type checking work naturally. Formula-level equality and disequality ASTs are built via `Eq(a, b)` and `Distinct(a, b, ...)`. Arithmetic, comparison, and bitwise/logical operators (`+`, `-`, `*`, `<`, `<=`, `>`, `>=`, `&`, `|`, `~`, etc.) are overloaded on `Expr`, while `Expr.__bool__` raises `TypeError` to catch accidental Python truth-value coercion (such as `if x < 5:` or `a and b`).

### CDCL(T) Orchestration (`unsat.smt`)

- **Incremental `push` / `pop`**: At the SAT layer, assertion scopes use per-scope activation literals passed via `assumptions`, permanently falsifying popped scope literals at decision level 0 so dead scope clauses are invalidated while keeping learned clauses sound and reusable across scopes. At the theory layer, solvers maintain backtrackable undo trails unifying user `push` / `pop` with search-level backtracking.
- **Polarity-aware Tseitin clausification**: Translating Boolean AST formulas into integer SAT clauses (Plaisted-Greenbaum polarity-aware incremental encoding, avoiding fragile incremental clause-level pure-literal elimination) alongside the bidirectional AST-to-SAT variable mapping lives in `unsat.smt`. `unsat.tactics` stays strictly AST-to-AST (paired with `ModelConverter` in `unsat.model`).
- **Theory combination (MBTC)**: Multi-theory reasoning uses Z3-style Model-Based Theory Combination (`MBTC`) with `EUF` as the shared-equality hub. Interface equalities between shared terms are speculated and checked on demand when candidate theory models assign equal values, avoiding eager `O(n^2)` equality case-splitting.

### Theories, Tactics & Quantifiers (`unsat.theories`, `unsat.tactics`, `unsat.quantifiers`)

- **EUF (`unsat.theories`)**: Congruence Closure backed by a Signature Table for `O(1)` congruence lookup, a copy-free trail-length undo log (avoiding per-merge list copies), and a proof forest for minimal conflict explanations. Predicate congruence is handled uniformly by registering Boolean predicate applications `P(t)` as `Eq(P(t), true)`.
- **Linear arithmetic (`LRA`, `LIA`)**: Exact rational arithmetic built on `fractions.Fraction` paired with infinitesimal `a + b * delta` values (Dutertre & de Moura Simplex) handles strict inequalities with zero floating-point precision errors. `LIA` builds on `LRA` with branch-and-bound and cutting planes (e.g., Gomory cuts).
- **Bit-Vectors (`BV`)**: Initial support uses word-level simplification and eager bit-blasting tactics in `unsat.tactics` paired with `ModelConverter` for clean, fast `QF_BV`. When mixed-theory logics (such as `QF_AUFBV`) require MBTC interaction, bit-vectors extend into a lazy `unsat.theories.bv` theory solver.
- **Arrays (`Arrays`)**: Lazy Read-over-Write (`select` / `store`) and extensionality axiom instantiation integrated with `EUF`.
- **Quantifiers (`unsat.quantifiers`)**: Anytime resource budgets (`max_rounds` and `max_matches` candidate-binding caps) with conservative three-valued verdicts (`SAT`, `UNSAT`, `UNKNOWN`). Truncating quantifier search on a spent budget never claims `SAT` (downgrading to `UNKNOWN`), while ground-derived `UNSAT` remains sound. Extracted default triggers/patterns stay in matcher-owned tables rather than mutating immutable AST nodes.

### Verification & Soundness Strategy

- **Zero runtime dependencies**: The shipped package keeps zero runtime dependencies; `z3-solver` is strictly a dev-only verification dependency.
- **Multi-layered verification**:
  - **Z3 differential testing**: Render backend-neutral generated formulas and terms into both `unsat` and `z3` and assert verdict agreement across SAT, EUF, arithmetic, BV, arrays, and combined fragments (treating unexpected `UNKNOWN` on complete fragments as failures).
  - Small-domain exhaustive brute-force reference oracles for propositional/finite-domain correctness.
  - `hypothesis` property-based fuzzing across incremental solving, `push`/`pop`, both-polarity assumption `unsat_core` soundness, reused-vs-fresh solver equivalence, and mock `TheoryPropagator` interactions.
  - Independent model evaluation (`model.eval(formula) == True`) verified on every `SAT` result.
  - `unsat_core` soundness re-verification (confirming the extracted core alone is `UNSAT`).
  - Curated in-repo DIMACS and SMT-LIB2 benchmark and regression suites.
- **Package quality invariants**: As public modules grow, enforce PEP 649 public annotation resolution (`typing.get_type_hints()` on all exported callables and classes in `__all__`, keeping runtime-inspectable annotations free of `TC001`–`TC003` breaks) and import-isolation/cost checks ensuring lightweight entry points (such as `unsat.sat`) do not load parser or CLI overhead.

## Milestones

| Milestone | Logics / Scope | Key Modules |
| --- | --- | --- |
| M1 | Standalone CDCL SAT & DIMACS | `sat`, `parser`, `cli` |
| M2 | Propositional SMT End-to-End (`QF_BOOL`) | `syntax`, `model`, `tactics`, `smt`, `api`, `parser`, `cli` |
| M3 | Congruence Closure & Online CDCL(T) (`QF_UF`) | `theories`, `smt`, `syntax`, `model`, `api`, `parser` |
| M4 | Linear Arithmetic & Theory Combination (`QF_LRA`, `QF_LIA`, `QF_UFLRA`, `QF_UFLIA`) | `theories`, `smt`, `syntax`, `model`, `api`, `parser` |
| M5 | Bit-Vectors & Arrays (`QF_BV`, `QF_AX`, `QF_AUFLIA`) | `tactics`, `theories`, `syntax`, `model`, `api`, `parser` |
| M6 | Quantifiers & Advanced Tactics (`UF`, quantified arithmetic) | `quantifiers`, `tactics`, `smt`, `api`, `parser` |

### M1 — Standalone CDCL SAT Core & DIMACS Frontend

- **Primary modules**: `sat`, `parser`, `cli`
- **Scope**:
  - Implement incremental CDCL in `unsat.sat` (signed-bit `Lit`, `lit_eval`, `bin_watches`, blocker-literal `watches`, 1-UIP + recursive clause minimization, EVSIDS, phase saving, restarts, LBD clause deletion with watch cleanup, input deduplication/tautology handling, `ok` state, `assumptions`, `unsat_core`).
  - Define the integer-literal `TheoryPropagator` `Protocol` (default `None`) with propagation, conflict, true lazy explanation, and backtrack hooks.
  - Add a DIMACS CNF parser, model printer, and `unsat` CLI execution mode.
- **Exit criteria**:
  - Small CNF formulas match an exhaustive brute-force truth-table oracle across randomized tests.
  - Z3 differential tests and `hypothesis` suites pass for incremental `add_clause`, `assumptions`, `unsat_core` soundness (including both-polarity assumptions and 0-variable `SAT`), and mock `TheoryPropagator` callbacks.
  - Curated DIMACS `SAT`/`UNSAT` benchmarks and CLI smoke tests pass.

### M2 — Propositional SMT End-to-End (`QF_BOOL`)

- **Primary modules**: `syntax`, `model`, `tactics`, `smt`, `api`, `parser`, `cli`
- **Scope**:
  - Implement `WeakValueDictionary`-backed hash-consed `Context`, `Sort`, `FuncDecl` (with `DeclKind` enum), and strictly immutable `Expr` nodes (`Bool` sort, Boolean connectives/constructors including `Eq`, `Distinct`, `Ite`, and lightweight normalization).
  - Implement `Model`, formula evaluation (`eval`), and `ModelConverter` in `unsat.model`.
  - Add initial AST-to-AST simplification and NNF tactics in `unsat.tactics`.
  - Implement Plaisted-Greenbaum incremental Tseitin clausification and activation-literal `push`/`pop` (with level-0 falsification of popped scope literals) in `unsat.smt`.
  - Expose thin Boolean DSL builders (`Bool`, `Bools`, `And`, `Or`, `Not`, `Implies`, `Xor`, `Eq`, `Distinct`, `If`, `Solver`) in `unsat.api` and re-export via `unsat.__init__`.
  - Add core SMT-LIB2 parser, formatter, and command runner (`set-logic`, `declare-const`, `declare-fun`, `assert`, `check-sat`, `get-model`, `push`, `pop`, `reset`) in `unsat.parser` and wire into `unsat.cli`.
  - Add PEP 649 `typing.get_type_hints()` public annotation resolution tests and lightweight import-isolation tests.
- **Exit criteria**:
  - `QF_BOOL` problems solve end-to-end via both the Python DSL and SMT-LIB2 CLI, matching Z3 verdicts on differential tests.
  - Every `SAT` test asserts independent `model.eval(formula)` soundness; `hypothesis` covers AST construction, tactics, `push`/`pop`, reused-vs-fresh solver equivalence, and SMT-LIB2 round-trips.

### M3 — Congruence Closure & Online CDCL(T) (`QF_UF`)

- **Primary modules**: `theories`, `smt`, `syntax`, `model`, `api`, `parser`
- **Scope**:
  - Define the shared `TheorySolver` interface in `unsat.theories` with trail-based `push`/`pop` and lazy conflict/propagation explanation hooks.
  - Implement `EUF` (Congruence Closure with Signature Table for `O(1)` lookup, copy-free undo log, proof forest for minimal conflict explanations, theory propagation, and unified predicate congruence via `Eq(P(t), true)`).
  - Connect `unsat.smt` to `unsat.sat` via the `TheoryPropagator` `Protocol` for online CDCL(T) propagation, theory conflicts, and lazy explanations.
  - Extend `syntax`, `model` (finite domain interpretations), `api`, and `parser` for uninterpreted sorts and function symbols.
- **Exit criteria**:
  - `QF_UF` instances solve via both the Python DSL and SMT-LIB2, agreeing with Z3 differential tests alongside model verification on `SAT` results and minimal conflict/propagation unit tests.

### M4 — Linear Arithmetic & Theory Combination (`QF_LRA`, `QF_LIA`, `QF_UFLRA`, `QF_UFLIA`)

- **Primary modules**: `theories`, `smt`, `syntax`, `model`, `api`, `parser`
- **Scope**:
  - Add `Int` and `Real` sorts, numeric literals, arithmetic AST nodes, and operator overloads in `syntax`/`api`/`parser`.
  - Implement `LRA` Simplex using `fractions.Fraction` and `a + b * delta` infinitesimals, with theory propagation and minimal conflict explanations.
  - Implement `LIA` on top of `LRA` via branch-and-bound and cutting planes.
  - Implement `MBTC` in `unsat.smt` using `EUF` as the shared-equality hub across `EUF` + `LRA`/`LIA`.
- **Exit criteria**:
  - `QF_LRA`, `QF_LIA`, `QF_UFLRA`, and `QF_UFLIA` suites pass with exact rational/integer model evaluation checks, Z3 differential verification, and `hypothesis` randomized tests.

### M5 — Bit-Vectors & Arrays (`QF_BV`, `QF_AX`, `QF_AUFLIA`)

- **Primary modules**: `tactics`, `theories`, `syntax`, `model`, `api`, `parser`
- **Scope**:
  - Add `BitVec` and `Array` sorts, operations, and AST constructors across `syntax`, `model`, `api`, and `parser`.
  - Implement word-level bit-vector simplification and eager bit-blasting tactics paired with `ModelConverter` in `unsat.tactics` (keeping a clean path to a lazy `theories.bv` solver when mixed theories require MBTC).
  - Implement `Arrays` theory solver in `unsat.theories` via lazy Read-over-Write and extensionality lemmas cooperating with `EUF` and `MBTC`.
- **Exit criteria**:
  - `QF_BV`, `QF_AX`, and `QF_AUFLIA` benchmarks pass with verified models (including `ModelConverter` reconstruction back to bit-vector/array expressions) and Z3 differential agreement.

### M6 — Quantifiers & Advanced Tactics (`UF`, quantified arithmetic)

- **Primary modules**: `quantifiers`, `tactics`, `smt`, `api`, `parser`
- **Scope**:
  - Add `ForAll` and `Exists` binders, pattern annotations, and variable scoping across `syntax`, `model`, `api`, and `parser`.
  - Implement `E-matching` over the `EUF` E-graph and `MBQI` in `unsat.quantifiers`, using injected sub-solver `Protocol` callbacks provided by `unsat.smt`, matcher-owned pattern tables (preserving AST immutability), and anytime `max_rounds`/`max_matches` budgets with conservative `UNKNOWN` handling.
  - Expand `unsat.tactics` with stronger formula preprocessing (e.g., Skolemization, contextual simplification, Gaussian elimination / bound propagation).
- **Exit criteria**:
  - Representative quantified benchmarks produce sound `SAT`, `UNSAT`, and budget-bounded `UNKNOWN` results verified against test suites and Z3 checks.
