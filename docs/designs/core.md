# Core Solver Design

This document records the core architectural and algorithmic decisions in `unsat`.

## Project Positioning

- **Goal**: A pure Python 3.14 (`requires-python = ">=3.14"`) Z3-inspired SMT solver balancing a practical, production-style CDCL(T) architecture with algorithmic clarity and extensibility, targeting reliable solving on small-to-medium instances.
- **Target scope**: Five core theories (`EUF`, `LRA`, `LIA`, `BV`, `Arrays`), multi-theory combination via Model-Based Theory Combination (`MBTC`), and quantifier reasoning (`E-matching` and `MBQI`).
- **Frontends**: The Python DSL (`unsat.api`) and text format frontends (`DIMACS` and `SMT-LIB2` in `unsat.parser`) evolve in parallel. `unsat.api` aims for Z3Py-like ergonomics while prioritizing Pythonic clarity and static type safety (`ty`) over strict 100% Z3Py API compatibility.

## SAT Core (`unsat.sat`)

- **Representation and hot path**: Encode literals as signed integers `Lit = (var << 1) | sign` (`lit ^ 1` negation, `lit >> 1` variable) with direct `lit_eval[lit]` indexing. Use dedicated binary-clause watch lists (`bin_watches`) and blocker-literal watch lists (`watches`) for clauses of length 3+.
- **Full incremental CDCL**: Two-watched literals (2WL), 1-UIP conflict analysis with recursive learned-clause minimization, EVSIDS variable decision heuristic, phase saving, Glucose LBD restarts and database reduction (cleaning deleted clauses from both `watches` and `bin_watches`), incremental `add_clause`, `solve(assumptions=...)`, assumption-based `unsat_core()`, and `max_conflicts` / `deadline` resource budgets.
- **Top-level state and input hygiene**: Normalize duplicate literals and drop tautologies in `add_clause`, track top-level consistency cleanly via an explicit `ok` state, distinguish a valid 0-variable `SAT` model (`{}`) from `UNSAT`, and keep `ok` intact when aborting with `UNKNOWN`.
- **Online CDCL(T) hooks with true lazy explanation**: `unsat.sat` defines an optional integer-literal `TheoryPropagator` `Protocol` (defaulting to `None` for standalone SAT) covering theory propagation, conflict reporting, **lazy explanation** clauses requested only when conflict analysis traverses a theory-propagated literal, batch theory lemma installation without dropping post-conflict lemmas, and backtrack notifications.

## AST & Python DSL (`unsat.syntax`, `unsat.api`)

- **Explicit `Context` with weakref hash-consing**: `unsat.syntax` manages `Sort`, `FuncDecl`, and `Expr` nodes inside an explicit `Context` via `WeakValueDictionary` (using `@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)` nodes), assigning sequential integer IDs and storing an explicit reference to the owning `Context`. Nodes are strictly immutable post-construction—`unsat.syntax` holds no global state, and `unsat.api` manages a convenient default context.
- **Structural operator dispatch and lightweight normalization**: Identify built-in operators and symbols via a `DeclKind` / `SortKind` `Enum` rather than string-name comparisons (preventing collisions with user-defined uninterpreted symbols), paired with lightweight normalizing constructors (`And`/`Or` flattening, deduplication, identity/absorbing constants, and double-negation elimination).
- **No duplicate AST wrapper hierarchy**: `unsat.api` is a thin builder/sugar layer that constructs and returns `syntax` objects directly rather than wrapping them in a second AST class hierarchy.
- **Equality, hashing, and operators**: `Expr.__eq__` and `Expr.__ne__` preserve standard Python structural identity (`bool`, `self is other`), and `Expr` remains hashable (keyed by its hash-consed ID) so `dict[Expr, T]`, `set[Expr]`, and static type checking work naturally. Formula-level equality and disequality ASTs are built via `Eq(a, b)` and `Distinct(a, b, ...)` (which coerce matching scalar Python literals when paired with an `Expr`). Arithmetic, comparison, and bitwise/logical operators (`+`, `-`, `*`, `<`, `<=`, `>`, `>=`, `&`, `|`, `~`, etc.) are overloaded on `Expr`, while `Expr.__bool__` raises `TypeError` to catch accidental Python truth-value coercion (such as `if x < 5:` or `a and b`).

## CDCL(T) Orchestration (`unsat.smt`)

- **Incremental `push` / `pop`**: At the SAT layer, assertion scopes use per-scope activation literals passed via `assumptions`, permanently falsifying popped scope literals at decision level 0 so dead scope clauses are invalidated while keeping learned clauses sound and reusable across scopes (with quantifier ownership propagated cleanly across nested scopes). At the theory layer, solvers maintain backtrackable undo trails unifying user `push` / `pop` with search-level backtracking.
- **Polarity-aware Tseitin clausification**: Translating Boolean AST formulas into integer SAT clauses (Plaisted-Greenbaum polarity-aware incremental encoding, avoiding fragile incremental clause-level pure-literal elimination) alongside the bidirectional AST-to-SAT variable mapping lives in `unsat.smt`. `unsat.tactics` stays strictly AST-to-AST (paired with `ModelConverter` in `unsat.model`), with standalone preprocessing exposed via `solve_with_tactic`.
- **Theory combination (`MBTC`)**: Multi-theory reasoning uses Z3-style Model-Based Theory Combination (`MBTC`) with `EUF` as the shared-equality hub. Interface equalities between shared terms are speculated and checked on demand when candidate theory models assign equal values, avoiding eager `O(n^2)` equality case-splitting.

## Theories, Tactics & Quantifiers (`unsat.theories`, `unsat.tactics`, `unsat.quantifiers`)

- **EUF (`unsat.theories`)**: Congruence Closure backed by a Signature Table for `O(1)` congruence lookup, a copy-free trail-length undo log (avoiding per-merge list copies), and a proof forest for minimal conflict explanations. Predicate congruence is handled uniformly by registering Boolean predicate applications `P(t)` as `Eq(P(t), true)`.
- **Linear arithmetic (`LRA`, `LIA`)**: Exact rational arithmetic built on `fractions.Fraction` paired with infinitesimal `a + b * delta` values (Dutertre & de Moura Simplex) handles strict inequalities with zero floating-point precision errors. `LIA` builds on `LRA` with branch-and-bound and cutting planes (Gomory cuts).
- **Bit-Vectors (`BV`)**: Current support uses word-level simplification and eager bit-blasting tactics paired with shared-term bit-level propagation in `unsat.tactics` / `unsat.smt` and `ModelConverter` reconstruction for `QF_BV` and mixed `QF_AUFBV`/`BV` logics. Extending to a native lazy `unsat.theories.bv` theory solver is scheduled in [M8](roadmap.md#m8--lazy-bit-vector-theory-solver-unsattheoriesbv).
- **Arrays (`Arrays`)**: Lazy Read-over-Write (`select` / `store`) across full store equivalence classes, constant arrays (`const`), and extensionality axiom instantiation integrated with `EUF`.
- **Quantifiers (`unsat.quantifiers`)**: Anytime resource budgets (`max_rounds`, `max_matches`, timeout, and conflict caps) with conservative three-valued verdicts (`SAT`, `UNSAT`, `UNKNOWN`). Truncating quantifier search on a spent budget never claims `SAT` (downgrading to `UNKNOWN`), while ground-derived `UNSAT` remains sound. Extracted default triggers/patterns stay in matcher-owned tables rather than mutating immutable AST nodes.
