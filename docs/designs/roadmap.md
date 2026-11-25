# Milestones & Roadmap

This document tracks detailed milestone scopes and exit criteria for `unsat`. For the summary table, see [Solver Designs & Roadmap](README.md).

## Completed Milestones (M1–M9)

### M1 — Standalone CDCL SAT Core & DIMACS Frontend

- **Primary modules**: `sat`, `parser`, `cli`
- **Scope**:
  - Implement incremental CDCL in `unsat.sat` (signed-bit `Lit`, `lit_eval`, `bin_watches`, blocker-literal `watches`, 1-UIP + recursive clause minimization, EVSIDS, phase saving, restarts, LBD clause deletion with watch cleanup, input deduplication/tautology handling, `ok` state, `assumptions`, `unsat_core`, `max_conflicts`/`deadline` budgets).
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

### M5 — Bit-Vectors & Arrays (`QF_BV`, `QF_AX`, `QF_AUFBV`, `QF_AUFLIA`)

- **Primary modules**: `tactics`, `theories`, `syntax`, `model`, `api`, `parser`
- **Scope**:
  - Add `BitVec` and `Array` sorts, operations, and AST constructors across `syntax`, `model`, `api`, and `parser`.
  - Implement word-level bit-vector simplification and eager bit-blasting tactics paired with shared-term propagation and `ModelConverter` in `unsat.tactics` / `unsat.smt` (keeping a clean path to a lazy `theories.bv` solver in M8).
  - Implement `Arrays` theory solver in `unsat.theories` via lazy Read-over-Write across full store equivalence classes and extensionality lemmas cooperating with `EUF` and `MBTC`.
- **Exit criteria**:
  - `QF_BV`, `QF_AX`, `QF_AUFBV`, and `QF_AUFLIA` benchmarks pass with verified models (including `ModelConverter` reconstruction back to bit-vector/array expressions) and Z3 differential agreement.

### M6 — Quantifiers & Advanced Tactics (`UF`, quantified arithmetic)

- **Primary modules**: `quantifiers`, `tactics`, `smt`, `api`, `parser`
- **Scope**:
  - Add `ForAll` and `Exists` binders, pattern annotations, and variable scoping across `syntax`, `model`, `api`, and `parser`.
  - Implement `E-matching` over the `EUF` E-graph and `MBQI` in `unsat.quantifiers`, using injected sub-solver `Protocol` callbacks provided by `unsat.smt`, matcher-owned pattern tables (preserving AST immutability), and anytime `max_rounds`/`max_matches` budgets with conservative `UNKNOWN` handling.
  - Expand `unsat.tactics` with stronger formula preprocessing (`SkolemizeTactic`, `CtxSimplifyTactic`, `GaussianElimTactic`, `PropagateBoundsTactic`), expose `solve_with_tactic`, timeout/conflict resource limits, and add practical SMT-LIB2 commands (`define-sort`, parameterized `define-fun`, `:named` + `get-unsat-core`, `get-assertions`, `echo`).
- **Exit criteria**:
  - Representative quantified benchmarks and Hypothesis differential suites produce sound `SAT`, `UNSAT`, and budget-bounded `UNKNOWN` results verified against Z3.

### M7 — Large-Scale Benchmarking & Profiling Optimization

- **Primary modules**: `sat`, `theories`, `tactics`, `smt`, `benchmarks`
- **Scope**:
  - Expanded [`benchmarks/`](../../benchmarks/run.py) with a 17-problem scale corpus (`benchmarks/scale/` across `dimacs`, `qf_uf`, `qf_lra`, `qf_lia`, `qf_bv`, `qf_aufbv`, and `qf_auflia`) and added suite selection (`--suite {core,scale,all}`), `cProfile` reporting (`--profile`, `--profile-top`), `tracemalloc` allocation metrics (`--alloc`), and JSON baseline comparison (`--save-baseline`, `--compare`) in `benchmarks/run.py`.
  - Optimized CDCL hot loops in `unsat.sat` (`_propagate_sat` local hoisting & binary/watcher fast paths, 1-UIP analysis with recursive clause-minimization parent-chain poisoning, and inlined `VarMaxHeap` sifting).
  - Optimized `EUF` congruence lookup and proof-forest explanations (`_compute_sig` small-arity specialization, empty use-list skipping in `_union`, and stamped lockstep LCA walk in `_explain_eq`), `LRA` Simplex pivoting (precomputed `register_atom` bounds, allocation-free Bland's rule scans, module-level `Fraction` constants, and delta-zero tableau fast paths in `_update_nonbasic`/`_pivot_and_update`), and `BitBlaster` circuit construction (structurally memoized canonical gate builders, zero-sum borrow-chain `_ult_bits`, seen-one `_neg_bits`, sparsity-aware sliced `_mul_bits`, and shared `_sdiv_cache` across `sdiv`/`srem`/`smod`).
- **Exit criteria**:
  - All 44 core and scale benchmarks pass with Z3 differential agreement, achieving measurable end-to-end speedups (`6756.71 ms` -> `4214.25 ms`, `1.60x` overall with `--alloc`) and reduced peak allocations across division and arithmetic workloads.

### M8 — Lazy Bit-Vector Theory Solver (`unsat.theories.bv`)

- **Primary modules**: `theories`, `smt`, `tactics`
- **Scope**:
  - Implemented `BVDomain` (known zero/one bit masks synchronized with unsigned/signed intervals) and incremental word-level `BVSolver` in [`theories/bv.py`](../../src/unsat/theories/bv.py) with `BVStats` in [`theories/base.py`](../../src/unsat/theories/base.py), keeping `unsat.theories` decoupled from `unsat.tactics` and `unsat.sat`.
  - Integrated lazy BV solving into `unsat.smt` (`_PlaistedGreenbaumEncoder`, `_CombinedPropagator`, `SMTSolver`, and `SATSolver` unassigned-lemma continuation), propagating word-level domains/conflicts online, synthesizing candidate word-level BV models coordinated with `EUF`/`Arrays` via `MBTC`, and escalating only violated atoms to on-demand `BitBlaster` encoding (`BVBlastRequest`) while keeping `BitBlastTactic`/`bitblast()` intact for explicit preprocessing.
- **Exit criteria**:
  - Mixed `QF_BV` / `QF_UFBV` / `QF_ABV` / `QF_AUFBV` instances solve with fewer upfront SAT variables (including 0-blast resolution on word-level solvable constraints and `theory_bv_blasted_atoms` telemetry), match Z3 across Hypothesis differential tests, and pass curated `qf_ufbv` benchmarks.

### M9 — Nonlinear Arithmetic (`QF_NRA`, `QF_NIA`) & Complete Integer Operators

- **Primary modules**: `syntax`, `theories`, `parser`, `model`
- **Scope**:
  - Added complete SMT-LIB2 integer operators (`div`, `mod`, `abs`, `to_int`, `is_int`, `(_ divisible n)`) and Python DSL builders/overloads (`IDiv`, `Mod`, `Abs`, `ToInt`, `IsInt`, `Divisible`, `//`, `%`, `abs()`, `**`) across `syntax`, `model`, `tactics`, `smt`, `api`, and `parser` with exact Euclidean semantics, defining axioms in `_PlaistedGreenbaumEncoder`, `EUFSolver` congruence for division-by-zero, and `Model` `div_zero` evaluation support.
  - Added optional nonlinear monomial/divisor tracking (`allow_nonlinear=True`) to `LRASolver` and implemented [`NLASolver`](../../src/unsat/theories/nla.py) + [`NLAStats`](../../src/unsat/theories/base.py) combining rational/strict Interval Constraint Propagation (ICP), exact univariate rational polynomial Sturm real-root isolation with 2-variable linear substitution, incremental linearization lemmas (squares, zero/sign, McCormick envelopes, tangent planes, integer point slicing), budgeted case splitting, and conservative `NLAUnknown` handling (including irrational-only `Real` roots).
  - Registered `QF_NRA`/`QF_NIA`/`QF_NIRA` logic families in SMT-LIB2 and added representative `benchmarks/smt2/{qf_nra,qf_nia}/` benchmarks.
- **Exit criteria**:
  - Sound `SAT`/`UNSAT`/`UNKNOWN` handling, `model.eval_bool(...)` validation on `SAT`, and Z3 differential agreement across complete integer operator suites and decidable `QF_NRA`/`QF_NIA` test cases and benchmarks.

## Planned Milestones (M10)

### M10 — Theory of Strings & Regular Expressions (`QF_S`, `QF_SLIA`)

- **Primary modules**: `syntax`, `theories`, `parser`, `model`
- **Scope**:
  - Add `String` and `RegLan` sorts and SMT-LIB2 string/regex operators (`str.++`, `str.len`, `str.at`, `str.substr`, `str.indexof`, `str.replace`, `str.contains`, `str.in_re`, `str.to_re`, regex combinators).
  - Implement a word-equation and regular-expression derivative solver coupled with `LIA` length constraints and `EUF`.
- **Exit criteria**:
  - Representative `QF_S` and `QF_SLIA` benchmarks solve with concrete `str` model evaluation checks and Z3 differential agreement.
