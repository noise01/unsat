# Changelog

All notable changes to `unsat` are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.0] - 2026-11-26

### Added

- Full SMT-LIB2 2.6 `String` and `RegLan` sorts, Unicode escape parsing/formatting (`\u{...}`, `\uXXXX`), operators (`str.++`, `str.len`, `str.at`, `str.substr`, `str.indexof`, `str.replace`, `str.replace_all`, `str.contains`, `str.prefixof`, `str.suffixof`, `str.<`, `str.<=`, `str.to_int`, `str.from_int`, `str.to_code`, `str.from_code`, `str.is_digit`, `str.in_re`, `str.to_re`, `re.*` / `re.+` / `re.opt` / `re.range` / `re.comp` / `re.diff` / `re.^` / `re.loop`), polymorphic Python `Concat` + `+`/`<`/`<=`/`>`/`>=` DSL builders, and `StringSolver` ([`unsat.theories.strings`](src/unsat/theories/strings.py)) combining Brzozowski regex derivatives, word-equation Nielsen splitting, character-slot model synthesis, and `EUF`/`LIA` integration with curated [`benchmarks/smt2/qf_s/`](benchmarks/smt2/qf_s/sat_word_eq_regex.smt2) and [`benchmarks/smt2/qf_slia/`](benchmarks/smt2/qf_slia/sat_substr_indexof.smt2) benchmarks.
- Complete SMT-LIB2 integer operators (`div`, `mod`, `abs`, `to_int`, `is_int`, `(_ divisible n)`) and Python DSL helpers/overloads (`IDiv`, `Mod`, `Abs`, `ToInt`, `IsInt`, `Divisible`, `//`, `%`, `abs()`, `**`) with exact Euclidean semantics, defining axioms, `EUFSolver` division-by-zero congruence, and `Model` `div_zero` support.
- Nonlinear arithmetic theory solver [`unsat.theories.nla`](src/unsat/theories/nla.py) (`NLASolver`, `NLBudget`, `NLALemma`, `NLAUnknown`, `NLAStats`), `LRASolver(..., allow_nonlinear=True)` monomial relaxation, ICP + Sturm real-root isolation + incremental linearization + bounded branching for `QF_NRA`/`QF_NIA`/`QF_NIRA`, and curated [`benchmarks/smt2/qf_nra/`](benchmarks/smt2/qf_nra/sat_circle_line.smt2) / [`benchmarks/smt2/qf_nia/`](benchmarks/smt2/qf_nia/sat_pythagorean.smt2) benchmarks.
- Lazy word-level bit-vector theory solver (`unsat.theories.bv` with `BVSolver`, `BVDomain`, `BVBlastRequest`, and `BVStats` in `unsat.theories.base`) integrated into [`unsat.smt`](src/unsat/smt/solver.py) for `QF_BV`, `QF_UFBV`, `QF_ABV`, and `QF_AUFBV`, with online known-bit/interval propagation, word-level model synthesis, MBTC interface sharing, and on-demand `BitBlaster` escalation alongside representative [`benchmarks/smt2/qf_ufbv/`](benchmarks/smt2/qf_ufbv/sat_congruence_bv.smt2) benchmarks.
- Large-scale M7 benchmark corpus under [`benchmarks/scale/`](benchmarks/scale/) (17 DIMACS and SMT-LIB2 instances) plus suite selection (`--suite {core,scale,all}`), `cProfile` profiling (`--profile`, `--profile-top`), `tracemalloc` allocation metrics (`--alloc`), and baseline comparison (`--save-baseline`, `--compare`) in [`benchmarks/run.py`](benchmarks/run.py).
- Automatic Python scalar coercion (`bool`, `int`, `Fraction`) in `Eq`, `Distinct`, and `If` builders in [`unsat.api`](src/unsat/api.py).
- Reserved [`packages/unsat-legacy/`](packages/unsat-legacy/README.md) `uv` workspace package slot for future archived/legacy solver implementations.
- Repository [`AGENTS.md`](AGENTS.md) and restructured architecture/design documentation under [`docs/architecture/`](docs/architecture/README.md) and [`docs/designs/`](docs/designs/README.md).
- Automated GitHub Release creation job in [`publish.yml`](.github/workflows/publish.yml) gated on PyPI publish success.
- Isolated wheel smoke testing (`import unsat`, `py.typed`, `Solver`, `unsat --version`, stdin SMT-LIB2), `benchmarks/run.py --suite all --check` in CI, full commit SHA Action pinning, concurrency guards, and [`.github/dependabot.yml`](.github/dependabot.yml).

### Changed

- Optimized core solver and preprocessing hot paths for M7: inlined SAT propagation/conflict minimization/heap sifting (`unsat.sat`), specialized `EUF` congruence hashing and lockstep LCA explanations (`unsat.theories.euf`), precomputed atom bounds and allocation-free Bland Simplex pivoting (`unsat.theories.lra`), and structurally memoized bit-blasting gates with borrow-only `_ult_bits`, sparse `_mul_bits`, and shared `_sdiv_cache` (`unsat.tactics.bitblast`).

## [0.1.0] - 2026-11-25

### Added

- Standalone incremental CDCL SAT solver (`unsat.sat`) with two-watched literals, binary watch lists, 1-UIP learning with recursive minimization, EVSIDS branching, Glucose LBD restarts/reduction, assumption-based `unsat_core()`, lazy `TheoryPropagator` hooks, and `max_conflicts`/`deadline` budgets.
- Immutable `WeakValueDictionary` hash-consed AST (`unsat.syntax`), Z3Py-style Python DSL (`unsat.api`), and `Model` / `FuncInterp` evaluator with `ModelConverter` reconstruction (`unsat.model`).
- Online CDCL(T) theory solvers (`unsat.theories`): `EUF` congruence closure with proof-forest explanations, exact rational `LRA` Simplex with infinitesimals, `LIA` branch-and-bound + Gomory cuts, and lazy Read-over-Write / extensional `Arrays`.
- Quantifier reasoning (`unsat.quantifiers`) with E-matching and `MBQI` under `QuantifierBudget` limits, plus AST preprocessing tactics (`SimplifyTactic`, `NNFTactic`, `BitBlastTactic`, `SkolemizeTactic`, `CtxSimplifyTactic`, `GaussianElimTactic`, `PropagateBoundsTactic`) and `solve_with_tactic` (`unsat.smt`).
- DIMACS CNF and SMT-LIB2 parser/runner/CLI (`unsat`) supporting core logics (`QF_BOOL` through `ALL`), parameterized `define-fun`, `define-sort` with cycle checks, `:named` + `get-unsat-core`, `get-assertions`, `echo`, and `--timeout` / `--max-conflicts` / quantifier budget flags.
- Curated DIMACS & SMT-LIB2 [`benchmarks/`](benchmarks/run.py) suite, Hypothesis differential test suites against `z3-solver`, and strict `import-linter` / PEP 649 annotation / import-isolation checks.
