# Solver Designs & Roadmap

Design documentation and phased milestones for `unsat`. See [Architecture](../architecture/README.md) for package structure and dependency invariants.

## Design Documents

- [Core Solver Design](core.md) — SAT core, hash-consed AST & Python DSL, CDCL(T), theories, tactics, and quantifiers
- [Verification & Soundness Strategy](verification.md) — differential Z3 fuzzing, model checking, and packaging invariants
- [Milestones & Roadmap](roadmap.md) — completed M1–M12 milestones, planned M13 milestone, and post-M13 backlog

## Milestone Overview

| Milestone | Status | Logics / Scope | Key Modules |
| --- | --- | --- | --- |
| M1 | Completed | Standalone CDCL SAT & DIMACS | `sat`, `parser`, `cli` |
| M2 | Completed | Propositional SMT End-to-End (`QF_BOOL`) | `syntax`, `model`, `tactics`, `smt`, `api`, `parser`, `cli` |
| M3 | Completed | Congruence Closure & Online CDCL(T) (`QF_UF`) | `theories`, `smt`, `syntax`, `model`, `api`, `parser` |
| M4 | Completed | Linear Arithmetic & Theory Combination (`QF_LRA`, `QF_LIA`, `QF_UFLRA`, `QF_UFLIA`) | `theories`, `smt`, `syntax`, `model`, `api`, `parser` |
| M5 | Completed | Bit-Vectors & Arrays (`QF_BV`, `QF_AX`, `QF_AUFBV`, `QF_AUFLIA`) | `tactics`, `theories`, `syntax`, `model`, `api`, `parser` |
| M6 | Completed | Quantifiers & Advanced Tactics (`UF`, quantified arithmetic) | `quantifiers`, `tactics`, `smt`, `api`, `parser` |
| M7 | Completed | Large-Scale Benchmarking & Profiling Optimization | `sat`, `theories`, `tactics`, `smt`, `benchmarks` |
| M8 | Completed | Lazy Bit-Vector Theory Solver (`unsat.theories.bv`) | `theories`, `smt`, `tactics` |
| M9 | Completed | Nonlinear Arithmetic (`QF_NRA`, `QF_NIA`) & Complete Integer Ops | `syntax`, `theories`, `parser`, `model` |
| M10 | Completed | Theory of Strings & Regular Expressions (`QF_S`, `QF_SLIA`) | `syntax`, `theories`, `parser`, `model` |
| M11 | Completed | Legacy Solver Archival & Differential Baseline | `packages/unsat-legacy`, `docs/designs` |
| M12 | Completed | Zero-Dependency TPTP FOF Frontend & `endoxa` Integration | `parser`, `cli`, `smt`, `api` |
| M13 | Planned | Post-M10 Verification & Scale Benchmark Hardening | `tests`, `benchmarks`, `theories` |
