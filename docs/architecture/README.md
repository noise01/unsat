# Architecture

`unsat` is a Z3-inspired SMT solver written in Python. The codebase adopts Z3's conceptual separation across syntax, CDCL SAT, theory solvers, tactics, quantifier instantiation, CDCL(T) orchestration, and frontends while enforcing strict Python package and dependency contracts.

## Documents

- [Directory Layout & Design Conventions](layout.md)
- [Module Responsibilities & Dependency DAG](dependencies.md)
