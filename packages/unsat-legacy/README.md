# unsat-legacy

Frozen archive of the pre-extraction SMT solver originally built inside `endoxa` (`endoxa.solver`), packaged as an isolated `uv` workspace member (`unsat_legacy`) for reference and differential benchmarking against `unsat`.

## Scope & Isolation

- **Includes**: The original `EUF` congruence-closure solver, CDCL SAT core, `E-matching` quantifier instantiation, `TseitinEncoder` / `Skolemizer` / `Preprocessor`, `lark`-backed TPTP FOF parser (`unsat_legacy.parsers`), standalone `unsat_legacy.errors` hierarchy, and the ported unit + Z3-differential test suites.
- **Dependency isolation**: `unsat-legacy` declares `lark>=1.3.1` in its own `pyproject.toml` and is included only in the root `dev` dependency group. The shipped `unsat` package under `src/unsat/` keeps zero runtime dependencies (`dependencies = []`) and never imports `unsat_legacy` or `lark`.

## Running Tests

From the repository root:

```bash
uv run pytest packages/unsat-legacy/tests
```
