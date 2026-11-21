"""Generalized Simplex solver with exact rationals and delta-infinitesimals.

Implements Dutertre & de Moura (2006) incremental Simplex for ``QF_LRA`` and the
continuous relaxation base for ``QF_LIA``:
- Exact arithmetic via ``fractions.Fraction`` and ``DeltaRational(r, delta)``.
- Canonical sparse linear forms and dynamic slack insertion after arbitrary pivots.
- Copy-free undo trail saving/restoring only bounds, reasons, and assertions
  while keeping simplex pivots intact across backtracking (warm-starting).
- Bland's pivoting rule and exact Farkas conflict explanations.
- Backtrackable bound-subsumption propagation with level-exact explanations.

Depends on: ``syntax``, ``model``.
"""

import math
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from fractions import Fraction

from unsat.model import Model, Value
from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl
from unsat.theories.base import LRAStats, TheoryLit


@dataclass(frozen=True, slots=True, order=True)
class DeltaRational:
    """Exact extended rational ``real + delta * eps`` for infinitesimal ``eps > 0``."""

    real: Fraction
    delta: Fraction = Fraction(0)

    def __add__(self, other: DeltaRational) -> DeltaRational:
        return DeltaRational(self.real + other.real, self.delta + other.delta)

    def __sub__(self, other: DeltaRational) -> DeltaRational:
        return DeltaRational(self.real - other.real, self.delta - other.delta)

    def __neg__(self) -> DeltaRational:
        return DeltaRational(-self.real, -self.delta)

    def scale(self, factor: Fraction) -> DeltaRational:
        """Multiply this delta-rational by exact scalar ``factor``."""
        return DeltaRational(self.real * factor, self.delta * factor)

    def is_integer(self) -> bool:
        """Return whether this value is an exact integer (zero delta and denom 1)."""
        return self.delta == 0 and self.real.denominator == 1


_DELTA_ZERO = DeltaRational(Fraction(0), Fraction(0))

# Undo opcodes stored on LRASolver._history when _trail_marks is non-empty.
_OP_ASSERT = 0
_OP_LOWER = 1
_OP_UPPER = 2
_OP_PROP_REASON = 3


def _dedup_lits(lits: Iterable[TheoryLit]) -> list[TheoryLit]:
    return list(dict.fromkeys(lits))


def _apply_dir(is_upper: bool, strictly: bool, sign: int) -> tuple[bool, bool]:
    """Flip bound direction if ``sign < 0``."""
    return (not is_upper, strictly) if sign < 0 else (is_upper, strictly)


def _bound_from_cmp(kind: DeclKind, polarity: bool) -> tuple[bool, bool]:
    """Return ``(is_upper, strict)`` for ``lhs - rhs <cmp> 0`` under ``polarity``."""
    match kind:
        case DeclKind.LE:
            return (True, False) if polarity else (False, True)
        case DeclKind.LT:
            return (True, True) if polarity else (False, False)
        case DeclKind.GE:
            return (False, False) if polarity else (True, True)
        case DeclKind.GT:
            return (False, True) if polarity else (True, False)
        case _:
            msg = f"Expected arithmetic comparison DeclKind, got {kind}"
            raise TypeError(msg)


def _tighten_bound(
    is_int: bool, bound: Fraction, *, is_upper: bool, strict: bool
) -> DeltaRational:
    """Convert numeric bound into an exact ``DeltaRational`` (tightening ``Int``)."""
    if is_int:
        if is_upper:
            int_val = math.ceil(bound) - 1 if strict else math.floor(bound)
        else:
            int_val = math.floor(bound) + 1 if strict else math.ceil(bound)
        return DeltaRational(Fraction(int_val), Fraction(0))

    delta = (Fraction(-1) if is_upper else Fraction(1)) if strict else Fraction(0)
    return DeltaRational(bound, delta)


def _eval_cmp(val: Fraction, is_upper: bool, strict: bool) -> bool:
    if is_upper:
        return val < 0 if strict else val <= 0
    return val > 0 if strict else val >= 0


class LRASolver:
    """Incremental generalized Simplex solver for ``QF_LRA`` and ``QF_LIA``."""

    def __init__(self, ctx: Context) -> None:
        self._ctx = ctx
        self._stats = LRAStats()

        # Arithmetic leaf terms -> original variable ID.
        self._expr_to_var: dict[Expr, int] = {}
        self._var_expr: list[Expr | None] = []
        self._is_int: list[bool] = []
        self._is_original: list[bool] = []
        self._slack_orig_coeffs: list[dict[int, Fraction] | None] = []

        # Canonical linear form -> (slack_or_single_var, row_all_int).
        self._slack_map: dict[tuple[tuple[int, Fraction], ...], int] = {}

        # Sparse Simplex tableau: basic_id -> {non_basic_id: coeff}.
        self._basic_rows: dict[int, dict[int, Fraction]] = {}
        self._col_uses: dict[int, set[int]] = {}

        # Variable assignment and bounds.
        self._val: list[DeltaRational] = []
        self._lower: list[DeltaRational | None] = []
        self._upper: list[DeltaRational | None] = []
        self._lower_reason: list[TheoryLit | None] = []
        self._upper_reason: list[TheoryLit | None] = []

        # Registered comparison atoms:
        # atom -> ("const", bool_val) | ("linear", vid, scale, rhs, cmp_kind)
        self._atom_info: dict[Expr, tuple[object, ...]] = {}
        self._var_atoms: dict[int, list[Expr]] = {}
        self._asserted_atoms: dict[Expr, bool] = {}

        # Backtrackable propagation & conflict tracking.
        self._pending_props: list[tuple[Expr, bool]] = []
        self._pending_prop_set: set[Expr] = set()
        self._prop_reasons: dict[tuple[Expr, bool], list[TheoryLit]] = {}
        self._conflict: list[TheoryLit] | None = None

        # Incremental trail: only bounds, bound reasons, prop reasons, and assertions.
        self._history: list[tuple[object, ...]] = []
        self._trail_marks: list[tuple[int, list[TheoryLit] | None]] = []

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._ctx

    @property
    def stats(self) -> LRAStats:
        """Instrumentation counters for pivots, updates, conflicts, and LIA lemmas."""
        return self._stats

    @property
    def decision_level(self) -> int:
        """Current incremental backtracking depth."""
        return len(self._trail_marks)

    def push(self) -> None:
        """Save the current bound/assertion frame onto the undo trail."""
        self._trail_marks.append((len(self._history), self._conflict))

    def pop(self, num_levels: int = 1) -> None:
        """Restore the assertion state by popping ``num_levels`` frames."""
        if num_levels < 0:
            msg = f"Cannot pop negative levels: {num_levels}"
            raise ValueError(msg)
        if num_levels == 0:
            return
        if num_levels > len(self._trail_marks):
            msg = (
                f"Cannot pop {num_levels} levels: only {len(self._trail_marks)} active"
            )
            raise ValueError(msg)

        target_len, saved_conflict = self._trail_marks[
            len(self._trail_marks) - num_levels
        ]
        del self._trail_marks[len(self._trail_marks) - num_levels :]

        self._pending_props.clear()
        self._pending_prop_set.clear()
        self._conflict = saved_conflict

        history = self._history
        while len(history) > target_len:
            entry = history.pop()
            op = entry[0]
            if op == _OP_ASSERT:
                atom = entry[1]
                assert isinstance(atom, Expr)
                del self._asserted_atoms[atom]
            elif op == _OP_LOWER:
                _, vid, old_bound, old_reason = entry
                assert isinstance(vid, int)
                assert old_bound is None or isinstance(old_bound, DeltaRational)
                assert old_reason is None or isinstance(old_reason, TheoryLit)
                self._lower[vid] = old_bound
                self._lower_reason[vid] = old_reason
            elif op == _OP_UPPER:
                _, vid, old_bound, old_reason = entry
                assert isinstance(vid, int)
                assert old_bound is None or isinstance(old_bound, DeltaRational)
                assert old_reason is None or isinstance(old_reason, TheoryLit)
                self._upper[vid] = old_bound
                self._upper_reason[vid] = old_reason
            elif op == _OP_PROP_REASON:
                key = entry[1]
                assert isinstance(key, tuple)
                self._prop_reasons.pop(key, None)

    def register_term(self, term: Expr) -> None:
        """Register an ``Int`` or ``Real`` term and extract its linear leaf vars."""
        self._check_expr(term)
        if not term.is_arith:
            msg = f"Expected Int or Real expression, got sort '{term.sort}'"
            raise TypeError(msg)
        self._linearize(term)

    def register_atom(self, atom: Expr) -> None:
        """Register an arithmetic comparison atom ``<``, ``<=``, ``>``, ``>=``."""
        self._check_expr(atom)
        if not (
            isinstance(atom, App)
            and atom.decl.kind in (DeclKind.LT, DeclKind.LE, DeclKind.GT, DeclKind.GE)
        ):
            msg = f"Expected arithmetic comparison expression, got '{atom}'"
            raise TypeError(msg)
        if atom in self._atom_info:
            return

        coeffs, const_val = self._linearize(atom.args[0])
        rhs_coeffs, rhs_const = self._linearize(atom.args[1])
        for v, c in rhs_coeffs.items():
            updated = coeffs.get(v, Fraction(0)) - c
            if updated == 0:
                coeffs.pop(v, None)
            else:
                coeffs[v] = updated
        const_diff = const_val - rhs_const

        if not coeffs:
            is_upper, strict = _bound_from_cmp(atom.decl.kind, True)
            fixed_truth = _eval_cmp(const_diff, is_upper, strict)
            self._atom_info[atom] = ("const", fixed_truth)
            self._enqueue_prop(atom, fixed_truth, [])
            return

        vid, scale, scaled_rhs = self._get_or_create_var_for_form(coeffs, -const_diff)
        self._atom_info[atom] = ("linear", vid, scale, scaled_rhs, atom.decl.kind)
        self._var_atoms.setdefault(vid, []).append(atom)

        # Check if existing bounds already decide this newly registered atom.
        self._check_atom_subsumed(atom)

    def assert_atom(self, atom: Expr, polarity: bool) -> None:
        """Assert arithmetic atom ``atom`` with truth value ``polarity``."""
        self.register_atom(atom)
        existing = self._asserted_atoms.get(atom)
        if existing is not None:
            if existing == polarity:
                return
            if self._conflict is None:
                self._conflict = [TheoryLit(atom, True), TheoryLit(atom, False)]
                self._stats.conflicts += 1
            return

        self._asserted_atoms[atom] = polarity
        if self._trail_marks:
            self._history.append((_OP_ASSERT, atom))

        info = self._atom_info[atom]
        if info[0] == "const":
            fixed_truth = bool(info[1])
            if fixed_truth != polarity and self._conflict is None:
                self._conflict = [TheoryLit(atom, polarity)]
                self._stats.conflicts += 1
            return

        _, vid, scale, scaled_rhs, cmp_kind = info
        assert isinstance(vid, int)
        assert isinstance(scale, Fraction)
        assert isinstance(scaled_rhs, Fraction)
        assert isinstance(cmp_kind, DeclKind)

        raw_upper, strict = _bound_from_cmp(cmp_kind, polarity)
        is_upper, strict = _apply_dir(raw_upper, strict, 1 if scale > 0 else -1)
        target = _tighten_bound(
            self._is_int[vid], scaled_rhs, is_upper=is_upper, strict=strict
        )
        reason = TheoryLit(atom, polarity)
        self._apply_bound_update(vid, target, reason, is_upper=is_upper)

    def propagate(
        self,
    ) -> tuple[Sequence[tuple[Expr, bool]], Sequence[TheoryLit] | None]:
        """Return queued propagations or a direct bound conflict if detected."""
        if self._conflict is not None:
            return (), list(self._conflict)
        if not self._pending_props:
            return (), None
        props = list(self._pending_props)
        self._pending_props.clear()
        self._pending_prop_set.clear()
        return props, None

    def explain_propagation(self, atom: Expr, polarity: bool) -> Sequence[TheoryLit]:
        """Return asserted ``TheoryLit`` reasons explaining ``(atom, polarity)``."""
        reasons = self._prop_reasons.get((atom, polarity))
        if reasons is None:
            msg = f"No LRA propagation explanation recorded for ({atom}, {polarity})"
            raise KeyError(msg)
        return list(reasons)

    def check(self) -> Sequence[Sequence[TheoryLit]]:
        """Run generalized Simplex and return any Farkas conflict lemma(s)."""
        self._stats.checks += 1
        if self._conflict is not None:
            return [list(self._conflict)]
        if not self._solve_simplex():
            assert self._conflict is not None
            return [list(self._conflict)]
        return ()

    def concrete_values(self) -> dict[Expr, Fraction]:
        """Collapse delta-rationals to concrete ``Fraction`` values per var term."""
        eps = Fraction(1)
        for vid in range(len(self._val)):
            r_v, d_v = self._val[vid].real, self._val[vid].delta
            ub = self._upper[vid]
            if ub is not None and r_v < ub.real and d_v > ub.delta:
                cand = (ub.real - r_v) / (2 * (d_v - ub.delta))
                if cand < eps:
                    eps = cand
            lb = self._lower[vid]
            if lb is not None and r_v > lb.real and lb.delta > d_v:
                cand = (r_v - lb.real) / (2 * (lb.delta - d_v))
                if cand < eps:
                    eps = cand

        result: dict[Expr, Fraction] = {}
        for expr, vid in self._expr_to_var.items():
            dr = self._val[vid]
            result[expr] = dr.real + dr.delta * eps
        return result

    def term_values(self, terms: Iterable[Expr]) -> dict[Expr, Fraction]:
        """Evaluate every linear arithmetic expression in ``terms`` concretely."""
        orig_vals = self.concrete_values()
        out: dict[Expr, Fraction] = {}
        for term in terms:
            if term in orig_vals:
                out[term] = orig_vals[term]
                continue
            coeffs, const_val = self._linearize(term)
            total = const_val
            for vid, coef in coeffs.items():
                var_expr = self._var_expr[vid]
                assert var_expr is not None
                total += coef * orig_vals[var_expr]
            out[term] = total
        return out

    def build_model(self) -> Model:
        """Build an arithmetic ``Model`` with ``int``/``Fraction`` values."""
        if self._conflict is not None:
            msg = "Cannot build an LRA model in a conflicted state"
            raise ValueError(msg)
        conc = self.concrete_values()
        values: dict[FuncDecl, Value] = {}
        for expr, frac in conc.items():
            if isinstance(expr, App) and expr.is_const_symbol:
                if expr.is_int:
                    if frac.denominator != 1:
                        msg = f"Non-integral value {frac} assigned to Int '{expr.decl}'"
                        raise ValueError(msg)
                    values[expr.decl] = frac.numerator
                elif expr.is_real:
                    values[expr.decl] = frac
        return Model(self._ctx, values)

    # ------------------------------------------------------------------
    # Accessors used by LIA (gomory cuts & branch-and-bound)
    # ------------------------------------------------------------------

    @property
    def num_vars(self) -> int:
        """Number of internal tableau variables (original and slack)."""
        return len(self._val)

    def var_value(self, vid: int) -> DeltaRational:
        """Return current Simplex assignment of variable ``vid``."""
        return self._val[vid]

    def var_is_int(self, vid: int) -> bool:
        """Return whether variable ``vid`` must take integer values."""
        return self._is_int[vid]

    def var_is_original(self, vid: int) -> bool:
        """Return whether variable ``vid`` corresponds directly to an AST term."""
        return self._is_original[vid]

    def var_expr(self, vid: int) -> Expr | None:
        """Return the AST expression for original variable ``vid`` (or ``None``)."""
        return self._var_expr[vid]

    def var_lower(self, vid: int) -> tuple[DeltaRational | None, TheoryLit | None]:
        """Return ``(lower_bound, reason)`` for variable ``vid``."""
        return self._lower[vid], self._lower_reason[vid]

    def var_upper(self, vid: int) -> tuple[DeltaRational | None, TheoryLit | None]:
        """Return ``(upper_bound, reason)`` for variable ``vid``."""
        return self._upper[vid], self._upper_reason[vid]

    def basic_row(self, vid: int) -> dict[int, Fraction] | None:
        """Return the sparse tableau row for basic variable ``vid``, or ``None``."""
        return self._basic_rows.get(vid)

    def var_orig_coeffs(self, vid: int) -> dict[int, Fraction]:
        """Return the expansion of variable ``vid`` in terms of original vars."""
        if self._is_original[vid]:
            return {vid: Fraction(1)}
        coeffs = self._slack_orig_coeffs[vid]
        assert coeffs is not None
        return dict(coeffs)

    # ------------------------------------------------------------------
    # LIA integrality patching & vertex tightening
    # ------------------------------------------------------------------

    def _real_freedom_interval(
        self, j_nb: int
    ) -> tuple[Fraction | None, bool, Fraction | None, bool]:
        """Return ``(lo_d, lo_strict, hi_d, hi_strict)`` for shifts of ``j_nb``."""
        lo_d: Fraction | None = None
        lo_strict = False
        hi_d: Fraction | None = None
        hi_strict = False

        def _tighten_hi(bound: Fraction, strict: bool) -> None:
            nonlocal hi_d, hi_strict
            if (
                hi_d is None
                or bound < hi_d
                or (bound == hi_d and strict and not hi_strict)
            ):
                hi_d = bound
                hi_strict = strict

        def _tighten_lo(bound: Fraction, strict: bool) -> None:
            nonlocal lo_d, lo_strict
            if (
                lo_d is None
                or bound > lo_d
                or (bound == lo_d and strict and not lo_strict)
            ):
                lo_d = bound
                lo_strict = strict

        def _apply_var(vid: int, coef: Fraction) -> None:
            cur_val = self._val[vid]
            ub = self._upper[vid]
            if ub is not None:
                diff_r = ub.real - cur_val.real
                strict = cur_val.delta > ub.delta
                bound = diff_r / coef
                if coef > 0:
                    _tighten_hi(bound, strict)
                else:
                    _tighten_lo(bound, strict)
            lb = self._lower[vid]
            if lb is not None:
                diff_r = lb.real - cur_val.real
                strict = cur_val.delta < lb.delta
                bound = diff_r / coef
                if coef > 0:
                    _tighten_lo(bound, strict)
                else:
                    _tighten_hi(bound, strict)

        _apply_var(j_nb, Fraction(1))
        for k_basic in self._col_uses.get(j_nb, ()):
            _apply_var(k_basic, self._basic_rows[k_basic][j_nb])

        return lo_d, lo_strict, hi_d, hi_strict

    @staticmethod
    def _in_real_interval(
        d: Fraction,
        lo_d: Fraction | None,
        lo_strict: bool,
        hi_d: Fraction | None,
        hi_strict: bool,
    ) -> bool:
        if lo_d is not None and (d < lo_d or (lo_strict and d == lo_d)):
            return False
        return hi_d is None or not (d > hi_d or (hi_strict and d == hi_d))

    def patch_int_vars(self) -> bool:
        """Shift free non-basic variables to reduce fractionality of basic ``Int``s."""
        if self._conflict is not None:
            return False

        any_changed = False
        while True:
            pass_changed = False
            for i_basic in sorted(self._basic_rows):
                if not (self._is_original[i_basic] and self._is_int[i_basic]):
                    continue
                val_i = self._val[i_basic]
                if val_i.delta != 0 or val_i.real.denominator == 1:
                    continue

                r_i = val_i.real
                row = self._basic_rows[i_basic]
                patched_this = False
                for j_nb in sorted(row):
                    if self._val[j_nb].delta != 0:
                        continue
                    a_ij = row[j_nb]
                    lo_d, lo_strict, hi_d, hi_strict = self._real_freedom_interval(j_nb)
                    if lo_d is not None and hi_d is not None:
                        if lo_d > hi_d or (lo_d == hi_d and (lo_strict or hi_strict)):
                            continue
                        if lo_d == 0 and hi_d == 0:
                            continue

                    candidates: list[Fraction] = []
                    if not self._is_int[j_nb]:
                        raw = [
                            (Fraction(math.floor(r_i)) - r_i) / a_ij,
                            (Fraction(math.ceil(r_i)) - r_i) / a_ij,
                        ]
                        candidates = [
                            d
                            for d in raw
                            if d != 0
                            and self._in_real_interval(
                                d, lo_d, lo_strict, hi_d, hi_strict
                            )
                        ]
                    else:
                        int_lo = (
                            None
                            if lo_d is None
                            else (
                                math.floor(lo_d) + 1 if lo_strict else math.ceil(lo_d)
                            )
                        )
                        int_hi = (
                            None
                            if hi_d is None
                            else (
                                math.ceil(hi_d) - 1 if hi_strict else math.floor(hi_d)
                            )
                        )
                        if (
                            int_lo is not None
                            and int_hi is not None
                            and (int_lo > int_hi or (int_lo == 0 and int_hi == 0))
                        ):
                            continue

                        p_i, q_i = r_i.numerator, r_i.denominator
                        p_a, q_a = a_ij.numerator, a_ij.denominator
                        lcm_q = math.lcm(q_i, q_a)
                        a_int = p_a * (lcm_q // q_a)
                        b_int = -(p_i * (lcm_q // q_i))
                        g = math.gcd(abs(a_int), lcm_q)
                        modulus = lcm_q // g
                        if modulus <= 1:
                            continue
                        if b_int % g == 0:
                            d0 = ((b_int // g) * pow(a_int // g, -1, modulus)) % modulus
                        elif math.gcd(abs(a_int), modulus) == 1:
                            d0 = (b_int * pow(a_int, -1, modulus)) % modulus
                        else:
                            continue

                        lo_pos = 1 if int_lo is None else max(1, int_lo)
                        k_pos = (lo_pos - d0 + modulus - 1) // modulus
                        cand_pos = d0 + k_pos * modulus
                        if int_hi is None or cand_pos <= int_hi:
                            candidates.append(Fraction(cand_pos))

                        hi_neg = -1 if int_hi is None else min(-1, int_hi)
                        k_neg = (hi_neg - d0) // modulus
                        cand_neg = d0 + k_neg * modulus
                        if int_lo is None or cand_neg >= int_lo:
                            candidates.append(Fraction(cand_neg))

                    if not candidates:
                        continue
                    candidates.sort(key=abs)

                    col_basics = [
                        k_basic
                        for k_basic in self._col_uses.get(j_nb, ())
                        if self._is_original[k_basic] and self._is_int[k_basic]
                    ]
                    best_d: Fraction | None = None
                    for cand_d in candidates:
                        delta_frac = 0
                        delta_denom = 0
                        for k_basic in col_basics:
                            old_v = self._val[k_basic]
                            new_v = DeltaRational(
                                old_v.real + cand_d * self._basic_rows[k_basic][j_nb],
                                old_v.delta,
                            )
                            old_f = 0 if old_v.is_integer() else 1
                            new_f = 0 if new_v.is_integer() else 1
                            delta_frac += new_f - old_f
                            old_den = old_v.real.denominator + (
                                1 if old_v.delta != 0 else 0
                            )
                            new_den = new_v.real.denominator + (
                                1 if new_v.delta != 0 else 0
                            )
                            delta_denom += new_den - old_den
                        if delta_frac < 0 or (delta_frac == 0 and delta_denom < 0):
                            best_d = cand_d
                            break

                    if best_d is not None:
                        self._update_nonbasic(
                            j_nb,
                            self._val[j_nb] + DeltaRational(best_d, Fraction(0)),
                        )
                        any_changed = True
                        pass_changed = True
                        patched_this = True
                        break

                if patched_this:
                    continue

            if not pass_changed:
                break

        return any_changed

    def push_nonbasic_to_bound(self, j_nb: int) -> bool:
        """Move non-basic ``j_nb`` toward the closest blocking bound or pivot out."""
        if self._conflict is not None or j_nb in self._basic_rows:
            return False

        val_j = self._val[j_nb]
        lb_j = self._lower[j_nb]
        ub_j = self._upper[j_nb]
        if (lb_j is not None and val_j == lb_j) or (ub_j is not None and val_j == ub_j):
            return False

        hi_delta: DeltaRational | None = None
        hi_blocker: tuple[int, DeltaRational] | None = None
        lo_delta: DeltaRational | None = None
        lo_blocker: tuple[int, DeltaRational] | None = None

        if ub_j is not None:
            hi_delta = ub_j - val_j
            hi_blocker = (j_nb, ub_j)
        if lb_j is not None:
            lo_delta = lb_j - val_j
            lo_blocker = (j_nb, lb_j)

        def _consider_hi(cand: DeltaRational, vid: int, bnd: DeltaRational) -> None:
            nonlocal hi_delta, hi_blocker
            if hi_delta is None or cand < hi_delta:
                hi_delta = cand
                hi_blocker = (vid, bnd)

        def _consider_lo(cand: DeltaRational, vid: int, bnd: DeltaRational) -> None:
            nonlocal lo_delta, lo_blocker
            if lo_delta is None or cand > lo_delta:
                lo_delta = cand
                lo_blocker = (vid, bnd)

        for k_basic in sorted(self._col_uses.get(j_nb, ())):
            a_kj = self._basic_rows[k_basic][j_nb]
            inv_a = Fraction(1) / a_kj
            val_k = self._val[k_basic]
            ub_k = self._upper[k_basic]
            lb_k = self._lower[k_basic]
            if a_kj > 0:
                if ub_k is not None:
                    _consider_hi((ub_k - val_k).scale(inv_a), k_basic, ub_k)
                if lb_k is not None:
                    _consider_lo((lb_k - val_k).scale(inv_a), k_basic, lb_k)
            else:
                if lb_k is not None:
                    _consider_hi((lb_k - val_k).scale(inv_a), k_basic, lb_k)
                if ub_k is not None:
                    _consider_lo((ub_k - val_k).scale(inv_a), k_basic, ub_k)

        if hi_blocker is None and lo_blocker is None:
            return False

        if lo_blocker is None:
            chosen = hi_blocker
        elif hi_blocker is None:
            chosen = lo_blocker
        else:
            assert hi_delta is not None
            assert lo_delta is not None
            chosen = hi_blocker if hi_delta <= -lo_delta else lo_blocker

        assert chosen is not None
        blocker_var, bound_val = chosen
        if blocker_var == j_nb:
            self._update_nonbasic(j_nb, bound_val)
        else:
            self._pivot_and_update(blocker_var, j_nb, bound_val)
        return True

    # ------------------------------------------------------------------
    # Linearization & slack management
    # ------------------------------------------------------------------

    def _check_expr(self, expr: Expr) -> None:
        if expr.ctx is not self._ctx:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)

    def _alloc_orig_var(self, expr: Expr) -> int:
        existing = self._expr_to_var.get(expr)
        if existing is not None:
            return existing
        vid = len(self._val)
        self._expr_to_var[expr] = vid
        self._var_expr.append(expr)
        self._is_int.append(expr.is_int)
        self._is_original.append(True)
        self._slack_orig_coeffs.append(None)
        self._val.append(_DELTA_ZERO)
        self._lower.append(None)
        self._upper.append(None)
        self._lower_reason.append(None)
        self._upper_reason.append(None)
        return vid

    def _linearize(self, expr: Expr) -> tuple[dict[int, Fraction], Fraction]:
        memo: dict[Expr, tuple[dict[int, Fraction], Fraction]] = {}
        stack: list[tuple[Expr, bool]] = [(expr, False)]

        while stack:
            node, expanded = stack.pop()
            if node in memo:
                continue
            if isinstance(node, Const):
                assert not isinstance(node.value, bool)
                if node.is_int:
                    assert isinstance(node.value, int)
                    memo[node] = ({}, Fraction(node.value))
                elif node.is_real:
                    assert isinstance(node.value, Fraction)
                    memo[node] = ({}, node.value)
                else:
                    msg = f"Expected numeric Const, got '{node}'"
                    raise TypeError(msg)
                continue

            if not isinstance(node, App):
                msg = f"Unsupported AST node in LRA linearizer: {node!r}"
                raise TypeError(msg)

            kind = node.decl.kind
            if kind in (DeclKind.UNINTERPRETED, DeclKind.ITE, DeclKind.SELECT):
                vid = self._alloc_orig_var(node)
                memo[node] = ({vid: Fraction(1)}, Fraction(0))
                continue

            if not expanded:
                stack.append((node, True))
                for arg in reversed(node.args):
                    if arg not in memo:
                        stack.append((arg, False))
                continue

            if kind is DeclKind.TO_REAL:
                c_map, const = memo[node.args[0]]
                memo[node] = (dict(c_map), const)
            elif kind is DeclKind.NEG:
                c_map, const = memo[node.args[0]]
                memo[node] = ({v: -c for v, c in c_map.items()}, -const)
            elif kind is DeclKind.ADD:
                acc_map: dict[int, Fraction] = {}
                acc_const = Fraction(0)
                for arg in node.args:
                    c_map, c_const = memo[arg]
                    acc_const += c_const
                    for v, c in c_map.items():
                        nxt = acc_map.get(v, Fraction(0)) + c
                        if nxt == 0:
                            acc_map.pop(v, None)
                        else:
                            acc_map[v] = nxt
                memo[node] = (acc_map, acc_const)
            elif kind is DeclKind.SUB:
                l_map, l_const = memo[node.args[0]]
                r_map, r_const = memo[node.args[1]]
                sub_map = dict(l_map)
                for v, c in r_map.items():
                    nxt = sub_map.get(v, Fraction(0)) - c
                    if nxt == 0:
                        sub_map.pop(v, None)
                    else:
                        sub_map[v] = nxt
                memo[node] = (sub_map, l_const - r_const)
            elif kind is DeclKind.MUL:
                const_factor = Fraction(1)
                var_term: tuple[dict[int, Fraction], Fraction] | None = None
                for arg in node.args:
                    c_map, c_const = memo[arg]
                    if not c_map:
                        const_factor *= c_const
                    elif var_term is None:
                        var_term = (c_map, c_const)
                    else:
                        msg = f"Non-linear multiplication in linear arithmetic: {node}"
                        raise ValueError(msg)
                if const_factor == 0 or var_term is None:
                    scaled_val = const_factor if var_term is None else Fraction(0)
                    memo[node] = ({}, scaled_val)
                else:
                    v_map, v_const = var_term
                    memo[node] = (
                        {v: c * const_factor for v, c in v_map.items()},
                        v_const * const_factor,
                    )
            elif kind is DeclKind.DIV:
                l_map, l_const = memo[node.args[0]]
                r_map, r_const = memo[node.args[1]]
                if r_map or r_const == 0:
                    msg = f"Non-linear or zero division in linear arithmetic: {node}"
                    raise ValueError(msg)
                memo[node] = (
                    {v: c / r_const for v, c in l_map.items()},
                    l_const / r_const,
                )
            else:
                msg = f"Unsupported operator in arithmetic expression: {kind}"
                raise TypeError(msg)

        res_map, res_const = memo[expr]
        return dict(res_map), res_const

    def _get_or_create_var_for_form(
        self, coeffs: dict[int, Fraction], rhs: Fraction
    ) -> tuple[int, Fraction, Fraction]:
        """Normalize linear form, returning ``(vid, scale, scaled_rhs)``."""
        items = sorted(coeffs.items())
        if len(items) == 1:
            vid, coeff = items[0]
            if self._is_int[vid]:
                # Keep sign via scale +/-1 and scale RHS to Fraction(rhs, abs(coeff))
                sign = Fraction(1) if coeff > 0 else Fraction(-1)
                return vid, sign, rhs / coeff
            return vid, coeff, rhs / coeff

        all_int = all(self._is_int[v] for v, _ in items)
        if all_int:
            lcm_den = math.lcm(*(c.denominator for _, c in items))
            int_coeffs = [(v, int(c * lcm_den)) for v, c in items]
            g = math.gcd(*(abs(ic) for _, ic in int_coeffs))
            sign = -1 if int_coeffs[0][1] < 0 else 1
            factor = Fraction(lcm_den * sign, g)
            key = tuple((v, Fraction(sign * ic // g)) for v, ic in int_coeffs)
        else:
            lead_coeff = items[0][1]
            factor = Fraction(1) / lead_coeff
            key = tuple((v, c * factor) for v, c in items)

        scaled_rhs = rhs * factor
        existing = self._slack_map.get(key)
        if existing is not None:
            return existing, factor, scaled_rhs

        # Create a fresh basic slack variable equal to sum(key).
        s_id = len(self._val)
        self._slack_map[key] = s_id
        self._var_expr.append(None)
        self._is_int.append(all_int)
        self._is_original.append(False)
        self._slack_orig_coeffs.append(dict(key))
        self._lower.append(None)
        self._upper.append(None)
        self._lower_reason.append(None)
        self._upper_reason.append(None)

        expanded_row: dict[int, Fraction] = {}
        for orig_v, c_v in key:
            basic_def = self._basic_rows.get(orig_v)
            if basic_def is not None:
                for nb, coef_nb in basic_def.items():
                    upd = expanded_row.get(nb, Fraction(0)) + c_v * coef_nb
                    if upd == 0:
                        expanded_row.pop(nb, None)
                    else:
                        expanded_row[nb] = upd
            else:
                upd = expanded_row.get(orig_v, Fraction(0)) + c_v
                if upd == 0:
                    expanded_row.pop(orig_v, None)
                else:
                    expanded_row[orig_v] = upd

        init_val = _DELTA_ZERO
        for nb, coef_nb in expanded_row.items():
            init_val = init_val + self._val[nb].scale(coef_nb)
            self._col_uses.setdefault(nb, set()).add(s_id)

        self._val.append(init_val)
        self._basic_rows[s_id] = expanded_row
        return s_id, factor, scaled_rhs

    # ------------------------------------------------------------------
    # Bound updates, subsumption propagation, pivoting & Simplex
    # ------------------------------------------------------------------

    def _enqueue_prop(
        self, atom: Expr, polarity: bool, reasons: list[TheoryLit]
    ) -> None:
        key = (atom, polarity)
        if (
            atom in self._asserted_atoms
            or atom in self._pending_prop_set
            or key in self._prop_reasons
        ):
            return
        self._pending_prop_set.add(atom)
        self._pending_props.append(key)
        self._prop_reasons[key] = reasons
        if self._trail_marks:
            self._history.append((_OP_PROP_REASON, key))
        self._stats.propagations += 1

    def _check_atom_subsumed(self, atom: Expr) -> None:
        info = self._atom_info[atom]
        if info[0] == "const" or atom in self._asserted_atoms:
            return

        _, vid, scale, scaled_rhs, cmp_kind = info
        assert isinstance(vid, int)
        assert isinstance(scale, Fraction)
        assert isinstance(scaled_rhs, Fraction)
        assert isinstance(cmp_kind, DeclKind)
        var_int = self._is_int[vid]
        dir_sign = 1 if scale > 0 else -1

        # Check whether polarity=True is already forced by current bounds.
        for pol in (True, False):
            raw_upper, strict = _bound_from_cmp(cmp_kind, pol)
            need_upper, strict = _apply_dir(raw_upper, strict, dir_sign)
            req = _tighten_bound(
                var_int, scaled_rhs, is_upper=need_upper, strict=strict
            )
            # ``v <= ub_req`` holds if current upper <= ub_req.
            # ``v >= lb_req`` holds if current lower >= lb_req.
            if need_upper:
                cur_ub = self._upper[vid]
                if cur_ub is not None and cur_ub <= req:
                    reason = self._upper_reason[vid]
                    assert reason is not None
                    self._enqueue_prop(atom, pol, [reason])
                    return
            else:
                cur_lb = self._lower[vid]
                if cur_lb is not None and cur_lb >= req:
                    reason = self._lower_reason[vid]
                    assert reason is not None
                    self._enqueue_prop(atom, pol, [reason])
                    return

    def _propagate_var_atoms(self, vid: int) -> None:
        atoms = self._var_atoms.get(vid)
        if atoms:
            for atom in atoms:
                self._check_atom_subsumed(atom)

    def _apply_bound_update(
        self,
        vid: int,
        target: DeltaRational,
        reason: TheoryLit,
        *,
        is_upper: bool,
    ) -> None:
        self._stats.bound_updates += 1
        if is_upper:
            cur_upper = self._upper[vid]
            if cur_upper is not None and cur_upper <= target:
                return
            cur_lower = self._lower[vid]
            if cur_lower is not None and target < cur_lower:
                low_reason = self._lower_reason[vid]
                assert low_reason is not None
                if self._conflict is None:
                    self._conflict = _dedup_lits([low_reason, reason])
                    self._stats.conflicts += 1
                return
            if self._trail_marks:
                self._history.append(
                    (_OP_UPPER, vid, cur_upper, self._upper_reason[vid])
                )
            self._upper[vid] = target
            self._upper_reason[vid] = reason
            if vid not in self._basic_rows and self._val[vid] > target:
                self._update_nonbasic(vid, target)
            self._propagate_var_atoms(vid)
            return

        cur_lower = self._lower[vid]
        if cur_lower is not None and cur_lower >= target:
            return
        cur_upper = self._upper[vid]
        if cur_upper is not None and target > cur_upper:
            up_reason = self._upper_reason[vid]
            assert up_reason is not None
            if self._conflict is None:
                self._conflict = _dedup_lits([up_reason, reason])
                self._stats.conflicts += 1
            return
        if self._trail_marks:
            self._history.append((_OP_LOWER, vid, cur_lower, self._lower_reason[vid]))
        self._lower[vid] = target
        self._lower_reason[vid] = reason
        if vid not in self._basic_rows and self._val[vid] < target:
            self._update_nonbasic(vid, target)
        self._propagate_var_atoms(vid)

    def _update_nonbasic(self, j_nb: int, new_val: DeltaRational) -> None:
        diff = new_val - self._val[j_nb]
        self._val[j_nb] = new_val
        uses = self._col_uses.get(j_nb)
        if not uses:
            return
        for r_basic in uses:
            a_rj = self._basic_rows[r_basic][j_nb]
            self._val[r_basic] = self._val[r_basic] + diff.scale(a_rj)

    def _solve_simplex(self) -> bool:
        while True:
            # Bland's rule: pick smallest violated basic variable ID.
            i_basic: int | None = None
            need_inc = False
            for r_id in sorted(self._basic_rows):
                val = self._val[r_id]
                lb = self._lower[r_id]
                if lb is not None and val < lb:
                    i_basic = r_id
                    need_inc = True
                    break
                ub = self._upper[r_id]
                if ub is not None and val > ub:
                    i_basic = r_id
                    need_inc = False
                    break

            if i_basic is None:
                return True

            row = self._basic_rows[i_basic]
            entering_nb: int | None = None
            if need_inc:
                for j_nb in sorted(row):
                    a_ij = row[j_nb]
                    if a_ij > 0:
                        ub = self._upper[j_nb]
                        if ub is None or self._val[j_nb] < ub:
                            entering_nb = j_nb
                            break
                    else:
                        lb = self._lower[j_nb]
                        if lb is None or self._val[j_nb] > lb:
                            entering_nb = j_nb
                            break
                if entering_nb is None:
                    self._record_farkas_conflict(i_basic, row, violated_lower=True)
                    return False
                target = self._lower[i_basic]
                assert target is not None
                self._pivot_and_update(i_basic, entering_nb, target)
            else:
                for j_nb in sorted(row):
                    a_ij = row[j_nb]
                    if a_ij > 0:
                        lb = self._lower[j_nb]
                        if lb is None or self._val[j_nb] > lb:
                            entering_nb = j_nb
                            break
                    else:
                        ub = self._upper[j_nb]
                        if ub is None or self._val[j_nb] < ub:
                            entering_nb = j_nb
                            break
                if entering_nb is None:
                    self._record_farkas_conflict(i_basic, row, violated_lower=False)
                    return False
                target = self._upper[i_basic]
                assert target is not None
                self._pivot_and_update(i_basic, entering_nb, target)

    def _record_farkas_conflict(
        self, i_basic: int, row: dict[int, Fraction], *, violated_lower: bool
    ) -> None:
        reasons: list[TheoryLit] = []
        base_reason = (
            self._lower_reason[i_basic]
            if violated_lower
            else self._upper_reason[i_basic]
        )
        assert base_reason is not None
        reasons.append(base_reason)

        for j_nb, a_ij in row.items():
            use_upper = (a_ij > 0) if violated_lower else (a_ij < 0)
            r = self._upper_reason[j_nb] if use_upper else self._lower_reason[j_nb]
            assert r is not None
            reasons.append(r)

        self._conflict = _dedup_lits(reasons)
        self._stats.conflicts += 1

    def _pivot_and_update(
        self, i_basic: int, j_nb: int, target_val: DeltaRational
    ) -> None:
        self._stats.pivots += 1
        row_i = self._basic_rows.pop(i_basic)
        a_ij = row_i[j_nb]
        theta = (target_val - self._val[i_basic]).scale(Fraction(1) / a_ij)

        self._val[i_basic] = target_val
        self._val[j_nb] = self._val[j_nb] + theta
        for k_basic in list(self._col_uses.get(j_nb, ())):
            if k_basic == i_basic or k_basic not in self._basic_rows:
                continue
            a_kj = self._basic_rows[k_basic][j_nb]
            self._val[k_basic] = self._val[k_basic] + theta.scale(a_kj)

        for col in row_i:
            self._col_uses[col].discard(i_basic)

        inv_aij = Fraction(1) / a_ij
        new_row_j: dict[int, Fraction] = {i_basic: inv_aij}
        for col, a_ik in row_i.items():
            if col != j_nb:
                new_row_j[col] = -a_ik * inv_aij

        self._basic_rows[j_nb] = new_row_j
        for col in new_row_j:
            self._col_uses.setdefault(col, set()).add(j_nb)

        for k_basic in list(self._col_uses.get(j_nb, ())):
            if k_basic == j_nb:
                continue
            row_k = self._basic_rows[k_basic]
            a_kj = row_k.pop(j_nb)
            self._col_uses[j_nb].discard(k_basic)
            for col, coef_jm in new_row_j.items():
                upd = row_k.get(col, Fraction(0)) + a_kj * coef_jm
                if upd == 0:
                    row_k.pop(col, None)
                    self._col_uses[col].discard(k_basic)
                else:
                    row_k[col] = upd
                    self._col_uses.setdefault(col, set()).add(k_basic)
