"""Nonlinear Real & Integer Arithmetic (NLA) solver.

Uses ICP, Sturm root isolation, and incremental linearization.
Operates on top of an :class:`LRASolver` relaxation (with ``allow_nonlinear=True``)
without touching ``sat`` or ``smt``:
- Interval Constraint Propagation (ICP) over rational/strict intervals.
- Exact univariate rational polynomial algebra & Sturm real-root isolation.
- Incremental linearization lemmas (squares, zero/sign, McCormick envelopes,
  tangent planes, exact integer slicing) plus budgeted case splitting.
- Conservative ``NLAUnknown`` reporting on irrational roots or exhausted budgets.

Depends on: ``syntax``, ``model``, ``theories.base``, ``theories.lra``.
"""

import math
from dataclasses import dataclass
from fractions import Fraction

from unsat.syntax import App, Const, Context, DeclKind, Expr
from unsat.theories.base import NLAStats, TheoryLit
from unsat.theories.lra import LRASolver

type Poly = tuple[Fraction, ...]


@dataclass(frozen=True, slots=True)
class NLBudget:
    """Budget limiting nonlinear lemma generation and case splits per check."""

    max_lemmas: int = 200
    max_splits: int = 64


@dataclass(frozen=True, slots=True)
class NLALemma:
    """Conditional nonlinear theory lemma ``(reasons => formula)``."""

    formula: Expr
    reasons: tuple[TheoryLit, ...] = ()


@dataclass(frozen=True, slots=True)
class NLAUnknown:
    """NLA could not decide satisfiability within rational or budget bounds."""

    reason: str


# ------------------------------------------------------------------
# Exact univariate rational polynomial algebra & Sturm root isolation
# ------------------------------------------------------------------


def _poly_norm(coeffs: list[Fraction] | tuple[Fraction, ...]) -> Poly:
    end = len(coeffs)
    while end > 0 and coeffs[end - 1] == 0:
        end -= 1
    return tuple(coeffs[:end])


def poly_add(a: Poly, b: Poly) -> Poly:
    """Return polynomial sum ``a + b``."""
    n = max(len(a), len(b))
    out = [
        (a[i] if i < len(a) else Fraction(0)) + (b[i] if i < len(b) else Fraction(0))
        for i in range(n)
    ]
    return _poly_norm(out)


def poly_sub(a: Poly, b: Poly) -> Poly:
    """Return polynomial difference ``a - b``."""
    n = max(len(a), len(b))
    out = [
        (a[i] if i < len(a) else Fraction(0)) - (b[i] if i < len(b) else Fraction(0))
        for i in range(n)
    ]
    return _poly_norm(out)


def poly_mul(a: Poly, b: Poly) -> Poly:
    """Return polynomial product ``a * b``."""
    if not a or not b:
        return ()
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            out[i + j] += ca * cb
    return _poly_norm(out)


def poly_divmod(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    """Return Euclidean polynomial quotient and remainder ``(q, r)`` over ``Q``."""
    if not b:
        msg = "Polynomial division by zero"
        raise ZeroDivisionError(msg)
    rem = list(a)
    deg_b = len(b) - 1
    lc_b = b[deg_b]
    if len(a) - 1 < deg_b:
        return (), a
    quot = [Fraction(0)] * (len(a) - deg_b)
    for k in range(len(a) - 1, deg_b - 1, -1):
        if k >= len(rem):
            continue
        c = rem[k]
        if c == 0:
            continue
        q_coeff = c / lc_b
        shift = k - deg_b
        quot[shift] = q_coeff
        for j in range(deg_b + 1):
            rem[shift + j] -= q_coeff * b[j]
    return _poly_norm(quot), _poly_norm(rem)


def poly_deriv(p: Poly) -> Poly:
    """Return formal derivative ``p'(x)``."""
    if len(p) <= 1:
        return ()
    return _poly_norm([p[i] * i for i in range(1, len(p))])


def poly_gcd(a: Poly, b: Poly) -> Poly:
    """Return monic GCD of univariate polynomials ``a`` and ``b`` over ``Q``."""
    while b:
        _, r = poly_divmod(a, b)
        a, b = b, r
    if not a:
        return ()
    lc = a[-1]
    return tuple(c / lc for c in a)


def poly_squarefree(p: Poly) -> Poly:
    """Return monic squarefree part ``p / gcd(p, p')``."""
    if len(p) <= 1:
        return ()
    g = poly_gcd(p, poly_deriv(p))
    q, _ = poly_divmod(p, g)
    lc = q[-1]
    return tuple(c / lc for c in q)


def poly_eval(p: Poly, x: Fraction) -> Fraction:
    """Evaluate polynomial ``p(x)`` using Horner's method."""
    acc = Fraction(0)
    for c in reversed(p):
        acc = acc * x + c
    return acc


def sturm_sequence(p: Poly) -> list[Poly]:
    """Build standard Sturm chain for non-constant polynomial ``p``."""
    f0 = poly_squarefree(p)
    if len(f0) <= 1:
        return []
    f1 = poly_deriv(f0)
    seq: list[Poly] = [f0, f1]
    while len(seq[-1]) > 1:
        _, rem = poly_divmod(seq[-2], seq[-1])
        if not rem:
            break
        seq.append(tuple(-c for c in rem))
    return seq


def _sign_variations(vals: list[int]) -> int:
    changes = 0
    prev = 0
    for s in vals:
        if s == 0:
            continue
        if prev != 0 and s != prev:
            changes += 1
        prev = s
    return changes


def sturm_variations(seq: list[Poly], x: Fraction) -> int:
    """Count sign changes in Sturm chain ``seq`` evaluated at ``x``."""
    signs: list[int] = []
    for f in seq:
        val = poly_eval(f, x)
        signs.append(1 if val > 0 else -1 if val < 0 else 0)
    return _sign_variations(signs)


def _sturm_variations_inf(seq: list[Poly], *, neg: bool) -> int:
    signs: list[int] = []
    for f in seq:
        deg = len(f) - 1
        lc = f[deg]
        s = 1 if lc > 0 else -1
        if neg and (deg & 1):
            s = -s
        signs.append(s)
    return _sign_variations(signs)


def _divisors(n: int) -> list[int]:
    n = abs(n)
    if n == 0:
        return []
    small: list[int] = []
    large: list[int] = []
    d = 1
    while d * d <= n and len(small) < 256:
        if n % d == 0:
            small.append(d)
            q = n // d
            if q != d:
                large.append(q)
        d += 1
    return small + list(reversed(large))


def _extract_rational_roots(p: Poly) -> tuple[list[Fraction], Poly]:
    """Factor out all exact rational roots of ``p``, returning ``(roots, rem)``."""
    if not p:
        return [], ()
    roots: list[Fraction] = []
    cur = p
    while cur and cur[0] == 0:
        if Fraction(0) not in roots:
            roots.append(Fraction(0))
        cur = cur[1:]

    while len(cur) > 1:
        lcm_den = math.lcm(*(c.denominator for c in cur))
        int_coeffs = [int(c * lcm_den) for c in cur]
        a0 = abs(int_coeffs[0])
        an = abs(int_coeffs[-1])
        if a0 > 1_000_000 or an > 1_000_000:
            break
        num_divs = _divisors(a0)
        den_divs = _divisors(an)
        found: Fraction | None = None
        seen_cands: set[Fraction] = set()
        for num in num_divs:
            for den in den_divs:
                cand = Fraction(num, den)
                if cand in seen_cands:
                    continue
                seen_cands.add(cand)
                if poly_eval(cur, cand) == 0:
                    found = cand
                    break
                if poly_eval(cur, -cand) == 0:
                    found = -cand
                    break
            if found is not None:
                break
        if found is None:
            break
        roots.append(found)
        divisor = (-found, Fraction(1))
        while len(cur) > 1 and poly_eval(cur, found) == 0:
            cur, _ = poly_divmod(cur, divisor)
    return roots, cur


def isolate_real_roots(p: Poly) -> list[tuple[Fraction, Fraction, bool]]:
    """Return sorted disjoint root brackets ``(lo, hi, is_rational)`` for ``p``.

    Rational roots satisfy ``lo == hi`` and ``is_rational is True``.
    Irrational roots have strictly open brackets ``(lo, hi)`` with ``lo < hi``
    and ``is_rational is False``.
    """
    if len(p) <= 1:
        return []
    sf = poly_squarefree(p)
    rat_roots, rem = _extract_rational_roots(sf)
    out: list[tuple[Fraction, Fraction, bool]] = [(r, r, True) for r in rat_roots]

    if len(rem) > 1:
        seq = sturm_sequence(rem)
        total = _sturm_variations_inf(seq, neg=True) - _sturm_variations_inf(
            seq, neg=False
        )
        if total > 0:
            lc_abs = abs(rem[-1])
            bound = Fraction(1) + max(
                (abs(c) / lc_abs for c in rem[:-1]), default=Fraction(0)
            )
            lo = -bound
            hi = bound
            while poly_eval(rem, lo) == 0:
                lo *= 2
            while poly_eval(rem, hi) == 0:
                hi *= 2

            stack: list[tuple[Fraction, Fraction, int, int]] = [
                (lo, hi, sturm_variations(seq, lo), sturm_variations(seq, hi))
            ]
            while stack:
                a, b, va, vb = stack.pop()
                count = va - vb
                if count <= 0:
                    continue
                if count == 1:
                    fa = poly_eval(rem, a)
                    for _ in range(10):
                        if b - a <= Fraction(1, 256):
                            break
                        mid = (a + b) / 2
                        fm = poly_eval(rem, mid)
                        if fm == 0:
                            out.append((mid, mid, True))
                            a = b
                            break
                        if (fa < 0 and fm > 0) or (fa > 0 and fm < 0):
                            b = mid
                        else:
                            a = mid
                            fa = fm
                    if a < b:
                        out.append((a, b, False))
                    continue
                mid = (a + b) / 2
                # Safeguard in case rational factor extraction skipped huge coeffs:
                if poly_eval(rem, mid) == 0:
                    out.append((mid, mid, True))
                    eps = (b - a) / 64
                    if eps <= 0:
                        eps = Fraction(1, 1024)
                    stack.append((a, mid - eps, va, sturm_variations(seq, mid - eps)))
                    stack.append((mid + eps, b, sturm_variations(seq, mid + eps), vb))
                else:
                    vm = sturm_variations(seq, mid)
                    stack.append((mid, b, vm, vb))
                    stack.append((a, mid, va, vm))

    out.sort(key=lambda item: (item[0], item[1]))
    return out


# ------------------------------------------------------------------
# Interval arithmetic helpers for ICP
# ------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class _BoundInterval:
    lo: Fraction | None
    lo_strict: bool
    lo_reasons: tuple[TheoryLit, ...]
    hi: Fraction | None
    hi_strict: bool
    hi_reasons: tuple[TheoryLit, ...]

    def is_empty(self) -> bool:
        if self.lo is None or self.hi is None:
            return False
        if self.lo > self.hi:
            return True
        return self.lo == self.hi and (self.lo_strict or self.hi_strict)

    def contains(self, val: Fraction) -> bool:
        if self.lo is not None and (
            val < self.lo or (self.lo_strict and val == self.lo)
        ):
            return False
        return not (
            self.hi is not None
            and (val > self.hi or (self.hi_strict and val == self.hi))
        )

    def intersect(self, other: _BoundInterval) -> _BoundInterval:
        lo, lo_s, lo_r = self.lo, self.lo_strict, self.lo_reasons
        if other.lo is not None and (
            lo is None
            or other.lo > lo
            or (other.lo == lo and other.lo_strict and not lo_s)
        ):
            lo, lo_s, lo_r = other.lo, other.lo_strict, other.lo_reasons

        hi, hi_s, hi_r = self.hi, self.hi_strict, self.hi_reasons
        if other.hi is not None and (
            hi is None
            or other.hi < hi
            or (other.hi == hi and other.hi_strict and not hi_s)
        ):
            hi, hi_s, hi_r = other.hi, other.hi_strict, other.hi_reasons

        return _BoundInterval(lo, lo_s, lo_r, hi, hi_s, hi_r)


def _mul_intervals(a: _BoundInterval, b: _BoundInterval) -> _BoundInterval:
    """Compute sound rational interval product ``a * b`` with reason tracking."""
    reasons = tuple(
        dict.fromkeys(a.lo_reasons + a.hi_reasons + b.lo_reasons + b.hi_reasons)
    )
    a_points = [
        (p, s) for p, s in ((a.lo, a.lo_strict), (a.hi, a.hi_strict)) if p is not None
    ]
    b_points = [
        (p, s) for p, s in ((b.lo, b.lo_strict), (b.hi, b.hi_strict)) if p is not None
    ]

    # Exact square rule whenever either interval is a single interval [a] * [a]
    if a.lo is not None and a.hi is not None and b.lo is not None and b.hi is not None:
        corners: list[tuple[Fraction, bool]] = []
        for va, sa in a_points:
            for vb, sb in b_points:
                if va == 0:
                    strict = sa and (vb != 0)
                elif vb == 0:
                    strict = sb and (va != 0)
                else:
                    strict = sa or sb
                corners.append((va * vb, strict))
        lo_val, lo_s = corners[0]
        hi_val, hi_s = corners[0]
        for v, s in corners[1:]:
            if v < lo_val or (v == lo_val and not s and lo_s):
                lo_val, lo_s = v, s
            if v > hi_val or (v == hi_val and not s and hi_s):
                hi_val, hi_s = v, s
        return _BoundInterval(lo_val, lo_s, reasons, hi_val, hi_s, reasons)

    # One-sided sign bounds when intervals are half-bounded
    a_pos = a.lo is not None and a.lo > 0
    a_nonneg = a.lo is not None and a.lo >= 0
    a_neg = a.hi is not None and a.hi < 0
    a_nonpos = a.hi is not None and a.hi <= 0
    b_pos = b.lo is not None and b.lo > 0
    b_nonneg = b.lo is not None and b.lo >= 0
    b_neg = b.hi is not None and b.hi < 0
    b_nonpos = b.hi is not None and b.hi <= 0

    lo: Fraction | None = None
    lo_s = False
    hi: Fraction | None = None
    hi_s = False
    lo_r: tuple[TheoryLit, ...] = ()
    hi_r: tuple[TheoryLit, ...] = ()

    if a_nonneg and b_nonneg:
        assert a.lo is not None
        assert b.lo is not None
        lo = a.lo * b.lo
        lo_s = (
            (a_pos and b_pos and (a.lo_strict or b.lo_strict))
            or (a.lo == 0 and a.lo_strict and b_pos)
            or (b.lo == 0 and b.lo_strict and a_pos)
        )
        lo_r = tuple(dict.fromkeys(a.lo_reasons + b.lo_reasons))
    elif a_nonpos and b_nonpos:
        assert a.hi is not None
        assert b.hi is not None
        lo = a.hi * b.hi
        lo_s = (
            (a_neg and b_neg and (a.hi_strict or b.hi_strict))
            or (a.hi == 0 and a.hi_strict and b_neg)
            or (b.hi == 0 and b.hi_strict and a_neg)
        )
        lo_r = tuple(dict.fromkeys(a.hi_reasons + b.hi_reasons))
    elif a_nonneg and b_nonpos:
        assert a.lo is not None
        assert b.hi is not None
        hi = a.lo * b.hi
        hi_s = (
            (a_pos and b_neg and (a.lo_strict or b.hi_strict))
            or (a.lo == 0 and a.lo_strict and b_neg)
            or (b.hi == 0 and b.hi_strict and a_pos)
        )
        hi_r = tuple(dict.fromkeys(a.lo_reasons + b.hi_reasons))
    elif a_nonpos and b_nonneg:
        assert a.hi is not None
        assert b.lo is not None
        hi = a.hi * b.lo
        hi_s = (
            (a_neg and b_pos and (a.hi_strict or b.lo_strict))
            or (a.hi == 0 and a.hi_strict and b_pos)
            or (b.lo == 0 and b.lo_strict and a_neg)
        )
        hi_r = tuple(dict.fromkeys(a.hi_reasons + b.lo_reasons))

    return _BoundInterval(lo, lo_s, lo_r, hi, hi_s, hi_r)


def _square_interval(a: _BoundInterval) -> _BoundInterval:
    """Compute tighter sound interval for ``a * a`` (always >= 0)."""
    lo_r = a.lo_reasons
    hi_r = a.hi_reasons
    if a.lo is not None and a.lo >= 0:
        lo_val = a.lo * a.lo
        lo_s = a.lo_strict
        hi_val = a.hi * a.hi if a.hi is not None else None
        hi_s = a.hi_strict if a.hi is not None else False
        return _BoundInterval(lo_val, lo_s, lo_r, hi_val, hi_s, hi_r)
    if a.hi is not None and a.hi <= 0:
        lo_val = a.hi * a.hi
        lo_s = a.hi_strict
        hi_val = a.lo * a.lo if a.lo is not None else None
        hi_s = a.lo_strict if a.lo is not None else False
        return _BoundInterval(lo_val, lo_s, hi_r, hi_val, hi_s, lo_r)

    hi_val: Fraction | None = None
    hi_s = False
    both_r: tuple[TheoryLit, ...] = ()
    if a.lo is not None and a.hi is not None:
        sq_lo = a.lo * a.lo
        sq_hi = a.hi * a.hi
        if sq_lo > sq_hi:
            hi_val, hi_s = sq_lo, a.lo_strict
        elif sq_hi > sq_lo:
            hi_val, hi_s = sq_hi, a.hi_strict
        else:
            hi_val, hi_s = sq_lo, a.lo_strict and a.hi_strict
        both_r = tuple(dict.fromkeys(lo_r + hi_r))
    return _BoundInterval(Fraction(0), False, (), hi_val, hi_s, both_r)


def _div_intervals(m: _BoundInterval, b: _BoundInterval) -> _BoundInterval | None:
    """Return sound interval for ``m / b`` when ``0`` is outside ``b``."""
    b_pos = b.lo is not None and (b.lo > 0 or (b.lo == 0 and b.lo_strict))
    b_neg = b.hi is not None and (b.hi < 0 or (b.hi == 0 and b.hi_strict))
    if not (b_pos or b_neg):
        return None
    inv_lo: Fraction | None = None
    inv_lo_s = False
    inv_hi: Fraction | None = None
    inv_hi_s = False
    if b_pos:
        if b.hi is not None:
            inv_lo, inv_lo_s = Fraction(1) / b.hi, b.hi_strict
        else:
            inv_lo, inv_lo_s = Fraction(0), True
        if b.lo is not None and b.lo > 0:
            inv_hi, inv_hi_s = Fraction(1) / b.lo, b.lo_strict
        inv_b = _BoundInterval(
            inv_lo, inv_lo_s, b.hi_reasons, inv_hi, inv_hi_s, b.lo_reasons
        )
        return _mul_intervals(m, inv_b)

    # b < 0
    if b.hi is not None and b.hi < 0:
        inv_lo, inv_lo_s = Fraction(1) / b.hi, b.hi_strict
    if b.lo is not None:
        inv_hi, inv_hi_s = Fraction(1) / b.lo, b.lo_strict
    else:
        inv_hi, inv_hi_s = Fraction(0), True
    inv_b = _BoundInterval(
        inv_lo, inv_lo_s, b.hi_reasons, inv_hi, inv_hi_s, b.lo_reasons
    )
    return _mul_intervals(m, inv_b)


class NLASolver:
    """Nonlinear arithmetic checker paired with an :class:`LRASolver` relaxation."""

    def __init__(self, ctx: Context, *, budget: NLBudget | None = None) -> None:
        self._ctx = ctx
        self._budget = budget if budget is not None else NLBudget()
        self._stats = NLAStats()
        self._splits_used = 0

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._ctx

    @property
    def stats(self) -> NLAStats:
        """Instrumentation counters for NLA checks, lemmas, and splits."""
        return self._stats

    def reset_check_state(self) -> None:
        """Reset per-solve split counters before a fresh ``check()``."""
        self._splits_used = 0

    @staticmethod
    def _num_val(ctx: Context, template: Expr, val: Fraction) -> Expr:
        if template.is_int:
            assert val.denominator == 1
            return ctx.mk_int_val(val.numerator)
        return ctx.mk_real_val(val)

    def _emit_bound(
        self,
        term: Expr,
        bound: Fraction,
        *,
        is_upper: bool,
        strict: bool,
        reasons: tuple[TheoryLit, ...],
        emitted_lemmas: set[Expr],
    ) -> NLALemma | None:
        ctx = self._ctx
        if not term.is_int and bound.denominator > 10_000:
            return None
        if term.is_int:
            val_int = (
                (math.ceil(bound) - 1 if strict else math.floor(bound))
                if is_upper
                else (math.floor(bound) + 1 if strict else math.ceil(bound))
            )
            rhs = ctx.mk_int_val(val_int)
            atom = ctx.mk_le(term, rhs) if is_upper else ctx.mk_ge(term, rhs)
        else:
            rhs = ctx.mk_real_val(bound)
            if is_upper:
                atom = ctx.mk_lt(term, rhs) if strict else ctx.mk_le(term, rhs)
            else:
                atom = ctx.mk_gt(term, rhs) if strict else ctx.mk_ge(term, rhs)
        if atom in emitted_lemmas or atom is ctx.true_expr:
            return None
        emitted_lemmas.add(atom)
        return NLALemma(atom, reasons)

    def _run_icp(
        self,
        lra: LRASolver,
        muls: dict[Expr, tuple[Expr, Expr]],
        vals: dict[Expr, Fraction],
        emitted_lemmas: set[Expr],
    ) -> list[NLALemma]:
        intervals: dict[Expr, _BoundInterval] = {}
        orig_terms = set(muls)
        for a, b in muls.values():
            orig_terms.add(a)
            orig_terms.add(b)

        for term in orig_terms:
            vid = lra.var_id_or_none(term)
            if vid is None:
                intervals[term] = _BoundInterval(None, False, (), None, False, ())
                continue
            lb, lr, ub, ur = lra.var_bounds_with_reasons(vid)
            lo = lb.real if lb is not None else None
            lo_s = lb is not None and lb.delta > 0
            hi = ub.real if ub is not None else None
            hi_s = ub is not None and ub.delta < 0
            intervals[term] = _BoundInterval(
                lo,
                lo_s,
                (lr,) if lr is not None else (),
                hi,
                hi_s,
                (ur,) if ur is not None else (),
            )
            if intervals[term].is_empty():
                rsn = tuple(
                    dict.fromkeys(
                        intervals[term].lo_reasons + intervals[term].hi_reasons
                    )
                )
                self._stats.icp_conflicts += 1
                return [NLALemma(self._ctx.false_expr, rsn)]

        initial = dict(intervals)
        for _ in range(4):
            changed = False
            for m, (a, b) in muls.items():
                fwd = (
                    _square_interval(intervals[a])
                    if a is b
                    else _mul_intervals(intervals[a], intervals[b])
                )
                merged_m = intervals[m].intersect(fwd)
                if merged_m.is_empty():
                    self._stats.icp_conflicts += 1
                    rsn = tuple(
                        dict.fromkeys(merged_m.lo_reasons + merged_m.hi_reasons)
                    )
                    return [NLALemma(self._ctx.false_expr, rsn)]
                if merged_m != intervals[m]:
                    intervals[m] = merged_m
                    changed = True

                # Backward narrowing
                if a is b:
                    if merged_m.hi is not None and merged_m.hi >= 0:
                        pass
                else:
                    ba = _div_intervals(intervals[m], intervals[b])
                    if ba is not None:
                        ma = intervals[a].intersect(ba)
                        if ma.is_empty():
                            self._stats.icp_conflicts += 1
                            rsn = tuple(dict.fromkeys(ma.lo_reasons + ma.hi_reasons))
                            return [NLALemma(self._ctx.false_expr, rsn)]
                        if ma != intervals[a]:
                            intervals[a] = ma
                            changed = True
                    bb = _div_intervals(intervals[m], intervals[a])
                    if bb is not None:
                        mb = intervals[b].intersect(bb)
                        if mb.is_empty():
                            self._stats.icp_conflicts += 1
                            rsn = tuple(dict.fromkeys(mb.lo_reasons + mb.hi_reasons))
                            return [NLALemma(self._ctx.false_expr, rsn)]
                        if mb != intervals[b]:
                            intervals[b] = mb
                            changed = True
            if not changed:
                break

        lemmas: list[NLALemma] = []
        for term, iv in intervals.items():
            if iv == initial[term]:
                continue
            cur_v = vals[term]
            if iv.lo is not None and (
                cur_v < iv.lo or (iv.lo_strict and cur_v == iv.lo)
            ):
                lem = self._emit_bound(
                    term,
                    iv.lo,
                    is_upper=False,
                    strict=iv.lo_strict,
                    reasons=iv.lo_reasons,
                    emitted_lemmas=emitted_lemmas,
                )
                if lem is not None:
                    lemmas.append(lem)
            if iv.hi is not None and (
                cur_v > iv.hi or (iv.hi_strict and cur_v == iv.hi)
            ):
                lem = self._emit_bound(
                    term,
                    iv.hi,
                    is_upper=True,
                    strict=iv.hi_strict,
                    reasons=iv.hi_reasons,
                    emitted_lemmas=emitted_lemmas,
                )
                if lem is not None:
                    lemmas.append(lem)
        return lemmas

    def _expand_univariate(
        self,
        expr: Expr,
        muls: dict[Expr, tuple[Expr, Expr]],
        subst: dict[Expr, tuple[Expr, Fraction, Fraction]] | None = None,
    ) -> tuple[Expr | None, Poly] | None:
        """Try expressing monomial/var ``expr`` as ``(base_var, poly(base_var))``."""
        sub_map = subst or {}
        if expr in sub_map:
            bx, k1, k0 = sub_map[expr]
            return bx, _poly_norm([k0, k1])
        if expr not in muls:
            if isinstance(expr, Const):
                assert not isinstance(expr.value, bool)
                return None, _poly_norm([Fraction(expr.value)])
            return expr, (Fraction(0), Fraction(1))

        memo: dict[Expr, tuple[Expr | None, Poly]] = {}
        stack: list[tuple[Expr, bool]] = [(expr, False)]
        while stack:
            node, expanded = stack.pop()
            if node in memo:
                continue
            if node in sub_map:
                bx, k1, k0 = sub_map[node]
                memo[node] = (bx, _poly_norm([k0, k1]))
                continue
            if node not in muls:
                if isinstance(node, Const):
                    assert not isinstance(node.value, bool)
                    memo[node] = (None, _poly_norm([Fraction(node.value)]))
                else:
                    memo[node] = (node, (Fraction(0), Fraction(1)))
                continue
            a, b = muls[node]
            if not expanded:
                stack.append((node, True))
                stack.append((b, False))
                stack.append((a, False))
                continue
            va, pa = memo[a]
            vb, pb = memo[b]
            if va is not None and vb is not None and va is not vb:
                return None
            base = va if va is not None else vb
            memo[node] = (base, poly_mul(pa, pb))
        return memo[expr]

    def _collect_linear_substitutions(
        self,
        lra: LRASolver,
        muls: dict[Expr, tuple[Expr, Expr]],
    ) -> tuple[
        dict[Expr, tuple[Expr, Fraction, Fraction]], dict[Expr, tuple[TheoryLit, ...]]
    ]:
        """Extract explicit equalities ``y = k1 * x + k0`` for 2-var elimination."""
        # Collect upper/lower halfspaces in canonical normalized form.
        upper_forms: dict[
            tuple[tuple[tuple[Expr, Fraction], ...], Fraction], TheoryLit
        ] = {}
        lower_forms: dict[
            tuple[tuple[tuple[Expr, Fraction], ...], Fraction], TheoryLit
        ] = {}

        def _canon_form(
            c_map: dict[Expr, Fraction], c0: Fraction
        ) -> tuple[tuple[tuple[tuple[Expr, Fraction], ...], Fraction], Fraction] | None:
            items = sorted(
                ((e, c) for e, c in c_map.items() if c != 0), key=lambda kv: kv[0].id
            )
            if not items or len(items) > 2:
                return None
            if any(e in muls for e, _ in items):
                return None
            scale = items[0][1]
            norm_items = tuple((e, c / scale) for e, c in items)
            return (norm_items, c0 / scale), scale

        equalities: list[
            tuple[dict[Expr, Fraction], Fraction, tuple[TheoryLit, ...]]
        ] = []
        for atom, pol in lra.active_atoms():
            if not isinstance(atom, App) or len(atom.args) != 2:
                continue
            kind = atom.decl.kind
            if kind not in (DeclKind.LE, DeclKind.GE):
                continue
            coeffs, const_val = lra.atom_linear_form(atom.args[0])
            r_coeffs, r_const = lra.atom_linear_form(atom.args[1])
            for term, c in r_coeffs.items():
                coeffs[term] = coeffs.get(term, Fraction(0)) - c
            c0 = const_val - r_const
            cf = _canon_form(coeffs, c0)
            if cf is None:
                continue
            key, scale = cf
            tlit = TheoryLit(atom, pol)
            is_upper = (kind is DeclKind.LE) if pol else (kind is DeclKind.GE)
            if scale < 0:
                is_upper = not is_upper
            if is_upper:
                upper_forms[key] = tlit
                other = lower_forms.get(key)
                if other is not None:
                    equalities.append((coeffs, c0, (tlit, other)))
            else:
                lower_forms[key] = tlit
                other = upper_forms.get(key)
                if other is not None:
                    equalities.append((coeffs, c0, (other, tlit)))

        subst: dict[Expr, tuple[Expr, Fraction, Fraction]] = {}
        sub_reasons: dict[Expr, tuple[TheoryLit, ...]] = {}
        for coeffs, c0, eq_rsns in equalities:
            items = sorted(
                ((e, c) for e, c in coeffs.items() if c != 0), key=lambda kv: kv[0].id
            )
            if len(items) != 2:
                continue
            (e0, c0_v), (e1, c1_v) = items
            # Eliminate higher-id variable e1 in terms of e0 when free.
            if e1 in subst or e0 in subst:
                continue
            if e1.is_int and not e0.is_int:
                continue
            subst[e1] = (e0, -c0_v / c1_v, -c0 / c1_v)
            sub_reasons[e1] = eq_rsns
        return subst, sub_reasons

    def _analyze_univariate(
        self,
        lra: LRASolver,
        muls: dict[Expr, tuple[Expr, Expr]],
        vals: dict[Expr, Fraction],
        emitted_lemmas: set[Expr],
    ) -> list[NLALemma] | NLAUnknown | None:
        """Analyze univariate polynomial subsystems using exact Sturm isolation."""
        ctx = self._ctx
        subst, sub_reasons = self._collect_linear_substitutions(lra, muls)
        per_var: dict[
            Expr, list[tuple[Poly, DeclKind, bool, tuple[TheoryLit, ...]]]
        ] = {}

        for atom, pol in lra.active_atoms():
            if not isinstance(atom, App) or len(atom.args) != 2:
                continue
            coeffs, const_val = lra.atom_linear_form(atom.args[0])
            r_coeffs, r_const = lra.atom_linear_form(atom.args[1])
            for term, c in r_coeffs.items():
                coeffs[term] = coeffs.get(term, Fraction(0)) - c
            c0 = const_val - r_const

            base_var: Expr | None = None
            has_nl = False
            poly_acc: Poly = _poly_norm([c0])
            atom_reasons: list[TheoryLit] = [TheoryLit(atom, pol)]
            multi_var = False
            for term, c in coeffs.items():
                if c == 0:
                    continue
                if term in muls:
                    has_nl = True
                exp_res = self._expand_univariate(term, muls, subst)
                if exp_res is None:
                    multi_var = True
                    break
                tv, tp = exp_res
                if term in subst:
                    atom_reasons.extend(sub_reasons[term])
                elif term in muls:
                    a_f, b_f = muls[term]
                    if a_f in subst:
                        atom_reasons.extend(sub_reasons[a_f])
                    if b_f in subst:
                        atom_reasons.extend(sub_reasons[b_f])
                if tv is not None:
                    if base_var is None:
                        base_var = tv
                    elif base_var is not tv:
                        multi_var = True
                        break
                scaled = tuple(coeff * c for coeff in tp)
                poly_acc = poly_add(poly_acc, scaled)
            if multi_var or base_var is None or not has_nl:
                continue
            per_var.setdefault(base_var, []).append(
                (poly_acc, atom.decl.kind, pol, tuple(dict.fromkeys(atom_reasons)))
            )

        for var_expr, sys_list in per_var.items():
            # Gather all active reasons contributing to this univariate subsystem.
            reasons = tuple(dict.fromkeys(r for item in sys_list for r in item[3]))

            def _holds(rel_kind: DeclKind, pol: bool, val: Fraction) -> bool:
                match rel_kind:
                    case DeclKind.LT:
                        return (val < 0) if pol else (val >= 0)
                    case DeclKind.LE:
                        return (val <= 0) if pol else (val > 0)
                    case DeclKind.GT:
                        return (val > 0) if pol else (val <= 0)
                    case DeclKind.GE:
                        return (val >= 0) if pol else (val < 0)
                    case _:
                        return True

            def _point_sat(
                pt: Fraction,
                items: list[
                    tuple[Poly, DeclKind, bool, tuple[TheoryLit, ...]]
                ] = sys_list,
            ) -> bool:
                return all(_holds(k, pol, poly_eval(p, pt)) for p, k, pol, _ in items)

            # Isolate roots of every constraint polynomial.
            all_brackets: list[tuple[Fraction, Fraction, bool]] = []
            for p, _kind, _pol, _ in sys_list:
                all_brackets.extend(isolate_real_roots(p))
            refined = all_brackets

            # Collect exact rational partition boundaries and check overlaps.
            pts: set[Fraction] = set()
            for lo, hi, is_rat in refined:
                pts.add(lo)
                pts.add(hi)
                if is_rat:
                    pts.add(lo)
            sorted_pts = sorted(pts) if pts else [Fraction(0)]

            sample_points: list[Fraction] = [sorted_pts[0] - 1, *sorted_pts]
            for i in range(len(sorted_pts) - 1):
                sample_points.append((sorted_pts[i] + sorted_pts[i + 1]) / 2)
            sample_points.append(sorted_pts[-1] + 1)

            if var_expr.is_int:
                int_cands: set[int] = set()
                for sp in sample_points:
                    fl = math.floor(sp)
                    int_cands.update((fl - 1, fl, fl + 1))
                sat_ints = [pt for pt in sorted(int_cands) if _point_sat(Fraction(pt))]
                # Double-check open tails for polynomials with roots inside bounds.
                if not sat_ints and all(
                    not (
                        _holds(k, pol, poly_eval(p, sorted_pts[0] - 1000))
                        and _holds(k, pol, poly_eval(p, sorted_pts[-1] + 1000))
                    )
                    or _point_sat(Fraction(math.floor(sorted_pts[0]) - 1))
                    or _point_sat(Fraction(math.ceil(sorted_pts[-1]) + 1))
                    for p, k, pol, _ in sys_list
                ):
                    self._stats.sturm_lemmas += 1
                    return [NLALemma(ctx.false_expr, reasons)]
                continue

            rat_sat = [sp for sp in sample_points if _point_sat(sp)]
            if rat_sat:
                cur_x = vals[var_expr]
                if not _point_sat(cur_x):
                    # Check if cur_x hits an infeasible point or sits in an open gap.
                    for sp in sorted_pts:
                        if cur_x == sp:
                            rhs = ctx.mk_real_val(sp)
                            lemma_e = ctx.mk_or(
                                ctx.mk_lt(var_expr, rhs), ctx.mk_gt(var_expr, rhs)
                            )
                            if lemma_e not in emitted_lemmas:
                                emitted_lemmas.add(lemma_e)
                                self._stats.sturm_lemmas += 1
                                return [NLALemma(lemma_e, reasons)]
                    # Find first enclosing infeasible open interval around cur_x
                    low_b: Fraction | None = None
                    hi_b: Fraction | None = None
                    for pt in sorted_pts:
                        if pt <= cur_x:
                            low_b = pt
                        elif hi_b is None:
                            hi_b = pt
                    mid_ok_low = low_b is not None and _point_sat(low_b)
                    mid_ok_hi = hi_b is not None and _point_sat(hi_b)
                    if (
                        low_b is not None
                        and hi_b is not None
                        and not _point_sat((low_b + hi_b) / 2)
                    ):
                        lo_e = ctx.mk_real_val(low_b)
                        hi_e = ctx.mk_real_val(hi_b)
                        left = (
                            ctx.mk_le(var_expr, lo_e)
                            if mid_ok_low
                            else ctx.mk_lt(var_expr, lo_e)
                        )
                        right = (
                            ctx.mk_ge(var_expr, hi_e)
                            if mid_ok_hi
                            else ctx.mk_gt(var_expr, hi_e)
                        )
                        lemma_e = ctx.mk_or(left, right)
                        if lemma_e not in emitted_lemmas:
                            emitted_lemmas.add(lemma_e)
                            self._stats.sturm_lemmas += 1
                            return [NLALemma(lemma_e, reasons)]
                continue

            # Zero rational points satisfy the system; test irrational root brackets.
            # An irrational bracket (lo, hi, False) can only satisfy `<= 0` and
            # `>= 0` simultaneously when sign flips strictly across lo vs hi.
            has_irrational_root = False
            for lo, hi, is_rat in refined:
                if is_rat:
                    continue
                # An irrational bracket (lo, hi) is only needed for p == 0
                # (open inequalities have rational sample points unless the
                # bracket overlaps another polynomial's root).
                other_ok = True
                for p, kind, pol, _ in sys_list:
                    plo = poly_eval(p, lo)
                    phi = poly_eval(p, hi)
                    s_lo = _holds(kind, pol, plo)
                    s_hi = _holds(kind, pol, phi)
                    s_mid = _holds(kind, pol, poly_eval(p, (lo + hi) / 2))
                    # Check if p can flip sign across [lo, hi].
                    if not (s_lo or s_hi or s_mid) and (
                        (plo > 0 and phi > 0) or (plo < 0 and phi < 0)
                    ):
                        other_ok = False
                        break
                if other_ok:
                    has_irrational_root = True
                    break

            if not has_irrational_root:
                self._stats.sturm_lemmas += 1
                return [NLALemma(ctx.false_expr, reasons)]
            self._stats.unknowns += 1
            return NLAUnknown("Univariate polynomial requires irrational real root")

        return None

    def check(
        self,
        lra: LRASolver,
        *,
        emitted_lemmas: set[Expr],
    ) -> list[NLALemma] | NLAUnknown | None:
        """Check nonlinear constraints under current ``LRASolver`` assignment."""
        muls = lra.nonlinear_muls
        divs = lra.nonlinear_divs
        if not muls and not divs:
            return None

        self._stats.checks += 1
        all_terms = set(muls) | set(divs)
        for a, b in muls.values():
            all_terms.add(a)
            all_terms.add(b)
        for num, den in divs.values():
            all_terms.add(num)
            all_terms.add(den)
        vals = lra.term_values(all_terms)

        violated_muls = [
            (m, a, b) for m, (a, b) in muls.items() if vals[m] != vals[a] * vals[b]
        ]
        if not violated_muls and all(
            vals[den] == 0 or vals[d] * vals[den] == vals[num]
            for d, (num, den) in divs.items()
        ):
            return None

        if len(emitted_lemmas) >= self._budget.max_lemmas:
            self._stats.unknowns += 1
            return NLAUnknown("NLA lemma budget exhausted")

        # 1. Interval Constraint Propagation (ICP)
        icp_lemmas = self._run_icp(lra, muls, vals, emitted_lemmas)
        if icp_lemmas:
            return icp_lemmas

        # 2. Univariate polynomial / Sturm real-root analysis
        sturm_res = self._analyze_univariate(lra, muls, vals, emitted_lemmas)
        if sturm_res is not None:
            return sturm_res

        if not violated_muls:
            # Division violation is handled via `(den == 0) \/ (d * den == num)`.
            return None

        ctx = self._ctx
        lemmas: list[NLALemma] = []

        def _add_lemma(expr: Expr, category: str) -> None:
            if len(lemmas) + len(emitted_lemmas) >= self._budget.max_lemmas:
                return
            if expr is not ctx.true_expr and expr not in emitted_lemmas:
                emitted_lemmas.add(expr)
                lemmas.append(NLALemma(expr))
                if category == "zero":
                    self._stats.zero_lemmas += 1
                elif category == "sign":
                    self._stats.sign_lemmas += 1
                elif category == "tangent":
                    self._stats.tangent_lemmas += 1

        # 3. Incremental linearization lemmas on violated monomials
        for m, a, b in violated_muls:
            va = vals[a]
            vb = vals[b]
            vm = vals[m]
            zero_a = self._num_val(ctx, a, Fraction(0))
            zero_b = self._num_val(ctx, b, Fraction(0))
            zero_m = self._num_val(ctx, m, Fraction(0))

            # Square non-negativity + tangent: x * x >= 0 and x*x >= 2*va*x - va^2
            if a is b:
                if vm < 0:
                    _add_lemma(ctx.mk_ge(m, zero_m), "sign")
                if vm < va * va and va != 0:
                    c2 = self._num_val(ctx, a, 2 * va)
                    cva2 = self._num_val(ctx, m, va * va)
                    _add_lemma(
                        ctx.mk_ge(m, ctx.mk_sub(ctx.mk_mul(c2, a), cva2)),
                        "tangent",
                    )

            # Zero lemmas active at current point
            if va == 0:
                _add_lemma(
                    ctx.mk_implies(ctx.mk_eq(a, zero_a), ctx.mk_eq(m, zero_m)),
                    "zero",
                )
            if vb == 0 and a is not b:
                _add_lemma(
                    ctx.mk_implies(ctx.mk_eq(b, zero_b), ctx.mk_eq(m, zero_m)),
                    "zero",
                )

            # Sign lemmas for active quadrant
            if va != 0 and vb != 0:
                ca = ctx.mk_gt(a, zero_a) if va > 0 else ctx.mk_lt(a, zero_a)
                cb = ctx.mk_gt(b, zero_b) if vb > 0 else ctx.mk_lt(b, zero_b)
                pos_prod = (va > 0 and vb > 0) or (va < 0 and vb < 0)
                cm = ctx.mk_gt(m, zero_m) if pos_prod else ctx.mk_lt(m, zero_m)
                _add_lemma(ctx.mk_implies(ctx.mk_and(ca, cb), cm), "sign")

            # McCormick envelope when bounded
            vid_a = lra.var_id_or_none(a)
            vid_b = lra.var_id_or_none(b)
            if vid_a is not None and vid_b is not None:
                l_a, lr_a, u_a, ur_a = lra.var_bounds_with_reasons(vid_a)
                l_b, lr_b, u_b, ur_b = lra.var_bounds_with_reasons(vid_b)
                if (
                    l_a is not None
                    and u_a is not None
                    and l_b is not None
                    and u_b is not None
                ):
                    la, ua, lb_v, ub_v = l_a.real, u_a.real, l_b.real, u_b.real
                    mc_rsn = tuple(r for r in (lr_a, ur_a, lr_b, ur_b) if r is not None)
                    for a_bnd, b_bnd, is_lower in (
                        (la, lb_v, True),
                        (ua, ub_v, True),
                        (la, ub_v, False),
                        (ua, lb_v, False),
                    ):
                        # m >= a_bnd * b + b_bnd * a - a_bnd * b_bnd (or <=)
                        rhs = ctx.mk_sub(
                            ctx.mk_add(
                                ctx.mk_mul(self._num_val(ctx, b, a_bnd), b),
                                ctx.mk_mul(self._num_val(ctx, a, b_bnd), a),
                            ),
                            self._num_val(ctx, m, a_bnd * b_bnd),
                        )
                        latom = ctx.mk_ge(m, rhs) if is_lower else ctx.mk_le(m, rhs)
                        if latom not in emitted_lemmas and latom is not ctx.true_expr:
                            emitted_lemmas.add(latom)
                            lemmas.append(NLALemma(latom, mc_rsn))
                            self._stats.tangent_lemmas += 1

            # Exact integer point slice or bilinear tangent plane at (va, vb)
            if a.is_int and va.denominator == 1:
                ca_eq = ctx.mk_eq(a, self._num_val(ctx, a, va))
                prod_b = zero_m if va == 0 else ctx.mk_mul(self._num_val(ctx, b, va), b)
                _add_lemma(
                    ctx.mk_implies(ca_eq, ctx.mk_eq(m, prod_b)),
                    "tangent",
                )
            elif b.is_int and vb.denominator == 1 and a is not b:
                cb_eq = ctx.mk_eq(b, self._num_val(ctx, b, vb))
                prod_a = zero_m if vb == 0 else ctx.mk_mul(self._num_val(ctx, a, vb), a)
                _add_lemma(
                    ctx.mk_implies(cb_eq, ctx.mk_eq(m, prod_a)),
                    "tangent",
                )
            else:
                a_v = self._num_val(ctx, a, va)
                b_v = self._num_val(ctx, b, vb)
                tan_rhs = ctx.mk_sub(
                    ctx.mk_add(
                        ctx.mk_mul(b_v, a),
                        ctx.mk_mul(a_v, b),
                    ),
                    self._num_val(ctx, m, va * vb),
                )
                if vm < va * vb:
                    _add_lemma(
                        ctx.mk_implies(
                            ctx.mk_and(ctx.mk_ge(a, a_v), ctx.mk_ge(b, b_v)),
                            ctx.mk_ge(m, tan_rhs),
                        ),
                        "tangent",
                    )
                    _add_lemma(
                        ctx.mk_implies(
                            ctx.mk_and(ctx.mk_le(a, a_v), ctx.mk_le(b, b_v)),
                            ctx.mk_ge(m, tan_rhs),
                        ),
                        "tangent",
                    )
                else:
                    _add_lemma(
                        ctx.mk_implies(
                            ctx.mk_and(ctx.mk_ge(a, a_v), ctx.mk_le(b, b_v)),
                            ctx.mk_le(m, tan_rhs),
                        ),
                        "tangent",
                    )
                    _add_lemma(
                        ctx.mk_implies(
                            ctx.mk_and(ctx.mk_le(a, a_v), ctx.mk_ge(b, b_v)),
                            ctx.mk_le(m, tan_rhs),
                        ),
                        "tangent",
                    )

        if lemmas:
            return lemmas

        # 4. Bounded branching fallback on violated factors
        if (
            self._splits_used >= self._budget.max_splits
            or len(emitted_lemmas) >= self._budget.max_lemmas
        ):
            self._stats.unknowns += 1
            return NLAUnknown("NLA linearization/branching budget exhausted")

        for _, a, b in violated_muls:
            for factor in (a, b):
                vid = lra.var_id_or_none(factor)
                lb = None
                ub = None
                if vid is not None:
                    l_dr, _, u_dr, _ = lra.var_bounds_with_reasons(vid)
                    lb = l_dr.real if l_dr is not None else None
                    ub = u_dr.real if u_dr is not None else None
                vf = vals[factor]
                if factor.is_int:
                    if lb is not None and ub is not None and lb + 1 <= ub:
                        k = (math.floor(lb) + math.ceil(ub)) // 2
                    elif lb is not None and ub is None:
                        k = max(math.floor(lb), math.floor(vf))
                    elif ub is not None and lb is None:
                        k = min(math.ceil(ub) - 1, math.floor(vf))
                    else:
                        k = math.floor(vf)
                    split = ctx.mk_or(
                        ctx.mk_le(factor, ctx.mk_int_val(k)),
                        ctx.mk_ge(factor, ctx.mk_int_val(k + 1)),
                    )
                else:
                    if lb is not None and ub is not None and lb < ub:
                        lo_i = math.floor(lb) + 1
                        hi_i = math.ceil(ub) - 1
                        if lo_i <= hi_i:
                            mid = Fraction((lo_i + hi_i) // 2)
                        else:
                            mid = (lb + ub) / 2
                    elif lb is None and ub is None:
                        mid = Fraction(0) if vf != 0 else Fraction(1)
                    else:
                        mid = vf + Fraction(1) if ub is None else vf - Fraction(1)
                    rmid = ctx.mk_real_val(mid)
                    split = ctx.mk_or(
                        ctx.mk_le(factor, rmid),
                        ctx.mk_ge(factor, rmid),
                    )
                if split not in emitted_lemmas:
                    emitted_lemmas.add(split)
                    self._splits_used += 1
                    self._stats.branch_splits += 1
                    return [NLALemma(split)]

        self._stats.unknowns += 1
        return NLAUnknown("No applicable nonlinear progress lemma")
