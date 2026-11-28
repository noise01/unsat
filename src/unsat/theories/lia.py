"""Linear Integer Arithmetic (LIA) solver layer via Gomory cuts & Branch-and-Bound.

Operates on top of a continuous ``LRASolver`` relaxation without touching ``sat``
or ``smt``. Produces either Gomory Mixed-Integer (GMI) cut lemmas or
exact branch-and-bound split pairs whenever an original ``Int`` variable takes
a non-integral relaxation value.

Depends on: ``syntax``, ``model``, ``theories.base``, ``theories.lra``.
"""

import math
from dataclasses import dataclass
from fractions import Fraction

from unsat.syntax import Expr
from unsat.theories.base import TheoryLit
from unsat.theories.lra import DeltaRational, LRASolver


@dataclass(frozen=True, slots=True)
class LIACutLemma:
    """Conditional Gomory cut ``(reasons => cut_atom)`` (conflict if ``false``)."""

    reasons: tuple[TheoryLit, ...]
    cut_atom: Expr


@dataclass(frozen=True, slots=True)
class LIASplitLemma:
    r"""Branch-and-bound disjunction ``(x <= k) \\/ (x >= k + 1)``."""

    le_atom: Expr
    ge_atom: Expr
    prefer_ge: bool = False


def _floor_delta_rational(val: DeltaRational) -> int:
    if val.real.denominator == 1:
        base = val.real.numerator
        return base - 1 if val.delta < 0 else base
    return math.floor(val.real)


def _frac_part(x: Fraction) -> Fraction:
    return x - math.floor(x)


def _build_ge_atom(lra: LRASolver, orig_coeffs: dict[int, Fraction], rhs: Fraction) -> Expr | None:
    """Build ``sum w_k x_k >= rhs`` if non-empty, clearing denominators."""
    ctx = lra.ctx
    if not orig_coeffs:
        return ctx.true_expr if rhs <= 0 else ctx.false_expr

    denoms = [c.denominator for c in orig_coeffs.values()]
    denoms.append(rhs.denominator)
    lcm_den = math.lcm(*denoms)

    all_int = all(lra.var_is_int(v) for v in orig_coeffs)
    if all_int:
        int_coeffs = {v: int(c * lcm_den) for v, c in orig_coeffs.items()}
        int_rhs = int(rhs * lcm_den)
        g = math.gcd(*(abs(val) for val in int_coeffs.values()), abs(int_rhs))
        terms: list[Expr] = []
        for vid in sorted(int_coeffs):
            c_int = int_coeffs[vid] // g
            var_e = lra.var_expr(vid)
            assert var_e is not None
            terms.append(var_e if c_int == 1 else ctx.mk_mul(ctx.mk_int_val(c_int), var_e))
        lhs_expr = terms[0] if len(terms) == 1 else ctx.mk_add(*terms)
        return ctx.mk_ge(lhs_expr, ctx.mk_int_val(int_rhs // g))

    real_terms: list[Expr] = []
    for vid in sorted(orig_coeffs):
        scaled_c = orig_coeffs[vid] * lcm_den
        var_e = lra.var_expr(vid)
        assert var_e is not None
        real_var = ctx.mk_to_real(var_e) if var_e.is_int else var_e
        real_terms.append(real_var if scaled_c == 1 else ctx.mk_mul(ctx.mk_real_val(scaled_c), real_var))
    lhs_real = real_terms[0] if len(real_terms) == 1 else ctx.mk_add(*real_terms)
    return ctx.mk_ge(lhs_real, ctx.mk_real_val(rhs * lcm_den))


def _try_gomory_cut(
    lra: LRASolver,
    basic_vid: int,
    *,
    emitted_cuts: set[Expr],
    max_cut_coeff: int,
) -> LIACutLemma | None:
    row = lra.basic_row(basic_vid)
    if row is None:
        return None
    val_basic = lra.var_value(basic_vid)
    if val_basic.delta != 0 or val_basic.real.denominator == 1:
        return None

    at_bound: list[
        tuple[
            int,
            Fraction,
            bool,
            Fraction,
            TheoryLit,
            TheoryLit | None,
            TheoryLit | None,
            bool,
        ]
    ] = []
    free_int_denoms: list[int] = []

    for j_nb, a_ij in row.items():
        if lra.var_is_int(j_nb) and a_ij.denominator == 1:
            # Pure-integer non-basic term with integer coeff vanishes mod 1 cleanly.
            continue

        val_j = lra.var_value(j_nb)
        if val_j.delta != 0:
            return None

        lb, l_reason = lra.var_lower(j_nb)
        ub, u_reason = lra.var_upper(j_nb)
        at_lb = lb is not None and lb == val_j and lb.delta == 0
        at_ub = ub is not None and ub == val_j and ub.delta == 0
        if at_lb or at_ub:
            if at_lb:
                assert lb is not None
                assert l_reason is not None
                use_lower = True
                bound_real = lb.real
                active_reason = l_reason
            else:
                assert ub is not None
                assert u_reason is not None
                use_lower = False
                bound_real = ub.real
                active_reason = u_reason
            is_fixed = at_lb and at_ub
            at_bound.append(
                (
                    j_nb,
                    a_ij,
                    use_lower,
                    bound_real,
                    active_reason,
                    l_reason,
                    u_reason,
                    is_fixed,
                )
            )
        elif lra.var_is_int(j_nb) and val_j.is_integer():
            free_int_denoms.append(a_ij.denominator)
        else:
            return None

    scale_d = math.lcm(*free_int_denoms) if free_int_denoms else 1
    if scale_d > max_cut_coeff:
        return None
    scaled_val = val_basic.real * scale_d
    if scaled_val.denominator == 1:
        return None

    active_at_bound = [
        entry for entry in at_bound if not (lra.var_is_int(entry[0]) and (entry[1] * scale_d).denominator == 1)
    ]

    if all(entry[7] for entry in active_at_bound):
        fixed_reasons: list[TheoryLit] = []
        seen_fixed: set[TheoryLit] = set()
        for _, _, _, _, _, l_reason, u_reason, _ in active_at_bound:
            for r in (l_reason, u_reason):
                if r is not None and r not in seen_fixed:
                    seen_fixed.add(r)
                    fixed_reasons.append(r)
        lra.stats.gomory_cuts += 1
        return LIACutLemma(tuple(fixed_reasons), lra.ctx.false_expr)

    f0 = _frac_part(scaled_val)
    orig_lhs: dict[int, Fraction] = {}
    orig_rhs = Fraction(1)
    reasons: list[TheoryLit] = []
    seen_reasons: set[TheoryLit] = set()

    for j_nb, a_ij, use_lower, bound_real, active_reason, _, _, _ in active_at_bound:
        if active_reason not in seen_reasons:
            seen_reasons.add(active_reason)
            reasons.append(active_reason)

        # Standard form z + sum c_j y_j = f_0, c_j = -a_ij (lower) or +a_ij (upper).
        scaled_a = a_ij * scale_d
        alpha_j = scaled_a if use_lower else -scaled_a
        c_j = -alpha_j

        if lra.var_is_int(j_nb):
            f_j = _frac_part(c_j)
            if f_j == 0:
                continue
            g_j = f_j / f0 if f_j <= f0 else (Fraction(1) - f_j) / (Fraction(1) - f0)
        elif c_j > 0:
            g_j = c_j / f0
        elif c_j < 0:
            g_j = -c_j / (Fraction(1) - f0)
        else:
            continue

        # y_j = x_j - bound_real (lower) or bound_real - x_j (upper)
        y_sign = Fraction(1) if use_lower else Fraction(-1)
        weight = g_j * y_sign
        orig_rhs += g_j * y_sign * bound_real
        for orig_v, orig_c in lra.var_orig_coeffs(j_nb).items():
            upd = orig_lhs.get(orig_v, Fraction(0)) + weight * orig_c
            if upd == 0:
                orig_lhs.pop(orig_v, None)
            else:
                orig_lhs[orig_v] = upd

    cut_atom = _build_ge_atom(lra, orig_lhs, orig_rhs)
    if cut_atom is None or cut_atom is lra.ctx.true_expr:
        return None
    if cut_atom is lra.ctx.false_expr:
        lra.stats.gomory_cuts += 1
        return LIACutLemma(tuple(reasons), cut_atom)
    if cut_atom in emitted_cuts:
        return None

    # Guard coefficient blowup across deep GMI chains.
    denoms = [c.denominator for c in orig_lhs.values()]
    denoms.append(orig_rhs.denominator)
    scale = math.lcm(*denoms)
    if max((abs(int(c * scale)) for c in orig_lhs.values()), default=0) > max_cut_coeff:
        return None
    if abs(int(orig_rhs * scale)) > max_cut_coeff:
        return None

    lra.stats.gomory_cuts += 1
    return LIACutLemma(tuple(reasons), cut_atom)


def _fractional_orig_ints(lra: LRASolver) -> list[tuple[int, Expr, DeltaRational]]:
    fractional_orig: list[tuple[int, Expr, DeltaRational]] = []
    for vid in range(lra.num_vars):
        if not lra.var_is_original(vid) or not lra.var_is_int(vid):
            continue
        val = lra.var_value(vid)
        if not val.is_integer():
            expr = lra.var_expr(vid)
            assert expr is not None
            fractional_orig.append((vid, expr, val))
    return fractional_orig


def _split_key(lra: LRASolver, vid: int, val: DeltaRational) -> tuple[int, Fraction, Fraction, int]:
    lb, _ = lra.var_lower(vid)
    ub, _ = lra.var_upper(vid)
    if lb is not None and ub is not None:
        return (0, ub.real - lb.real, abs(val.real), vid)
    if lb is not None or ub is not None:
        return (1, Fraction(0), abs(val.real), vid)
    return (2, Fraction(0), abs(val.real), vid)


def find_lia_lemma(
    lra: LRASolver,
    *,
    emitted_cuts: set[Expr],
    max_cut_coeff: int = 10**6,
) -> LIACutLemma | LIASplitLemma | None:
    """Return a Gomory cut or branch-and-bound split for fractional ``Int`` vars."""
    fractional_orig = _fractional_orig_ints(lra)
    if not fractional_orig:
        return None

    lra.patch_int_vars()
    fractional_orig = _fractional_orig_ints(lra)
    if not fractional_orig:
        return None

    for vid, _, _ in fractional_orig:
        cut = _try_gomory_cut(lra, vid, emitted_cuts=emitted_cuts, max_cut_coeff=max_cut_coeff)
        if cut is not None:
            return cut

    # Vertex tightening: push free non-basic vars to blocking bounds to unlock cuts.
    for _ in range(lra.num_vars):
        pushed = False
        for vid, _, _ in fractional_orig:
            row = lra.basic_row(vid)
            if row is None:
                continue
            for j_nb in sorted(row):
                a_ij = row[j_nb]
                if lra.var_is_int(j_nb) and a_ij.denominator == 1:
                    continue
                if lra.push_nonbasic_to_bound(j_nb):
                    pushed = True
                    break
            if pushed:
                break
        if not pushed:
            break

        lra.patch_int_vars()
        fractional_orig = _fractional_orig_ints(lra)
        if not fractional_orig:
            return None

        for vid, _, _ in fractional_orig:
            cut = _try_gomory_cut(lra, vid, emitted_cuts=emitted_cuts, max_cut_coeff=max_cut_coeff)
            if cut is not None:
                return cut

    # Fallback: Smart Branch-and-Bound split on best candidate fractional Int var.
    vid, expr, val = min(fractional_orig, key=lambda item: _split_key(lra, item[0], item[2]))
    k = _floor_delta_rational(val)
    lb, _ = lra.var_lower(vid)
    ub, _ = lra.var_upper(vid)
    if lb is not None and ub is None:
        prefer_ge = False
    elif ub is not None and lb is None:
        prefer_ge = True
    elif lb is None and ub is None:
        prefer_ge = val.real < 0
    else:
        prefer_ge = (val.real - k) > Fraction(1, 2)

    ctx = lra.ctx
    lra.stats.branch_splits += 1
    return LIASplitLemma(
        ctx.mk_le(expr, ctx.mk_int_val(k)),
        ctx.mk_ge(expr, ctx.mk_int_val(k + 1)),
        prefer_ge=prefer_ge,
    )
