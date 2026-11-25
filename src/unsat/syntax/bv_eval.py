"""Bit-vector constant arithmetic and rational formatting helpers."""

from fractions import Fraction


def _format_pos_fraction(frac: Fraction) -> str:
    if frac.denominator == 1:
        return f"{frac.numerator}.0"
    return f"(/ {frac.numerator}.0 {frac.denominator}.0)"


def _format_real_fraction(frac: Fraction) -> str:
    if frac < 0:
        return f"(- {_format_pos_fraction(-frac)})"
    return _format_pos_fraction(frac)


def _bv_mask(width: int) -> int:
    return (1 << width) - 1


def _bv_to_signed(val: int, width: int) -> int:
    sign_bit = 1 << (width - 1)
    return val - (1 << width) if (val & sign_bit) else val


def _bv_udiv(a: int, b: int, mask: int) -> int:
    return mask if b == 0 else a // b


def _bv_urem(a: int, b: int) -> int:
    return a if b == 0 else a % b


def _bv_sdiv(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    neg_a = (-a) & mask
    neg_b = (-b) & mask
    if not ma and not mb:
        return _bv_udiv(a, b, mask)
    if ma and not mb:
        return (-_bv_udiv(neg_a, b, mask)) & mask
    if not ma and mb:
        return (-_bv_udiv(a, neg_b, mask)) & mask
    return _bv_udiv(neg_a, neg_b, mask)


def _bv_srem(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    neg_a = (-a) & mask
    neg_b = (-b) & mask
    if not ma and not mb:
        return _bv_urem(a, b)
    if ma and not mb:
        return (-_bv_urem(neg_a, b)) & mask
    if not ma and mb:
        return _bv_urem(a, neg_b)
    return (-_bv_urem(neg_a, neg_b)) & mask


def _bv_smod(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    abs_a = (-a) & mask if ma else a
    abs_b = (-b) & mask if mb else b
    u = _bv_urem(abs_a, abs_b)
    if u == 0:
        return 0
    if not ma and not mb:
        return u
    if ma and not mb:
        return ((-u) + b) & mask
    if not ma and mb:
        return (u + b) & mask
    return (-u) & mask
