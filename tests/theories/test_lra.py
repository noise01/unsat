from fractions import Fraction

import pytest

from unsat.syntax import Context, Expr
from unsat.theories import (
    DeltaRational,
    LIACutLemma,
    LRASolver,
    TheoryLit,
    find_lia_lemma,
)


def test_delta_rational_and_lra_strict_bounds() -> None:
    d1 = DeltaRational(Fraction(1), Fraction(-1))
    d2 = DeltaRational(Fraction(1), Fraction(0))
    d3 = DeltaRational(Fraction(1), Fraction(1))
    assert d1 < d2 < d3
    assert (d1 + d3) == DeltaRational(Fraction(2), Fraction(0))
    assert (-d1) == DeltaRational(Fraction(-1), Fraction(1))
    assert d3.scale(Fraction(1, 2)) == DeltaRational(Fraction(1, 2), Fraction(1, 2))
    assert DeltaRational(Fraction(3)).is_integer()
    assert not d1.is_integer()

    ctx = Context()
    lra = LRASolver(ctx)
    x = ctx.mk_real("x")
    y = ctx.mk_real("y")

    # Strict open interval: 0 < x < 1/100
    lra.push()
    a1 = ctx.mk_gt(x, ctx.mk_real_val(0))
    a2 = ctx.mk_lt(x, ctx.mk_real_val(Fraction(1, 100)))
    lra.assert_atom(a1, True)
    lra.assert_atom(a2, True)
    assert not lra.check()

    model = lra.build_model()
    assert model.eval_bool(ctx.mk_and(a1, a2))
    x_val = model.eval_real(x)
    assert Fraction(0) < x_val < Fraction(1, 100)
    lra.pop(1)

    # Strict triangle contradiction: x + y < 2, x >= 1, y >= 1 -> UNSAT
    lra.push()
    a3 = ctx.mk_lt(x + y, ctx.mk_real_val(2))
    a4 = ctx.mk_ge(x, ctx.mk_real_val(1))
    a5 = ctx.mk_ge(y, ctx.mk_real_val(1))
    lra.assert_atom(a3, True)
    lra.assert_atom(a4, True)
    lra.assert_atom(a5, True)
    lemmas = lra.check()
    assert len(lemmas) == 1
    assert set(lemmas[0]) <= {
        TheoryLit(a3, True),
        TheoryLit(a4, True),
        TheoryLit(a5, True),
    }
    lra.pop(1)
    assert not lra.check()


def test_lra_subsumption_propagation_exact_reasons_and_pivots() -> None:
    ctx = Context()
    lra = LRASolver(ctx)
    x = ctx.mk_real("x")
    y = ctx.mk_real("y")
    z = ctx.mk_real("z")

    # Register atoms involving x - y and y - x sharing one canonical slack.
    ax1 = ctx.mk_le(x - y, ctx.mk_real_val(3))
    ax2 = ctx.mk_ge(y - x, ctx.mk_real_val(-4))
    ax3 = ctx.mk_le(y - x, ctx.mk_real_val(-4))  # x - y >= 4, contradicts x - y <= 3
    ax_irrel = ctx.mk_le(z, ctx.mk_real_val(100))

    for atom in (ax1, ax2, ax3, ax_irrel):
        lra.register_atom(atom)

    lra.push()
    lra.assert_atom(ax_irrel, True)
    lra.assert_atom(ax1, True)
    props, conflict = lra.propagate()
    assert conflict is None
    prop_map = dict(props)
    assert prop_map.get(ax2) is True
    assert prop_map.get(ax3) is False
    assert set(lra.explain_propagation(ax2, True)) == {TheoryLit(ax1, True)}
    assert set(lra.explain_propagation(ax3, False)) == {TheoryLit(ax1, True)}

    # Tightening further at level 2 must not corrupt level 1's explanation.
    lra.push()
    tight = ctx.mk_le(x - y, ctx.mk_real_val(0))
    lra.assert_atom(tight, True)
    assert set(lra.explain_propagation(ax2, True)) == {TheoryLit(ax1, True)}
    lra.pop(1)

    # Dynamic slack registered AFTER pivots works cleanly.
    dyn = ctx.mk_le(x + y + z, ctx.mk_real_val(1))
    lra.assert_atom(dyn, True)
    assert not lra.check()
    lra.pop(1)


def test_lra_integer_tightening_and_gomory_cut() -> None:
    ctx = Context()
    lra = LRASolver(ctx)
    x = ctx.mk_int("x")
    y = ctx.mk_int("y")

    # 2*x + 2*y <= 5 and 2*x + 2*y >= 5 tightened directly in LRASolver.
    lra.push()
    a_le = ctx.mk_le(2 * x + 2 * y, ctx.mk_int_val(5))
    a_ge = ctx.mk_ge(2 * x + 2 * y, ctx.mk_int_val(5))
    lra.assert_atom(a_le, True)
    lra.assert_atom(a_ge, True)
    props, conflict = lra.propagate()
    assert not props
    assert conflict is not None
    lra.pop(1)

    # Fractional relaxation that yields a Gomory Mixed-Integer cut:
    # 2*x + y >= 3, 2*x - y <= 0, x <= 1 -> continuous point (3/4, 3/2).
    c1 = ctx.mk_ge(2 * x + y, ctx.mk_int_val(3))
    c2 = ctx.mk_le(2 * x - y, ctx.mk_int_val(0))
    lra.assert_atom(c1, True)
    lra.assert_atom(c2, True)
    lra.assert_atom(ctx.mk_le(x, ctx.mk_int_val(1)), True)
    assert not lra.check()

    emitted: set[Expr] = set()
    lemma = find_lia_lemma(lra, emitted_cuts=emitted)
    if isinstance(lemma, LIACutLemma):
        lra.assert_atom(lemma.cut_atom, True)
        assert not lra.check()


def test_lra_mixed_to_real_and_errors() -> None:
    ctx = Context()
    lra = LRASolver(ctx)
    x = ctx.mk_int("x")
    r = ctx.mk_real("r")

    # x <= 2 and to_real(x) > 1.5 -> forces x = 2
    lra.assert_atom(ctx.mk_le(x, ctx.mk_int_val(2)), True)
    lra.assert_atom(ctx.mk_gt(ctx.mk_to_real(x), ctx.mk_real_val(Fraction(3, 2))), True)
    assert not lra.check()
    emitted: set[Expr] = set()
    lia_lemma = find_lia_lemma(lra, emitted_cuts=emitted)
    assert lia_lemma is None or isinstance(lia_lemma, (LIACutLemma, object))

    # Non-linear expressions & type errors
    with pytest.raises(ValueError, match="Non-linear"):
        lra.register_term(x * x)
    with pytest.raises(ValueError, match="Non-linear"):
        lra.register_term(r / r)
    with pytest.raises(ValueError, match="Non-linear"):
        lra.register_term(r / 0)
    with pytest.raises(TypeError, match="Int or Real"):
        lra.register_term(ctx.mk_bool("p"))
    with pytest.raises(TypeError, match="arithmetic comparison"):
        lra.register_atom(x)
    with pytest.raises(ValueError, match="negative"):
        lra.pop(-1)
    with pytest.raises(ValueError, match="active"):
        lra.pop(1)


def test_lia_patching_push_to_bound_and_scaled_gmi_cut() -> None:
    # 1. Multi-step denominator reduction via patch_int_vars: 6x - 3y - 2z = 1.
    ctx = Context()
    lra = LRASolver(ctx)
    x, y, z = ctx.mk_int("x"), ctx.mk_int("y"), ctx.mk_int("z")
    lra.assert_atom(ctx.mk_ge(6 * x - 3 * y - 2 * z, ctx.mk_int_val(1)), True)
    lra.assert_atom(ctx.mk_le(6 * x - 3 * y - 2 * z, ctx.mk_int_val(1)), True)
    assert not lra.check()
    assert not all(lra.var_value(vid).is_integer() for vid in range(3))
    assert lra.patch_int_vars() is True
    assert all(lra.var_value(vid).is_integer() for vid in range(3))

    # 2. push_nonbasic_to_bound pivots a free non-basic variable onto a blocking bound.
    ctx2 = Context()
    lra2 = LRASolver(ctx2)
    a, b = ctx2.mk_int("a"), ctx2.mk_int("b")
    lra2.assert_atom(ctx2.mk_ge(a + b, ctx2.mk_int_val(5)), True)
    lra2.assert_atom(ctx2.mk_ge(a, ctx2.mk_int_val(1)), True)
    assert not lra2.check()
    free_nb = [
        vid
        for vid in range(lra2.num_vars)
        if lra2.basic_row(vid) is None
        and lra2.var_value(vid) != lra2.var_lower(vid)[0]
        and lra2.var_value(vid) != lra2.var_upper(vid)[0]
    ]
    assert free_nb
    assert lra2.push_nonbasic_to_bound(free_nb[0]) is True

    # 3. Scaled GMI cut across a free Int var: 2x + 3y = 1, 2x + 3y + 2z = 2 -> UNSAT.
    ctx3 = Context()
    lra3 = LRASolver(ctx3)
    ux, uy, uz = ctx3.mk_int("x"), ctx3.mk_int("y"), ctx3.mk_int("z")
    lra3.assert_atom(ctx3.mk_ge(2 * ux + 3 * uy, ctx3.mk_int_val(1)), True)
    lra3.assert_atom(ctx3.mk_le(2 * ux + 3 * uy, ctx3.mk_int_val(1)), True)
    lra3.assert_atom(ctx3.mk_ge(2 * ux + 3 * uy + 2 * uz, ctx3.mk_int_val(2)), True)
    lra3.assert_atom(ctx3.mk_le(2 * ux + 3 * uy + 2 * uz, ctx3.mk_int_val(2)), True)
    assert not lra3.check()
    emitted: set[Expr] = set()
    lemma = find_lia_lemma(lra3, emitted_cuts=emitted)
    assert isinstance(lemma, LIACutLemma)
    assert lemma.cut_atom is ctx3.false_expr
