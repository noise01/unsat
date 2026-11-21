import pytest

from unsat.syntax import Context
from unsat.theories import EUFSolver, TheoryLit


def test_euf_transitivity_congruence_and_propagation() -> None:
    ctx = Context()
    euf = EUFSolver(ctx)
    s_sort = ctx.mk_uninterpreted_sort("S")
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    g = ctx.mk_decl("g", (s_sort, s_sort), s_sort)
    h = ctx.mk_decl("h", (s_sort,), s_sort)

    a = ctx.mk_const("a", s_sort)
    b = ctx.mk_const("b", s_sort)
    c = ctx.mk_const("c", s_sort)

    eq_ab = ctx.mk_eq(a, b)
    eq_bc = ctx.mk_eq(b, c)
    eq_ac = ctx.mk_eq(a, c)
    fa = f(a)
    fc = f(c)
    eq_fa_fc = ctx.mk_eq(fa, fc)
    eq_f_h_distinct = ctx.mk_eq(fa, h(c))
    gac = g(a, c)
    gbc = g(b, a)
    eq_g = ctx.mk_eq(gac, gbc)

    for eq_atom in (eq_ab, eq_bc, eq_ac, eq_fa_fc, eq_f_h_distinct, eq_g):
        euf.register_eq(eq_atom)

    euf.assert_atom(eq_ab, True)
    euf.assert_atom(eq_bc, True)
    props, conflict = euf.propagate()
    assert conflict is None

    prop_map = dict(props)
    assert prop_map.get(eq_ac) is True
    assert prop_map.get(eq_fa_fc) is True
    assert prop_map.get(eq_g) is True
    assert eq_f_h_distinct not in prop_map
    assert not euf.are_equal(fa, h(c))

    reason_ac = set(euf.explain_propagation(eq_ac, True))
    assert reason_ac == {TheoryLit(eq_ab, True), TheoryLit(eq_bc, True)}

    reason_fa = set(euf.explain_propagation(eq_fa_fc, True))
    assert reason_fa == {TheoryLit(eq_ab, True), TheoryLit(eq_bc, True)}


def test_euf_minimal_explanation_and_nested_congruence() -> None:
    ctx = Context()
    euf = EUFSolver(ctx)
    s_sort = ctx.mk_uninterpreted_sort("S")
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    g = ctx.mk_decl("g", (s_sort,), s_sort)

    a, b, c, d, e = (ctx.mk_const(name, s_sort) for name in ("a", "b", "c", "d", "e"))
    eq_ab = ctx.mk_eq(a, b)
    eq_bc = ctx.mk_eq(b, c)
    eq_de = ctx.mk_eq(d, e)  # Irrelevant side equivalence.
    eq_fa_c = ctx.mk_eq(f(a), c)
    eq_fc_a = ctx.mk_eq(f(c), a)
    eq_gf = ctx.mk_eq(g(f(f(a))), g(a))

    euf.assert_atom(eq_de, True)
    euf.assert_atom(eq_ab, True)
    euf.assert_atom(eq_bc, True)
    euf.assert_atom(eq_fa_c, True)
    euf.assert_atom(eq_fc_a, True)
    euf.assert_atom(eq_gf, False)

    props, conflict = euf.propagate()
    assert not props
    assert conflict is not None
    assert TheoryLit(eq_de, True) not in conflict
    assert TheoryLit(eq_gf, False) in conflict
    assert len(conflict) <= 5


def test_euf_predicate_and_const_conflicts() -> None:
    ctx = Context()
    euf = EUFSolver(ctx)
    s_sort = ctx.mk_uninterpreted_sort("S")
    pred = ctx.mk_decl("P", (s_sort,), ctx.bool_sort)
    a = ctx.mk_const("a", s_sort)
    b = ctx.mk_const("b", s_sort)
    pa = pred(a)
    pb = pred(b)
    eq_ab = ctx.mk_eq(a, b)

    euf.register_bool_term(pa)
    euf.register_bool_term(pb)
    euf.push()
    euf.assert_atom(pa, True)
    euf.assert_atom(eq_ab, True)
    props, conflict = euf.propagate()
    assert conflict is None
    assert (pb, True) in props
    reason_pb = set(euf.explain_propagation(pb, True))
    assert reason_pb == {TheoryLit(pa, True), TheoryLit(eq_ab, True)}
    euf.pop(1)

    # Opposite polarity after pop triggers conflict on congruence.
    euf.push()
    euf.assert_atom(pa, True)
    euf.assert_atom(pb, False)
    euf.assert_atom(eq_ab, True)
    _, conflict = euf.propagate()
    assert conflict is not None
    assert set(conflict) == {
        TheoryLit(pa, True),
        TheoryLit(pb, False),
        TheoryLit(eq_ab, True),
    }
    euf.pop(1)
    assert not euf.check()


def test_euf_push_pop_and_model_building() -> None:
    ctx = Context()
    euf = EUFSolver(ctx)
    s_sort = ctx.mk_uninterpreted_sort("S")
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    a, b, c = (ctx.mk_const(name, s_sort) for name in ("a", "b", "c"))
    v0 = ctx.mk_domain_val(s_sort, 0)

    euf.assert_atom(ctx.mk_eq(a, v0), True)
    euf.push()
    euf.assert_atom(ctx.mk_eq(a, b), True)
    euf.assert_atom(ctx.mk_eq(f(a), c), True)
    euf.register_term(f(b))
    assert not euf.check()
    assert euf.are_equal(f(b), c)
    euf.pop(1)

    assert not euf.are_equal(a, b)
    euf.assert_atom(ctx.mk_eq(a, b), False)
    euf.register_term(f(a))
    euf.register_term(f(c))
    assert not euf.check()

    model = euf.build_model()
    assert model[a] == v0
    assert model[b] != v0
    assert model.eval_bool(ctx.mk_and(ctx.mk_eq(a, v0), ctx.mk_not(ctx.mk_eq(a, b))))

    interp = model.func_interp(f)
    assert interp(v0) == model.eval(f(a))


def test_euf_validation_errors() -> None:
    ctx1 = Context()
    ctx2 = Context()
    euf = EUFSolver(ctx1)

    p = ctx1.mk_bool("p")
    q = ctx1.mk_bool("q")
    s_sort = ctx1.mk_uninterpreted_sort("S")
    s_other = ctx2.mk_uninterpreted_sort("S")

    with pytest.raises(ValueError, match="different Context"):
        euf.register_term(ctx2.mk_const("x", s_other))
    with pytest.raises(TypeError, match="Eq expression"):
        euf.register_eq(p)
    with pytest.raises(TypeError, match="non-Bool Eq"):
        euf.register_eq(ctx1.mk_eq(p, q))
    with pytest.raises(TypeError, match="Bool expression"):
        euf.register_bool_term(ctx1.mk_const("a", s_sort))
    with pytest.raises(ValueError, match="negative"):
        euf.pop(-1)
    with pytest.raises(ValueError, match="active"):
        euf.pop(1)
