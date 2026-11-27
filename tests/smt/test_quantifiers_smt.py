import z3

import unsat


def test_quantifiers_uf_ematching_and_finite_models() -> None:
    unsat.reset_default_context()
    s_sort = unsat.DeclareSort("U")
    x, y, z = unsat.Constants("x y z", s_sort)
    a, b, c, d = unsat.Constants("a b c d", s_sort)
    f = unsat.Function("f", s_sort, s_sort)
    g = unsat.Function("g", s_sort, s_sort)
    p = unsat.Function("P", s_sort, unsat.BoolSort())
    r = unsat.Function("R", s_sort, s_sort, unsat.BoolSort())

    # 1. UF symmetry axiom + E-matching modulo EUF
    solver = unsat.Solver()
    sym = unsat.ForAll([x, y], unsat.Implies(r(x, y), r(y, x)))
    solver.add(sym, r(a, b), unsat.Not(r(b, a)))
    assert solver.check() is unsat.UNSAT

    solver.reset()
    ax = unsat.ForAll([x], p(f(g(x))), patterns=[f(g(x))])
    solver.add(ax, unsat.Eq(g(a), c), unsat.Eq(f(c), d), unsat.Not(p(d)))
    assert solver.check() is unsat.UNSAT
    assert solver.statistics()["quantifier_ematch_rounds"] >= 1

    # 2. Finite cardinality axiom: <= 2 elements -> UNSAT with 3 distinct, SAT with 2.
    card2 = unsat.ForAll(
        [x, y, z],
        unsat.Or(unsat.Eq(x, y), unsat.Eq(x, z), unsat.Eq(y, z)),
    )
    solver.reset()
    solver.add(card2, unsat.Distinct(a, b, c))
    assert solver.check() is unsat.UNSAT

    solver.reset()
    solver.add(card2, unsat.Distinct(a, b), p(a))
    assert solver.check() is unsat.SAT
    m = solver.model()
    assert m.eval_bool(card2) is True
    assert m.eval_bool(unsat.Distinct(a, b)) is True

    # Cross-check with Z3
    zs_sort = z3.DeclareSort("U")
    zx, zy, zz = z3.Consts("x y z", zs_sort)
    za, zb = z3.Consts("a b", zs_sort)
    zs = z3.Solver()
    zs.add(
        z3.ForAll([zx, zy, zz], z3.Or(zx == zy, zx == zz, zy == zz)),
        z3.Distinct(za, zb),
    )
    assert zs.check() == z3.sat


def test_quantifiers_arithmetic_arrays_and_bv() -> None:
    unsat.reset_default_context()
    ix, iy = unsat.Ints("ix iy")
    rx = unsat.Real("rx")
    s = unsat.Solver()

    # Quantified LIA SAT & UNSAT
    q_pos = unsat.ForAll(ix, unsat.Implies(ix > 0, ix + 1 > 1))
    s.add(q_pos)
    assert s.check() is unsat.SAT
    assert s.statistics()["quantifier_mbqi_verified"] >= 1

    s.reset()
    s.add(unsat.ForAll(ix, unsat.Implies(ix > 5, ix > 10)))
    assert s.check() is unsat.UNSAT

    # Skolemized Exists-ForAll LRA/LIA: exists x. forall y. y >= 0 => y >= x -> SAT
    s.reset()
    ef = unsat.Exists(ix, unsat.ForAll(iy, unsat.Implies(iy >= 0, iy >= ix)))
    s.add(ef)
    assert s.check() is unsat.SAT

    # ForAll x. (x > 0 => Exists y. (y > x /\ y < x + 1)) -> UNSAT over Int!
    s.reset()
    no_between = unsat.ForAll(
        ix, unsat.Implies(ix > 0, unsat.Exists(iy, unsat.And(iy > ix, iy < ix + 1)))
    )
    s.add(no_between)
    assert s.check() is unsat.UNSAT

    # LRA SAT: forall rx. rx + 1 > rx
    s.reset()
    s.add(unsat.ForAll(rx, rx + 1 > rx))
    assert s.check() is unsat.SAT
    zrx = z3.Real("rx")
    zs = z3.Solver()
    zs.add(z3.ForAll([zrx], zrx + 1 > zrx))
    assert zs.check() == z3.sat

    # Array + Int quantifier (AUFLIA): forall i. 0 <= i < 3 => arr[i] >= 0 -> UNSAT
    arr = unsat.Array("arr", unsat.IntSort(), unsat.IntSort())
    i = unsat.Int("i")
    s.reset()
    s.add(
        unsat.ForAll(
            i,
            unsat.Implies(unsat.And(i >= 0, i < 3), unsat.Select(arr, i) >= 0),
        ),
        unsat.Eq(unsat.Select(arr, 1), unsat.IntVal(-1)),
    )
    assert s.check() is unsat.UNSAT

    # BitVec quantifier: forall bv4. (bv & 0) == 0 /\ exists bv4. bv + 1 == 0 -> SAT
    bv = unsat.BitVec("bv", 4)
    s.reset()
    q_bv = unsat.ForAll(bv, unsat.Eq(bv & 0, unsat.BitVecVal(0, 4)))
    s.add(q_bv, unsat.Exists(bv, unsat.Eq(bv + 1, unsat.BitVecVal(0, 4))))
    assert s.check() is unsat.SAT
    mbv = s.model()
    assert mbv.eval_bool(q_bv) is True


def test_quantifiers_incremental_push_pop_cores_and_unknown_budget() -> None:
    unsat.reset_default_context()
    x = unsat.Int("x")
    f = unsat.Function("f", unsat.IntSort(), unsat.IntSort())
    p = unsat.Function("P", unsat.IntSort(), unsat.BoolSort())
    b = unsat.Bool("b")

    # 1. Incremental push/pop retracts quantified assertions & unknown loops safely
    s = unsat.Solver()
    s.push()
    s.add(unsat.ForAll(x, x > 0))
    assert s.check() is unsat.UNSAT
    s.pop(1)
    assert s.check() is unsat.SAT

    # Popped unverifiable quantifier must not trigger after pop.
    s.push()
    s.add(unsat.ForAll(x, unsat.Eq(f(x), x + 1)))
    assert s.check() is unsat.UNKNOWN
    s.pop(1)
    assert s.check() is unsat.SAT

    # 2. Disjunction with falsified quantifier & assumption unsat core
    s.reset()
    q_all_p = unsat.ForAll(x, p(x))
    a_neg = unsat.Not(p(unsat.IntVal(0)))
    a_unused = unsat.Eq(x, unsat.IntVal(7))
    s.add(unsat.Or(b, q_all_p))
    assert s.check(a_neg) is unsat.SAT
    assert s.model().eval_bool(b) is True

    assert s.check(q_all_p, a_neg, a_unused) is unsat.UNSAT
    core = s.unsat_core()
    assert a_unused not in core
    recheck = unsat.Solver()
    recheck.add(*core)
    assert recheck.check() is unsat.UNSAT

    # 3. Budget-bounded UNKNOWN vs ground-derived UNSAT
    limited = unsat.Solver(max_quantifier_rounds=0)
    limited.add(unsat.ForAll(x, p(x)))
    assert limited.check() is unsat.UNKNOWN
    assert limited.statistics()["quantifier_budget_exhausted"] >= 1

    # Ground contradiction alongside quantifier remains UNSAT even with 0 rounds.
    limited.add(unsat.Not(b), b)
    assert limited.check() is unsat.UNSAT

    # Unbounded piecewise axiom returns UNKNOWN, while adding conflict gives UNSAT.
    s_unk = unsat.Solver(max_quantifier_rounds=3)
    s_unk.add(unsat.ForAll(x, unsat.Eq(f(x), x + 1)))
    assert s_unk.check() is unsat.UNKNOWN
    s_unk.add(unsat.Eq(f(unsat.IntVal(0)), unsat.IntVal(2)))
    assert s_unk.check() is unsat.UNSAT

    # Nested quantifier spawned inside a pushed scope must retract on pop.
    y = unsat.Int("y")
    s_nested = unsat.Solver()
    s_nested.add(p(unsat.IntVal(1)))
    s_nested.push()
    inner_q = unsat.ForAll(y, unsat.Eq(f(y), y + 1))
    outer_q = unsat.ForAll(x, unsat.If(p(x), inner_q, unsat.BoolVal(True)))
    s_nested.add(outer_q)
    assert s_nested.check() is unsat.UNKNOWN
    s_nested.pop(1)
    assert s_nested.check() is unsat.SAT


def test_ematch_check_wide_budget_partial_truncation_and_disjunction() -> None:
    unsat.reset_default_context()
    u = unsat.DeclareSort("U")
    x = unsat.Constant("x", u)
    a, b = unsat.Constants("a b", u)
    f = unsat.Function("f", u, u)
    p = unsat.Function("P", u, unsat.BoolSort())
    q = unsat.Function("Q", u, unsat.BoolSort())
    flag = unsat.Bool("flag")

    # 1. Check-wide match budget is shared across rounds (not reset per round).
    s_chain = unsat.Solver()
    s_chain.add(
        unsat.ForAll([x], unsat.Implies(p(x), p(f(x))), patterns=[p(x)]),
        p(a),
    )
    assert (
        s_chain.check(max_quantifier_rounds=10, max_quantifier_matches=2)
        is unsat.UNKNOWN
    )
    assert s_chain.statistics()["quantifier_ematch_candidates"] <= 2

    # 2. Partial round-1 truncation still allows ground UNSAT when contradicted,
    #    and stays conservative UNKNOWN (not SAT) without a contradiction.
    rule = unsat.ForAll([x], unsat.Implies(p(x), q(x)), patterns=[p(x)])
    s_partial_unsat = unsat.Solver()
    s_partial_unsat.add(rule, p(a), p(b), unsat.Not(q(a)))
    assert s_partial_unsat.check(max_quantifier_matches=1) is unsat.UNSAT

    s_partial_unk = unsat.Solver()
    s_partial_unk.add(rule, p(a), p(b))
    assert s_partial_unk.check(max_quantifier_matches=1) is unsat.UNKNOWN

    # 3. Disjunction-disabled quantifier remains SAT even with a tight match budget.
    s_disj = unsat.Solver()
    s_disj.add(unsat.Or(flag, rule), p(a), unsat.Not(q(a)))
    assert s_disj.check(max_quantifier_matches=1) is unsat.SAT
    assert s_disj.model().eval_bool(flag) is True
