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
