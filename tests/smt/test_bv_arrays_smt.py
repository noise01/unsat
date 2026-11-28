import pytest
import z3

import unsat


def test_qf_bv_dsl_arithmetic_bitops_and_models() -> None:
    unsat.reset_default_context()
    x, y = unsat.BitVecs("x y", 8)
    s = unsat.Solver()

    # x ^ y = 0x5A, x + y = 0x64 (e.g. x=0x15, y=0x4F), pin x < y and hi nibble(x)=1.
    f = unsat.And(
        unsat.Eq(x ^ y, unsat.BitVecVal(0x5A, 8)),
        unsat.Eq(x + y, unsat.BitVecVal(0x64, 8)),
        unsat.ULT(x, y),
        unsat.Eq(unsat.Extract(7, 4, x), unsat.BitVecVal(0x1, 4)),
    )
    s.add(f)
    assert s.check() is unsat.SAT
    m = s.model()
    assert m.eval_bool(f)
    xv, yv = m.eval_bv(x), m.eval_bv(y)
    assert (xv ^ yv) == 0x5A
    assert (xv + yv) & 0xFF == 0x64
    assert xv < yv
    assert (xv >> 4) == 1
    assert m[x] == xv

    # Check carry-incompatible pair x ^ y = 0x5A, x + y = 0x82 is UNSAT.
    s.reset()
    s.add(
        unsat.Eq(x ^ y, unsat.BitVecVal(0x5A, 8)),
        unsat.Eq(x + y, unsat.BitVecVal(0x82, 8)),
    )
    assert s.check() is unsat.UNSAT

    # Bit-vector swap & shift/rotate/concat invariants (UNSAT negation).
    a, b = unsat.BitVecs("a b", 4)
    s.reset()
    a1 = a ^ b
    b1 = a1 ^ b
    a2 = a1 ^ b1
    s.add(unsat.Or(unsat.Not(unsat.Eq(a2, b)), unsat.Not(unsat.Eq(b1, a))))
    assert s.check() is unsat.UNSAT

    # RotateLeft(RotateRight(a, 1), 1) == a
    s.reset()
    s.add(unsat.Not(unsat.Eq(unsat.RotateLeft(unsat.RotateRight(a, 1), 1), a)))
    assert s.check() is unsat.UNSAT

    # Python coercion guards
    with pytest.raises(TypeError):
        _ = bool(x < y)
    with pytest.raises(TypeError):
        _ = x + True
    with pytest.raises(TypeError):
        _ = x + unsat.Int("i")


def test_qf_ax_extensionality_nested_arrays_and_const_arrays() -> None:
    unsat.reset_default_context()
    idx_sort = unsat.DeclareSort("Idx")
    val_sort = unsat.DeclareSort("Val")
    a = unsat.Array("a", idx_sort, val_sort)
    b = unsat.Array("b", idx_sort, val_sort)
    i, j = unsat.Constants("i j", idx_sort)
    v, w = unsat.Constants("v w", val_sort)

    # 1. Extensionality: store(a, i, select(a, i)) == a always holds.
    s = unsat.Solver()
    s.add(unsat.Not(unsat.Eq(unsat.Store(a, i, unsat.Select(a, i)), a)))
    assert s.check() is unsat.UNSAT
    assert s.statistics()["theory_array_ext_lemmas"] >= 0

    # 2. Array swap read-over-write with distinct indices i != j
    s.reset()
    swapped1 = unsat.Store(unsat.Store(a, i, unsat.Select(a, j)), j, unsat.Select(a, i))
    s.add(
        unsat.Distinct(i, j),
        unsat.Not(unsat.Eq(unsat.Select(swapped1, i), unsat.Select(a, j))),
    )
    assert s.check() is unsat.UNSAT

    # 3. Satisfiable QF_AX with extensional disequality a != b and RoW1
    s.reset()
    sat_ax = unsat.And(
        unsat.Distinct(a, b),
        unsat.Eq(unsat.Select(unsat.Store(a, i, v), j), w),
        unsat.Distinct(v, w),
    )
    s.add(sat_ax)
    assert s.check() is unsat.SAT
    m = s.model()
    assert m.eval_bool(sat_ax)

    # 4. Bool-indexed arrays (exhaustive finite domain of size 2)
    p, q = unsat.Bools("p q")
    s.reset()
    s.add(
        unsat.Eq(
            unsat.Store(unsat.Store(unsat.K(unsat.BoolSort(), 0), p, 1), q, 1),
            unsat.K(unsat.BoolSort(), 1),
        )
    )
    assert s.check() is unsat.SAT
    mb = s.model()
    assert mb[p] != mb[q]

    # Same array with identical indices p == q cannot equal K(1) -> UNSAT
    s.add(unsat.Eq(p, q))
    assert s.check() is unsat.UNSAT

    s.reset()
    s.add(
        unsat.Eq(
            unsat.Store(unsat.K(unsat.BoolSort(), 0), p, 1),
            unsat.Store(unsat.K(unsat.BoolSort(), 1), q, 0),
        )
    )
    assert s.check() is unsat.SAT
    mb2 = s.model()
    assert mb2[p] != mb2[q]
    s.add(unsat.Eq(p, q))
    assert s.check() is unsat.UNSAT

    # 5. Nested Array[Int, Array[Int, Int]]
    inner_sort = unsat.ArraySort(unsat.IntSort(), unsat.IntSort())
    mat = unsat.Array("mat", unsat.IntSort(), inner_sort)
    s.reset()
    mat1 = unsat.Store(mat, 0, unsat.Store(unsat.Select(mat, 0), 1, 42))
    f_nested = unsat.And(
        unsat.Eq(unsat.Select(unsat.Select(mat1, 0), 1), unsat.IntVal(42)),
        unsat.Distinct(unsat.Select(mat1, 0), unsat.Select(mat, 0)),
    )
    s.add(f_nested)
    assert s.check() is unsat.SAT
    mn = s.model()
    assert mn.eval_bool(f_nested)
    assert mn.eval_int(unsat.Select(unsat.Select(mat1, 0), 1)) == 42


def test_qf_auflia_and_bv_arrays_mbtc_incremental() -> None:
    unsat.reset_default_context()
    # 1. QF_AUFLIA: Int-indexed arrays + UF + LIA + push/pop + unsat_core
    arr = unsat.Array("arr", unsat.IntSort(), unsat.IntSort())
    f = unsat.Function("f", unsat.IntSort(), unsat.IntSort())
    i, j = unsat.Ints("i j")

    s = unsat.Solver()
    s.add(unsat.Eq(unsat.Store(arr, i + 1, 7), unsat.Store(arr, j, 7)))
    s.push()
    a1 = unsat.Eq(2 * i, unsat.IntVal(4))
    a2 = j >= 3
    a3 = j <= 3
    a4 = unsat.Distinct(f(unsat.Select(unsat.Store(arr, i + 1, 7), j)), f(unsat.IntVal(7)))
    unused = i > -10
    assert s.check(a1, a2, a3, a4, unused) is unsat.UNSAT
    core = s.unsat_core()
    assert unused not in core
    recheck = unsat.Solver()
    recheck.add(*s.assertions(), *core)
    assert recheck.check() is unsat.UNSAT
    s.pop(1)
    assert s.check() is unsat.SAT

    # 2. QF_UFBV + QF_ABV MBTC: x + 1 == 6 with f(x) != f(5), plus BV-indexed array
    unsat.reset_default_context()
    bv = unsat.BitVec("bv", 8)
    bw = unsat.BitVec("bw", 8)
    fbv = unsat.Function("fbv", unsat.BitVecSort(8), unsat.BitVecSort(8))
    barr = unsat.Array("barr", unsat.BitVecSort(8), unsat.BitVecSort(8))

    s2 = unsat.Solver()
    s2.add(
        unsat.Eq(bv + 1, unsat.BitVecVal(6, 8)),
        unsat.Not(unsat.Eq(fbv(bv), fbv(unsat.BitVecVal(5, 8)))),
    )
    assert s2.check() is unsat.UNSAT

    s2.reset()
    f_abv = unsat.And(
        unsat.Eq(bv + 1, unsat.BitVecVal(4, 8)),
        unsat.Eq(bw, unsat.BitVecVal(3, 8)),
        unsat.Eq(unsat.Select(unsat.Store(barr, bv, 0x2A), bw), unsat.BitVecVal(0x2A, 8)),
        unsat.UGT(unsat.Select(barr, bv), 1),
    )
    s2.add(f_abv)
    assert s2.check() is unsat.SAT
    m2 = s2.model()
    assert m2.eval_bool(f_abv)
    assert m2.eval_bv(bv) == 3
    assert m2.eval_bv(unsat.Select(barr, bv)) > 1
    assert "theory_array_checks" in s2.statistics()


def test_qf_aufbv_const_array_mbtc_regression() -> None:
    unsat.reset_default_context()
    bv4 = unsat.BitVecSort(4)
    b0 = unsat.Bool("b0")
    x, y, z = unsat.BitVecs("x y z", 4)
    arr = unsat.Array("A", bv4, bv4)
    pred = unsat.Function("P", bv4, unsat.BoolSort())
    k0 = unsat.K(bv4, unsat.BitVecVal(0, 4))

    f1 = unsat.And(pred(x), unsat.Distinct(y, x, ~x))
    f2 = unsat.And(
        unsat.If(unsat.Eq(k0, arr), b0, unsat.Not(unsat.Eq(x, y)) | (-(~x) <= x)),
        unsat.If(b0, unsat.Eq(x, z), unsat.BoolVal(False)),
    )
    f3 = (z ^ (unsat.Select(unsat.Store(k0, 0, x), x) << 2)) <= y

    solver = unsat.Solver()
    solver.add(f1, f2, f3)
    assert solver.check() is unsat.SAT
    model = solver.model()
    for formula in (f1, f2, f3):
        assert model.eval_bool(formula, model_completion=True) is True


def test_qf_aufbv_store_eclass_member_read_regression() -> None:
    unsat.reset_default_context()
    bv4 = unsat.BitVecSort(4)
    x = unsat.BitVec("x_eclass", bv4)
    z = unsat.BitVec("z_eclass", bv4)
    arr = unsat.Array("A_eclass", bv4, bv4)
    pred = unsat.Function("P_eclass", bv4, unsat.BoolSort())
    zero = unsat.BitVecVal(0, bv4)
    const_arr = unsat.K(bv4, zero)

    f1 = unsat.Not(pred(x))
    f2 = unsat.Eq(unsat.Store(const_arr, x, x), unsat.Store(arr, z, x))
    f3 = pred(z)

    solver = unsat.Solver()
    solver.add(f1, f2, f3)
    assert solver.check() is unsat.SAT
    model = solver.model()
    for formula in (f1, f2, f3):
        assert model.eval_bool(formula, model_completion=True) is True


def test_qf_aufbv_store_eclass_member_read_unsat_regression() -> None:
    unsat.reset_default_context()
    bv4 = unsat.BitVecSort(4)
    x = unsat.BitVec("x_eclass_u", bv4)
    z = unsat.BitVec("z_eclass_u", bv4)
    arr = unsat.Array("A_eclass_u", bv4, bv4)
    b0 = unsat.Bool("b0_eclass_u")
    pred = unsat.Function("P_eclass_u", bv4, unsat.BoolSort())
    zero = unsat.BitVecVal(0, bv4)
    const_arr = unsat.K(bv4, zero)

    f1 = unsat.Not(pred(x))
    f2 = unsat.Eq(unsat.Store(const_arr, x, x), unsat.Store(arr, z, x))
    f3 = pred(z)
    f4 = unsat.And(b0, unsat.Not(unsat.Eq(const_arr, unsat.Store(arr, z, x))))

    solver = unsat.Solver()
    solver.add(f1, f2, f3, f4)
    assert solver.check() is unsat.UNSAT


def test_const_index_store_simplification_soundness_and_models() -> None:
    unsat.reset_default_context()
    bv4 = unsat.BitVecSort(4)
    a_bv = unsat.Array("A_ci", bv4, bv4)
    b_bv = unsat.Array("B_ci", bv4, bv4)
    c_bv = unsat.Array("C_ci", bv4, bv4)
    x, y, z, w, k = unsat.BitVecs("x_ci y_ci z_ci w_ci k_ci", 4)
    c0, c1, c2, c3, c5 = (unsat.BitVecVal(v, 4) for v in (0, 1, 2, 3, 5))

    # 1. Hypothesis failure 1 (invalid model):
    #    (= (const 0) (store A 0 x)) /\ (bvslt y (select A 1))
    f1_sat = [
        unsat.Eq(unsat.K(bv4, c0), unsat.Store(a_bv, c0, x)),
        y < unsat.Select(a_bv, c1),
    ]
    zs = z3.Solver()
    za = z3.Array("A_ci", z3.BitVecSort(4), z3.BitVecSort(4))
    zx, zy = z3.BitVecs("x_ci y_ci", 4)
    z_k0 = z3.K(z3.BitVecSort(4), z3.BitVecVal(0, 4))
    zs.add(
        z_k0 == z3.Store(za, z3.BitVecVal(0, 4), zx),
        zy < z3.Select(za, z3.BitVecVal(1, 4)),
    )
    assert zs.check() == z3.sat
    s = unsat.Solver()
    s.add(*f1_sat)
    assert s.check() is unsat.SAT
    model = s.model()
    for formula in f1_sat:
        assert model.eval_bool(formula, model_completion=True) is True

    # 2. Hypothesis failure 2 (unsound SAT):
    #    (= (const 0) (store A 0 x)) /\ (bvult x (select A 1))
    zs.reset()
    zs.add(
        z_k0 == z3.Store(za, z3.BitVecVal(0, 4), zx),
        z3.ULT(zx, z3.Select(za, z3.BitVecVal(1, 4))),
    )
    assert zs.check() == z3.unsat
    s.reset()
    s.add(
        unsat.Eq(unsat.K(bv4, c0), unsat.Store(a_bv, c0, x)),
        unsat.ULT(x, unsat.Select(a_bv, c1)),
    )
    assert s.check() is unsat.UNSAT

    # 3. Store equality without const_array (QF_ABV and QF_AUFLIA)
    zc = z3.Array("C_ci", z3.BitVecSort(4), z3.BitVecSort(4))
    zs.reset()
    zs.add(
        z3.Store(za, z3.BitVecVal(0, 4), zx) == z3.Store(zc, z3.BitVecVal(2, 4), zy),
        z3.Select(za, z3.BitVecVal(1, 4)) != z3.Select(zc, z3.BitVecVal(1, 4)),
    )
    assert zs.check() == z3.unsat
    s.reset()
    s.add(
        unsat.Eq(unsat.Store(a_bv, c0, x), unsat.Store(c_bv, c2, y)),
        unsat.Distinct(unsat.Select(a_bv, c1), unsat.Select(c_bv, c1)),
    )
    assert s.check() is unsat.UNSAT

    i_arr = unsat.ArraySort(unsat.IntSort(), unsat.IntSort())
    ai = unsat.Array("Ai_ci", unsat.IntSort(), unsat.IntSort())
    ci = unsat.Array("Ci_ci", unsat.IntSort(), unsat.IntSort())
    xi, yi = unsat.Ints("xi_ci yi_ci")
    s.reset()
    s.add(
        unsat.Eq(unsat.Store(ai, 0, xi), unsat.Store(ci, 2, yi)),
        unsat.Distinct(unsat.Select(ai, 1), unsat.Select(ci, 1)),
    )
    assert s.check() is unsat.UNSAT
    assert i_arr is ai.sort

    # 4. Nested Const-stores + intermediate store == const skipped by RoW2-down
    s.reset()
    s.add(
        unsat.Eq(
            unsat.K(bv4, c5),
            unsat.Store(unsat.Store(a_bv, c0, x), c2, y),
        ),
        unsat.Distinct(unsat.Select(a_bv, c1), c5),
    )
    assert s.check() is unsat.UNSAT

    st_inner = unsat.Store(a_bv, c2, y)
    st_outer = unsat.Store(st_inner, c0, x)
    s.reset()
    s.add(
        unsat.Eq(b_bv, st_outer),
        unsat.Eq(st_inner, unsat.K(bv4, c5)),
        unsat.Distinct(unsat.Select(b_bv, c1), c5),
    )
    assert s.check() is unsat.UNSAT

    # 5. Pure nested stores with no select in input (R1, R2, R3)
    s.reset()
    s.add(
        unsat.Eq(unsat.K(bv4, c5), unsat.Store(unsat.Store(a_bv, c0, x), c2, y)),
        unsat.Distinct(x, c5),
    )
    assert s.check() is unsat.UNSAT

    s.reset()
    s.add(
        unsat.Eq(
            unsat.Store(unsat.Store(a_bv, c0, x), c2, y),
            unsat.Store(unsat.Store(c_bv, c0, z), c3, w),
        ),
        unsat.Distinct(x, z),
    )
    assert s.check() is unsat.UNSAT

    s.reset()
    s.add(
        unsat.Eq(
            unsat.Store(unsat.Store(a_bv, c0, x), c2, y),
            unsat.Store(c_bv, c3, w),
        ),
        unsat.Distinct(x, unsat.Select(c_bv, c0)),
    )
    assert s.check() is unsat.UNSAT

    # 6. Mixed Const-store and symbolic-index store (upward & downward)
    s.reset()
    s.add(
        unsat.Eq(unsat.K(bv4, c5), unsat.Store(unsat.Store(a_bv, c0, x), k, y)),
        unsat.Distinct(k, c0),
        unsat.Distinct(x, c5),
    )
    assert s.check() is unsat.UNSAT

    s.reset()
    s.add(
        unsat.Eq(unsat.K(bv4, c5), unsat.Store(unsat.Store(a_bv, c0, x), k, y)),
        unsat.Distinct(k, c1),
        unsat.Distinct(unsat.Select(a_bv, c1), c5),
    )
    assert s.check() is unsat.UNSAT

    # 7. Incremental push/pop + unsat_core minimality across transparent store path
    s.reset()
    a_base = unsat.Eq(unsat.K(bv4, c0), unsat.Store(a_bv, c0, x))
    s.add(a_base)
    s.push()
    a_rel = unsat.ULT(x, unsat.Select(a_bv, c1))
    a_unrel = unsat.Eq(y, c3)
    assert s.check(a_rel, a_unrel) is unsat.UNSAT
    core = s.unsat_core()
    assert a_unrel not in core
    assert set(core) == {a_rel}
    recheck = unsat.Solver()
    recheck.add(a_base, *core)
    assert recheck.check() is unsat.UNSAT
    s.pop(1)
    assert s.check() is unsat.SAT
    m_after_pop = s.model()
    assert m_after_pop.eval_bool(a_base, model_completion=True) is True
