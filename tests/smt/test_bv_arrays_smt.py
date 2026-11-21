import pytest

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
    a4 = unsat.Distinct(
        f(unsat.Select(unsat.Store(arr, i + 1, 7), j)), f(unsat.IntVal(7))
    )
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
        unsat.Eq(
            unsat.Select(unsat.Store(barr, bv, 0x2A), bw), unsat.BitVecVal(0x2A, 8)
        ),
        unsat.UGT(unsat.Select(barr, bv), 1),
    )
    s2.add(f_abv)
    assert s2.check() is unsat.SAT
    m2 = s2.model()
    assert m2.eval_bool(f_abv)
    assert m2.eval_bv(bv) == 3
    assert m2.eval_bv(unsat.Select(barr, bv)) > 1
    assert "theory_array_checks" in s2.statistics()
