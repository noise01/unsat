"""Unit and lazy-solving integration tests for ``unsat.theories.bv``."""

import unsat
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context
from unsat.tactics import BitBlastTactic
from unsat.theories import BVBlastRequest, BVDomain, BVSolver, TheoryLit


def test_bv_domain_tightening_and_values() -> None:
    d_top = BVDomain.top(8)
    assert d_top.umin == 0
    assert d_top.umax == 255
    assert d_top.smin == -128
    assert d_top.smax == 127

    # Cross-tightening signed positive range with unsigned range & known prefix bits.
    d1 = BVDomain(width=8, zeros=0, ones=0, umin=120, umax=200, smin=-10, smax=50).normalize()
    # [120, 200] & [-10, 50]: positive segment [120, 127] contradicts smax=50,
    # forcing negative segment [246, 255] which exceeds umax=200 -> empty.
    assert d1 is None

    # Disjoint known bits vs bounds:
    d2 = BVDomain(width=4, zeros=0b0001, ones=0b0010, umin=0, umax=15, smin=-8, smax=7).normalize()
    assert d2 is not None
    assert d2.umin == 2
    assert d2.umax == 14
    for cand in range(16):
        if d2.contains(cand):
            assert (cand & 0b0011) == 0b0010
    picked = d2.pick_value()
    assert d2.contains(picked)

    # Signed-positive range [10, 14] in 8 bits tightens MSB zero bit and umin/umax.
    d3 = BVDomain(width=8, zeros=0, ones=0, umin=0, umax=255, smin=10, smax=14).normalize()
    assert d3 is not None
    assert (d3.zeros & 0x80) != 0
    assert d3.umin == 10
    assert d3.umax == 14


def test_bv_solver_propagation_explain_and_incremental_pop() -> None:
    ctx = Context()
    solver = BVSolver(ctx)
    x = ctx.mk_bv("x", 8)
    y = ctx.mk_bv("y", 8)
    z = ctx.mk_bv("z", 8)

    masked = ctx.mk_bv_and(x, ctx.mk_bv_val(0x0F, 8))
    ext = ctx.mk_extract(3, 0, x)
    a_ge = ctx.mk_bv_uge(x, ctx.mk_bv_val(0xF5, 8))
    a_eq_masked = ctx.mk_eq(masked, ctx.mk_bv_val(0x03, 8))
    a_bad_ext = ctx.mk_eq(ext, ctx.mk_bv_val(0x04, 4))
    a_sub = ctx.mk_bv_ule(x, ctx.mk_bv_val(0xFA, 8))
    a_sub2 = ctx.mk_bv_uge(y, ctx.mk_bv_val(0xFC, 8))
    a_gt_z = ctx.mk_bv_ugt(x, z)
    a_z_min = ctx.mk_bv_uge(z, ctx.mk_bv_val(0xFB, 8))

    for atom in (a_ge, a_eq_masked, a_bad_ext, a_sub, a_sub2, a_gt_z, a_z_min):
        solver.register_atom(atom)

    # 1. Online conflict across masked low nibble vs extract
    solver.push()
    solver.assert_atom(a_eq_masked, True)
    solver.assert_atom(a_bad_ext, True)
    props, conflict = solver.propagate()
    assert props == ()
    assert conflict is not None
    assert set(conflict) == {TheoryLit(a_eq_masked, True), TheoryLit(a_bad_ext, True)}
    assert list(solver.explain_conflict()) == list(conflict)
    solver.pop(1)

    # 2. Subsumption propagation: x <= 0xFA and z >= 0xFB entails not(x > z)
    solver.push()
    solver.assert_atom(a_sub, True)
    solver.assert_atom(a_z_min, True)
    props2, conflict2 = solver.propagate()
    assert conflict2 is None
    assert (a_gt_z, False) in props2
    reasons = set(solver.explain_propagation(a_gt_z, False))
    assert reasons == {TheoryLit(a_sub, True), TheoryLit(a_z_min, True)}
    solver.pop(1)

    # 3. Satisfiable word-level check synthesizes model without blast request
    solver.push()
    a_eq_yz = ctx.mk_eq(y, z)
    solver.register_atom(a_eq_yz)
    solver.assert_atom(a_sub2, True)
    solver.assert_atom(a_eq_yz, True)
    assert solver.check() is None
    conc = solver.concrete_values()
    assert conc[y.decl] == conc[z.decl]
    assert conc[y.decl] >= 0xFC
    solver.pop(1)

    # 4. Non-linear atom needing blast triggers BVBlastRequest when check disagrees
    mul_eq = ctx.mk_eq(x * y, ctx.mk_bv_val(15, 8))
    solver.register_atom(mul_eq)
    solver.assert_atom(mul_eq, True)
    res = solver.check()
    assert isinstance(res, BVBlastRequest)
    assert mul_eq in res.atoms


def test_lazy_bv_avoids_upfront_blasting_and_solves_mixed_theories() -> None:
    unsat.reset_default_context()
    # 1. Wide 64-bit QF_BV word-level UNSAT and SAT solved with 0 blasted atoms.
    x = unsat.BitVec("x64", 64)
    y = unsat.BitVec("y64", 64)

    s_unsat = unsat.Solver()
    s_unsat.add(unsat.ULT(x, 10), unsat.UGT(x, 20))
    assert s_unsat.check() is unsat.UNSAT
    assert s_unsat.statistics()["theory_bv_blasted_atoms"] == 0
    assert s_unsat._solver._sat._trail.num_vars < 20

    s_sat = unsat.Solver()
    f_wide = unsat.And(
        unsat.Eq(unsat.Extract(7, 0, unsat.Concat(x, unsat.BitVecVal(0x2A, 8))), 0x2A),
        unsat.UGE(x, 100),
        unsat.ULE(x, 105),
        unsat.Eq(y, x),
    )
    s_sat.add(f_wide)
    assert s_sat.check() is unsat.SAT
    assert s_sat.statistics()["theory_bv_blasted_atoms"] == 0
    assert s_sat._solver._sat._trail.num_vars < 50
    m = s_sat.model()
    assert m.eval_bool(f_wide) is True
    assert 100 <= m.eval_bv(x) <= 105
    assert m.eval_bv(y) == m.eval_bv(x)

    # Contrast with eager BitBlastTactic upfront variable blow-up.
    tactic_res = BitBlastTactic().apply([f_wide])
    eager_solver = SMTSolver(unsat.default_context())
    eager_solver.add(*tactic_res.formulas)
    assert eager_solver._sat._trail.num_vars > s_sat._solver._sat._trail.num_vars

    # 2. Mixed QF_UFBV solved at word level + EUF congruence with 0 blasted atoms.
    unsat.reset_default_context()
    a = unsat.BitVec("a", 32)
    b = unsat.BitVec("b", 32)
    f = unsat.Function("f32", unsat.BitVecSort(32), unsat.BitVecSort(32))
    p = unsat.Function("p32", unsat.BitVecSort(32), unsat.BoolSort())

    s_ufbv = unsat.Solver()
    s_ufbv.add(
        unsat.UGE(a, 5),
        unsat.ULE(a, 5),
        unsat.Eq(b, 5),
        p(a),
        unsat.Not(p(b)),
    )
    assert s_ufbv.check() is unsat.UNSAT
    assert s_ufbv.statistics()["theory_bv_blasted_atoms"] == 0

    # 3. Partial lazy blasting + push/pop + unsat_core in mixed QF_AUFBV:
    # Unrelated 32-bit bvmul constraint need not explode during core extraction.
    arr = unsat.Array("arr32", unsat.BitVecSort(32), unsat.BitVecSort(32))
    k1 = unsat.BitVec("k1", 32)
    k2 = unsat.BitVec("k2", 32)
    k3 = unsat.BitVec("k3", 32)
    v1 = unsat.BitVec("v1", 32)

    s_mix = unsat.Solver()
    s_mix.add(unsat.Eq(unsat.Select(unsat.Store(arr, k1, 0xCAFEBABE), k2), v1))
    s_mix.push()
    a1 = unsat.Eq(k1, k2)
    a2 = unsat.Not(unsat.Eq(f(v1), f(unsat.BitVecVal(0xCAFEBABE, 32))))
    unused = unsat.Eq(k3 * k1, unsat.BitVecVal(0x12345678, 32))
    assert s_mix.check(a1, a2, unused) is unsat.UNSAT
    core = s_mix.unsat_core()
    assert unused not in core
    assert set(core) == {a1, a2}
    assert s_mix.statistics()["theory_bv_blasted_atoms"] == 0
    s_mix.pop(1)

    # Partial escalation: solving SAT with unused asserted blasts only needed atoms.
    assert s_mix.check(a1, unused) is unsat.SAT
    m_mix = s_mix.model()
    assert m_mix.eval_bv(v1) == 0xCAFEBABE
    assert m_mix.eval_bool(unused) is True
    assert isinstance(SMTSolver(unsat.default_context()).statistics()["theory_bv_checks"], int)
    assert s_mix.check() is unsat.SAT
    assert SMTSolver(unsat.default_context()).check() is SolveResult.SAT
