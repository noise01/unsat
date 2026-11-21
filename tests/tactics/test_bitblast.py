import pytest
import z3

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, Context, DeclKind
from unsat.tactics import (
    BitBlaster,
    BitBlastTactic,
    BVSimplifyTactic,
    Then,
    bitblast,
    bv_simplify,
)


def _z3_bv_val(
    ctx: Context, term_fn, z3_fn, a: int, b: int | None = None, w: int = 4
) -> None:
    if b is None:
        u_expr = term_fn(ctx.mk_bv_val(a, w))
        z_expr = z3.simplify(z3_fn(z3.BitVecVal(a, w)))
    else:
        u_expr = term_fn(ctx.mk_bv_val(a, w), ctx.mk_bv_val(b, w))
        z_expr = z3.simplify(z3_fn(z3.BitVecVal(a, w), z3.BitVecVal(b, w)))

    solver = SMTSolver(ctx)
    blaster = BitBlaster(ctx)
    if u_expr.is_bool:
        expected = z3.is_true(z_expr)
        assert u_expr is ctx.mk_bool_val(expected)
        # Verify gate-level circuit evaluation on symbolic leaf variables too.
        x = ctx.mk_bv("x", w)
        solver.add(ctx.mk_eq(x, ctx.mk_bv_val(a, w)))
        if b is None:
            sym_expr = term_fn(x)
        else:
            y = ctx.mk_bv("y", w)
            solver.add(ctx.mk_eq(y, ctx.mk_bv_val(b, w)))
            sym_expr = term_fn(x, y)
        solver.add(sym_expr if expected else ctx.mk_not(sym_expr))
        assert solver.check() is SolveResult.SAT
        return

    expected_int = z_expr.as_long()
    assert u_expr is ctx.mk_bv_val(expected_int, u_expr.bv_size)
    # Also verify non-constant-folded gate blasting via symbolic variables.
    x = ctx.mk_bv("x", w)
    solver.add(ctx.mk_eq(x, ctx.mk_bv_val(a, w)))
    if b is None:
        sym_expr = term_fn(x)
    else:
        y = ctx.mk_bv("y", w)
        solver.add(ctx.mk_eq(y, ctx.mk_bv_val(b, w)))
        sym_expr = term_fn(x, y)
    # Use a fresh BitBlaster directly so bv_simplify doesn't rewrite away the op.
    blasted_eq = blaster.blast_eq(
        sym_expr, ctx.mk_bv_val(expected_int, sym_expr.bv_size)
    )
    solver.add(blasted_eq)
    assert solver.check() is SolveResult.SAT


def test_bv_simplify_identities_and_inversions() -> None:
    ctx = Context()
    x = ctx.mk_bv("x", 8)
    y = ctx.mk_bv("y", 8)

    # Neutral & absorbing identities
    assert bv_simplify(ctx.mk_bv_add(x, ctx.mk_bv_val(0, 8))) is x
    assert bv_simplify(ctx.mk_bv_sub(x, x)) is ctx.mk_bv_val(0, 8)
    assert bv_simplify(ctx.mk_bv_and(x, ctx.mk_bv_not(x))) is ctx.mk_bv_val(0, 8)
    assert bv_simplify(ctx.mk_bv_or(x, ctx.mk_bv_not(x))) is ctx.mk_bv_val(0xFF, 8)
    assert bv_simplify(ctx.mk_bv_xor(x, ctx.mk_bv_val(0xFF, 8))) is ctx.mk_bv_not(x)
    assert bv_simplify(ctx.mk_bv_udiv(x, ctx.mk_bv_val(1, 8))) is x
    assert bv_simplify(ctx.mk_bv_udiv(x, ctx.mk_bv_val(0, 8))) is ctx.mk_bv_val(0xFF, 8)
    assert bv_simplify(ctx.mk_bv_urem(x, ctx.mk_bv_val(1, 8))) is ctx.mk_bv_val(0, 8)
    assert bv_simplify(ctx.mk_bv_urem(x, ctx.mk_bv_val(0, 8))) is x
    assert bv_simplify(ctx.mk_bv_shl(x, ctx.mk_bv_val(8, 8))) is ctx.mk_bv_val(0, 8)
    assert bv_simplify(ctx.mk_bv_ashr(x, ctx.mk_bv_val(0, 8))) is x

    # Extract & Concat coalescing
    cat = ctx.mk_concat(x, y)
    assert bv_simplify(ctx.mk_extract(15, 8, cat)) is x
    assert bv_simplify(ctx.mk_extract(7, 0, cat)) is y
    assert bv_simplify(
        ctx.mk_extract(11, 4, ctx.mk_extract(15, 2, cat))
    ) is bv_simplify(ctx.mk_extract(13, 6, cat))
    assert (
        bv_simplify(ctx.mk_concat(ctx.mk_extract(7, 4, x), ctx.mk_extract(3, 0, x)))
        is x
    )
    zext = ctx.mk_zero_ext(4, x)
    assert bv_simplify(ctx.mk_extract(11, 8, zext)) is ctx.mk_bv_val(0, 4)
    assert bv_simplify(ctx.mk_extract(5, 2, zext)) is ctx.mk_extract(5, 2, x)

    # Comparison tautologies
    assert bv_simplify(ctx.mk_bv_ult(x, ctx.mk_bv_val(0, 8))) is ctx.false_expr
    assert bv_simplify(ctx.mk_bv_ule(x, ctx.mk_bv_val(0xFF, 8))) is ctx.true_expr
    assert bv_simplify(ctx.mk_bv_slt(x, ctx.mk_bv_val(0x80, 8))) is ctx.false_expr
    assert bv_simplify(ctx.mk_bv_sle(x, ctx.mk_bv_val(0x7F, 8))) is ctx.true_expr

    # Equality inversions: (~(x + 3)) == 10  <=>  x + 3 == ~10  <=>  x == (~10 - 3)
    inv_eq = ctx.mk_eq(
        ctx.mk_bv_not(ctx.mk_bv_add(x, ctx.mk_bv_val(3, 8))),
        ctx.mk_bv_val(10, 8),
    )
    expected_rhs = ctx.mk_bv_val(((~10) - 3) & 0xFF, 8)
    assert bv_simplify(inv_eq) is ctx.mk_eq(x, expected_rhs)
    assert (
        bv_simplify(ctx.mk_eq(ctx.mk_zero_ext(4, x), ctx.mk_bv_val(0x105, 12)))
        is ctx.false_expr
    )

    # Tactic short-circuiting
    tac = BVSimplifyTactic()
    res = tac.apply((ctx.mk_eq(x, x), ctx.mk_bv_ugt(x, ctx.mk_bv_val(0xFF, 8))))
    assert res.formulas == (ctx.false_expr,)


def test_bitblast_tactic_standalone_roundtrip_and_converter() -> None:
    ctx = Context()
    x = ctx.mk_bv("x", 6)
    y = ctx.mk_bv("y", 6)
    p = ctx.mk_bool("p")

    formula = ctx.mk_and(
        ctx.mk_eq(x + y, ctx.mk_bv_val(19, 6)),
        ctx.mk_ite(p, ctx.mk_bv_ult(x, y), ctx.mk_bv_uge(x, y)),
        p,
        ctx.mk_bv_sgt(y, ctx.mk_bv_val(0, 6)),
    )

    pipeline = Then(BVSimplifyTactic(), BitBlastTactic())
    tactic_res = pipeline.apply((formula,))
    assert len(tactic_res.formulas) == 1
    blasted = tactic_res.formulas[0]
    assert blasted.is_bool

    solver = SMTSolver(ctx)
    solver.add(*tactic_res.formulas)
    assert solver.check() is SolveResult.SAT
    raw_model = solver.model()
    full_model = tactic_res.converter.convert(raw_model)

    assert full_model.eval_bool(formula) is True
    assert (full_model.eval_bv(x) + full_model.eval_bv(y)) % 64 == 19
    assert full_model.eval_bv(x) < full_model.eval_bv(y)
    # Single-formula helper sanity
    single_res = bitblast(ctx.mk_eq(x & y, ctx.mk_bv_val(4, 6)))
    assert len(single_res.formulas) == 1


def test_bv_semantics_exhaustive_4bit_and_1bit_vs_z3() -> None:
    ctx = Context()
    sample_vals = (0, 1, 2, 7, 8, 9, 13, 15)
    for a in sample_vals:
        _z3_bv_val(ctx, lambda v: ~v, lambda z: ~z, a)
        _z3_bv_val(ctx, lambda v: -v, lambda z: -z, a)
        _z3_bv_val(ctx, lambda v: ctx.mk_zero_ext(3, v), lambda z: z3.ZeroExt(3, z), a)
        _z3_bv_val(ctx, lambda v: ctx.mk_sign_ext(3, v), lambda z: z3.SignExt(3, z), a)
        _z3_bv_val(
            ctx, lambda v: ctx.mk_rotate_left(1, v), lambda z: z3.RotateLeft(z, 1), a
        )
        _z3_bv_val(
            ctx, lambda v: ctx.mk_rotate_right(3, v), lambda z: z3.RotateRight(z, 3), a
        )
        _z3_bv_val(
            ctx, lambda v: ctx.mk_repeat(2, v), lambda z: z3.RepeatBitVec(2, z), a
        )
        _z3_bv_val(
            ctx, lambda v: ctx.mk_extract(2, 1, v), lambda z: z3.Extract(2, 1, z), a
        )

        for b in sample_vals:
            _z3_bv_val(ctx, lambda u, v: u + v, lambda x, y: x + y, a, b)
            _z3_bv_val(ctx, lambda u, v: u - v, lambda x, y: x - y, a, b)
            _z3_bv_val(ctx, lambda u, v: u * v, lambda x, y: x * y, a, b)
            _z3_bv_val(ctx, ctx.mk_bv_udiv, z3.UDiv, a, b)
            _z3_bv_val(ctx, ctx.mk_bv_urem, z3.URem, a, b)
            _z3_bv_val(ctx, lambda u, v: u / v, lambda x, y: x / y, a, b)
            _z3_bv_val(ctx, ctx.mk_bv_srem, z3.SRem, a, b)
            _z3_bv_val(ctx, lambda u, v: u % v, lambda x, y: x % y, a, b)
            _z3_bv_val(ctx, lambda u, v: u << v, lambda x, y: x << y, a, b)
            _z3_bv_val(ctx, ctx.mk_bv_lshr, z3.LShR, a, b)
            _z3_bv_val(ctx, lambda u, v: u >> v, lambda x, y: x >> y, a, b)
            _z3_bv_val(ctx, ctx.mk_bv_ult, z3.ULT, a, b)
            _z3_bv_val(ctx, ctx.mk_bv_ule, z3.ULE, a, b)
            _z3_bv_val(ctx, lambda u, v: u < v, lambda x, y: x < y, a, b)
            _z3_bv_val(ctx, lambda u, v: u <= v, lambda x, y: x <= y, a, b)
            _z3_bv_val(ctx, ctx.mk_concat, lambda x, y: z3.Concat(x, y), a, b)

    # 1-bit edge cases (shift >= 1, div/rem/sdiv/smod by 0 and -1)
    for a in (0, 1):
        for b in (0, 1):
            _z3_bv_val(ctx, ctx.mk_bv_udiv, z3.UDiv, a, b, w=1)
            _z3_bv_val(ctx, lambda u, v: u / v, lambda x, y: x / y, a, b, w=1)
            _z3_bv_val(ctx, lambda u, v: u % v, lambda x, y: x % y, a, b, w=1)
            _z3_bv_val(ctx, lambda u, v: u << v, lambda x, y: x << y, a, b, w=1)
            _z3_bv_val(ctx, ctx.mk_bv_lshr, z3.LShR, a, b, w=1)
            _z3_bv_val(ctx, lambda u, v: u >> v, lambda x, y: x >> y, a, b, w=1)

    with pytest.raises(ValueError, match="BitVec width"):
        ctx.mk_bv_sort(0)
    with pytest.raises(ValueError, match="Invalid extract"):
        ctx.mk_extract(8, 0, ctx.mk_bv("v", 8))
    z0 = ctx.mk_zero_ext(0, ctx.mk_bv("v", 8))
    assert isinstance(z0, App)
    assert z0.decl.kind is DeclKind.UNINTERPRETED
