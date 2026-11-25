"""Z3 differential property tests for QF_BV, QF_AX, QF_AUFLIA, QF_UFBV, QF_ABV."""

from typing import NamedTuple

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl, Sort, SortKind
from unsat.tactics import BitBlastTactic, BVSimplifyTactic, Then


def _as_bv(ref: z3.ExprRef) -> z3.BitVecRef:
    assert isinstance(ref, z3.BitVecRef)
    return ref


def _as_arith(ref: z3.ExprRef) -> z3.ArithRef:
    assert isinstance(ref, z3.ArithRef)
    return ref


def _as_arr(ref: z3.ExprRef) -> z3.ArrayRef:
    assert isinstance(ref, z3.ArrayRef)
    return ref


class _BVSig(NamedTuple):
    ctx: Context
    width: int
    bool_vars: tuple[App, ...]
    bv_vars: tuple[App, ...]
    arr_var: App
    uf_bv: FuncDecl
    pred_bv: FuncDecl
    z3_consts: dict[FuncDecl, z3.ExprRef]
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef]


class _AXSig(NamedTuple):
    ctx: Context
    with_lia: bool
    bool_vars: tuple[App, ...]
    idx_vars: tuple[App, ...]
    val_vars: tuple[App, ...]
    arr_vars: tuple[App, ...]
    uf_fn: FuncDecl | None
    z3_consts: dict[FuncDecl, z3.ExprRef]
    z3_sorts: dict[object, z3.SortRef]
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef]


def _make_bv_sig(width: int) -> _BVSig:
    ctx = Context()
    bv_sort = ctx.mk_bv_sort(width)
    arr_sort = ctx.mk_array_sort(bv_sort, bv_sort)
    z_bv = z3.BitVecSort(width)
    z_arr = z3.ArraySort(z_bv, z_bv)

    bool_vars = tuple(ctx.mk_bool(n) for n in ("b0", "b1"))
    bv_vars = tuple(ctx.mk_bv(n, width) for n in ("x", "y", "z"))
    arr_var = ctx.mk_const("A", arr_sort)
    uf_bv = ctx.mk_decl("f", (bv_sort,), bv_sort)
    pred_bv = ctx.mk_decl("P", (bv_sort,), ctx.bool_sort)

    z3_consts: dict[FuncDecl, z3.ExprRef] = {
        bv.decl: z3.Bool(bv.name) for bv in bool_vars
    }
    for v in bv_vars:
        z3_consts[v.decl] = z3.BitVec(v.name, width)
    z3_consts[arr_var.decl] = z3.Const("A", z_arr)

    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] = {
        uf_bv: z3.Function("f", z_bv, z_bv),
        pred_bv: z3.Function("P", z_bv, z3.BoolSort()),
    }
    return _BVSig(
        ctx=ctx,
        width=width,
        bool_vars=bool_vars,
        bv_vars=bv_vars,
        arr_var=arr_var,
        uf_bv=uf_bv,
        pred_bv=pred_bv,
        z3_consts=z3_consts,
        z3_funcs=z3_funcs,
    )


def _make_ax_sig(*, with_lia: bool) -> _AXSig:
    ctx = Context()
    if with_lia:
        idx_sort = ctx.int_sort
        val_sort = ctx.int_sort
        z_idx: z3.SortRef = z3.IntSort()
        z_val: z3.SortRef = z3.IntSort()
        uf_fn: FuncDecl | None = ctx.mk_decl("h", (val_sort,), val_sort)
    else:
        idx_sort = ctx.mk_uninterpreted_sort("Idx")
        val_sort = ctx.mk_uninterpreted_sort("Val")
        z_idx = z3.DeclareSort("Idx")
        z_val = z3.DeclareSort("Val")
        uf_fn = None

    arr_sort = ctx.mk_array_sort(idx_sort, val_sort)
    z_arr = z3.ArraySort(z_idx, z_val)

    bool_vars = tuple(ctx.mk_bool(n) for n in ("b0", "b1"))
    idx_vars = tuple(ctx.mk_const(n, idx_sort) for n in ("i", "j", "k"))
    val_vars = (
        idx_vars
        if with_lia
        else tuple(ctx.mk_const(n, val_sort) for n in ("u", "v", "w"))
    )
    arr_vars = tuple(ctx.mk_const(n, arr_sort) for n in ("A", "B"))

    z3_consts: dict[FuncDecl, z3.ExprRef] = {
        bv.decl: z3.Bool(bv.name) for bv in bool_vars
    }
    for iv in idx_vars:
        z3_consts[iv.decl] = z3.Int(iv.name) if with_lia else z3.Const(iv.name, z_idx)
    if not with_lia:
        for vv in val_vars:
            z3_consts[vv.decl] = z3.Const(vv.name, z_val)
    for av in arr_vars:
        z3_consts[av.decl] = z3.Const(av.name, z_arr)

    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] = {}
    if uf_fn is not None:
        z3_funcs[uf_fn] = z3.Function("h", z_val, z_val)

    return _AXSig(
        ctx=ctx,
        with_lia=with_lia,
        bool_vars=bool_vars,
        idx_vars=idx_vars,
        val_vars=val_vars,
        arr_vars=arr_vars,
        uf_fn=uf_fn,
        z3_consts=z3_consts,
        z3_sorts={idx_sort: z_idx, val_sort: z_val},
        z3_funcs=z3_funcs,
    )


def _to_z3_sort(sort: Sort, z3_sorts: dict[object, z3.SortRef]) -> z3.SortRef:
    existing = z3_sorts.get(sort)
    if existing is not None:
        return existing
    if sort.kind is SortKind.BOOL:
        return z3.BoolSort()
    if sort.kind is SortKind.INT:
        return z3.IntSort()
    if sort.kind is SortKind.REAL:
        return z3.RealSort()
    if sort.kind is SortKind.BITVEC:
        return z3.BitVecSort(sort.size)
    if sort.kind is SortKind.ARRAY:
        return z3.ArraySort(
            _to_z3_sort(sort.index_sort, z3_sorts),
            _to_z3_sort(sort.element_sort, z3_sorts),
        )
    msg = f"Unsupported sort in Z3 bridge: {sort}"
    raise TypeError(msg)


def _to_z3_expr(
    expr: Expr,
    z3_consts: dict[FuncDecl, z3.ExprRef],
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef],
    z3_sorts: dict[object, z3.SortRef],
) -> z3.ExprRef:
    memo: dict[Expr, z3.ExprRef] = {}
    stack: list[tuple[Expr, bool]] = [(expr, False)]
    while stack:
        node, expanded = stack.pop()
        if node in memo:
            continue
        if isinstance(node, Const):
            if node.is_bool:
                memo[node] = z3.BoolVal(bool(node.value))
            elif node.is_int:
                assert isinstance(node.value, int)
                memo[node] = z3.IntVal(node.value)
            elif node.is_bv:
                assert isinstance(node.value, int)
                memo[node] = z3.BitVecVal(node.value, node.bv_size)
            continue
        assert isinstance(node, App)
        if not node.args:
            memo[node] = z3_consts[node.decl]
            continue
        if not expanded:
            stack.append((node, True))
            for arg in reversed(node.args):
                if arg not in memo:
                    stack.append((arg, False))
            continue

        za = [memo[arg] for arg in node.args]
        k = node.decl.kind
        match k:
            case DeclKind.NOT:
                memo[node] = z3.Not(za[0])
            case DeclKind.AND:
                memo[node] = z3.And(*za)
            case DeclKind.OR:
                memo[node] = z3.Or(*za)
            case DeclKind.IMPLIES:
                memo[node] = z3.Implies(za[0], za[1])
            case DeclKind.XOR:
                memo[node] = z3.Xor(za[0], za[1])
            case DeclKind.EQ:
                memo[node] = za[0] == za[1]
            case DeclKind.DISTINCT:
                memo[node] = z3.Distinct(*za)
            case DeclKind.ITE:
                memo[node] = z3.If(za[0], za[1], za[2])
            case DeclKind.NEG:
                memo[node] = -_as_arith(za[0])
            case DeclKind.ADD:
                acc = _as_arith(za[0])
                for item in za[1:]:
                    acc = acc + _as_arith(item)
                memo[node] = acc
            case DeclKind.SUB:
                memo[node] = _as_arith(za[0]) - _as_arith(za[1])
            case DeclKind.MUL:
                acc_m = _as_arith(za[0])
                for item in za[1:]:
                    acc_m = acc_m * _as_arith(item)
                memo[node] = acc_m
            case DeclKind.LT:
                memo[node] = _as_arith(za[0]) < _as_arith(za[1])
            case DeclKind.LE:
                memo[node] = _as_arith(za[0]) <= _as_arith(za[1])
            case DeclKind.GT:
                memo[node] = _as_arith(za[0]) > _as_arith(za[1])
            case DeclKind.GE:
                memo[node] = _as_arith(za[0]) >= _as_arith(za[1])
            case DeclKind.BV_NOT:
                memo[node] = ~_as_bv(za[0])
            case DeclKind.BV_AND:
                bv_acc = _as_bv(za[0])
                for item in za[1:]:
                    bv_acc = bv_acc & _as_bv(item)
                memo[node] = bv_acc
            case DeclKind.BV_OR:
                bv_o = _as_bv(za[0])
                for item in za[1:]:
                    bv_o = bv_o | _as_bv(item)
                memo[node] = bv_o
            case DeclKind.BV_XOR:
                bv_x = _as_bv(za[0])
                for item in za[1:]:
                    bv_x = bv_x ^ _as_bv(item)
                memo[node] = bv_x
            case DeclKind.BV_NEG:
                memo[node] = -_as_bv(za[0])
            case DeclKind.BV_ADD:
                bv_a = _as_bv(za[0])
                for item in za[1:]:
                    bv_a = bv_a + _as_bv(item)
                memo[node] = bv_a
            case DeclKind.BV_SUB:
                memo[node] = _as_bv(za[0]) - _as_bv(za[1])
            case DeclKind.BV_MUL:
                bv_mu = _as_bv(za[0])
                for item in za[1:]:
                    bv_mu = bv_mu * _as_bv(item)
                memo[node] = bv_mu
            case DeclKind.BV_UDIV:
                memo[node] = z3.UDiv(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_UREM:
                memo[node] = z3.URem(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_SDIV:
                memo[node] = _as_bv(za[0]) / _as_bv(za[1])
            case DeclKind.BV_SREM:
                memo[node] = z3.SRem(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_SMOD:
                memo[node] = _as_bv(za[0]) % _as_bv(za[1])
            case DeclKind.BV_SHL:
                memo[node] = _as_bv(za[0]) << _as_bv(za[1])
            case DeclKind.BV_LSHR:
                memo[node] = z3.LShR(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_ASHR:
                memo[node] = _as_bv(za[0]) >> _as_bv(za[1])
            case DeclKind.BV_ULT:
                memo[node] = z3.ULT(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_ULE:
                memo[node] = z3.ULE(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_UGT:
                memo[node] = z3.UGT(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_UGE:
                memo[node] = z3.UGE(_as_bv(za[0]), _as_bv(za[1]))
            case DeclKind.BV_SLT:
                memo[node] = _as_bv(za[0]) < _as_bv(za[1])
            case DeclKind.BV_SLE:
                memo[node] = _as_bv(za[0]) <= _as_bv(za[1])
            case DeclKind.BV_SGT:
                memo[node] = _as_bv(za[0]) > _as_bv(za[1])
            case DeclKind.BV_SGE:
                memo[node] = _as_bv(za[0]) >= _as_bv(za[1])
            case DeclKind.BV_CONCAT:
                memo[node] = z3.Concat(*(_as_bv(item) for item in za))
            case DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                memo[node] = z3.Extract(hi, lo, _as_bv(za[0]))
            case DeclKind.BV_ZERO_EXT:
                memo[node] = z3.ZeroExt(node.decl.params[0], _as_bv(za[0]))
            case DeclKind.BV_SIGN_EXT:
                memo[node] = z3.SignExt(node.decl.params[0], _as_bv(za[0]))
            case DeclKind.BV_ROTATE_LEFT:
                memo[node] = z3.RotateLeft(_as_bv(za[0]), node.decl.params[0])
            case DeclKind.BV_ROTATE_RIGHT:
                memo[node] = z3.RotateRight(_as_bv(za[0]), node.decl.params[0])
            case DeclKind.BV_REPEAT:
                memo[node] = z3.RepeatBitVec(node.decl.params[0], _as_bv(za[0]))
            case DeclKind.SELECT:
                memo[node] = z3.Select(_as_arr(za[0]), za[1])
            case DeclKind.STORE:
                memo[node] = z3.Store(_as_arr(za[0]), za[1], za[2])
            case DeclKind.CONST_ARRAY:
                memo[node] = z3.K(_to_z3_sort(node.sort.index_sort, z3_sorts), za[0])
            case DeclKind.UNINTERPRETED:
                memo[node] = z3_funcs[node.decl](*za)
    return memo[expr]


def _z3_verdict(solver: z3.Solver) -> SolveResult:
    res = solver.check()
    if res == z3.sat:
        return SolveResult.SAT
    if res == z3.unsat:
        return SolveResult.UNSAT
    return SolveResult.UNKNOWN


@st.composite
def _bv_formulas(
    draw: st.DrawFn,
    *,
    with_uf: bool = False,
    with_arrays: bool = False,
) -> tuple[_BVSig, list[Expr]]:
    width = 4
    sig = _make_bv_sig(width)
    ctx = sig.ctx

    pool: list[Expr] = list(sig.bv_vars)
    pool.append(ctx.mk_bv_val(draw(st.integers(min_value=0, max_value=15)), width))
    pool.append(ctx.mk_bv_val(draw(st.integers(min_value=0, max_value=15)), width))

    arr_pool: list[Expr] = [sig.arr_var]
    if with_arrays:
        k_val = ctx.mk_bv_val(draw(st.integers(min_value=0, max_value=15)), width)
        arr_pool.append(ctx.mk_const_array(ctx.mk_bv_sort(width), k_val))
        for _ in range(draw(st.integers(min_value=1, max_value=2))):
            base = draw(st.sampled_from(arr_pool))
            idx = draw(st.sampled_from(pool))
            val = draw(st.sampled_from(pool))
            arr_pool.append(ctx.mk_store(base, idx, val))
        for _ in range(2):
            pool.append(
                ctx.mk_select(
                    draw(st.sampled_from(arr_pool)), draw(st.sampled_from(pool))
                )
            )

    if with_uf:
        for _ in range(draw(st.integers(min_value=1, max_value=2))):
            pool.append(sig.uf_bv(draw(st.sampled_from(pool))))

    def _bv_term(depth: int) -> Expr:
        if depth <= 0 or draw(st.integers(min_value=0, max_value=1)) == 0:
            return draw(st.sampled_from(pool))
        op = draw(st.integers(min_value=0, max_value=11))
        t1 = _bv_term(depth - 1)
        if op == 0:
            return ~t1
        if op == 1:
            return -t1
        if op == 2:
            return ctx.mk_rotate_left(draw(st.integers(min_value=0, max_value=3)), t1)
        if op == 3:
            c_part = ctx.mk_concat(
                ctx.mk_extract(1, 0, t1),
                ctx.mk_extract(3, 2, _bv_term(depth - 1)),
            )
            return c_part
        t2 = _bv_term(depth - 1)
        if op == 4:
            return t1 + t2
        if op == 5:
            return t1 - t2
        if op == 6:
            return t1 & t2
        if op == 7:
            return t1 ^ t2
        if op == 8:
            return t1 << (
                ctx.mk_bv_val(draw(st.integers(min_value=0, max_value=4)), width)
            )
        if op == 9:
            return ctx.mk_bv_lshr(t1, t2)
        if op == 10:
            return t1 >> t2
        return ctx.mk_ite(draw(st.sampled_from(sig.bool_vars)), t1, t2)

    def _bv_atom() -> Expr:
        ch = draw(st.integers(min_value=0, max_value=7))
        if ch == 0:
            return draw(st.sampled_from(sig.bool_vars))
        if ch == 1 and with_uf:
            return sig.pred_bv(_bv_term(1))
        if ch == 2 and with_arrays:
            a1 = draw(st.sampled_from(arr_pool))
            a2 = draw(st.sampled_from(arr_pool))
            return ctx.mk_eq(a1, a2)
        if ch == 3:
            return ctx.mk_eq(_bv_term(2), _bv_term(2))
        if ch == 4:
            return ctx.mk_distinct(_bv_term(1), _bv_term(1), _bv_term(1))
        cmp_op = draw(
            st.sampled_from(
                (
                    ctx.mk_bv_ult,
                    ctx.mk_bv_ule,
                    ctx.mk_bv_slt,
                    ctx.mk_bv_sle,
                    ctx.mk_eq,
                )
            )
        )
        return cmp_op(_bv_term(2), _bv_term(2))

    def _bv_bool(depth: int) -> Expr:
        if depth <= 0 or draw(st.integers(min_value=0, max_value=2)) == 0:
            return _bv_atom()
        op = draw(st.integers(min_value=0, max_value=4))
        if op == 0:
            return ctx.mk_not(_bv_bool(depth - 1))
        if op == 1:
            return ctx.mk_and(_bv_bool(depth - 1), _bv_bool(depth - 1))
        if op == 2:
            return ctx.mk_or(_bv_bool(depth - 1), _bv_bool(depth - 1))
        if op == 3:
            return ctx.mk_implies(_bv_bool(depth - 1), _bv_bool(depth - 1))
        return ctx.mk_ite(_bv_bool(depth - 1), _bv_bool(depth - 1), _bv_bool(depth - 1))

    n_forms = draw(st.integers(min_value=2, max_value=6))
    return sig, [_bv_bool(2) for _ in range(n_forms)]


@st.composite
def _ax_formulas(draw: st.DrawFn, *, with_lia: bool) -> tuple[_AXSig, list[Expr]]:
    sig = _make_ax_sig(with_lia=with_lia)
    ctx = sig.ctx
    idx_sort = sig.idx_vars[0].sort

    val_pool: list[Expr]
    idx_pool: list[Expr] = list(sig.idx_vars)
    if with_lia:
        idx_pool.extend(
            ctx.mk_add(draw(st.sampled_from(sig.idx_vars)), ctx.mk_int_val(off))
            for off in (-1, 0, 1)
        )
        val_pool = list(idx_pool) + [ctx.mk_int_val(c) for c in (0, 1, 2)]
    else:
        val_pool = list(sig.val_vars)

    arr_pool: list[Expr] = list(sig.arr_vars)
    if draw(st.booleans()):
        arr_pool.append(ctx.mk_const_array(idx_sort, draw(st.sampled_from(val_pool))))
    for _ in range(draw(st.integers(min_value=1, max_value=3))):
        base = draw(st.sampled_from(arr_pool))
        st_idx = draw(st.sampled_from(idx_pool))
        st_val = draw(st.sampled_from(val_pool))
        arr_pool.append(ctx.mk_store(base, st_idx, st_val))

    if with_lia and sig.uf_fn is not None:
        val_pool.append(sig.uf_fn(draw(st.sampled_from(val_pool))))

    for _ in range(draw(st.integers(min_value=1, max_value=3))):
        sel = ctx.mk_select(
            draw(st.sampled_from(arr_pool)), draw(st.sampled_from(idx_pool))
        )
        val_pool.append(sel)

    def _atom() -> Expr:
        ch = draw(st.integers(min_value=0, max_value=5))
        if ch == 0:
            return draw(st.sampled_from(sig.bool_vars))
        if ch == 1:
            return ctx.mk_eq(
                draw(st.sampled_from(arr_pool)), draw(st.sampled_from(arr_pool))
            )
        if ch == 2:
            return ctx.mk_eq(
                draw(st.sampled_from(idx_pool)), draw(st.sampled_from(idx_pool))
            )
        if ch == 3:
            return ctx.mk_eq(
                draw(st.sampled_from(val_pool)), draw(st.sampled_from(val_pool))
            )
        if ch == 4 and with_lia:
            v1 = draw(st.sampled_from(val_pool))
            v2 = draw(st.sampled_from(val_pool))
            op = draw(st.sampled_from((ctx.mk_lt, ctx.mk_le, ctx.mk_gt, ctx.mk_ge)))
            return op(
                v1, v2 + ctx.mk_int_val(draw(st.integers(min_value=-2, max_value=2)))
            )
        return ctx.mk_distinct(
            draw(st.sampled_from(arr_pool)), draw(st.sampled_from(arr_pool))
        )

    def _rand_bool(depth: int) -> Expr:
        if depth <= 0 or draw(st.integers(min_value=0, max_value=2)) == 0:
            return _atom()
        op = draw(st.integers(min_value=0, max_value=4))
        if op == 0:
            return ctx.mk_not(_rand_bool(depth - 1))
        if op == 1:
            return ctx.mk_and(_rand_bool(depth - 1), _rand_bool(depth - 1))
        if op == 2:
            return ctx.mk_or(_rand_bool(depth - 1), _rand_bool(depth - 1))
        if op == 3:
            return ctx.mk_implies(_rand_bool(depth - 1), _rand_bool(depth - 1))
        return ctx.mk_ite(
            _rand_bool(depth - 1), _rand_bool(depth - 1), _rand_bool(depth - 1)
        )

    n_forms = draw(st.integers(min_value=2, max_value=6))
    return sig, [_rand_bool(2) for _ in range(n_forms)]


@settings(max_examples=40, deadline=None)
@given(data=_bv_formulas(with_uf=False, with_arrays=False))
def test_qf_bv_and_standalone_tactic_match_z3(
    data: tuple[_BVSig, list[Expr]],
) -> None:
    sig, formulas = data
    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in formulas:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, sig.z3_consts, sig.z3_funcs, {}))

    ures = usolver.check()
    zres = _z3_verdict(zsolver)
    assert ures is zres
    if ures is SolveResult.SAT:
        model = usolver.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True

    # Also verify standalone BVSimplify + BitBlast + BitVecModelConverter pipeline.
    tactic = Then(BVSimplifyTactic(), BitBlastTactic())
    tres = tactic.apply(formulas)
    tsolver = SMTSolver(sig.ctx)
    tsolver.add(*tres.formulas)
    t_verdict = tsolver.check()
    assert t_verdict is zres
    if t_verdict is SolveResult.SAT:
        reconstructed = tres.converter.convert(tsolver.model())
        for f in formulas:
            assert reconstructed.eval_bool(f, model_completion=True) is True


@settings(max_examples=35, deadline=None)
@given(data=_bv_formulas(with_uf=True, with_arrays=False))
def test_qf_ufbv_matches_z3_and_validates_models(
    data: tuple[_BVSig, list[Expr]],
) -> None:
    sig, formulas = data
    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in formulas:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, sig.z3_consts, sig.z3_funcs, {}))

    ures = usolver.check()
    zres = _z3_verdict(zsolver)
    assert ures is zres
    if ures is SolveResult.SAT:
        model = usolver.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True


@settings(max_examples=35, deadline=None)
@given(data=_bv_formulas(with_uf=True, with_arrays=True))
def test_qf_aufbv_matches_z3_and_validates_models(
    data: tuple[_BVSig, list[Expr]],
) -> None:
    sig, formulas = data
    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in formulas:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, sig.z3_consts, sig.z3_funcs, {}))

    ures = usolver.check()
    zres = _z3_verdict(zsolver)
    assert ures is zres
    if ures is SolveResult.SAT:
        model = usolver.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True


@settings(max_examples=40, deadline=None)
@given(data=_ax_formulas(with_lia=False))
def test_qf_ax_matches_z3_and_validates_models(
    data: tuple[_AXSig, list[Expr]],
) -> None:
    sig, formulas = data
    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in formulas:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, sig.z3_consts, sig.z3_funcs, sig.z3_sorts))

    ures = usolver.check()
    zres = _z3_verdict(zsolver)
    assert ures is zres
    if ures is SolveResult.SAT:
        model = usolver.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True


@settings(max_examples=30, deadline=None)
@given(data=_ax_formulas(with_lia=True))
def test_qf_auflia_incremental_matches_z3(
    data: tuple[_AXSig, list[Expr]],
) -> None:
    sig, formulas = data
    mid = max(1, len(formulas) // 2)
    base = formulas[:mid]
    scoped = formulas[mid:]

    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in base:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, sig.z3_consts, sig.z3_funcs, sig.z3_sorts))
    assert usolver.check() is _z3_verdict(zsolver)

    usolver.push()
    zsolver.push()
    for f in scoped:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, sig.z3_consts, sig.z3_funcs, sig.z3_sorts))
    r_scoped = usolver.check()
    assert r_scoped is _z3_verdict(zsolver)
    if r_scoped is SolveResult.SAT:
        model = usolver.model()
        for f in [*base, *scoped]:
            assert model.eval_bool(f, model_completion=True) is True
    usolver.pop(1)
    zsolver.pop(1)

    i0 = sig.idx_vars[0]
    a_arr = sig.arr_vars[0]
    assump1 = sig.ctx.mk_eq(sig.ctx.mk_select(a_arr, i0), sig.ctx.mk_int_val(1))
    assump2 = sig.ctx.mk_eq(
        sig.ctx.mk_select(sig.ctx.mk_store(a_arr, i0, sig.ctx.mk_int_val(2)), i0),
        sig.ctx.mk_select(a_arr, i0),
    )
    assump_unused = sig.ctx.mk_ge(i0, sig.ctx.mk_int_val(0))
    # assump2 simplifies in mk_select to 2 == select(a, i), conflicting with assump1.
    zsolver.push()
    zsolver.add(
        _to_z3_expr(assump1, sig.z3_consts, sig.z3_funcs, sig.z3_sorts),
        _to_z3_expr(assump2, sig.z3_consts, sig.z3_funcs, sig.z3_sorts),
    )
    assert zsolver.check() == z3.unsat
    zsolver.pop(1)

    assert usolver.check(assump1, assump2, assump_unused) is SolveResult.UNSAT
    core = usolver.unsat_core()
    assert assump_unused not in core
    assert set(core) <= {assump1, assump2}
