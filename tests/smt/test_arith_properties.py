"""Z3 differential property-based tests for QF_LRA, QF_LIA, QF_UFLRA, and QF_UFLIA."""

from fractions import Fraction
from typing import NamedTuple

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl, SortKind


class _ArithSig(NamedTuple):
    ctx: Context
    sort_kind: SortKind
    bool_vars: tuple[App, ...]
    num_vars: tuple[App, ...]
    uf_unary: FuncDecl
    uf_pred: FuncDecl
    z3_vars: dict[FuncDecl, z3.ExprRef]
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef]


def _make_sig(is_int: bool) -> _ArithSig:
    ctx = Context()
    sort = ctx.int_sort if is_int else ctx.real_sort
    zsort = z3.IntSort() if is_int else z3.RealSort()

    bool_vars = tuple(ctx.mk_bool(n) for n in ("b0", "b1"))
    num_vars = tuple(ctx.mk_const(n, sort) for n in ("x", "y", "z"))
    uf_unary = ctx.mk_decl("f", (sort,), sort)
    uf_pred = ctx.mk_decl("P", (sort,), ctx.bool_sort)

    z3_vars: dict[FuncDecl, z3.ExprRef] = {
        bv.decl: z3.Bool(bv.name) for bv in bool_vars
    }
    for nv in num_vars:
        z3_vars[nv.decl] = z3.Int(nv.name) if is_int else z3.Real(nv.name)

    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] = {
        uf_unary: z3.Function("f", zsort, zsort),
        uf_pred: z3.Function("P", zsort, z3.BoolSort()),
    }

    return _ArithSig(
        ctx=ctx,
        sort_kind=sort.kind,
        bool_vars=bool_vars,
        num_vars=num_vars,
        uf_unary=uf_unary,
        uf_pred=uf_pred,
        z3_vars=z3_vars,
        z3_funcs=z3_funcs,
    )


def _as_arith(ref: z3.ExprRef) -> z3.ArithRef:
    assert isinstance(ref, z3.ArithRef)
    return ref


def _to_z3(expr: Expr, sig: _ArithSig) -> z3.ExprRef:
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
            else:
                assert isinstance(node.value, Fraction)
                memo[node] = z3.RatVal(node.value.numerator, node.value.denominator)
            continue
        assert isinstance(node, App)
        if not node.args:
            memo[node] = sig.z3_vars[node.decl]
            continue
        if not expanded:
            stack.append((node, True))
            for arg in reversed(node.args):
                if arg not in memo:
                    stack.append((arg, False))
            continue

        zargs = [memo[arg] for arg in node.args]
        match node.decl.kind:
            case DeclKind.NOT:
                memo[node] = z3.Not(zargs[0])
            case DeclKind.AND:
                memo[node] = z3.And(*zargs)
            case DeclKind.OR:
                memo[node] = z3.Or(*zargs)
            case DeclKind.IMPLIES:
                memo[node] = z3.Implies(zargs[0], zargs[1])
            case DeclKind.XOR:
                memo[node] = z3.Xor(zargs[0], zargs[1])
            case DeclKind.EQ:
                memo[node] = zargs[0] == zargs[1]
            case DeclKind.DISTINCT:
                memo[node] = z3.Distinct(*zargs)
            case DeclKind.ITE:
                memo[node] = z3.If(zargs[0], zargs[1], zargs[2])
            case DeclKind.NEG:
                memo[node] = -_as_arith(zargs[0])
            case DeclKind.ADD:
                acc = _as_arith(zargs[0])
                for item in zargs[1:]:
                    acc = acc + _as_arith(item)
                memo[node] = acc
            case DeclKind.SUB:
                memo[node] = _as_arith(zargs[0]) - _as_arith(zargs[1])
            case DeclKind.MUL:
                acc_m = _as_arith(zargs[0])
                for item in zargs[1:]:
                    acc_m = acc_m * _as_arith(item)
                memo[node] = acc_m
            case DeclKind.DIV:
                memo[node] = _as_arith(zargs[0]) / _as_arith(zargs[1])
            case DeclKind.LT:
                memo[node] = _as_arith(zargs[0]) < _as_arith(zargs[1])
            case DeclKind.LE:
                memo[node] = _as_arith(zargs[0]) <= _as_arith(zargs[1])
            case DeclKind.GT:
                memo[node] = _as_arith(zargs[0]) > _as_arith(zargs[1])
            case DeclKind.GE:
                memo[node] = _as_arith(zargs[0]) >= _as_arith(zargs[1])
            case DeclKind.TO_REAL:
                memo[node] = z3.ToReal(_as_arith(zargs[0]))
            case DeclKind.UNINTERPRETED:
                memo[node] = sig.z3_funcs[node.decl](*zargs)
    return memo[expr]


def _make_const(ctx: Context, is_int: bool, num: int, den: int) -> Expr:
    if is_int:
        return ctx.mk_int_val(num)
    return ctx.mk_real_val(Fraction(num, den))


@st.composite
def _arith_formulas(
    draw: st.DrawFn,
    *,
    is_int: bool,
    with_uf: bool,
) -> tuple[_ArithSig, list[Expr]]:
    sig = _make_sig(is_int)
    ctx = sig.ctx

    term_pool: list[Expr] = list(sig.num_vars)
    if with_uf:
        for _ in range(draw(st.integers(min_value=1, max_value=3))):
            arg = draw(st.sampled_from(term_pool))
            if draw(st.booleans()):
                c_val = draw(st.integers(min_value=-2, max_value=3))
                c_expr = _make_const(ctx, is_int, c_val, 2)
                arg = ctx.mk_add(arg, c_expr)
            term_pool.append(sig.uf_unary(arg))

    if draw(st.booleans()):
        cond = draw(st.sampled_from(sig.bool_vars))
        ite_term = ctx.mk_ite(
            cond,
            draw(st.sampled_from(term_pool)),
            draw(st.sampled_from(term_pool)),
        )
        term_pool.append(ite_term)

    def _lin_combo() -> Expr:
        n_terms = draw(st.integers(min_value=1, max_value=3))
        parts: list[Expr] = []
        for _ in range(n_terms):
            v = draw(st.sampled_from(term_pool))
            coef_num = draw(st.integers(min_value=-3, max_value=3))
            coef_den = 1 if is_int else draw(st.sampled_from((1, 2)))
            if coef_num == 0:
                continue
            parts.append(_make_const(ctx, is_int, coef_num, coef_den) * v)
        c_num = draw(st.integers(min_value=-4, max_value=4))
        c_den = 1 if is_int else draw(st.sampled_from((1, 2)))
        parts.append(_make_const(ctx, is_int, c_num, c_den))
        return ctx.mk_add(*parts)

    def _rand_atom() -> Expr:
        choice = draw(st.integers(min_value=0, max_value=6))
        if choice == 0:
            return draw(st.sampled_from(sig.bool_vars))
        if choice == 1 and with_uf:
            t = draw(st.sampled_from(term_pool))
            atom = sig.uf_pred(t)
            return ctx.mk_not(atom) if draw(st.booleans()) else atom
        if choice == 2:
            lhs = draw(st.sampled_from(term_pool))
            rhs = draw(st.sampled_from(term_pool))
            eq = ctx.mk_eq(lhs, rhs)
            return ctx.mk_not(eq) if draw(st.booleans()) else eq
        if choice == 3 and with_uf:
            k = draw(st.integers(min_value=2, max_value=3))
            return ctx.mk_distinct(
                *(draw(st.sampled_from(term_pool)) for _ in range(k))
            )
        lhs = _lin_combo()
        rhs = _lin_combo()
        cmp_op = draw(st.sampled_from((ctx.mk_lt, ctx.mk_le, ctx.mk_gt, ctx.mk_ge)))
        return cmp_op(lhs, rhs)

    def _rand_bool(depth: int) -> Expr:
        if depth <= 0 or draw(st.integers(min_value=0, max_value=2)) == 0:
            return _rand_atom()
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

    # Bound range on integer variables in UF+LIA fuzzing to keep B&B snappy.
    num_formulas = draw(st.integers(min_value=2, max_value=7))
    formulas = [_rand_bool(2) for _ in range(num_formulas)]
    if is_int:
        for nv in sig.num_vars:
            formulas.append(ctx.mk_ge(nv, ctx.mk_int_val(-5)))
            formulas.append(ctx.mk_le(nv, ctx.mk_int_val(5)))
    return sig, formulas


def _z3_verdict(solver: z3.Solver) -> SolveResult:
    res = solver.check()
    if res == z3.sat:
        return SolveResult.SAT
    if res == z3.unsat:
        return SolveResult.UNSAT
    return SolveResult.UNKNOWN


def _assert_differential_match(
    sig: _ArithSig, formulas: list[Expr], *, check_int: bool = False
) -> None:
    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in formulas:
        usolver.add(f)
        zsolver.add(_to_z3(f, sig))

    ures = usolver.check()
    zres = _z3_verdict(zsolver)
    assert ures is zres
    if ures is SolveResult.SAT:
        model = usolver.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True
        if check_int:
            for nv in sig.num_vars:
                val = model.eval_int(nv)
                assert isinstance(val, int)
                assert not isinstance(val, bool)


@settings(max_examples=50, deadline=None)
@given(data=_arith_formulas(is_int=False, with_uf=False))
def test_qf_lra_matches_z3_and_validates_models(
    data: tuple[_ArithSig, list[Expr]],
) -> None:
    sig, formulas = data
    _assert_differential_match(sig, formulas)


@settings(max_examples=50, deadline=None)
@given(data=_arith_formulas(is_int=True, with_uf=False))
def test_qf_lia_matches_z3_and_validates_models(
    data: tuple[_ArithSig, list[Expr]],
) -> None:
    sig, formulas = data
    _assert_differential_match(sig, formulas, check_int=True)


@settings(max_examples=40, deadline=None)
@given(data=_arith_formulas(is_int=False, with_uf=True))
def test_qf_uflra_matches_z3_and_validates_models(
    data: tuple[_ArithSig, list[Expr]],
) -> None:
    sig, formulas = data
    _assert_differential_match(sig, formulas)


@settings(max_examples=40, deadline=None)
@given(data=_arith_formulas(is_int=True, with_uf=True))
def test_qf_uflia_matches_z3_and_validates_models(
    data: tuple[_ArithSig, list[Expr]],
) -> None:
    sig, formulas = data
    _assert_differential_match(sig, formulas, check_int=True)


@settings(max_examples=25, deadline=None)
@given(
    data=_arith_formulas(is_int=True, with_uf=True),
    rhs=st.integers(min_value=-3, max_value=3),
)
def test_arith_incremental_push_pop_and_unsat_core_vs_z3(
    data: tuple[_ArithSig, list[Expr]],
    rhs: int,
) -> None:
    sig, formulas = data
    mid = max(1, len(formulas) // 2)
    base = formulas[:mid]
    scoped = formulas[mid:]

    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()
    for f in base:
        usolver.add(f)
        zsolver.add(_to_z3(f, sig))
    assert usolver.check() is _z3_verdict(zsolver)

    usolver.push()
    zsolver.push()
    for f in scoped:
        usolver.add(f)
        zsolver.add(_to_z3(f, sig))
    r_scoped = usolver.check()
    assert r_scoped is _z3_verdict(zsolver)
    if r_scoped is SolveResult.SAT:
        model = usolver.model()
        for f in [*base, *scoped]:
            assert model.eval_bool(f, model_completion=True) is True
    usolver.pop(1)
    zsolver.pop(1)

    x = sig.num_vars[0]
    a1 = sig.ctx.mk_ge(x, sig.ctx.mk_int_val(rhs))
    a2 = sig.ctx.mk_lt(x, sig.ctx.mk_int_val(rhs))
    zsolver.push()
    zsolver.add(_to_z3(a1, sig), _to_z3(a2, sig))
    assert zsolver.check() == z3.unsat
    zsolver.pop()
    r_assump = usolver.check(a1, a2)
    assert r_assump is SolveResult.UNSAT
    core = usolver.unsat_core()
    assert set(core) <= {a1, a2}
    recheck = SMTSolver(sig.ctx)
    recheck.add(*base, *core)
    assert recheck.check() is SolveResult.UNSAT
