"""Property-based Z3 differential tests for quantified UF and LIA solving."""

from typing import NamedTuple

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import (
    App,
    BoundVar,
    Const,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Quantifier,
    has_quantifiers,
)


class _QUFEnv(NamedTuple):
    ctx: Context
    consts: tuple[App, ...]
    f: FuncDecl
    g: FuncDecl
    pred_p: FuncDecl
    pred_q: FuncDecl
    z3_sorts: dict[str, z3.SortRef]
    z3_vars: dict[FuncDecl, z3.ExprRef]
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef]


def _make_quf_env() -> _QUFEnv:
    ctx = Context()
    sort_s = ctx.mk_uninterpreted_sort("S")
    zs = z3.DeclareSort("S")
    consts = tuple(ctx.mk_const(n, sort_s) for n in ("a", "b", "c", "d"))
    f = ctx.mk_decl("f", (sort_s,), sort_s)
    g = ctx.mk_decl("g", (sort_s,), sort_s)
    pred_p = ctx.mk_decl("P", (sort_s,), ctx.bool_sort)
    pred_q = ctx.mk_decl("Q", (sort_s,), ctx.bool_sort)

    z3_vars: dict[FuncDecl, z3.ExprRef] = {c.decl: z3.Const(c.decl.name, zs) for c in consts}
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] = {
        f: z3.Function("f", zs, zs),
        g: z3.Function("g", zs, zs),
        pred_p: z3.Function("P", zs, z3.BoolSort()),
        pred_q: z3.Function("Q", zs, z3.BoolSort()),
    }
    return _QUFEnv(
        ctx=ctx,
        consts=consts,
        f=f,
        g=g,
        pred_p=pred_p,
        pred_q=pred_q,
        z3_sorts={"S": zs},
        z3_vars=z3_vars,
        z3_funcs=z3_funcs,
    )


def _as_arith(ref: z3.ExprRef) -> z3.ArithRef:
    assert isinstance(ref, z3.ArithRef)
    return ref


def _to_z3(
    expr: Expr,
    z3_vars: dict[FuncDecl, z3.ExprRef],
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef],
    z3_sorts: dict[str, z3.SortRef],
) -> z3.ExprRef:
    def conv(node: Expr, bvars: tuple[z3.ExprRef, ...]) -> z3.ExprRef:
        if isinstance(node, BoundVar):
            return bvars[-1 - node.index]
        if isinstance(node, Const):
            if node.is_bool:
                return z3.BoolVal(bool(node.value))
            assert isinstance(node.value, int)
            return z3.IntVal(node.value)
        if isinstance(node, Quantifier):
            qvars = [
                z3.FreshConst(
                    z3.IntSort() if vs.is_int else z3.BoolSort() if vs.is_bool else z3_sorts[vs.name],
                    vn,
                )
                for vn, vs in zip(node.var_names, node.var_sorts, strict=True)
            ]
            body = conv(node.body, bvars + tuple(qvars))
            return z3.ForAll(qvars, body) if node.is_forall else z3.Exists(qvars, body)
        assert isinstance(node, App)
        if not node.args:
            return z3_vars[node.decl]
        zargs = [conv(a, bvars) for a in node.args]
        match node.decl.kind:
            case DeclKind.NOT:
                return z3.Not(zargs[0])
            case DeclKind.AND:
                return z3.And(*zargs)
            case DeclKind.OR:
                return z3.Or(*zargs)
            case DeclKind.IMPLIES:
                return z3.Implies(zargs[0], zargs[1])
            case DeclKind.EQ:
                return zargs[0] == zargs[1]
            case DeclKind.DISTINCT:
                return z3.Distinct(*zargs)
            case DeclKind.ADD:
                return _as_arith(zargs[0]) + _as_arith(zargs[1])
            case DeclKind.SUB:
                return _as_arith(zargs[0]) - _as_arith(zargs[1])
            case DeclKind.LE:
                return _as_arith(zargs[0]) <= _as_arith(zargs[1])
            case DeclKind.GE:
                return _as_arith(zargs[0]) >= _as_arith(zargs[1])
            case DeclKind.LT:
                return _as_arith(zargs[0]) < _as_arith(zargs[1])
            case DeclKind.GT:
                return _as_arith(zargs[0]) > _as_arith(zargs[1])
            case DeclKind.UNINTERPRETED:
                return z3_funcs[node.decl](*zargs)
            case _:
                msg = f"Unsupported AST kind in Z3 converter: {node.decl.kind}"
                raise AssertionError(msg)

    return conv(expr, ())


@st.composite
def _quf_cases(draw: st.DrawFn) -> tuple[_QUFEnv, list[Expr]]:
    env = _make_quf_env()
    ctx = env.ctx
    s = env.consts[0].sort
    x = ctx.mk_const("qx", s)
    formulas: list[Expr] = []

    n_axioms = draw(st.integers(min_value=1, max_value=2))
    for _ in range(n_axioms):
        ax_kind = draw(st.integers(min_value=0, max_value=3))
        if ax_kind == 0:
            body = ctx.mk_implies(ctx.mk_app(env.pred_p, x), ctx.mk_app(env.pred_q, ctx.mk_app(env.f, x)))
            formulas.append(ctx.mk_forall([x], body, patterns=[[ctx.mk_app(env.f, x)]]))
        elif ax_kind == 1:
            body = ctx.mk_eq(ctx.mk_app(env.f, ctx.mk_app(env.g, x)), ctx.mk_app(env.g, x))
            formulas.append(ctx.mk_forall([x], body, patterns=[[ctx.mk_app(env.f, ctx.mk_app(env.g, x))]]))
        elif ax_kind == 2:
            body = ctx.mk_or(ctx.mk_app(env.pred_p, x), ctx.mk_app(env.pred_q, x))
            formulas.append(ctx.mk_forall([x], body, patterns=[[ctx.mk_app(env.pred_p, x)]]))
        else:
            body = ctx.mk_implies(ctx.mk_app(env.pred_q, x), ctx.mk_not(ctx.mk_app(env.pred_p, x)))
            formulas.append(ctx.mk_forall([x], body, patterns=[[ctx.mk_app(env.pred_q, x)]]))

    n_ground = draw(st.integers(min_value=2, max_value=5))
    for _ in range(n_ground):
        c1, c2 = draw(st.sampled_from(env.consts)), draw(st.sampled_from(env.consts))
        gk = draw(st.integers(min_value=0, max_value=4))
        if gk == 0:
            formulas.append(ctx.mk_app(env.pred_p, c1))
        elif gk == 1:
            formulas.append(ctx.mk_not(ctx.mk_app(env.pred_q, c1)))
        elif gk == 2:
            formulas.append(ctx.mk_eq(ctx.mk_app(env.f, c1), c2))
        elif gk == 3:
            formulas.append(ctx.mk_eq(ctx.mk_app(env.g, c1), c2))
        else:
            formulas.append(ctx.mk_app(env.pred_q, ctx.mk_app(env.f, c1)))

    return env, formulas


@settings(max_examples=20, deadline=None)
@given(data=_quf_cases())
def test_quantified_uf_soundness_vs_z3_and_model_validation(
    data: tuple[_QUFEnv, list[Expr]],
) -> None:
    env, formulas = data
    solver = SMTSolver(env.ctx, max_quantifier_rounds=8, max_quantifier_matches=128)
    solver.add(*formulas)
    res = solver.check()

    z3_solver = z3.Solver()
    z3_solver.set("timeout", 2000)
    for formula in formulas:
        z3_solver.add(_to_z3(formula, env.z3_vars, env.z3_funcs, env.z3_sorts))
    z3_res = z3_solver.check()

    if z3_res == z3.sat:
        assert res is not SolveResult.UNSAT
    elif z3_res == z3.unsat:
        assert res is not SolveResult.SAT

    if res is SolveResult.SAT:
        model = solver.model()
        for formula in formulas:
            assert model.eval_bool(formula, model_completion=True) is True


@settings(max_examples=15, deadline=None)
@given(
    flag1=st.booleans(),
    flag2=st.booleans(),
    use_other=st.booleans(),
)
def test_quantifier_push_pop_matches_fresh_solver(
    flag1: bool,
    flag2: bool,
    use_other: bool,
) -> None:
    env = _make_quf_env()
    ctx = env.ctx
    s = env.consts[0].sort
    a, b, c, d = env.consts
    x = ctx.mk_const("qx", s)

    base = [
        ctx.mk_eq(ctx.mk_app(env.g, a), b),
        ctx.mk_eq(ctx.mk_app(env.f, b), c),
        ctx.mk_app(env.pred_p, a),
    ]
    scoped_1: list[Expr] = [
        ctx.mk_forall(
            [x],
            ctx.mk_implies(ctx.mk_app(env.pred_p, x), ctx.mk_app(env.pred_q, x)),
            patterns=[[ctx.mk_app(env.pred_p, x)]],
        ),
        ctx.mk_not(ctx.mk_app(env.pred_q, a)) if flag1 else ctx.mk_app(env.pred_q, c),
    ]
    target = d if use_other else a
    scoped_2: list[Expr] = [
        ctx.mk_forall(
            [x],
            ctx.mk_app(env.pred_p, ctx.mk_app(env.f, x)),
            patterns=[[ctx.mk_app(env.f, x)]],
        ),
        ctx.mk_not(ctx.mk_app(env.pred_p, c)) if flag2 else ctx.mk_app(env.pred_q, target),
    ]

    inc = SMTSolver(ctx, max_quantifier_rounds=8)
    inc.add(*base)
    inc.push()
    inc.add(*scoped_1)
    r1 = inc.check()
    inc.pop()
    inc.push()
    inc.add(*scoped_2)
    r2 = inc.check()
    inc.pop()
    r_base = inc.check()

    for group, actual in ((base + scoped_1, r1), (base + scoped_2, r2), (base, r_base)):
        fresh = SMTSolver(ctx, max_quantifier_rounds=8)
        fresh.add(*group)
        assert actual is fresh.check()


@st.composite
def _bounded_qlia_cases(
    draw: st.DrawFn,
) -> tuple[
    Context,
    list[Expr],
    dict[FuncDecl, z3.ExprRef],
    dict[FuncDecl, z3.FuncDeclRef],
]:
    ctx = Context()
    int_s = ctx.int_sort
    a = ctx.mk_const("a", int_s)
    b = ctx.mk_const("b", int_s)
    p = ctx.mk_decl("P", (int_s,), ctx.bool_sort)
    z3_vars: dict[FuncDecl, z3.ExprRef] = {a.decl: z3.Int("a"), b.decl: z3.Int("b")}
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] = {p: z3.Function("P", z3.IntSort(), z3.BoolSort())}

    lo = draw(st.integers(min_value=-2, max_value=1))
    hi = draw(st.integers(min_value=lo, max_value=lo + 3))
    c = draw(st.integers(min_value=-3, max_value=4))
    x = ctx.mk_const("ix", int_s)

    formulas: list[Expr] = []
    # Mix decidable guarded LIA quantified constraints + ground integer facts.
    if draw(st.booleans()):
        guard = ctx.mk_and(ctx.mk_ge(x, ctx.mk_int_val(lo)), ctx.mk_le(x, ctx.mk_int_val(hi)))
        concl = ctx.mk_le(x, a) if draw(st.booleans()) else ctx.mk_gt(x, b)
        formulas.append(ctx.mk_forall([x], ctx.mk_implies(guard, concl)))
    else:
        witness = ctx.mk_and(
            ctx.mk_ge(x, a),
            ctx.mk_le(x, ctx.mk_add(a, ctx.mk_int_val(2))),
            ctx.mk_ge(x, ctx.mk_int_val(c)),
        )
        formulas.append(ctx.mk_exists([x], witness))

    if draw(st.booleans()):
        formulas.append(ctx.mk_le(a, ctx.mk_int_val(c)))
    else:
        formulas.append(ctx.mk_ge(a, ctx.mk_int_val(lo - 1)))
    if draw(st.booleans()):
        formulas.append(ctx.mk_ge(b, ctx.mk_int_val(hi)))
    if draw(st.booleans()):
        formulas.append(ctx.mk_app(p, a))

    return ctx, formulas, z3_vars, z3_funcs


@settings(max_examples=20, deadline=None)
@given(data=_bounded_qlia_cases())
def test_quantified_lia_soundness_vs_z3_and_ground_models(
    data: tuple[
        Context,
        list[Expr],
        dict[FuncDecl, z3.ExprRef],
        dict[FuncDecl, z3.FuncDeclRef],
    ],
) -> None:
    ctx, formulas, z3_vars, z3_funcs = data
    solver = SMTSolver(ctx, max_quantifier_rounds=8)
    solver.add(*formulas)
    res = solver.check()

    z3_solver = z3.Solver()
    z3_solver.set("timeout", 2000)
    for formula in formulas:
        z3_solver.add(_to_z3(formula, z3_vars, z3_funcs, {}))
    z3_res = z3_solver.check()

    if z3_res == z3.sat:
        assert res is not SolveResult.UNSAT
    elif z3_res == z3.unsat:
        assert res is not SolveResult.SAT

    if res is SolveResult.SAT:
        model = solver.model()
        for formula in formulas:
            if not has_quantifiers(formula):
                assert model.eval_bool(formula, model_completion=True) is True
