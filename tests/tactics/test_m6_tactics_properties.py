"""Property-based Z3 differential tests for M6 tactics and solve_with_tactic."""

from fractions import Fraction
from typing import NamedTuple

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.smt import SMTSolver, SolveResult, solve_with_tactic
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
from unsat.tactics import (
    CtxSimplifyTactic,
    GaussianElimTactic,
    NNFTactic,
    PropagateBoundsTactic,
    SimplifyTactic,
    SkolemizeTactic,
    Then,
)


class _ArithEnv(NamedTuple):
    ctx: Context
    bools: tuple[App, ...]
    nums: tuple[App, ...]
    z3_vars: dict[FuncDecl, z3.ExprRef]


def _make_arith_env(is_int: bool) -> _ArithEnv:
    ctx = Context()
    sort = ctx.int_sort if is_int else ctx.real_sort
    bools = tuple(ctx.mk_bool(n) for n in ("b0", "b1"))
    nums = tuple(ctx.mk_const(n, sort) for n in ("x", "y", "z"))
    z3_vars: dict[FuncDecl, z3.ExprRef] = {bv.decl: z3.Bool(bv.name) for bv in bools}
    for nv in nums:
        z3_vars[nv.decl] = z3.Int(nv.name) if is_int else z3.Real(nv.name)
    return _ArithEnv(ctx=ctx, bools=bools, nums=nums, z3_vars=z3_vars)


def _as_arith(ref: z3.ExprRef) -> z3.ArithRef:
    assert isinstance(ref, z3.ArithRef)
    return ref


def _expr_to_z3(
    expr: Expr,
    z3_vars: dict[FuncDecl, z3.ExprRef],
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] | None = None,
    z3_sorts: dict[str, z3.SortRef] | None = None,
) -> z3.ExprRef:
    func_map = z3_funcs or {}
    sort_map = z3_sorts or {}

    def conv(node: Expr, bvars: tuple[z3.ExprRef, ...]) -> z3.ExprRef:
        if isinstance(node, BoundVar):
            return bvars[-1 - node.index]
        if isinstance(node, Const):
            if node.is_bool:
                return z3.BoolVal(bool(node.value))
            if node.is_int:
                assert isinstance(node.value, int)
                return z3.IntVal(node.value)
            assert isinstance(node.value, Fraction)
            return z3.RatVal(node.value.numerator, node.value.denominator)

        if isinstance(node, Quantifier):
            qvars = [
                z3.FreshConst(
                    z3.IntSort()
                    if vs.is_int
                    else z3.RealSort()
                    if vs.is_real
                    else z3.BoolSort()
                    if vs.is_bool
                    else sort_map[vs.name],
                    vn,
                )
                for vn, vs in zip(node.var_names, node.var_sorts, strict=True)
            ]
            # De Bruijn index 0 maps to the last binder (qvars[-1]).
            next_bvars = bvars + tuple(qvars)
            body_ref = conv(node.body, next_bvars)
            return z3.ForAll(qvars, body_ref) if node.is_forall else z3.Exists(qvars, body_ref)

        assert isinstance(node, App)
        if not node.args:
            return z3_vars[node.decl]

        zargs = [conv(arg, bvars) for arg in node.args]
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
            case DeclKind.ITE:
                return z3.If(zargs[0], zargs[1], zargs[2])
            case DeclKind.ADD:
                acc = _as_arith(zargs[0])
                for arg_z in zargs[1:]:
                    acc = acc + _as_arith(arg_z)
                return acc
            case DeclKind.SUB:
                return _as_arith(zargs[0]) - _as_arith(zargs[1])
            case DeclKind.MUL:
                acc = _as_arith(zargs[0])
                for arg_z in zargs[1:]:
                    acc = acc * _as_arith(arg_z)
                return acc
            case DeclKind.NEG:
                return -_as_arith(zargs[0])
            case DeclKind.LT:
                return _as_arith(zargs[0]) < _as_arith(zargs[1])
            case DeclKind.LE:
                return _as_arith(zargs[0]) <= _as_arith(zargs[1])
            case DeclKind.GT:
                return _as_arith(zargs[0]) > _as_arith(zargs[1])
            case DeclKind.GE:
                return _as_arith(zargs[0]) >= _as_arith(zargs[1])
            case DeclKind.UNINTERPRETED:
                return func_map[node.decl](*zargs)
            case _:
                msg = f"Unsupported AST kind in Z3 converter: {node.decl.kind}"
                raise AssertionError(msg)

    return conv(expr, ())


@st.composite
def _arith_tactic_cases(draw: st.DrawFn) -> tuple[_ArithEnv, list[Expr]]:
    is_int = draw(st.booleans())
    env = _make_arith_env(is_int)
    ctx = env.ctx

    def num_const(val: int) -> Expr:
        return ctx.mk_int_val(val) if is_int else ctx.mk_real_val(Fraction(val, 2))

    def lin_term() -> Expr:
        terms: list[Expr] = []
        for var in env.nums:
            coeff = draw(st.integers(min_value=-2, max_value=2))
            if coeff == 0:
                continue
            terms.append(ctx.mk_mul(ctx.mk_int_val(coeff), var) if is_int else ctx.mk_mul(ctx.mk_real_val(coeff), var))
        offset = num_const(draw(st.integers(min_value=-4, max_value=4)))
        if not terms:
            return offset
        acc = terms[0] if len(terms) == 1 else ctx.mk_add(*terms)
        return ctx.mk_add(acc, offset)

    def atom() -> Expr:
        lhs = lin_term()
        rhs = num_const(draw(st.integers(min_value=-5, max_value=5)))
        kind = draw(st.sampled_from(["eq", "le", "lt", "ge", "gt"]))
        if kind == "eq":
            # Mix direct var = lin_term equalities to exercise GaussianElimTactic.
            v = draw(st.sampled_from(env.nums))
            return ctx.mk_eq(v, lin_term()) if draw(st.booleans()) else ctx.mk_eq(lhs, rhs)
        if kind == "le":
            return ctx.mk_le(lhs, rhs)
        if kind == "lt":
            return ctx.mk_lt(lhs, rhs)
        if kind == "ge":
            return ctx.mk_ge(lhs, rhs)
        return ctx.mk_gt(lhs, rhs)

    n_formulas = draw(st.integers(min_value=2, max_value=6))
    formulas: list[Expr] = []
    # Seed occasional pinned booleans to trigger CtxSimplifyTactic substitutions.
    if draw(st.booleans()):
        formulas.append(draw(st.sampled_from(env.bools)))
    for _ in range(n_formulas):
        shape = draw(st.integers(min_value=0, max_value=3))
        a0 = atom()
        if shape == 0:
            formulas.append(a0)
        elif shape == 1:
            b = draw(st.sampled_from(env.bools))
            formulas.append(ctx.mk_implies(b, a0))
        elif shape == 2:
            formulas.append(ctx.mk_or(a0, atom()))
        else:
            b = draw(st.sampled_from(env.bools))
            formulas.append(ctx.mk_ite(b, a0, atom()))
    return env, formulas


@settings(max_examples=25, deadline=None)
@given(data=_arith_tactic_cases())
def test_arith_tactic_pipeline_matches_z3_and_validates_models(
    data: tuple[_ArithEnv, list[Expr]],
) -> None:
    env, formulas = data
    pipeline = Then(
        NNFTactic(),
        CtxSimplifyTactic(),
        GaussianElimTactic(),
        PropagateBoundsTactic(),
        SimplifyTactic(),
    )
    tactic_res, tactic_model = solve_with_tactic(formulas, pipeline, ctx=env.ctx)

    direct = SMTSolver(env.ctx)
    direct.add(*formulas)
    direct_res = direct.check()

    z3_solver = z3.Solver()
    for formula in formulas:
        z3_solver.add(_expr_to_z3(formula, env.z3_vars))
    z3_res = z3_solver.check()

    expected = SolveResult.SAT if z3_res == z3.sat else SolveResult.UNSAT
    assert tactic_res is expected
    assert direct_res is expected

    if expected is SolveResult.SAT:
        assert tactic_model is not None
        for formula in formulas:
            assert tactic_model.eval_bool(formula, model_completion=True) is True
    else:
        assert tactic_model is None


@st.composite
def _skolem_cases(
    draw: st.DrawFn,
) -> tuple[
    Context,
    list[Expr],
    dict[FuncDecl, z3.ExprRef],
    dict[FuncDecl, z3.FuncDeclRef],
    dict[str, z3.SortRef],
]:
    ctx = Context()
    sort_s = ctx.mk_uninterpreted_sort("S")
    zs = z3.DeclareSort("S")

    consts = tuple(ctx.mk_const(n, sort_s) for n in ("a", "b", "c"))
    f_decl = ctx.mk_decl("f", (sort_s,), sort_s)
    p_decl = ctx.mk_decl("P", (sort_s,), ctx.bool_sort)
    q_decl = ctx.mk_decl("Q", (sort_s,), ctx.bool_sort)

    z3_vars: dict[FuncDecl, z3.ExprRef] = {c.decl: z3.Const(c.decl.name, zs) for c in consts}
    z3_funcs: dict[FuncDecl, z3.FuncDeclRef] = {
        f_decl: z3.Function("f", zs, zs),
        p_decl: z3.Function("P", zs, z3.BoolSort()),
        q_decl: z3.Function("Q", zs, z3.BoolSort()),
    }

    x = ctx.mk_const("qv", sort_s)
    formulas: list[Expr] = []

    n_ground = draw(st.integers(min_value=1, max_value=4))
    for _ in range(n_ground):
        c1, c2 = draw(st.sampled_from(consts)), draw(st.sampled_from(consts))
        choice = draw(st.integers(min_value=0, max_value=3))
        if choice == 0:
            formulas.append(ctx.mk_app(p_decl, c1))
        elif choice == 1:
            formulas.append(ctx.mk_not(ctx.mk_app(p_decl, c1)))
        elif choice == 2:
            formulas.append(ctx.mk_eq(ctx.mk_app(f_decl, c1), c2))
        else:
            formulas.append(ctx.mk_not(ctx.mk_eq(c1, c2)))

    n_exist = draw(st.integers(min_value=1, max_value=2))
    for _ in range(n_exist):
        target = draw(st.sampled_from(consts))
        body_choice = draw(st.integers(min_value=0, max_value=2))
        if body_choice == 0:
            body = ctx.mk_and(ctx.mk_app(p_decl, x), ctx.mk_eq(ctx.mk_app(f_decl, x), target))
            ex = ctx.mk_exists([x], body)
        elif body_choice == 1:
            body = ctx.mk_and(ctx.mk_app(p_decl, x), ctx.mk_not(ctx.mk_app(p_decl, x)))
            ex = ctx.mk_exists([x], body)
        else:
            # Test NNF pushing Not into ForAll -> Exists before SkolemizeTactic.
            inner = ctx.mk_implies(ctx.mk_app(p_decl, x), ctx.mk_app(q_decl, target))
            ex = ctx.mk_not(ctx.mk_forall([x], inner))
        formulas.append(ex)

    return ctx, formulas, z3_vars, z3_funcs, {"S": zs}


@settings(max_examples=25, deadline=None)
@given(data=_skolem_cases())
def test_skolemize_tactic_matches_z3_and_strips_internal_decls(
    data: tuple[
        Context,
        list[Expr],
        dict[FuncDecl, z3.ExprRef],
        dict[FuncDecl, z3.FuncDeclRef],
        dict[str, z3.SortRef],
    ],
) -> None:
    ctx, formulas, z3_vars, z3_funcs, z3_sorts = data
    pipeline = Then(NNFTactic(), SkolemizeTactic())
    res, model = solve_with_tactic(formulas, pipeline, ctx=ctx)

    z3_solver = z3.Solver()
    for formula in formulas:
        z3_solver.add(_expr_to_z3(formula, z3_vars, z3_funcs=z3_funcs, z3_sorts=z3_sorts))
    z3_res = z3_solver.check()

    if z3_res == z3.sat:
        assert res is not SolveResult.UNSAT
    elif z3_res == z3.unsat:
        assert res is not SolveResult.SAT

    if res is SolveResult.SAT:
        assert model is not None
        assert not any(decl.name.startswith("sk!") for decl in model.decls())
        for formula in formulas:
            if not has_quantifiers(formula):
                assert model.eval_bool(formula, model_completion=True) is True
