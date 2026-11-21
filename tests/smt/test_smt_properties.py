from dataclasses import dataclass

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context, Expr
from unsat.tactics import simplify, to_nnf


@dataclass(frozen=True, slots=True)
class _NConst:
    value: bool


@dataclass(frozen=True, slots=True)
class _NVar:
    idx: int


@dataclass(frozen=True, slots=True)
class _NNot:
    arg: NFormula


@dataclass(frozen=True, slots=True)
class _NNAry:
    op: str
    args: tuple[NFormula, ...]


@dataclass(frozen=True, slots=True)
class _NBinary:
    op: str
    lhs: NFormula
    rhs: NFormula


@dataclass(frozen=True, slots=True)
class _NIte:
    cond: NFormula
    then_b: NFormula
    else_b: NFormula


type NFormula = _NConst | _NVar | _NNot | _NNAry | _NBinary | _NIte


def _formula_strategy(num_vars: int) -> st.SearchStrategy[NFormula]:
    leaves: st.SearchStrategy[NFormula] = st.one_of(
        st.builds(_NConst, st.booleans()),
        st.builds(_NVar, st.integers(min_value=0, max_value=num_vars - 1)),
    )

    def extend(children: st.SearchStrategy[NFormula]) -> st.SearchStrategy[NFormula]:
        return st.one_of(
            st.builds(_NNot, children),
            st.builds(
                _NNAry,
                st.sampled_from(["and", "or", "distinct"]),
                st.lists(children, min_size=0, max_size=4).map(tuple),
            ),
            st.builds(
                _NBinary,
                st.sampled_from(["implies", "xor", "eq"]),
                children,
                children,
            ),
            st.builds(_NIte, children, children, children),
        )

    return st.recursive(leaves, extend, max_leaves=16)


def _render_unsat(node: NFormula, ctx: Context, env: list[Expr]) -> Expr:
    match node:
        case _NConst(v):
            return ctx.mk_bool_val(v)
        case _NVar(i):
            return env[i]
        case _NNot(arg):
            return ctx.mk_not(_render_unsat(arg, ctx, env))
        case _NNAry("and", args):
            return ctx.mk_and(*(_render_unsat(a, ctx, env) for a in args))
        case _NNAry("or", args):
            return ctx.mk_or(*(_render_unsat(a, ctx, env) for a in args))
        case _NNAry("distinct", args):
            return ctx.mk_distinct(*(_render_unsat(a, ctx, env) for a in args))
        case _NBinary("implies", lhs, rhs):
            return ctx.mk_implies(
                _render_unsat(lhs, ctx, env), _render_unsat(rhs, ctx, env)
            )
        case _NBinary("xor", lhs, rhs):
            return ctx.mk_xor(
                _render_unsat(lhs, ctx, env), _render_unsat(rhs, ctx, env)
            )
        case _NBinary("eq", lhs, rhs):
            return ctx.mk_eq(_render_unsat(lhs, ctx, env), _render_unsat(rhs, ctx, env))
        case _NIte(c, t, e):
            return ctx.mk_ite(
                _render_unsat(c, ctx, env),
                _render_unsat(t, ctx, env),
                _render_unsat(e, ctx, env),
            )
    msg = f"Unexpected formula node: {node!r}"
    raise TypeError(msg)


def _render_z3(node: NFormula, env: list[z3.BoolRef]) -> z3.BoolRef:
    match node:
        case _NConst(v):
            return z3.BoolVal(v)
        case _NVar(i):
            return env[i]
        case _NNot(arg):
            return z3.Not(_render_z3(arg, env))
        case _NNAry("and", args):
            return (
                z3.And([_render_z3(a, env) for a in args]) if args else z3.BoolVal(True)
            )
        case _NNAry("or", args):
            return (
                z3.Or([_render_z3(a, env) for a in args]) if args else z3.BoolVal(False)
            )
        case _NNAry("distinct", args):
            if len(args) <= 1:
                return z3.BoolVal(True)
            if len(args) >= 3:
                return z3.BoolVal(False)
            return z3.Distinct(_render_z3(args[0], env), _render_z3(args[1], env))
        case _NBinary("implies", lhs, rhs):
            return z3.Implies(_render_z3(lhs, env), _render_z3(rhs, env))
        case _NBinary("xor", lhs, rhs):
            return z3.Xor(_render_z3(lhs, env), _render_z3(rhs, env))
        case _NBinary("eq", lhs, rhs):
            return _render_z3(lhs, env) == _render_z3(rhs, env)
        case _NIte(c, t, e):
            res = z3.If(_render_z3(c, env), _render_z3(t, env), _render_z3(e, env))
            assert isinstance(res, z3.BoolRef)
            return res
    msg = f"Unexpected formula node: {node!r}"
    raise TypeError(msg)


def _z3_verdict(res: z3.CheckSatResult) -> SolveResult:
    if res == z3.sat:
        return SolveResult.SAT
    if res == z3.unsat:
        return SolveResult.UNSAT
    return SolveResult.UNKNOWN


@settings(max_examples=80, deadline=None)
@given(num_vars=st.integers(min_value=1, max_value=8), data=st.data())
def test_qf_bool_simplify_nnf_and_solver_match_z3(
    num_vars: int, data: st.DataObject
) -> None:
    formulas = data.draw(st.lists(_formula_strategy(num_vars), min_size=1, max_size=6))

    ctx = Context()
    u_vars: list[Expr] = [ctx.mk_bool(f"b_{i}") for i in range(num_vars)]
    z_vars = [z3.Bool(f"b_{i}") for i in range(num_vars)]

    u_formulas = [_render_unsat(f, ctx, u_vars) for f in formulas]
    z_formulas = [_render_z3(f, z_vars) for f in formulas]

    # Check single-formula equivalence of simplify() and to_nnf() inside unsat
    # (and verify their SAT/UNSAT behavior matches Z3 right below).
    f0_u = u_formulas[0]
    for transformed in (simplify(f0_u), to_nnf(f0_u)):
        equiv_solver = SMTSolver(ctx)
        equiv_solver.add(ctx.mk_not(ctx.mk_eq(f0_u, transformed)))
        assert equiv_solver.check() is SolveResult.UNSAT

    solver = SMTSolver(ctx)
    solver.add(*u_formulas)
    verdict = solver.check()

    z_solver = z3.Solver()
    z_solver.add(*z_formulas)
    expected = _z3_verdict(z_solver.check())
    assert verdict is expected

    if verdict is SolveResult.SAT:
        model = solver.model()
        for f in u_formulas:
            assert model.eval_bool(f) is True


@settings(max_examples=50, deadline=None)
@given(num_vars=st.integers(min_value=2, max_value=7), data=st.data())
def test_incremental_push_pop_assumptions_match_z3(
    num_vars: int, data: st.DataObject
) -> None:
    ctx = Context()
    u_vars: list[Expr] = [ctx.mk_bool(f"p_{i}") for i in range(num_vars)]
    z_vars = [z3.Bool(f"p_{i}") for i in range(num_vars)]

    solver = SMTSolver(ctx)
    z_solver = z3.Solver()
    scope_depth = 0

    ops = data.draw(
        st.lists(
            st.sampled_from(["add", "push", "pop", "check"]),
            min_size=4,
            max_size=18,
        )
    )
    f_strat = _formula_strategy(num_vars)

    for op in ops:
        if op == "add":
            nf = data.draw(f_strat)
            solver.add(_render_unsat(nf, ctx, u_vars))
            z_solver.add(_render_z3(nf, z_vars))
        elif op == "push":
            solver.push()
            z_solver.push()
            scope_depth += 1
        elif op == "pop":
            if scope_depth > 0:
                solver.pop()
                z_solver.pop()
                scope_depth -= 1
        else:
            n_assumps = data.draw(st.lists(f_strat, min_size=0, max_size=4))
            u_assumps = [_render_unsat(nf, ctx, u_vars) for nf in n_assumps]
            z_assumps = [_render_z3(nf, z_vars) for nf in n_assumps]

            verdict = solver.check(*u_assumps)
            expected = _z3_verdict(z_solver.check(*z_assumps))
            assert verdict is expected

            if verdict is SolveResult.SAT:
                model = solver.model()
                assert solver.unsat_core() == []
                for f in solver.assertions():
                    assert model.eval_bool(f) is True
                for a in u_assumps:
                    assert model.eval_bool(a) is True
            else:
                core = solver.unsat_core()
                assert set(core) <= set(u_assumps)
                # Re-verify extracted core soundness in a fresh solver.
                recheck = SMTSolver(ctx)
                recheck.add(*solver.assertions())
                assert recheck.check(*core) is SolveResult.UNSAT

            # Reused solver must agree with a fresh solver on current state.
            fresh = SMTSolver(ctx)
            fresh.add(*solver.assertions())
            assert fresh.check(*u_assumps) is verdict
