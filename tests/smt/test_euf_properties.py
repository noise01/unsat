"""Property-based & Z3 differential tests for QF_UF (EUF + Online CDCL(T))."""

from typing import NamedTuple

import z3
from hypothesis import given, settings
from hypothesis import strategies as st

from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl, Sort, SortKind


class _Signature(NamedTuple):
    ctx: Context
    z3_sorts: dict[Sort, z3.SortRef]
    z3_decls: dict[FuncDecl, z3.FuncDeclRef]
    bool_vars: tuple[App, ...]
    s_consts: tuple[App, ...]
    t_consts: tuple[App, ...]
    f_ss: FuncDecl
    g_st_s: FuncDecl
    h_bs: FuncDecl
    pred_s: FuncDecl
    pred_st: FuncDecl


def _build_signature() -> _Signature:
    ctx = Context()
    sort_s = ctx.mk_uninterpreted_sort("S")
    sort_t = ctx.mk_uninterpreted_sort("T")

    zs = z3.DeclareSort("S")
    zt = z3.DeclareSort("T")
    zb = z3.BoolSort()

    f_ss = ctx.mk_decl("f", (sort_s,), sort_s)
    g_st_s = ctx.mk_decl("g", (sort_s, sort_t), sort_s)
    h_bs = ctx.mk_decl("h", (ctx.bool_sort,), sort_s)
    pred_s = ctx.mk_decl("P", (sort_s,), ctx.bool_sort)
    pred_st = ctx.mk_decl("Q", (sort_s, sort_t), ctx.bool_sort)

    z3_decls: dict[FuncDecl, z3.FuncDeclRef] = {
        f_ss: z3.Function("f", zs, zs),
        g_st_s: z3.Function("g", zs, zt, zs),
        h_bs: z3.Function("h", zb, zs),
        pred_s: z3.Function("P", zs, zb),
        pred_st: z3.Function("Q", zs, zt, zb),
    }

    bool_vars = tuple(ctx.mk_bool(n) for n in ("p0", "p1", "p2"))
    for bv in bool_vars:
        z3_decls[bv.decl] = z3.Bool(bv.name).decl()

    s_consts = tuple(ctx.mk_const(n, sort_s) for n in ("s0", "s1", "s2", "s3"))
    for sc in s_consts:
        z3_decls[sc.decl] = z3.Const(sc.name, zs).decl()

    t_consts = tuple(ctx.mk_const(n, sort_t) for n in ("t0", "t1", "t2"))
    for tc in t_consts:
        z3_decls[tc.decl] = z3.Const(tc.name, zt).decl()

    return _Signature(
        ctx=ctx,
        z3_sorts={sort_s: zs, sort_t: zt},
        z3_decls=z3_decls,
        bool_vars=bool_vars,
        s_consts=s_consts,
        t_consts=t_consts,
        f_ss=f_ss,
        g_st_s=g_st_s,
        h_bs=h_bs,
        pred_s=pred_s,
        pred_st=pred_st,
    )


def _to_z3(expr: Expr, sig: _Signature) -> z3.ExprRef:
    memo: dict[Expr, z3.ExprRef] = {}
    stack: list[tuple[Expr, bool]] = [(expr, False)]
    while stack:
        node, expanded = stack.pop()
        if node in memo:
            continue
        if isinstance(node, Const):
            assert isinstance(node.value, bool)
            memo[node] = z3.BoolVal(node.value)
            continue
        assert isinstance(node, App)
        if not node.args:
            memo[node] = (
                z3.Const(node.decl.name, sig.z3_sorts[node.sort])
                if (node.sort.kind is SortKind.UNINTERPRETED)
                else z3.Bool(node.decl.name)
            )
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
            case DeclKind.UNINTERPRETED:
                memo[node] = sig.z3_decls[node.decl](*zargs)
    return memo[expr]


@st.composite
def _qf_uf_formulas(
    draw: st.DrawFn,
) -> tuple[_Signature, list[Expr]]:
    sig = _build_signature()
    ctx = sig.ctx

    s_pool: list[Expr] = list(sig.s_consts)
    t_pool: list[Expr] = list(sig.t_consts)
    b_atoms: list[Expr] = list(sig.bool_vars)

    # Grow uninterpreted term DAG bottom-up.
    num_terms = draw(st.integers(min_value=2, max_value=8))
    for _ in range(num_terms):
        choice = draw(st.integers(min_value=0, max_value=4))
        if choice == 0:
            s_pool.append(sig.f_ss(draw(st.sampled_from(s_pool))))
        elif choice == 1:
            s_pool.append(
                sig.g_st_s(
                    draw(st.sampled_from(s_pool)),
                    draw(st.sampled_from(t_pool)),
                )
            )
        elif choice == 2:
            b_arg = draw(st.sampled_from([ctx.mk_true(), ctx.mk_false(), *b_atoms]))
            s_pool.append(sig.h_bs(b_arg))
        elif choice == 3:
            b_atoms.append(sig.pred_s(draw(st.sampled_from(s_pool))))
        else:
            b_atoms.append(
                sig.pred_st(
                    draw(st.sampled_from(s_pool)),
                    draw(st.sampled_from(t_pool)),
                )
            )

    # Optionally include a non-Bool ITE term inside the S pool.
    if draw(st.booleans()):
        cond = draw(st.sampled_from(b_atoms))
        s_ite = ctx.mk_ite(
            cond,
            draw(st.sampled_from(s_pool)),
            draw(st.sampled_from(s_pool)),
        )
        s_pool.append(s_ite)
        if draw(st.booleans()):
            s_pool.append(sig.f_ss(s_ite))

    def _rand_atom() -> Expr:
        kind = draw(st.integers(min_value=0, max_value=4))
        if kind <= 1:
            lhs = draw(st.sampled_from(s_pool))
            rhs = draw(st.sampled_from(s_pool))
            eq = ctx.mk_eq(lhs, rhs)
            return ctx.mk_not(eq) if draw(st.booleans()) else eq
        if kind == 2:
            lhs = draw(st.sampled_from(t_pool))
            rhs = draw(st.sampled_from(t_pool))
            return ctx.mk_eq(lhs, rhs)
        if kind == 3:
            k = draw(st.integers(min_value=2, max_value=4))
            args = [draw(st.sampled_from(s_pool)) for _ in range(k)]
            return ctx.mk_distinct(*args)
        atom = draw(st.sampled_from(b_atoms))
        return ctx.mk_not(atom) if draw(st.booleans()) else atom

    def _rand_bool(depth: int) -> Expr:
        if depth <= 0 or draw(st.integers(min_value=0, max_value=2)) == 0:
            return _rand_atom()
        op = draw(st.integers(min_value=0, max_value=6))
        if op == 0:
            return ctx.mk_not(_rand_bool(depth - 1))
        if op == 1:
            n_children = draw(st.integers(min_value=2, max_value=3))
            return ctx.mk_and(*(_rand_bool(depth - 1) for _ in range(n_children)))
        if op == 2:
            n_children = draw(st.integers(min_value=2, max_value=3))
            return ctx.mk_or(*(_rand_bool(depth - 1) for _ in range(n_children)))
        if op == 3:
            return ctx.mk_implies(_rand_bool(depth - 1), _rand_bool(depth - 1))
        if op == 4:
            return ctx.mk_xor(_rand_bool(depth - 1), _rand_bool(depth - 1))
        if op == 5:
            return ctx.mk_eq(_rand_bool(depth - 1), _rand_bool(depth - 1))
        return ctx.mk_ite(
            _rand_bool(depth - 1),
            _rand_bool(depth - 1),
            _rand_bool(depth - 1),
        )

    num_formulas = draw(st.integers(min_value=1, max_value=10))
    formulas = [_rand_bool(2) for _ in range(num_formulas)]
    return sig, formulas


def _z3_verdict(solver: z3.Solver) -> SolveResult:
    res = solver.check()
    if res == z3.sat:
        return SolveResult.SAT
    if res == z3.unsat:
        return SolveResult.UNSAT
    return SolveResult.UNKNOWN


@settings(max_examples=75, deadline=None)
@given(data=_qf_uf_formulas())
def test_euf_matches_z3_and_validates_models(
    data: tuple[_Signature, list[Expr]],
) -> None:
    sig, formulas = data
    usolver = SMTSolver(sig.ctx)
    zsolver = z3.Solver()

    for f in formulas:
        usolver.add(f)
        zsolver.add(_to_z3(f, sig))

    u_res = usolver.check()
    z_res = _z3_verdict(zsolver)
    assert u_res is z_res

    if u_res is SolveResult.SAT:
        model = usolver.model()
        for f in formulas:
            assert model.eval_bool(f, model_completion=True) is True


@settings(max_examples=40, deadline=None)
@given(
    f1=_qf_uf_formulas(),
    extra_idx=st.integers(min_value=0, max_value=3),
)
def test_euf_incremental_push_pop_and_assumptions_vs_z3(
    f1: tuple[_Signature, list[Expr]],
    extra_idx: int,
) -> None:
    sig, formulas = f1
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
    res_scoped = usolver.check()
    assert res_scoped is _z3_verdict(zsolver)
    if res_scoped is SolveResult.SAT:
        model = usolver.model()
        for f in [*base, *scoped]:
            assert model.eval_bool(f, model_completion=True) is True

    usolver.pop(1)
    zsolver.pop(1)

    # Check under assumptions on restored base scope.
    assumption = sig.ctx.mk_eq(
        sig.s_consts[0], sig.s_consts[extra_idx % len(sig.s_consts)]
    )
    neg_assumption = sig.ctx.mk_not(
        sig.ctx.mk_eq(
            sig.f_ss(sig.s_consts[0]),
            sig.f_ss(sig.s_consts[extra_idx % len(sig.s_consts)]),
        )
    )
    assumps = (assumption, neg_assumption) if scoped else (assumption,)
    u_a = usolver.check(*assumps)
    z_a = zsolver.check(*[_to_z3(a, sig) for a in assumps])
    expected = SolveResult.SAT if z_a == z3.sat else SolveResult.UNSAT
    assert u_a is expected
    if u_a is SolveResult.UNSAT:
        core = usolver.unsat_core()
        assert set(core) <= set(assumps)
        # Re-check that base assertions + unsat core alone remain UNSAT.
        check_core = SMTSolver(sig.ctx)
        check_core.add(*base, *core)
        assert check_core.check() is SolveResult.UNSAT
