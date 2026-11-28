from collections.abc import Sequence

import pytest

from unsat.model import Model
from unsat.quantifiers import (
    EMatcher,
    MBQIEngine,
    QuantifierBudget,
    QuantifierStats,
    SubSolverStatus,
    extract_patterns,
)
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context, Expr, Quantifier
from unsat.theories import EUFSolver


class _MockSubSolver:
    def __init__(self, ctx: Context, *, force_unknown: bool = False) -> None:
        self._ctx = ctx
        self._force_unknown = force_unknown

    def check_formula(self, formulas: Sequence[Expr]) -> tuple[SubSolverStatus, Model | None]:
        if self._force_unknown:
            return SubSolverStatus.UNKNOWN, None
        s = SMTSolver(self._ctx)
        s.add(*formulas)
        res = s.check()
        if res is SolveResult.SAT:
            return SubSolverStatus.SAT, s.model()
        if res is SolveResult.UNSAT:
            return SubSolverStatus.UNSAT, None
        return SubSolverStatus.UNKNOWN, None


def test_extract_patterns_and_ematching_modulo_euf() -> None:
    ctx = Context()
    s_sort = ctx.mk_uninterpreted_sort("S")
    x = ctx.mk_const("x", s_sort)
    y = ctx.mk_const("y", s_sort)
    a = ctx.mk_const("a", s_sort)
    b = ctx.mk_const("b", s_sort)
    c = ctx.mk_const("c", s_sort)
    d = ctx.mk_const("d", s_sort)
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    g = ctx.mk_decl("g", (s_sort,), s_sort)
    h2 = ctx.mk_decl("h2", (s_sort, s_sort), ctx.bool_sort)
    p = ctx.mk_decl("P", (s_sort,), ctx.bool_sort)

    # Explicit pattern preserved; single minimal trigger chosen over compound enclosing;
    # multi-pattern constructed for separate unary triggers; empty for pure arithmetic.
    q_exp = ctx.mk_forall((x,), p(f(g(x))), patterns=(f(g(x)),))
    assert isinstance(q_exp, Quantifier)
    assert len(extract_patterns(q_exp)) == 1

    q_auto = ctx.mk_forall((x,), ctx.mk_eq(f(g(x)), x))
    assert isinstance(q_auto, Quantifier)
    auto_pats = extract_patterns(q_auto)
    assert len(auto_pats) >= 1
    assert auto_pats[0] == (g(ctx.mk_bound_var(0, s_sort)),)

    q_multi = ctx.mk_forall((x, y), ctx.mk_implies(p(x), ctx.mk_eq(g(y), x)))
    assert isinstance(q_multi, Quantifier)
    multi_pats = extract_patterns(q_multi)
    assert multi_pats
    assert len(multi_pats[0]) == 2

    ix = ctx.mk_int("ix")
    q_arith = ctx.mk_forall((ix,), ix > ctx.mk_int_val(0))
    assert isinstance(q_arith, Quantifier)
    assert extract_patterns(q_arith) == ()

    # Modulo-EUF E-matching: pattern f(g(x)) matches f(c) when g(a) == c.
    euf = EUFSolver(ctx)
    euf.register_term(g(a))
    euf.register_term(f(c))
    euf.register_term(d)
    euf.assert_atom(ctx.mk_eq(g(a), c), True)
    euf.assert_atom(ctx.mk_eq(f(c), d), True)
    euf.propagate()

    matcher = EMatcher()
    stats = QuantifierStats()
    budget = QuantifierBudget(max_matches=8, max_ematch_depth=2)
    res1 = matcher.match_round(euf, (q_exp,), budget, stats)
    assert len(res1.instantiations) == 1
    assert res1.instantiations[0][1] == (a,)
    assert res1.instantiations[0][2] is p(f(g(a)))

    # Nonlinear pattern h2(x, x) only matches h2(a, b) after merging a == b.
    q_nl = ctx.mk_forall((x,), h2(x, x))
    assert isinstance(q_nl, Quantifier)
    euf.register_bool_term(h2(a, b))
    res_no = matcher.match_round(euf, (q_nl,), budget, stats)
    assert not res_no.instantiations
    euf.assert_atom(ctx.mk_eq(a, b), True)
    euf.propagate()
    res_yes = matcher.match_round(euf, (q_nl,), budget, stats)
    assert len(res_yes.instantiations) == 1

    # Matching loop bound: truncates at max_matches=1 and max_ematch_depth=0.
    q_loop = ctx.mk_forall((x,), ctx.mk_eq(g(x), g(g(x))))
    assert isinstance(q_loop, Quantifier)
    euf.register_term(g(g(a)))
    match_budget = QuantifierBudget(max_matches=1, max_ematch_depth=2)
    res_trunc = matcher.match_round(euf, (q_loop,), match_budget, stats)
    assert res_trunc.truncated is True
    assert stats.budget_exhausted >= 1

    zero_depth = QuantifierBudget(max_matches=8, max_ematch_depth=0)
    res_depth = matcher.match_round(euf, (q_loop,), zero_depth, stats)
    assert res_depth.truncated is True
    assert not res_depth.instantiations


def test_mbqi_engine_verification_generalization_and_unknown() -> None:
    ctx = Context()
    s_sort = ctx.mk_uninterpreted_sort("S")
    u0 = ctx.mk_domain_val(s_sort, 0)
    a = ctx.mk_const("a", s_sort)
    p = ctx.mk_decl("P", (s_sort,), ctx.bool_sort)
    q = ctx.mk_forall((ctx.mk_const("x", s_sort),), p(ctx.mk_const("x", s_sort)))
    assert isinstance(q, Quantifier)

    euf = EUFSolver(ctx)
    euf.register_term(a)
    euf.register_bool_term(p(a))
    euf.assert_atom(p(a), True)
    euf.propagate()

    # Finite-universe S={u0} already verifies on P(u0)=True.
    ground_model = euf.build_model()
    mbqi = MBQIEngine()
    stats = QuantifierStats()
    res_fin = mbqi.check_and_refine(
        (q,),
        ground_model,
        euf,
        _MockSubSolver(ctx),
        QuantifierBudget(),
        stats,
    )
    assert res_fin.verified is True

    # Over infinite Int domain with P_i(0)=True and default else=False,
    # MBQI candidate #1 generalizes else_value to True and verifies.
    pi = ctx.mk_decl("Pi", (ctx.int_sort,), ctx.bool_sort)
    ix = ctx.mk_int("ix")
    q_int = ctx.mk_forall((ix,), pi(ix))
    assert isinstance(q_int, Quantifier)
    euf_int = EUFSolver(ctx)
    euf_int.register_bool_term(pi(ctx.mk_int_val(0)))
    euf_int.assert_atom(pi(ctx.mk_int_val(0)), True)
    euf_int.propagate()
    res = mbqi.check_and_refine(
        (q_int,),
        euf_int.build_model(),
        euf_int,
        _MockSubSolver(ctx),
        QuantifierBudget(),
        stats,
    )
    assert res.verified is True
    assert res.model is not None
    assert stats.mbqi_verified >= 2
    assert res.model.func_interp(pi).else_value is ctx.true_expr

    # Sub-solver returning UNKNOWN never claims verified=True.
    res_unk = mbqi.check_and_refine(
        (q,),
        Model(ctx, {a.decl: u0}, universes={s_sort: (u0,)}),
        euf,
        _MockSubSolver(ctx, force_unknown=True),
        QuantifierBudget(),
        stats,
    )
    assert res_unk.verified is False


def test_ematch_candidate_work_budget_bounds_and_validation() -> None:
    ctx = Context()
    s_sort = ctx.mk_uninterpreted_sort("S")
    x = ctx.mk_const("x", s_sort)
    consts = [ctx.mk_const(f"c{i}", s_sort) for i in range(6)]
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    g = ctx.mk_decl("g", (s_sort,), s_sort)
    h2 = ctx.mk_decl("h2", (s_sort, s_sort), ctx.bool_sort)
    p = ctx.mk_decl("P", (s_sort,), ctx.bool_sort)

    # 1. Pathological non-emitting nonlinear candidates still stop at max_matches.
    euf_nl = EUFSolver(ctx)
    for i in range(0, len(consts), 2):
        euf_nl.register_bool_term(h2(consts[i], consts[i + 1]))
    euf_nl.propagate()
    q_nl = ctx.mk_forall((x,), h2(x, x))
    assert isinstance(q_nl, Quantifier)
    matcher_nl = EMatcher()
    stats_nl = QuantifierStats()
    res_nl = matcher_nl.match_round(euf_nl, (q_nl,), QuantifierBudget(max_matches=2), stats_nl)
    assert res_nl.instantiations == ()
    assert res_nl.truncated is True
    assert res_nl.matches_used == 2
    assert stats_nl.ematch_candidates == 2
    assert stats_nl.budget_exhausted == 1

    # 2. Nested E-class member scan in f(g(x)) consumes candidate budget.
    euf_nested = EUFSolver(ctx)
    anchor = consts[0]
    euf_nested.register_term(f(anchor))
    for c in consts[1:]:
        euf_nested.register_term(c)
        euf_nested.assert_atom(ctx.mk_eq(c, anchor), True)
    euf_nested.propagate()
    q_nested = ctx.mk_forall((x,), p(f(g(x))), patterns=(f(g(x)),))
    assert isinstance(q_nested, Quantifier)
    matcher_nested = EMatcher()
    stats_nested = QuantifierStats()
    res_nested = matcher_nested.match_round(euf_nested, (q_nested,), QuantifierBudget(max_matches=3), stats_nested)
    assert res_nested.instantiations == ()
    assert res_nested.truncated is True
    assert res_nested.matches_used == 3
    assert stats_nested.ematch_candidates == 3

    # 3. Exact-fit budget does not falsely truncate, while overflow truncates.
    euf_fit = EUFSolver(ctx)
    euf_fit.register_bool_term(p(consts[0]))
    euf_fit.propagate()
    q_p = ctx.mk_forall((x,), p(x), patterns=(p(x),))
    assert isinstance(q_p, Quantifier)
    stats_fit = QuantifierStats()
    res_fit = EMatcher().match_round(euf_fit, (q_p,), QuantifierBudget(max_matches=1), stats_fit)
    assert len(res_fit.instantiations) == 1
    assert res_fit.truncated is False
    assert res_fit.matches_used == 1
    assert stats_fit.ematch_candidates == 1

    euf_fit.register_bool_term(p(consts[1]))
    euf_fit.propagate()
    stats_over = QuantifierStats()
    res_over = EMatcher().match_round(euf_fit, (q_p,), QuantifierBudget(max_matches=1), stats_over)
    assert len(res_over.instantiations) == 1
    assert res_over.truncated is True
    assert res_over.matches_used == 1
    assert stats_over.ematch_candidates == 1

    # 4. Explicit max_matches validation on match_round.
    with pytest.raises(ValueError, match="max_matches"):
        EMatcher().match_round(euf_fit, (q_p,), QuantifierBudget(), stats_over, max_matches=-1)
    with pytest.raises(ValueError, match="max_matches"):
        EMatcher().match_round(euf_fit, (q_p,), QuantifierBudget(), stats_over, max_matches=True)
