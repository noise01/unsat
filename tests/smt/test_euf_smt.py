import unsat
from unsat.model import FuncInterp
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import Context, collect_func_decls
from unsat.tactics import NNFTactic, to_nnf


def test_euf_smt_congruence_and_cycles() -> None:
    ctx = Context()
    s_sort = ctx.mk_uninterpreted_sort("S")
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    a, b, c, d = (ctx.mk_const(name, s_sort) for name in ("a", "b", "c", "d"))

    # Diamond Boolean choice over equalities: (a=b | a=c), b=d, c=d, f(a) != f(d)
    solver = SMTSolver(ctx)
    solver.add(
        ctx.mk_or(ctx.mk_eq(a, b), ctx.mk_eq(a, c)),
        ctx.mk_eq(b, d),
        ctx.mk_eq(c, d),
        ctx.mk_not(ctx.mk_eq(f(a), f(d))),
    )
    assert solver.check() is SolveResult.UNSAT

    # Classic cycle puzzle: f^3(a) = a & f^2(a) = a & f(a) != a -> UNSAT
    solver.reset()
    f3 = f(f(f(a)))
    f2 = f(f(a))
    solver.add(
        ctx.mk_eq(f3, a),
        ctx.mk_eq(f2, a),
        ctx.mk_not(ctx.mk_eq(f(a), a)),
    )
    assert solver.check() is SolveResult.UNSAT

    # Cycle of length 2 alone is SAT: f(f(a)) = a & f(a) != a
    solver.reset()
    f2_formula = ctx.mk_and(ctx.mk_eq(f2, a), ctx.mk_not(ctx.mk_eq(f(a), a)))
    solver.add(f2_formula)
    assert solver.check() is SolveResult.SAT
    model = solver.model()
    assert model.eval_bool(f2_formula)
    assert model.has_func_interp(f)
    assert isinstance(model.func_interp(f), FuncInterp)
    assert set(collect_func_decls(f2_formula)) == {f, a.decl}


def test_euf_smt_distinct_and_ite_axioms() -> None:
    ctx = Context()
    s_sort = ctx.mk_uninterpreted_sort("S")
    f = ctx.mk_decl("f", (s_sort,), s_sort)
    a, b, c = (ctx.mk_const(name, s_sort) for name in ("a", "b", "c"))
    p = ctx.mk_bool("p")

    # Non-Bool Distinct
    solver = SMTSolver(ctx)
    solver.add(ctx.mk_distinct(a, b, c), ctx.mk_or(ctx.mk_eq(a, b), ctx.mk_eq(b, c)))
    assert solver.check() is SolveResult.UNSAT

    solver.reset()
    neg_dist = ctx.mk_and(
        ctx.mk_not(ctx.mk_distinct(a, b, c)),
        ctx.mk_not(ctx.mk_eq(a, b)),
        ctx.mk_not(ctx.mk_eq(b, c)),
    )
    solver.add(neg_dist)
    assert solver.check() is SolveResult.SAT
    model = solver.model()
    assert model.eval_bool(neg_dist)
    assert model.eval_bool(ctx.mk_eq(a, c))

    # Non-Bool ITE inside function app
    solver.reset()
    ite_term = ctx.mk_ite(p, a, b)
    solver.add(
        ctx.mk_not(ctx.mk_eq(f(ite_term), f(a))),
        ctx.mk_not(ctx.mk_eq(f(ite_term), f(b))),
    )
    assert solver.check() is SolveResult.UNSAT

    solver.reset()
    sat_ite = ctx.mk_and(
        ctx.mk_eq(f(ite_term), f(b)),
        ctx.mk_not(ctx.mk_eq(a, b)),
        ctx.mk_not(ctx.mk_eq(f(a), f(b))),
    )
    solver.add(sat_ite)
    assert solver.check() is SolveResult.SAT
    m2 = solver.model()
    assert m2[p] is False
    assert m2.eval_bool(sat_ite)


def test_euf_smt_bool_args_predicates_level0_catchup_and_assumptions() -> None:
    ctx = Context()
    s_sort = ctx.mk_uninterpreted_sort("S")
    h = ctx.mk_decl("h", (ctx.bool_sort,), s_sort)
    pred = ctx.mk_decl("P", (s_sort,), ctx.bool_sort)
    a = ctx.mk_const("a", s_sort)
    b = ctx.mk_const("b", s_sort)
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")

    # Level-0 unit propagation on p BEFORE h(p) is ever mentioned.
    solver = SMTSolver(ctx)
    solver.add(p)
    assert solver.check() is SolveResult.SAT
    solver.add(q, ctx.mk_not(ctx.mk_eq(h(ctx.mk_and(p, q)), h(ctx.mk_true()))))
    assert solver.check() is SolveResult.UNSAT

    # Eq inside Bool arg of h: (= a b) => h(= a b) = h(true)
    solver.reset()
    eq_ab = ctx.mk_eq(a, b)
    solver.add(eq_ab, ctx.mk_not(ctx.mk_eq(h(eq_ab), h(ctx.mk_true()))))
    assert solver.check() is SolveResult.UNSAT

    # Negative Bool arg Not(p)
    solver.reset()
    solver.add(ctx.mk_not(p), ctx.mk_not(ctx.mk_eq(h(ctx.mk_not(p)), h(ctx.mk_true()))))
    assert solver.check() is SolveResult.UNSAT

    # Predicate congruence + push/pop + assumptions + unsat_core
    solver.reset()
    solver.add(pred(a))
    solver.push()
    a1 = ctx.mk_eq(a, b)
    a2 = ctx.mk_not(pred(b))
    a3 = ctx.mk_eq(h(p), h(ctx.mk_true()))
    assert solver.check(a1, a2, a3) is SolveResult.UNSAT
    core = solver.unsat_core()
    assert a3 not in core
    assert set(core) <= {a1, a2}
    solver.pop(1)

    stats = solver.statistics()
    assert "conflicts" in stats
    assert "theory_merges" in stats


def test_euf_tactics_nnf_and_public_api_dsl() -> None:
    unsat.reset_default_context()
    sort_s = unsat.DeclareSort("S")
    sort_t = unsat.DeclareSort("T")
    a, b = unsat.Constants("a b", sort_s)
    f = unsat.Function("f", sort_s, sort_t)
    p = unsat.Bool("p")

    formula = unsat.Implies(
        unsat.And(unsat.Eq(a, b), p),
        unsat.Or(unsat.Eq(f(a), f(b)), unsat.Distinct(a, b)),
    )
    nnf = to_nnf(formula)
    tactic_res = NNFTactic().apply([formula])
    assert len(tactic_res.formulas) == 1
    assert tactic_res.formulas[0] is nnf
    assert to_nnf(unsat.Not(unsat.Distinct(a, b))) is unsat.Not(unsat.Distinct(a, b))
    assert to_nnf(unsat.Not(unsat.Eq(a, b))) is unsat.Not(unsat.Eq(a, b))

    solver = unsat.Solver()
    solver.add(unsat.Not(nnf))
    assert solver.check() is unsat.UNSAT

    # Constrain constant against domain value directly via Context.mk_domain_val
    ctx = unsat.default_context()
    v0 = ctx.mk_domain_val(sort_s, 0)
    v1 = ctx.mk_domain_val(sort_s, 1)
    solver2 = unsat.Solver()
    solver2.add(unsat.Or(unsat.Eq(a, v0), unsat.Eq(a, v1)), unsat.Distinct(a, v0, v1))
    assert solver2.check() is unsat.UNSAT
