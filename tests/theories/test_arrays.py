from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import App, Context, DeclKind
from unsat.theories import ArraySolver, EUFSolver


def test_array_solver_row_and_const_lemmas() -> None:
    ctx = Context()
    arr_sort = ctx.mk_array_sort(ctx.int_sort, ctx.int_sort)
    a = ctx.mk_const("a", arr_sort)
    b = ctx.mk_const("b", arr_sort)
    i = ctx.mk_int("i")
    j = ctx.mk_int("j")

    # 1. RoW1 & RoW2-down on s = store(a, i, 5), select(b, j) with b == s
    euf = EUFSolver(ctx)
    arr_solver = ArraySolver(ctx)
    st = ctx.mk_store(a, i, ctx.mk_int_val(5))
    sel_bj = ctx.mk_select(b, j)
    for t in (st, sel_bj):
        euf.register_term(t)
        arr_solver.register_term(t)

    euf.push()
    euf.assert_atom(ctx.mk_eq(b, st), True)
    euf.assert_atom(ctx.mk_eq(i, j), True)
    euf.propagate()
    lemmas_row1 = arr_solver.check(euf)
    assert lemmas_row1
    target_row1 = ctx.mk_eq(sel_bj, ctx.mk_int_val(5))
    assert any(lm.formula is target_row1 for lm in lemmas_row1)
    assert arr_solver.stats.row1_lemmas >= 1
    euf.pop(1)

    # Without i == j, emits RoW2 disjunction (i == j) \/ (select(b, j) == select(a, j))
    euf.push()
    euf.assert_atom(ctx.mk_eq(b, st), True)
    euf.propagate()
    lemmas_row2 = arr_solver.check(euf)
    assert lemmas_row2
    expected_row2 = ctx.mk_or(ctx.mk_eq(i, j), ctx.mk_eq(sel_bj, ctx.mk_select(a, j)))
    assert any(lm.formula is expected_row2 for lm in lemmas_row2)
    assert arr_solver.stats.row2_lemmas >= 1
    euf.pop(1)

    # 2. ConstArray chain check: store(K(0), i, 5) == K(5) -> 0 == 5 (UNSAT)
    euf2 = EUFSolver(ctx)
    arr2 = ArraySolver(ctx)
    k0 = ctx.mk_const_array(ctx.int_sort, ctx.mk_int_val(0))
    k5 = ctx.mk_const_array(ctx.int_sort, ctx.mk_int_val(5))
    stk = ctx.mk_store(k0, i, ctx.mk_int_val(5))
    for t in (stk, k5):
        euf2.register_term(t)
        arr2.register_term(t)
    euf2.assert_atom(ctx.mk_eq(stk, k5), True)
    euf2.propagate()
    const_lemmas = arr2.check(euf2)
    assert any(lm.formula is ctx.false_expr for lm in const_lemmas)
    assert arr2.stats.const_lemmas >= 1


def test_array_solver_extensionality_and_store_chain_model() -> None:
    ctx = Context()
    arr_sort = ctx.mk_array_sort(ctx.int_sort, ctx.int_sort)
    a = ctx.mk_const("a", arr_sort)
    b = ctx.mk_const("b", arr_sort)
    euf = EUFSolver(ctx)
    arr_solver = ArraySolver(ctx)
    euf.register_term(a)
    euf.register_term(b)
    arr_solver.register_term(a)
    arr_solver.register_term(b)
    euf.assert_atom(ctx.mk_eq(a, b), False)
    euf.propagate()
    ext_lemmas = arr_solver.check(euf)
    assert len(ext_lemmas) == 1
    assert isinstance(ext_lemmas[0].formula, App)
    assert ext_lemmas[0].formula.decl.kind is DeclKind.OR
    assert arr_solver.stats.ext_lemmas == 1

    # End-to-end store-chain model preserves base writes/reads cleanly.
    s1 = ctx.mk_store(a, ctx.mk_int_val(0), ctx.mk_int_val(5))
    s2 = ctx.mk_store(s1, ctx.mk_int_val(1), ctx.mk_int_val(7))
    sel_a2 = ctx.mk_select(a, ctx.mk_int_val(2))
    solver = SMTSolver(ctx)
    solver.add(ctx.mk_eq(sel_a2, ctx.mk_int_val(9)), ctx.mk_eq(b, s2))
    assert solver.check() is SolveResult.SAT
    m = solver.model()
    assert m.eval_int(ctx.mk_select(b, ctx.mk_int_val(0))) == 5
    assert m.eval_int(ctx.mk_select(b, ctx.mk_int_val(1))) == 7
    assert m.eval_int(ctx.mk_select(b, ctx.mk_int_val(2))) == 9
    assert m.eval_int(sel_a2) == 9
