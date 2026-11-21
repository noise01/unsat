import gc

import pytest

from unsat.syntax import (
    App,
    Const,
    Context,
    DeclKind,
    Expr,
    SortKind,
    collect_const_decls,
    format_expr,
    iter_subexprs,
    quote_smt2_symbol,
)


def test_hash_consing_weakref_gc_and_ids() -> None:
    ctx = Context()
    assert ctx.bool_sort.kind is SortKind.BOOL
    assert ctx.mk_bool_sort() is ctx.bool_sort

    a1 = ctx.mk_bool("a")
    a2 = ctx.mk_bool("a")
    assert a1 is a2
    assert a1 == a2
    assert isinstance(a1 == a2, bool)
    assert hash(a1) == a1.id

    # Sequential IDs increase strictly.
    b = ctx.mk_bool("b")
    assert b.id > a1.id

    # WeakValueDictionary collects unreachable compound expressions.
    e = ctx.mk_and(a1, b)
    e_id = e.id
    assert ctx.mk_and(a1, b).id == e_id
    del e
    gc.collect()
    e_new = ctx.mk_and(a1, b)
    assert e_new.id > e_id

    # Expressions work in dict/set and reject bool coercion.
    table: dict[Expr, str] = {a1: "alpha", b: "beta"}
    assert table[a2] == "alpha"
    assert len({a1, a2, b}) == 2
    with pytest.raises(TypeError, match="bool"):
        bool(a1)


def test_immutability_and_cross_context_isolation() -> None:
    ctx1 = Context()
    ctx2 = Context()
    a1 = ctx1.mk_bool("a")
    a2 = ctx2.mk_bool("a")

    assert a1 is not a2
    assert a1 != a2
    assert a1.ctx is ctx1
    assert a2.ctx is ctx2

    attr = "id"
    with pytest.raises(AttributeError):
        setattr(a1, attr, 999)

    with pytest.raises(ValueError, match="different Context"):
        ctx1.mk_and(a1, a2)

    u2 = ctx2._intern_sort(SortKind.UNINTERPRETED, "U")
    with pytest.raises(ValueError, match="different Context"):
        ctx1.mk_const("x", u2)


def test_decl_kind_prevents_builtin_name_collision() -> None:
    ctx = Context()
    user_and = ctx.mk_bool("and")
    user_not = ctx.mk_bool("not")
    assert isinstance(user_and, App)
    assert user_and.is_const_symbol
    assert user_and.decl.kind is DeclKind.UNINTERPRETED

    conj = ctx.mk_and(user_and, user_not)
    assert isinstance(conj, App)
    assert conj.decl.kind is DeclKind.AND
    assert format_expr(conj) == "(and |and| |not|)"


def test_normalizing_constructors_and_sort_errors() -> None:
    ctx = Context()
    t = ctx.mk_true()
    f = ctx.mk_false()
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")

    assert ctx.mk_not(t) is f
    assert ctx.mk_not(f) is t
    assert ctx.mk_not(ctx.mk_not(p)) is p
    assert ~(~p) is p

    # And normalization: flatten, deduplicate, drop true, absorb false, complement.
    assert ctx.mk_and() is t
    assert ctx.mk_and(p) is p
    assert ctx.mk_and(p, t, p) is p
    assert ctx.mk_and(p, f) is f
    assert ctx.mk_and(p, ~p) is f
    nested_and = ctx.mk_and(ctx.mk_and(p, q), p)
    assert nested_and == (p & q)
    assert isinstance(nested_and, App)
    assert nested_and.args == (p, q)

    # Or normalization.
    assert ctx.mk_or() is f
    assert ctx.mk_or(p) is p
    assert ctx.mk_or(p, f, p) is p
    assert ctx.mk_or(p, t) is t
    assert ctx.mk_or(p, ~p) is t
    assert ctx.mk_or(ctx.mk_or(p, q), p) == (p | q)

    # Implies / Xor / Eq / Distinct / Ite.
    assert ctx.mk_implies(f, p) is t
    assert ctx.mk_implies(p, t) is t
    assert ctx.mk_implies(p, p) is t
    assert ctx.mk_implies(t, p) is p
    assert ctx.mk_implies(p, f) is ~p

    assert (p ^ p) is f
    assert (p ^ (~p)) is t
    assert (f ^ p) is p
    assert (t ^ p) is ~p

    assert ctx.mk_eq(p, p) is t
    assert ctx.mk_eq(t, f) is f
    assert ctx.mk_eq(p, ~p) is f

    assert ctx.mk_distinct() is t
    assert ctx.mk_distinct(p) is t
    assert ctx.mk_distinct(p, p) is f
    assert ctx.mk_distinct(t, f) is t
    assert ctx.mk_distinct(t, t) is f

    assert ctx.mk_ite(t, p, q) is p
    assert ctx.mk_ite(f, p, q) is q
    assert ctx.mk_ite(p, q, q) is q

    # Sort & arity checks.
    u_sort = ctx._intern_sort(SortKind.UNINTERPRETED, "U")
    u = ctx.mk_const("u", u_sort)
    with pytest.raises(TypeError, match="Expected Bool"):
        ctx.mk_not(u)
    with pytest.raises(TypeError, match="Sort mismatch"):
        ctx.mk_eq(p, u)
    with pytest.raises(TypeError, match="Sort mismatch"):
        ctx.mk_distinct(p, u)
    with pytest.raises(TypeError, match="Sort mismatch"):
        ctx.mk_ite(p, p, u)

    fn = ctx.mk_decl("f", (u_sort, ctx.bool_sort), u_sort)
    with pytest.raises(ValueError, match="Arity mismatch"):
        fn(u)
    with pytest.raises(TypeError, match="Sort mismatch"):
        fn(p, p)


def test_deep_traversal_collect_and_format() -> None:
    ctx = Context()
    p = ctx.mk_bool("p")
    cur: Expr = p
    for i in range(2000):
        q = ctx.mk_bool(f"q_{i}")
        cur = ctx.mk_xor(cur, q)

    subexprs = list(iter_subexprs(cur))
    assert subexprs[-1] is cur
    assert len(subexprs) == 4001  # 2001 vars + 2000 xor nodes

    decls = collect_const_decls(cur)
    assert len(decls) == 2001
    assert decls[0].name == "p"

    assert quote_smt2_symbol("abc_1") == "abc_1"
    assert quote_smt2_symbol("1abc") == "|1abc|"
    assert quote_smt2_symbol("a b") == "|a b|"
    assert quote_smt2_symbol("true") == "|true|"
    with pytest.raises(ValueError, match="empty"):
        quote_smt2_symbol("")
    with pytest.raises(ValueError, match="illegal"):
        quote_smt2_symbol("a|b")

    sample = ctx.mk_implies(ctx.mk_bool("x 1"), ctx.mk_bool("and"))
    assert format_expr(sample) == "(=> |x 1| |and|)"
    assert isinstance(ctx.mk_true(), Const)
