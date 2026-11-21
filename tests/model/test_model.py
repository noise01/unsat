import pytest

from unsat.model import (
    CompositeModelConverter,
    IdentityModelConverter,
    Model,
    SubstitutionModelConverter,
)
from unsat.syntax import Context


def test_model_lookup_and_evaluation() -> None:
    ctx = Context()
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")
    r = ctx.mk_bool("r")

    model = Model(ctx, {p.decl: True, q.decl: False})
    assert len(model) == 2
    assert p in model
    assert p.decl in model
    assert r not in model
    assert "not_expr" not in model
    assert model[p] is True
    assert model[q.decl] is False
    assert model.get(r) is None
    assert model.get(r, True) is True
    assert model.decls() == (p.decl, q.decl)
    assert model.items() == [(p.decl, True), (q.decl, False)]

    expr = ctx.mk_ite(p, ctx.mk_xor(p, q), ctx.mk_implies(q, r))
    assert model.eval(expr) is ctx.mk_true()
    assert model.eval_bool(expr) is True

    # Partial evaluation preserves unassigned variable unless model_completion=True.
    partial_expr = ctx.mk_and(p, r)
    assert model.eval(partial_expr, model_completion=False) is r
    with pytest.raises(ValueError, match="did not reduce"):
        model.eval_bool(partial_expr, model_completion=False)
    assert model.eval_bool(partial_expr, model_completion=True) is False

    # 3-argument Boolean Distinct evaluates to False.
    distinct3 = ctx.mk_distinct(p, q, r)
    assert model.eval_bool(distinct3, model_completion=False) is False

    # Cross-context rejection.
    other_ctx = Context()
    other_p = other_ctx.mk_bool("p")
    with pytest.raises(ValueError, match="different Context"):
        model.eval(other_p)
    with pytest.raises(ValueError, match="different Context"):
        _ = model[other_p]
    with pytest.raises(KeyError):
        _ = model[ctx.mk_and(p, q)]


def test_model_converters() -> None:
    ctx = Context()
    a = ctx.mk_bool("a")
    b = ctx.mk_bool("b")
    c = ctx.mk_bool("c")

    base = Model(ctx, {a.decl: True})
    assert IdentityModelConverter().convert(base) is base

    sub1 = SubstitutionModelConverter({b.decl: ctx.mk_not(a)})
    sub2 = SubstitutionModelConverter({c.decl: ctx.mk_and(a, ctx.mk_not(b))})

    # Composite undoes pipeline from last converter to first:
    # if tactic1 produced sub1 (eliminated b) and tactic2 produced sub2 (eliminated c),
    # here sub2 depends on b, so putting [sub2, sub1] runs sub1 first then sub2!
    composite = CompositeModelConverter([sub2, sub1])
    reconstructed = composite.convert(base)
    assert reconstructed[a] is True
    assert reconstructed[b] is False
    assert reconstructed[c] is True
