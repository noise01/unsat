"""Tests for the zero-dependency TPTP FOF parser, formatter, and solver helpers."""

from pathlib import Path
from typing import cast

import pytest
import z3

import unsat
from unsat.parser import (
    FofStatement,
    TPTPParseError,
    format_fof,
    parse_fof,
    parse_tptp,
    parse_tptp_file,
    solve_tptp,
    to_tptp_expr,
)
from unsat.sat import SolveResult
from unsat.syntax import Context

ROUND_TRIP_FORMULAS = [
    "p",
    "socrates",
    "human(socrates)",
    "likes(alice, bob)",
    "~p",
    "(p & q)",
    "(p | q)",
    "(p => q)",
    "(p <=> q)",
    "(a = b)",
    "(a != b)",
    "![X] : (human(X) => mortal(X))",
    "?[Y] : cat(Y)",
    "![X, Y] : (loves(X, Y) => knows(Y, X))",
    "![X] : ?[Y] : loves(X, Y)",
    "![X] : ?[X] : shadow(X)",
    "((p & q) | ~r)",
    "(f(g(a), b) = h(c))",
    "$true",
    "$false",
    "(p & q & r)",
    "(p | q | r)",
    "![X] : (p(X) & q(X) & r(X))",
]


def _parse_single(formula: str, ctx: Context) -> unsat.Expr:
    _, _, expr = parse_fof(f"fof(r, axiom, {formula}).", ctx=ctx)
    return expr


@pytest.mark.parametrize("formula", ROUND_TRIP_FORMULAS)
def test_tptp_round_trip_identity(formula: str) -> None:
    ctx = Context()
    expr = _parse_single(formula, ctx)
    written = to_tptp_expr(expr)
    reparsed = _parse_single(written, ctx)
    assert reparsed is expr, f"{formula!r} -> {written!r}"
    stmt_text = format_fof("ax1", "axiom", expr)
    name, role, stmt_expr = parse_fof(stmt_text, ctx=ctx)
    assert (name, role) == ("ax1", "axiom")
    assert stmt_expr is expr


def test_tptp_round_trip_special_cases_and_comments() -> None:
    ctx = Context()
    u = ctx.mk_uninterpreted_sort("U")
    implies_fn = ctx.mk_decl("implies", (u, u), u)
    a = ctx.mk_const("a", u)
    b = ctx.mk_const("b", u)
    c = ctx.mk_const("c", u)

    # User predicate named 'implies' stays a function/predicate, not '=>'.
    app_written = to_tptp_expr(implies_fn(a, b))
    assert app_written == "implies(a, b)"
    assert "=>" not in app_written

    # Explicit Or(Not(p), q) round-trips without collapsing into Implies.
    p = ctx.mk_bool("p")
    q = ctx.mk_bool("q")
    or_not = ctx.mk_or(ctx.mk_not(p), q)
    assert to_tptp_expr(or_not) == "(~p | q)"
    assert _parse_single(to_tptp_expr(or_not), ctx) is or_not

    # Distinct (2-ary and 3-ary) formats as != conjunctions.
    d2 = ctx.mk_distinct(a, b)
    assert to_tptp_expr(d2) == "(a != b)"
    assert _parse_single(to_tptp_expr(d2), ctx) is ctx.mk_not(ctx.mk_eq(a, b))

    d3 = ctx.mk_distinct(a, b, c)
    assert to_tptp_expr(d3) == "((a != b) & (a != c) & (b != c))"
    reparsed_d3 = _parse_single(to_tptp_expr(d3), ctx)
    assert reparsed_d3 is ctx.mk_and(
        ctx.mk_not(ctx.mk_eq(a, b)),
        ctx.mk_not(ctx.mk_eq(a, c)),
        ctx.mk_not(ctx.mk_eq(b, c)),
    )

    # Comments (BOM, % line comments, /* ... */ block comments) are ignored cleanly.
    commented = (
        "\ufeff% leading comment\n"
        "fof(42, hypothesis, /* inline */ ![X] : (human(X) => mortal(X))).\n"
        "% trailing comment\n"
    )
    name, role, expr = parse_fof(commented, ctx=ctx)
    assert (name, role) == ("42", "hypothesis")
    assert expr is _parse_single("![X] : (human(X) => mortal(X))", ctx)


@pytest.mark.parametrize(
    ("bad_input", "expected_line"),
    [
        ("", 1),
        ("   \n% only comments\n", 3),
        ("fof(r, axiom, p)", 1),
        ("fof(r, axiom, (p & q).", 1),
        ("fof(r, axiom, p()).", 1),
        ("fof(r, axiom, X).", 1),
        ("fof(r, axiom, ![X, X] : p(X)).", 1),
        ("fof(r, axiom, p).\nextra", 2),
        ("fof(r, axiom, /* unterminated\np).", 1),
        ("fof(r, axiom, $bad).", 1),
        ("cnf(r, axiom, p).", 1),
        ("fof(r, axiom, p & ).", 1),
        ("fof(r, axiom, @).", 1),
    ],
)
def test_tptp_parse_errors_include_location(bad_input: str, expected_line: int) -> None:
    assert issubclass(TPTPParseError, ValueError)
    with pytest.raises(TPTPParseError, match="TPTP") as exc_info:
        parse_fof(bad_input)
    assert exc_info.value.line == expected_line
    assert exc_info.value.column >= 1


def test_parse_fof_rejects_non_string() -> None:
    with pytest.raises(TPTPParseError, match="TPTP"):
        parse_fof(cast("str", 123))


def test_parse_tptp_and_file(tmp_path: Path) -> None:
    script = (
        "% Socrates syllogism\n"
        "fof(rule1, axiom, ![X] : (human(X) => mortal(X))).\n"
        "fof(fact1, axiom, human(socrates)).\n"
        "fof(goal, conjecture, mortal(socrates)).\n"
    )
    tptp_file = tmp_path / "syllogism.tptp"
    tptp_file.write_text(script, encoding="utf-8-sig")

    ctx = Context()
    stmts = parse_tptp_file(tptp_file, ctx=ctx)
    assert len(stmts) == 3
    assert all(isinstance(s, FofStatement) for s in stmts)
    assert [(s.name, s.role) for s in stmts] == [
        ("rule1", "axiom"),
        ("fact1", "axiom"),
        ("goal", "conjecture"),
    ]
    assert parse_tptp("", ctx=ctx) == []


def test_solve_tptp_entailment_and_satisfiability() -> None:
    entailed_script = (
        "fof(r1, axiom, ![X] : (human(X) => mortal(X))).\n"
        "fof(f1, axiom, human(socrates)).\n"
        "fof(c1, conjecture, mortal(socrates)).\n"
    )
    verdict, stats = solve_tptp(entailed_script)
    assert verdict is SolveResult.UNSAT
    assert stats["quantifier_ematch_rounds"] >= 1

    not_entailed_script = (
        "fof(r1, axiom, ![X] : (human(X) => mortal(X))).\n"
        "fof(c1, conjecture, human(socrates)).\n"
    )
    verdict_sat, _ = solve_tptp(not_entailed_script)
    assert verdict_sat is SolveResult.SAT

    euf_unsat = (
        "fof(e1, axiom, a = b).\n"
        "fof(e2, axiom, b = c).\n"
        "fof(e3, axiom, f(a) != f(c)).\n"
    )
    assert solve_tptp(euf_unsat)[0] is SolveResult.UNSAT


def test_per_check_quantifier_budget_overrides() -> None:
    unsat.reset_default_context()
    ctx = unsat.default_context()
    _, _, rule = parse_fof("fof(loop, axiom, ![X] : (p(X) => p(f(X)))).", ctx=ctx)
    _, _, seed = parse_fof("fof(seed, axiom, p(a)).", ctx=ctx)

    solver = unsat.Solver()
    solver.add(rule, seed)

    assert solver.check(max_quantifier_rounds=2) is unsat.UNKNOWN
    assert solver.check(max_quantifier_matches=0) is unsat.UNKNOWN

    # Ground formulas still solve as SAT even with 0 quantifier rounds/matches.
    ground_solver = unsat.Solver()
    _, _, ground = parse_fof("fof(g, axiom, (a = b) & p(a)).", ctx=ctx)
    ground_solver.add(ground)
    assert (
        ground_solver.check(max_quantifier_rounds=0, max_quantifier_matches=0)
        is unsat.SAT
    )

    with pytest.raises(ValueError, match="max_rounds"):
        solver.check(max_quantifier_rounds=-1)
    with pytest.raises(ValueError, match="max_matches"):
        solver.check(max_quantifier_matches=True)


def test_tptp_qf_euf_differential_against_z3() -> None:
    cases = [
        ("fof(a1, axiom, (a = b) & (b = c) & (f(a) != f(c))).", z3.unsat),
        ("fof(a2, axiom, (a = b) & p(a) & ~p(b)).", z3.unsat),
        ("fof(a3, axiom, (a = b) & (p(a) | q(c)) & ~p(b)).", z3.sat),
        ("fof(a4, axiom, ((a = b) => (f(a) = f(b))) & (a != b)).", z3.sat),
        ("fof(a5, axiom, (a != a)).", z3.unsat),
    ]
    z_u = z3.DeclareSort("U")
    za, zb, zc = z3.Consts("a b c", z_u)
    zf = z3.Function("f", z_u, z_u)
    zp = z3.Function("p", z_u, z3.BoolSort())
    zq = z3.Function("q", z_u, z3.BoolSort())
    z3_map = [
        z3.And(za == zb, zb == zc, zf(za) != zf(zc)),
        z3.And(za == zb, zp(za), z3.Not(zp(zb))),
        z3.And(za == zb, z3.Or(zp(za), zq(zc)), z3.Not(zp(zb))),
        z3.And(z3.Implies(za == zb, zf(za) == zf(zb)), za != zb),
        za != za,
    ]
    for (tptp_text, expected_z3), z3_expr in zip(cases, z3_map, strict=True):
        zs = z3.Solver()
        zs.add(z3_expr)
        assert zs.check() == expected_z3

        verdict, _ = solve_tptp(tptp_text)
        expected_unsat = (
            SolveResult.UNSAT if expected_z3 == z3.unsat else SolveResult.SAT
        )
        assert verdict is expected_unsat
