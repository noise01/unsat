"""Differential baseline checks comparing ``unsat`` against ``unsat_legacy``."""

import random
import subprocess
import sys

import unsat_legacy

import unsat
from unsat.parser import parse_fof as parse_tptp_fof
from unsat.parser import to_tptp_expr as unsat_to_tptp_expr

from .differential.formula import And as NAnd
from .differential.formula import Apply as NApply
from .differential.formula import Atom as NAtom
from .differential.formula import Equal as NEqual
from .differential.formula import Formula, Term, generate_euf_formula, generate_formula
from .differential.formula import Implies as NImplies
from .differential.formula import Not as NNot
from .differential.formula import Or as NOr
from .differential.formula import Var as NVar


def _render_unsat_term(
    node: Term,
    sort: unsat.Sort,
    consts: dict[str, unsat.Expr],
    fns: dict[tuple[str, int], unsat.FuncDecl],
) -> unsat.Expr:
    match node:
        case NAtom(name):
            if name not in consts:
                consts[name] = unsat.Constant(name, sort)
            return consts[name]
        case NApply(fn, args):
            rendered = [_render_unsat_term(a, sort, consts, fns) for a in args]
            key = (fn, len(rendered))
            if key not in fns:
                fns[key] = unsat.Function(
                    f"{fn}/{len(rendered)}", *([sort] * (len(rendered) + 1))
                )
            return fns[key](*rendered)
    msg = f"Unknown term node: {node!r}"
    raise TypeError(msg)


def _render_unsat(
    node: Formula,
    sort: unsat.Sort,
    bool_vars: dict[str, unsat.Expr],
    consts: dict[str, unsat.Expr],
    fns: dict[tuple[str, int], unsat.FuncDecl],
) -> unsat.Expr:
    match node:
        case NVar(name):
            if name not in bool_vars:
                bool_vars[name] = unsat.Bool(name)
            return bool_vars[name]
        case NEqual(left, right):
            return unsat.Eq(
                _render_unsat_term(left, sort, consts, fns),
                _render_unsat_term(right, sort, consts, fns),
            )
        case NNot(child):
            return unsat.Not(_render_unsat(child, sort, bool_vars, consts, fns))
        case NImplies(left, right):
            return unsat.Implies(
                _render_unsat(left, sort, bool_vars, consts, fns),
                _render_unsat(right, sort, bool_vars, consts, fns),
            )
        case NAnd(children):
            return unsat.And(
                *(_render_unsat(c, sort, bool_vars, consts, fns) for c in children)
            )
        case NOr(children):
            return unsat.Or(
                *(_render_unsat(c, sort, bool_vars, consts, fns) for c in children)
            )
    msg = f"Unknown formula node: {node!r}"
    raise TypeError(msg)


def _render_legacy_term(node: Term, sort: unsat_legacy.USort) -> unsat_legacy.Expr:
    match node:
        case NAtom(name):
            return unsat_legacy.Function(name, sort)()
        case NApply(fn, args):
            rendered = [_render_legacy_term(a, sort) for a in args]
            decl = unsat_legacy.Function(
                f"{fn}/{len(rendered)}", *([sort] * (len(rendered) + 1))
            )
            return decl(*rendered)
    msg = f"Unknown term node: {node!r}"
    raise TypeError(msg)


def _render_legacy(node: Formula, sort: unsat_legacy.USort) -> unsat_legacy.Expr:
    match node:
        case NVar(name):
            return unsat_legacy.Bool(name)
        case NEqual(left, right):
            return unsat_legacy.Eq(
                _render_legacy_term(left, sort), _render_legacy_term(right, sort)
            )
        case NNot(child):
            return unsat_legacy.Not(_render_legacy(child, sort))
        case NImplies(left, right):
            return unsat_legacy.Implies(
                _render_legacy(left, sort), _render_legacy(right, sort)
            )
        case NAnd(children):
            return unsat_legacy.And(*(_render_legacy(c, sort) for c in children))
        case NOr(children):
            return unsat_legacy.Or(*(_render_legacy(c, sort) for c in children))
    msg = f"Unknown formula node: {node!r}"
    raise TypeError(msg)


def _verdict_label(res: unsat.SolveResult) -> str:
    if res is unsat.SAT:
        return "SAT"
    if res is unsat.UNSAT:
        return "UNSAT"
    return "UNKNOWN"


def test_propositional_differential_unsat_vs_legacy() -> None:
    unsat.reset_default_context()
    rng = random.Random(20261126)
    u_sort = unsat.DeclareSort("U")
    legacy_u = unsat_legacy.USort("U")
    verdicts: set[str] = set()

    for _ in range(80):
        formula = generate_formula(rng)
        s_new = unsat.Solver()
        s_new.add(_render_unsat(formula, u_sort, {}, {}, {}))
        v_new = _verdict_label(s_new.check())

        s_old = unsat_legacy.Solver()
        s_old.add(_render_legacy(formula, legacy_u))
        v_old = s_old.check()

        assert v_new in {"SAT", "UNSAT"}
        assert v_new == v_old
        verdicts.add(v_new)

    assert verdicts == {"SAT", "UNSAT"}


def test_euf_differential_unsat_vs_legacy() -> None:
    unsat.reset_default_context()
    rng = random.Random(20261127)
    u_sort = unsat.DeclareSort("U")
    legacy_u = unsat_legacy.USort("U")
    verdicts: set[str] = set()

    for _ in range(80):
        formula = generate_euf_formula(rng)
        s_new = unsat.Solver()
        s_new.add(_render_unsat(formula, u_sort, {}, {}, {}))
        v_new = _verdict_label(s_new.check())

        s_old = unsat_legacy.Solver()
        s_old.add(_render_legacy(formula, legacy_u))
        v_old = s_old.check()

        assert v_new in {"SAT", "UNSAT"}
        assert v_new == v_old
        verdicts.add(v_new)

    assert verdicts == {"SAT", "UNSAT"}


def test_assumption_unsat_core_soundness_unsat_vs_legacy() -> None:
    unsat.reset_default_context()
    u_new = unsat.DeclareSort("U")
    a, b, c, d = unsat.Constants("a b c d", u_new)
    f_new = unsat.Function("f", u_new, u_new)
    new_assumptions = [
        unsat.Eq(a, b),
        unsat.Eq(b, c),
        unsat.Not(unsat.Eq(f_new(a), f_new(c))),
        unsat.Eq(c, d),
    ]
    s_new = unsat.Solver()
    assert s_new.check(*new_assumptions) is unsat.UNSAT
    core_new = s_new.unsat_core()
    assert set(core_new) <= set(new_assumptions)
    assert unsat.Solver().check(*core_new) is unsat.UNSAT

    u_old = unsat_legacy.USort("U")
    la = unsat_legacy.Function("a", u_old)()
    lb = unsat_legacy.Function("b", u_old)()
    lc = unsat_legacy.Function("c", u_old)()
    ld = unsat_legacy.Function("d", u_old)()
    f_old = unsat_legacy.Function("f", u_old, u_old)
    old_assumptions = [
        unsat_legacy.Eq(la, lb),
        unsat_legacy.Eq(lb, lc),
        unsat_legacy.Not(unsat_legacy.Eq(f_old(la), f_old(lc))),
        unsat_legacy.Eq(lc, ld),
    ]
    s_old = unsat_legacy.Solver()
    assert s_old.check(*old_assumptions) == "UNSAT"
    core_old = s_old.unsat_core()
    assert set(core_old) <= set(old_assumptions)
    assert unsat_legacy.Solver().check(*core_old) == "UNSAT"


def test_quantifier_ematching_and_budget_unknown_unsat_vs_legacy() -> None:
    unsat.reset_default_context()
    u_new = unsat.DeclareSort("U")
    x_new = unsat.Constant("x", u_new)
    a_new = unsat.Constant("a", u_new)
    f_new = unsat.Function("f", u_new, u_new)
    p_new = unsat.Function("P", u_new, unsat.BoolSort())

    # Finite chain UNSAT
    s_new = unsat.Solver()
    s_new.add(
        unsat.ForAll(
            [x_new],
            unsat.Implies(p_new(x_new), p_new(f_new(x_new))),
            patterns=[p_new(x_new)],
        ),
        p_new(a_new),
        unsat.Not(p_new(f_new(f_new(a_new)))),
    )
    assert s_new.check() is unsat.UNSAT

    u_old = unsat_legacy.USort("U")
    x_old = unsat_legacy.BoundVar("X", u_old)
    a_old = unsat_legacy.Function("a", u_old)()
    f_old = unsat_legacy.Function("f", u_old, u_old)
    p_old = unsat_legacy.Function("P", u_old, unsat_legacy.BOOL_SORT)
    s_old = unsat_legacy.Solver()
    s_old.add(
        unsat_legacy.ForAll(
            [x_old],
            unsat_legacy.Implies(p_old(x_old), p_old(f_old(x_old))),
            patterns=[unsat_legacy.MultiPattern(p_old(x_old))],
        )
    )
    s_old.add(p_old(a_old))
    s_old.add(unsat_legacy.Not(p_old(f_old(f_old(a_old)))))
    assert s_old.check() == "UNSAT"

    # Matching loop under tight budget -> conservative UNKNOWN on both solvers
    s_loop_new = unsat.Solver(max_quantifier_rounds=2, max_quantifier_matches=4)
    s_loop_new.add(
        unsat.ForAll([x_new], p_new(f_new(x_new)), patterns=[p_new(x_new)]),
        p_new(a_new),
    )
    assert s_loop_new.check() is unsat.UNKNOWN

    s_loop_old = unsat_legacy.Solver()
    s_loop_old.add(
        unsat_legacy.ForAll(
            [x_old],
            p_old(f_old(x_old)),
            patterns=[unsat_legacy.MultiPattern(p_old(x_old))],
        )
    )
    s_loop_old.add(p_old(a_old))
    assert s_loop_old.check(max_rounds=2, max_matches=4) == "UNKNOWN"


def test_tptp_fof_differential_unsat_vs_legacy() -> None:
    cases = [
        (
            [
                "fof(a1, axiom, (p => q)).",
                "fof(a2, axiom, p).",
                "fof(a3, axiom, ~q).",
            ],
            "UNSAT",
            None,
        ),
        (
            [
                "fof(e1, axiom, (a = b)).",
                "fof(e2, axiom, p(a)).",
                "fof(e3, axiom, ~p(b)).",
            ],
            "UNSAT",
            None,
        ),
        (
            [
                "fof(e1, axiom, (a = b)).",
                "fof(e2, axiom, p(a)).",
            ],
            "SAT",
            None,
        ),
        (
            [
                "fof(r1, axiom, ![X] : (human(X) => mortal(X))).",
                "fof(f1, axiom, human(socrates)).",
                "fof(g1, axiom, ~mortal(socrates)).",
            ],
            "UNSAT",
            None,
        ),
        (
            [
                "fof(loop, axiom, ![X] : (p(X) => p(f(X)))).",
                "fof(seed, axiom, p(a)).",
            ],
            "UNKNOWN",
            2,
        ),
    ]
    for stmts, expected, rounds in cases:
        ctx = unsat.Context()
        s_new = unsat.Solver(ctx)
        s_old = unsat_legacy.Solver()
        for stmt in stmts:
            n_name, n_role, n_expr = parse_tptp_fof(stmt, ctx=ctx)
            o_name, o_role, o_expr = unsat_legacy.parse_fof(stmt)
            assert (n_name, n_role) == (o_name, o_role)
            assert (
                parse_tptp_fof(
                    f"fof({n_name}, {n_role}, {unsat_to_tptp_expr(n_expr)}).", ctx=ctx
                )[2]
                is n_expr
            )
            s_new.add(n_expr)
            s_old.add(o_expr)

        v_new = _verdict_label(
            s_new.check()
            if rounds is None
            else s_new.check(max_quantifier_rounds=rounds)
        )
        v_old = s_old.check() if rounds is None else s_old.check(max_rounds=rounds)
        assert v_new == expected
        assert v_old == expected


def test_import_unsat_does_not_load_unsat_legacy_or_lark() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import sys, unsat; "
                "assert 'unsat_legacy' not in sys.modules; "
                "assert 'lark' not in sys.modules"
            ),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
