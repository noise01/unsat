"""Tests for SMT-LIB2 Strings & Regular Expressions (QF_S, QF_SLIA, QF_AUFSLIA)."""

from __future__ import annotations

from typing import cast

import hypothesis.strategies as st
import pytest
import z3
from hypothesis import given, settings

import unsat
from unsat.parser import run_smt2
from unsat.smt import SMTSolver, SolveResult
from unsat.syntax import (
    MAX_CHAR_CODE,
    App,
    Const,
    DeclKind,
    Expr,
    format_expr,
    format_smt2_string,
    unescape_smt2_string,
)
from unsat.syntax.context_strings import expr_to_re
from unsat.syntax.str_eval import re_is_empty, re_matches
from unsat.tactics import SimplifyTactic


def test_unicode_escape_and_formatting_roundtrip() -> None:
    assert unescape_smt2_string(r"hi \u{41}\u0042!") == "hi AB!"
    assert unescape_smt2_string(r"\u{1f600}") == "\U0001f600"
    assert unescape_smt2_string(r"\u{2ffff}") == chr(0x2FFFF)
    # Invalid escape > MAX_CHAR_CODE remains literal per SMT-LIB2 2.6.
    assert unescape_smt2_string(r"\u{30000}") == r"\u{30000}"

    ctx = unsat.Context()
    samples = ["", 'a"b', "line\n\t", r"\u0041", "\U0001f600", chr(MAX_CHAR_CODE)]
    for val in samples:
        c = ctx.mk_string_val(val)
        lit_str = format_smt2_string(val)
        assert format_expr(c) == lit_str
        script = (
            f"(declare-const s String)(assert (= s {lit_str}))"
            "(check-sat)(get-value (s))"
        )
        out = run_smt2(script)
        assert out[0] == "sat"
        # Round-trip parsed string value through SMT2Runner back to unescape.
        inner = out[1].split(" ", 1)[1][1:-3].replace('""', '"')
        assert unescape_smt2_string(inner) == val

    with pytest.raises(ValueError, match="limit"):
        ctx.mk_string_val(chr(MAX_CHAR_CODE + 1))


def test_string_and_regex_concrete_eval_and_simplify() -> None:
    ctx = unsat.Context()
    s = ctx.mk_string("s")
    assert SimplifyTactic().apply((ctx.mk_eq(s + "", s),)).formulas == ()
    assert (
        SimplifyTactic().apply((ctx.mk_str_in_re(s, ctx.mk_re_all()),)).formulas == ()
    )

    m = unsat.Model(ctx, {s.decl: "abc123abc"})
    assert m.eval_str(s + "!") == "abc123abc!"
    assert m.eval_int(unsat.Length(s)) == 9
    assert m.eval_str(unsat.At(s, 3)) == "1"
    assert m.eval_str(unsat.At(s, 99)) == ""
    assert m.eval_str(unsat.SubString(s, 3, 3)) == "123"
    assert m.eval_str(unsat.SubString(s, -1, 3)) == ""
    assert m.eval_int(unsat.IndexOf(s, "bc", 0)) == 1
    assert m.eval_int(unsat.IndexOf(s, "bc", 2)) == 7
    assert m.eval_int(unsat.IndexOf(s, "", 4)) == 4
    assert m.eval_int(unsat.IndexOf(s, "", 99)) == -1
    assert m.eval_str(unsat.Replace(s, "abc", "X")) == "X123abc"
    assert m.eval_str(unsat.Replace(s, "", "X")) == "Xabc123abc"
    assert m.eval_str(unsat.ReplaceAll(s, "abc", "X")) == "X123X"
    assert m.eval_str(unsat.ReplaceAll(s, "", "X")) == "abc123abc"
    assert m.eval_bool(unsat.Contains(s, "123")) is True
    assert m.eval_bool(unsat.PrefixOf("abc", s)) is True
    assert m.eval_bool(unsat.SuffixOf("abc", s)) is True
    assert m.eval_bool(s < "abd") is True
    assert m.eval_bool(s <= "abc123abc") is True
    assert m.eval_bool(s > "ab") is True
    assert m.eval_bool(s >= "abc123abc") is True
    assert m.eval_int(unsat.StrToInt(unsat.StringVal("007", ctx=ctx))) == 7
    assert m.eval_int(unsat.StrToInt(s)) == -1
    assert m.eval_str(unsat.IntToStr(unsat.IntVal(42, ctx=ctx))) == "42"
    assert m.eval_str(unsat.IntToStr(unsat.IntVal(-5, ctx=ctx))) == ""
    assert m.eval_int(unsat.StrToCode(unsat.StringVal("A", ctx=ctx))) == 65
    assert m.eval_int(unsat.StrToCode(s)) == -1
    assert m.eval_str(unsat.StrFromCode(unsat.IntVal(66, ctx=ctx))) == "B"
    assert m.eval_bool(unsat.IsDigit(unsat.StringVal("7", ctx=ctx))) is True
    assert m.eval_bool(unsat.IsDigit(unsat.StringVal("a", ctx=ctx))) is False

    # Brzozowski regex engine checks
    digit = ctx.mk_re_range(ctx.mk_string_val("0"), ctx.mk_string_val("9"))
    letters = ctx.mk_re_plus(
        ctx.mk_re_range(ctx.mk_string_val("a"), ctx.mk_string_val("z"))
    )
    pattern = ctx.mk_re_concat(letters, ctx.mk_re_power(3, digit), letters)
    re_node = expr_to_re(pattern)
    assert re_node is not None
    assert re_matches(re_node, "abc123abc") is True
    assert re_matches(re_node, "abc12abc") is False
    assert m.eval_bool(unsat.InRe(s, pattern)) is True

    empty_re = ctx.mk_re_inter(
        ctx.mk_re_loop(2, 3, digit),
        ctx.mk_re_power(4, digit),
    )
    compiled_empty = expr_to_re(empty_re)
    assert compiled_empty is not None
    assert re_is_empty(compiled_empty) is True


def test_polymorphic_dsl_and_operators() -> None:
    ctx = unsat.Context()
    x, y = unsat.Strings("x y", ctx=ctx)
    bv1, bv2 = unsat.BitVecs("bv1 bv2", 4, ctx=ctx)

    bv_cat = unsat.Concat(bv1, bv2)
    assert bv_cat.is_bv
    assert bv_cat.bv_size == 8

    str_cat = unsat.Concat(x, "_mid_", y)
    assert str_cat.is_string

    reg_cat = unsat.Concat(unsat.Re("a", ctx=ctx), unsat.Star(unsat.Re("b", ctx=ctx)))
    assert reg_cat.is_reglan

    s = unsat.Solver(ctx)
    f = unsat.And(
        unsat.Eq(str_cat, "foo_mid_bar"),
        unsat.Eq(unsat.Length(x), 3),
        unsat.InRe(y, unsat.Union(unsat.Re("bar", ctx=ctx), unsat.Re("baz", ctx=ctx))),
        x > "a",
    )
    s.add(f)
    assert s.check() is unsat.SAT
    m = s.model()
    assert m.eval_bool(f, model_completion=True) is True
    assert m[x] == "foo"
    assert m[y] == "bar"


def test_word_equations_nielsen_and_regex_solver() -> None:
    ctx = unsat.Context()
    x, y, z = unsat.Strings("x y z", ctx=ctx)

    # SAT overlapping word equation via Nielsen split
    s = unsat.Solver(ctx)
    f_sat = unsat.And(
        unsat.Eq("a" + x, x + "a"),
        unsat.Eq(unsat.Length(x), 3),
    )
    s.add(f_sat)
    assert s.check() is unsat.SAT
    m = s.model()
    assert m.eval_bool(f_sat, model_completion=True) is True
    assert m[x] == "aaa"

    # UNSAT word equation by constant character collision
    s.reset()
    s.add(unsat.Eq("a" + x, y + "b"), unsat.Eq(x, y))
    assert s.check() is unsat.UNSAT

    # UNSAT regex intersection emptiness + length conflict
    s.reset()
    r1 = unsat.Star(unsat.Range("a", "b", ctx=ctx))
    r2 = unsat.Intersect(
        r1,
        unsat.Plus(unsat.Range("c", "d", ctx=ctx)),
    )
    s.add(unsat.InRe(z, r2))
    assert s.check() is unsat.UNSAT

    s.reset()
    s.add(
        unsat.InRe(
            z,
            unsat.Loop(unsat.Range("0", "9", ctx=ctx), 2, 4),
        ),
        unsat.Eq(unsat.Length(z), 5),
    )
    assert s.check() is unsat.UNSAT

    # SAT regex complement + difference + distinctness
    s.reset()
    f_re = unsat.And(
        unsat.InRe(
            x,
            unsat.ReDiff(
                unsat.RePower(unsat.Range("a", "b", ctx=ctx), 2),
                unsat.Re("aa", ctx=ctx),
            ),
        ),
        unsat.InRe(y, unsat.RePower(unsat.Range("a", "b", ctx=ctx), 2)),
        unsat.Distinct(x, y),
        unsat.Eq(y, "aa"),
    )
    s.add(f_re)
    assert s.check() is unsat.SAT
    assert s.model().eval_bool(f_re, model_completion=True) is True


def test_extended_string_operators_smt() -> None:
    ctx = unsat.Context()
    s, src, dst, out = unsat.Strings("s src dst out", ctx=ctx)
    n = unsat.Int("n", ctx=ctx)

    sol = unsat.Solver(ctx)
    # substr + indexof + prefix + suffix + to_code + is_digit
    f1 = unsat.And(
        unsat.Eq(unsat.Length(s), 5),
        unsat.PrefixOf("ab", s),
        unsat.SuffixOf("9", s),
        unsat.IsDigit(unsat.At(s, 4)),
        unsat.Eq(unsat.IndexOf(s, "x", 0), 2),
        unsat.Eq(unsat.SubString(s, 3, 1), "q"),
    )
    sol.add(f1)
    assert sol.check() is unsat.SAT
    m = sol.model()
    assert m.eval_bool(f1, model_completion=True) is True
    assert m[s] == "abxq9"

    # str.replace & str.replace_all
    sol.reset()
    f2 = unsat.And(
        unsat.Eq(s, "foo_bar_foo"),
        unsat.Eq(src, "foo"),
        unsat.Eq(dst, "z"),
        unsat.Eq(out, unsat.ReplaceAll(s, src, dst)),
    )
    sol.add(f2)
    assert sol.check() is unsat.SAT
    m2 = sol.model()
    assert m2.eval_bool(f2, model_completion=True) is True
    assert m2[out] == "z_bar_z"

    # str.to_int & str.from_int
    sol.reset()
    f3 = unsat.And(
        unsat.Eq(n, 25),
        unsat.Eq(s, unsat.IntToStr(n)),
        unsat.Eq(unsat.StrToInt(s), n),
    )
    sol.add(f3)
    assert sol.check() is unsat.SAT
    m3 = sol.model()
    assert m3.eval_bool(f3, model_completion=True) is True
    assert m3[s] == "25"

    # Negated contains / lexicographic comparison
    sol.reset()
    f4 = unsat.And(
        unsat.Eq(unsat.Length(s), 2),
        unsat.Not(unsat.Contains(s, "aa")),
        unsat.PrefixOf("a", s),
        s > "ab",
    )
    sol.add(f4)
    assert sol.check() is unsat.SAT
    m4 = sol.model()
    assert m4.eval_bool(f4, model_completion=True) is True


def test_combined_euf_arrays_incremental_and_smt2_strings() -> None:
    script = """
    (set-logic QF_AUFSLIA)
    (declare-const a (Array String Int))
    (declare-const s String)
    (declare-const t String)
    (declare-fun f (String) Int)
    (assert (! (= (str.++ s "x") "abx") :named eq1))
    (assert (= (select (store a s 10) "ab") 10))
    (push 1)
    (assert (= t "ab"))
    (assert (! (not (= (f s) (f t))) :named bad_euf))
    (check-sat)
    (get-unsat-core)
    (pop 1)
    (assert (= (f s) 7))
    (check-sat)
    (get-model)
    """
    out = run_smt2(script)
    assert out[0] == "unsat"
    assert "bad_euf" in out[1]
    assert out[2] == "sat"
    assert '"ab"' in out[3]


def _as_arith(ref: z3.ExprRef) -> z3.ArithRef:
    return cast(z3.ArithRef, ref)


def _as_seq(ref: z3.ExprRef) -> z3.SeqRef:
    return cast(z3.SeqRef, ref)


def _as_re(ref: z3.ExprRef) -> z3.ReRef:
    return cast(z3.ReRef, ref)


def _to_z3_expr(expr: Expr, env: dict[str, z3.ExprRef]) -> z3.ExprRef:
    memo: dict[Expr, z3.ExprRef] = {}
    stack: list[tuple[Expr, bool]] = [(expr, False)]
    while stack:
        node, expanded = stack.pop()
        if node in memo:
            continue
        if isinstance(node, Const):
            if node.is_bool:
                memo[node] = z3.BoolVal(bool(node.value))
            elif node.is_int:
                assert isinstance(node.value, int)
                memo[node] = z3.IntVal(node.value)
            elif node.is_string:
                assert isinstance(node.value, str)
                memo[node] = z3.StringVal(node.value)
            continue
        assert isinstance(node, App)
        if not node.args and node.decl.is_uninterpreted:
            if node.is_string:
                memo[node] = env.setdefault(node.name, z3.String(node.name))
            elif node.is_int:
                memo[node] = env.setdefault(node.name, z3.Int(node.name))
            else:
                memo[node] = env.setdefault(node.name, z3.Bool(node.name))
            continue
        if not expanded and node.args:
            stack.append((node, True))
            for arg in reversed(node.args):
                if arg not in memo:
                    stack.append((arg, False))
            continue
        za = [memo[a] for a in node.args]
        k = node.decl.kind
        match k:
            case DeclKind.NOT:
                memo[node] = z3.Not(za[0])
            case DeclKind.AND:
                memo[node] = z3.And(*za)
            case DeclKind.OR:
                memo[node] = z3.Or(*za)
            case DeclKind.IMPLIES:
                memo[node] = z3.Implies(za[0], za[1])
            case DeclKind.EQ:
                memo[node] = za[0] == za[1]
            case DeclKind.DISTINCT:
                memo[node] = z3.Distinct(*za)
            case DeclKind.ADD:
                acc = _as_arith(za[0])
                for item in za[1:]:
                    acc = acc + _as_arith(item)
                memo[node] = acc
            case DeclKind.SUB:
                memo[node] = _as_arith(za[0]) - _as_arith(za[1])
            case DeclKind.LT:
                memo[node] = _as_arith(za[0]) < _as_arith(za[1])
            case DeclKind.LE:
                memo[node] = _as_arith(za[0]) <= _as_arith(za[1])
            case DeclKind.GT:
                memo[node] = _as_arith(za[0]) > _as_arith(za[1])
            case DeclKind.GE:
                memo[node] = _as_arith(za[0]) >= _as_arith(za[1])
            case DeclKind.STR_CONCAT:
                memo[node] = z3.Concat(*za)
            case DeclKind.STR_LEN:
                memo[node] = z3.Length(za[0])
            case DeclKind.STR_AT:
                memo[node] = z3.SubString(za[0], za[1], 1)
            case DeclKind.STR_SUBSTR:
                memo[node] = z3.SubString(za[0], za[1], za[2])
            case DeclKind.STR_INDEXOF:
                memo[node] = z3.IndexOf(za[0], za[1], za[2])
            case DeclKind.STR_REPLACE:
                memo[node] = z3.Replace(za[0], za[1], za[2])
            case DeclKind.STR_CONTAINS:
                memo[node] = z3.Contains(za[0], za[1])
            case DeclKind.STR_PREFIXOF:
                memo[node] = z3.PrefixOf(za[0], za[1])
            case DeclKind.STR_SUFFIXOF:
                memo[node] = z3.SuffixOf(za[0], za[1])
            case DeclKind.STR_LT:
                memo[node] = _as_seq(za[0]) < _as_seq(za[1])
            case DeclKind.STR_LE:
                memo[node] = _as_seq(za[0]) <= _as_seq(za[1])
            case DeclKind.STR_IN_RE:
                memo[node] = z3.InRe(za[0], za[1])
            case DeclKind.STR_TO_RE:
                memo[node] = z3.Re(za[0])
            case DeclKind.RE_NONE:
                memo[node] = z3.Empty(z3.ReSort(z3.StringSort()))
            case DeclKind.RE_ALL:
                memo[node] = z3.Full(z3.ReSort(z3.StringSort()))
            case DeclKind.RE_ALLCHAR:
                memo[node] = z3.AllChar(z3.ReSort(z3.StringSort()))
            case DeclKind.RE_CONCAT:
                memo[node] = z3.Concat(*za)
            case DeclKind.RE_UNION:
                memo[node] = z3.Union(*za)
            case DeclKind.RE_INTER:
                memo[node] = z3.Intersect(*za)
            case DeclKind.RE_STAR:
                memo[node] = z3.Star(za[0])
            case DeclKind.RE_PLUS:
                memo[node] = z3.Plus(za[0])
            case DeclKind.RE_OPT:
                memo[node] = z3.Option(za[0])
            case DeclKind.RE_RANGE:
                memo[node] = z3.Range(za[0], za[1])
            case DeclKind.RE_COMP:
                memo[node] = z3.Complement(za[0])
            case DeclKind.RE_DIFF:
                memo[node] = z3.Diff(za[0], za[1])
            case DeclKind.RE_POWER:
                p_n = node.decl.params[0]
                memo[node] = z3.Loop(_as_re(za[0]), p_n, p_n)
            case DeclKind.RE_LOOP:
                memo[node] = z3.Loop(
                    _as_re(za[0]), node.decl.params[0], node.decl.params[1]
                )
            case _:
                msg = f"Unsupported op in test bridge: {k}"
                raise AssertionError(msg)
    return memo[expr]


@st.composite
def _string_formulas(draw: st.DrawFn) -> tuple[unsat.Context, list[Expr]]:
    ctx = unsat.Context()
    x, y = unsat.Strings("x y", ctx=ctx)
    vars_list = [x, y]
    consts = [ctx.mk_string_val(c) for c in ("", "a", "b", "ab", "ba")]
    terms = [*vars_list, *consts]

    ab = ctx.mk_re_range(ctx.mk_string_val("a"), ctx.mk_string_val("b"))
    res = [
        ctx.mk_re_star(ab),
        ctx.mk_re_plus(ab),
        ctx.mk_re_concat(ctx.mk_str_to_re(ctx.mk_string_val("a")), ctx.mk_re_star(ab)),
        ctx.mk_re_union(
            ctx.mk_str_to_re(ctx.mk_string_val("a")),
            ctx.mk_str_to_re(ctx.mk_string_val("b")),
        ),
        ctx.mk_re_power(2, ab),
    ]

    forms: list[Expr] = []
    # Bound variable lengths cleanly for fast differential fuzzing.
    for v in vars_list:
        forms.append(ctx.mk_le(ctx.mk_str_len(v), ctx.mk_int_val(3)))

    n_atoms = draw(st.integers(min_value=2, max_value=4))
    for _ in range(n_atoms):
        ch = draw(st.integers(min_value=0, max_value=5))
        v1 = draw(st.sampled_from(vars_list))
        t1 = draw(st.sampled_from(terms))
        t2 = draw(st.sampled_from(terms))
        if ch == 0:
            lhs = ctx.mk_str_concat(v1, t1)
            rhs = ctx.mk_str_concat(t2, draw(st.sampled_from(vars_list)))
            forms.append(
                ctx.mk_eq(lhs, rhs)
                if draw(st.booleans())
                else ctx.mk_distinct(lhs, rhs)
            )
        elif ch == 1:
            r = draw(st.sampled_from(res))
            atom = ctx.mk_str_in_re(v1, r)
            forms.append(atom if draw(st.booleans()) else ctx.mk_not(atom))
        elif ch == 2:
            atom = ctx.mk_str_prefixof(t1, v1)
            forms.append(atom if draw(st.booleans()) else ctx.mk_not(atom))
        elif ch == 3:
            atom = ctx.mk_str_suffixof(t1, v1)
            forms.append(atom if draw(st.booleans()) else ctx.mk_not(atom))
        elif ch == 4:
            k = draw(st.integers(min_value=0, max_value=3))
            forms.append(
                ctx.mk_le(ctx.mk_str_len(v1), ctx.mk_int_val(k))
                if draw(st.booleans())
                else ctx.mk_eq(ctx.mk_str_len(v1), ctx.mk_int_val(k))
            )
        else:
            atom = ctx.mk_str_lt(v1, t1)
            forms.append(atom if draw(st.booleans()) else ctx.mk_not(atom))
    return ctx, forms


@settings(max_examples=30, deadline=None)
@given(data=_string_formulas())
def test_qf_slia_matches_z3_and_validates_models(
    data: tuple[unsat.Context, list[Expr]],
) -> None:
    ctx, forms = data
    usolver = SMTSolver(ctx, timeout=5.0)
    zsolver = z3.Solver()
    zsolver.set("timeout", 5000)
    zenv: dict[str, z3.ExprRef] = {}
    for f in forms:
        usolver.add(f)
        zsolver.add(_to_z3_expr(f, zenv))

    ures = usolver.check()
    zres_raw = zsolver.check()
    zres = (
        SolveResult.SAT
        if zres_raw == z3.sat
        else SolveResult.UNSAT
        if zres_raw == z3.unsat
        else SolveResult.UNKNOWN
    )
    if ures is not SolveResult.UNKNOWN and zres is not SolveResult.UNKNOWN:
        assert ures is zres
    if ures is SolveResult.SAT:
        model = usolver.model()
        for f in forms:
            assert model.eval_bool(f, model_completion=True) is True
