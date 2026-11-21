import pytest

from unsat.model import Model
from unsat.parser import format_smt2_model, run_smt2
from unsat.parser.smt2 import tokenize_smt2
from unsat.syntax import Context, format_expr


def test_smt2_lexing_and_parse_errors() -> None:
    tokens = tokenize_smt2(
        '\ufeff; comment\n(assert (and |a b| (not (= x "hi ""there"""))))'
    )
    assert any(tok.kind == "QSYMBOL" and tok.value == "a b" for tok in tokens)
    assert any(tok.kind == "STRING" and tok.value == 'hi "there"' for tok in tokens)

    for bad_script in (
        "(assert true",
        "assert true)",
        "(assert |unterminated",
        '(set-info :note "unterminated)',
        "(assert :",
        "(assert \\)",
        "(set-logic QF_NRA)",
        "(declare-sort Foo 1)",
        "(declare-sort Bool 0)",
        "(declare-sort Int 0)",
        "(declare-sort Real 0)",
        "(declare-const x Float)",
        "(define-fun f ((x Bool)) Bool x)",
        "(assert unknown_var)",
        "(assert (not a b))",
        "(unknown-cmd)",
    ):
        with pytest.raises(ValueError, match=r".+"):
            run_smt2(bad_script)


def test_smt2_boolean_operators_associativity_and_let() -> None:
    # Right-associative => : (=> true false false) == (true => (false => false)) == true
    assert run_smt2("(assert (=> true false false))\n(check-sat)") == ["sat"]
    # Compare with left-assoc ((true => false) => false) == true, so test:
    # (=> false true false) => right-assoc: false => (true => false) = true;
    # left-assoc: (false => true) => false = true => false = false!
    assert run_smt2("(assert (=> false true false))\n(check-sat)") == ["sat"]

    # Left-associative xor: (xor true true false) = (true xor true) xor false = false
    assert run_smt2("(assert (xor true true false))\n(check-sat)") == ["unsat"]

    # Chained =: (= a b c) requires a == b and b == c
    assert run_smt2(
        """
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (assert (= a b c))
            (assert a)
            (assert (not c))
            (check-sat)
            """
    ) == ["unsat"]

    # Parallel let bindings: inner binding of x uses outer x, not sequential!
    out = run_smt2(
        """
        (declare-const x Bool)
        (assert x)
        (assert (let ((x false) (y x)) (and (not x) y)))
        (check-sat)
        """
    )
    assert out == ["sat"]


def test_smt2_commands_scoping_get_model_get_value_and_roundtrip() -> None:
    script = """
    (set-logic QF_BOOL)
    (set-option :produce-models true)
    (set-info :source "test")
    (declare-const p Bool)
    (declare-fun q () Bool)
    (define-fun both () Bool (and p q))
    (assert (! (=> p q) :named rule1))
    (check-sat-assuming ((not p) q))
    (push 1)
    (declare-const r Bool)
    (assert (and p (not q) r))
    (check-sat)
    (pop 1)
    (assert both)
    (check-sat)
    (get-model)
    (get-value (p q (xor p q)))
    (exit)
    (assert false)
    """
    out = run_smt2(script)
    assert out[0] == "sat"
    assert out[1] == "unsat"
    assert out[2] == "sat"
    assert "(define-fun p () Bool true)" in out[3]
    assert "(define-fun q () Bool true)" in out[3]
    assert "(define-fun r " not in out[3]
    assert out[4] == "((p true) (q true) ((xor p q) false))"

    # r was popped, so declaring r again in outer scope succeeds.
    out2 = run_smt2(
        """
        (declare-const p Bool)
        (push)
        (declare-const r Bool)
        (pop)
        (declare-const r Bool)
        (assert (and p r))
        (check-sat)
        (reset-assertions)
        (declare-const z Bool)
        (assert (not z))
        (check-sat)
        (reset)
        (check-sat)
        (get-model)
        """
    )
    assert out2 == ["sat", "sat", "sat", "()"]


def test_smt2_format_roundtrip_with_reserved_symbol_names() -> None:
    ctx = Context()
    user_and = ctx.mk_bool("and")
    user_true = ctx.mk_bool("true")
    expr = ctx.mk_implies(user_and, ctx.mk_not(user_true))

    script = "\n".join(
        [
            "(declare-const |and| Bool)",
            "(declare-const |true| Bool)",
            f"(assert {format_expr(expr)})",
            "(assert |and|)",
            "(check-sat)",
            "(get-model)",
        ]
    )
    out = run_smt2(script)
    assert out[0] == "sat"
    assert "(define-fun |and| () Bool true)" in out[1]
    assert "(define-fun |true| () Bool false)" in out[1]

    model = Model(ctx, {user_and.decl: True, user_true.decl: False})
    formatted = format_smt2_model(model)
    assert "(define-fun |and| () Bool true)" in formatted
    assert "(define-fun |true| () Bool false)" in formatted


def test_smt2_qf_uf_congruence_models_and_scoping() -> None:
    unsat_script = """
    (set-logic QF_UF)
    (declare-sort S 0)
    (declare-const a S)
    (declare-const b S)
    (declare-const c S)
    (declare-fun f (S) S)
    (assert (= a b))
    (assert (= (f a) c))
    (assert (distinct (f b) c))
    (check-sat)
    """
    assert run_smt2(unsat_script) == ["unsat"]

    sat_script = """
    (set-logic QF_UF)
    (declare-sort S 0)
    (declare-sort T 0)
    (declare-const a S)
    (declare-const b S)
    (declare-const x T)
    (declare-fun f (S) S)
    (declare-fun P (S T) Bool)
    (declare-fun g (Bool) S)
    (define-fun fa () S (f a))
    (assert (distinct a b))
    (assert (P a x))
    (assert (not (P b x)))
    (assert (= (g true) a))
    (check-sat)
    (get-model)
    (get-value (a fa (P a x)))
    (push)
    (declare-sort U 0)
    (declare-const u U)
    (assert (= a b))
    (check-sat)
    (pop)
    (declare-sort U 0)
    (check-sat)
    """
    out = run_smt2(sat_script)
    assert out[0] == "sat"
    model_str = out[1]
    assert "(define-fun a () S S!val!" in model_str
    assert "(define-fun f ((x!0 S)) S" in model_str
    assert "(define-fun P ((x!0 S) (x!1 T)) Bool" in model_str
    assert "(define-fun g ((x!0 Bool)) S" in model_str
    assert "(P a x) true" in out[2]
    assert out[3] == "unsat"
    assert out[4] == "sat"


def test_smt2_qf_lra_qf_lia_lira_and_qf_uflia() -> None:
    lra_script = """
    (set-logic QF_LRA)
    (declare-const x Real)
    (declare-const y Real)
    (assert (< 0 x (/ 1 2)))
    (assert (= (+ (* 2 x) (- y)) 1.5))
    (check-sat)
    (get-model)
    (push)
    (assert (>= x 1))
    (check-sat)
    (pop)
    (check-sat)
    """
    lra_out = run_smt2(lra_script)
    assert lra_out[0] == "sat"
    assert "(define-fun x () Real" in lra_out[1]
    assert "(define-fun y () Real" in lra_out[1]
    assert lra_out[2] == "unsat"
    assert lra_out[3] == "sat"

    lia_unsat = """
    (set-logic QF_LIA)
    (declare-const a Int)
    (declare-const b Int)
    (assert (= (+ (* 2 a) (* 2 b)) (- 3)))
    (check-sat)
    """
    assert run_smt2(lia_unsat) == ["unsat"]

    lira_and_uflia = """
    (set-logic ALL)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const r Real)
    (declare-fun f (Int) Int)
    (assert (<= 1 x))
    (assert (< (to_real x) 2.5))
    (assert (= r (/ (to_real x) 2)))
    (assert (= y x))
    (assert (distinct (f x) (f y)))
    (check-sat)
    (reset-assertions)
    (declare-const z Int)
    (declare-fun h (Int) Int)
    (assert (<= 0 z 0))
    (assert (<= 0 y 0))
    (assert (= (h z) 7))
    (assert (= z y))
    (check-sat)
    (get-model)
    (get-value (z y (h y)))
    """
    out = run_smt2(lira_and_uflia)
    assert out[0] == "unsat"
    assert out[1] == "sat"
    assert "(define-fun h ((x!0 Int)) Int (ite (= x!0 0) 7 0))" in out[2]
    assert out[3] == "((z 0) (y 0) ((h y) 7))"
