import pytest

from unsat.model import Model
from unsat.parser import SMT2Runner, execute_smt2, format_smt2_model, run_smt2
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
        "(define-fun f ((x Bool)) Bool (f x))",
        "(define-fun bad ((x Bool) (x Bool)) Bool x)",
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


def test_smt2_qf_bv_qf_ax_and_qf_auflia() -> None:
    bv_script = """
    (set-logic QF_BV)
    (declare-const x (_ BitVec 8))
    (declare-const y (_ BitVec 8))
    (assert (= (bvadd x y) #x10))
    (assert (= (bvor ((_ extract 3 0) x) #b0001) #x3))
    (assert (= (bvcomp ((_ zero_extend 4) ((_ extract 3 0) y)) (_ bv14 8)) #b1))
    (assert (distinct (bvnand x y) (bvnot (bvand x y))))
    (check-sat)
    (reset-assertions)
    (declare-const a (_ BitVec 8))
    (assert (= a #x0a))
    (assert (= ((_ rotate_left 2) a) #x28))
    (assert (= ((_ sign_extend 4) #x8) #xf8))
    (assert (= ((_ repeat 2) #x5) #x55))
    (check-sat)
    (get-model)
    (get-value (a))
    """
    bv_out = run_smt2(bv_script)
    assert bv_out[0] == "unsat"
    assert bv_out[1] == "sat"
    assert "(define-fun a () (_ BitVec 8) #x0a)" in bv_out[2]
    assert bv_out[3] == "((a #x0a))"

    ax_script = """
    (set-logic QF_AX)
    (declare-sort I 0)
    (declare-sort V 0)
    (declare-const a (Array I V))
    (declare-const i I)
    (declare-const v V)
    (assert (= (select a i) v))
    (assert (= (store a i v) a))
    (check-sat)
    (reset-assertions)
    (declare-const b (Array Int Int))
    (declare-const x Int)
    (assert (= (store ((as const (Array Int Int)) 0) x 9) b))
    (assert (= x 4))
    (check-sat)
    (get-model)
    (get-value ((select b 4) (select b 0)))
    """
    ax_out = run_smt2(ax_script)
    assert ax_out[0] == "sat"
    assert ax_out[1] == "sat"
    assert "(define-fun b () (Array Int Int)" in ax_out[2]
    assert ax_out[3] == "(((select b 4) 9) ((select b 0) 0))"

    auflia_script = """
    (set-logic QF_AUFLIA)
    (declare-const arr (Array Int Int))
    (declare-const i Int)
    (declare-const j Int)
    (declare-fun g (Int) Int)
    (assert (= (select (store arr i 11) j) (g 3)))
    (assert (= i j))
    (assert (distinct (g 3) 11))
    (check-sat)
    """
    assert run_smt2(auflia_script) == ["unsat"]


def test_smt2_quantifiers_uf_lia_patterns_and_let_capture() -> None:
    uf_script = """
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun f (U) U)
    (declare-fun g (U) U)
    (declare-fun P (U) Bool)
    (declare-const a U)
    (declare-const c U)
    (declare-const d U)
    (assert (forall ((x U)) (! (P (f (g x))) :pattern ((f (g x))))))
    (assert (= (g a) c))
    (assert (= (f c) d))
    (assert (not (P d)))
    (check-sat)
    """
    assert run_smt2(uf_script) == ["unsat"]

    lia_script = """
    (set-logic LIA)
    (assert (exists ((x Int)) (forall ((y Int)) (=> (>= y 0) (>= y x)))))
    (check-sat)
    (get-model)
    (reset)
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (assert (forall ((x Int)) (= (f x) (+ x 1))))
    (check-sat)
    """
    lia_out = run_smt2(lia_script)
    assert lia_out[0] == "sat"
    assert lia_out[1] == "()"
    assert lia_out[2] == "unknown"

    capture_script = """
    (set-logic LIA)
    (declare-const x Int)
    (assert (= x 5))
    (assert (not (let ((t x)) (forall ((x Int)) (= t x)))))
    (check-sat)
    (assert (let ((t x)) (forall ((x Int)) (= t x))))
    (check-sat)
    """
    assert run_smt2(capture_script) == ["sat", "unsat"]


def test_smt2_parameterized_define_fun_and_scoping() -> None:
    script = """
    (set-logic ALL)
    (define-fun inc ((x Int)) Int (+ x 1))
    (define-fun inc2 ((x Int)) Int (inc (inc x)))
    (define-fun half_plus ((x Real)) Real (+ (/ x 2) 1))
    (define-fun mask4 ((v (_ BitVec 4))) (_ BitVec 4) (bvand v #x3))
    (declare-const a Int)
    (declare-const r Real)
    (declare-const bv (_ BitVec 4))
    (assert (= (inc2 a) 10))
    (assert (= (half_plus 4) r))
    (assert (= (mask4 #b1101) bv))
    (check-sat)
    (get-value (a r bv))
    """
    out = run_smt2(script)
    assert out[0] == "sat"
    assert "(a 8)" in out[1]
    assert "(r 3.0)" in out[1] or "(r (/ 3 1))" in out[1]
    assert "(bv #x1)" in out[1]

    # Shadowing under push/pop and capture avoidance under quantifiers.
    shadow_and_capture = """
    (set-logic LIA)
    (declare-fun g (Int) Int)
    (declare-const x Int)
    (define-fun all_eq ((y Int)) Bool (forall ((x Int)) (= x y)))
    (assert (= (g 2) 10))
    (assert (not (all_eq x)))
    (check-sat)
    (push 1)
    (define-fun g ((z Int)) Int (+ z 1))
    (assert (= (g 2) 3))
    (check-sat)
    (pop 1)
    (assert (= (g 2) 10))
    (check-sat)
    """
    assert run_smt2(shadow_and_capture) == ["sat", "sat", "sat"]

    # Sort mismatch and arity errors.
    for bad in (
        "(define-fun f ((x Int)) Int (+ x 1))\n(assert (= (f 1 2) 3))",
        "(define-fun f ((x Int)) Int (+ x 1))\n(assert (= (f true) 3))",
        "(define-fun f ((x Int)) Int (+ x 1))\n(assert f)",
        "(define-fun f ((x Int)) Int true)",
    ):
        with pytest.raises((TypeError, ValueError), match=r".+"):
            run_smt2(bad)


def test_smt2_define_sort_and_cycles() -> None:
    script = """
    (set-logic QF_AUFBV)
    (define-sort Byte () (_ BitVec 8))
    (define-sort Pair (K V) (Array K V))
    (define-sort RegMap (V) (Pair Byte V))
    (declare-const m (RegMap (_ BitVec 4)))
    (declare-const k Byte)
    (assert (= (select (store m k #x5) k) #x5))
    (check-sat)
    (push 1)
    (define-sort Local () Int)
    (declare-const n Local)
    (assert (= (+ n 1) 4))
    (check-sat)
    (pop 1)
    """
    assert run_smt2(script) == ["sat", "sat"]

    for bad in (
        "(push 1)\n(define-sort Local () Int)\n(pop 1)\n(declare-const n Local)",
        (
            "(define-sort A () Bool)\n(define-sort B () A)\n"
            "(push 1)\n(define-sort A () B)\n(declare-const x A)"
        ),
        "(define-sort Pair (A B) (Array A B))\n(declare-const x Pair)",
        "(define-sort Pair (A B) (Array A B))\n(declare-const x (Pair Int))",
        "(define-sort Int () Bool)",
    ):
        with pytest.raises(ValueError, match=r".+"):
            run_smt2(bad)


def test_smt2_named_unsat_core_get_assertions_and_echo() -> None:
    script = '''
    (set-logic QF_LIA)
    (echo "starting ""check""")
    (declare-const x Int)
    (declare-const y Int)
    (assert (! (> x 5) :named a1))
    (assert (! (< x 2) :named |a 2|))
    (assert (! (= y 10) :named extra))
    (get-assertions)
    (check-sat)
    (get-unsat-core)
    '''
    out = run_smt2(script)
    assert out[0] == '"starting ""check"""'
    assert out[1] == "((> x 5) (< x 2) (= y 10))"
    assert out[2] == "unsat"
    assert "a1" in out[3]
    assert "|a 2|" in out[3]
    assert "extra" not in out[3]

    # push/pop retracts named assertions cleanly and allows name reuse; model hides
    # internal indicator constants.
    scoped = """
    (set-logic QF_BOOL)
    (declare-const p Bool)
    (assert (! p :named h1))
    (push 1)
    (assert (! (not p) :named h2))
    (check-sat)
    (get-unsat-core)
    (pop 1)
    (assert (! p :named h2))
    (check-sat)
    (get-model)
    (get-assertions)
    (reset-assertions)
    (get-assertions)
    """
    scoped_out = run_smt2(scoped)
    assert scoped_out[0] == "unsat"
    assert scoped_out[1] in ("(h1 h2)", "(h2 h1)")
    assert scoped_out[2] == "sat"
    assert "__smt2_named" not in scoped_out[3]
    assert scoped_out[4] == "(p p)"
    assert scoped_out[5] == "()"

    # Unnamed-only UNSAT returns empty core.
    unnamed_script = (
        "(declare-const p Bool)\n(assert p)\n(assert (not p))\n"
        "(check-sat)\n(get-unsat-core)"
    )
    assert run_smt2(unnamed_script) == ["unsat", "()"]

    # Quantified :named assertion core.
    q_core = """
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun P (U) Bool)
    (declare-const a U)
    (declare-const b U)
    (assert (! (forall ((x U)) (! (P x) :pattern ((P x)))) :named ax))
    (assert (! (not (P a)) :named neg_a))
    (assert (! (= b b) :named triv))
    (check-sat)
    (get-unsat-core)
    """
    q_out = run_smt2(q_core)
    assert q_out[0] == "unsat"
    assert "ax" in q_out[1]
    assert "neg_a" in q_out[1]
    assert "triv" not in q_out[1]

    # Invalid usages: get-unsat-core without unsat, duplicate :named, non-string echo.
    for bad in (
        "(get-unsat-core)",
        "(assert true)\n(check-sat)\n(get-unsat-core)",
        "(declare-const p Bool)\n(assert (! p :named h))\n(assert (! p :named h))",
        "(echo 123)",
    ):
        with pytest.raises(ValueError, match=r".+"):
            run_smt2(bad)


def test_smt2_runner_preserves_budgets_across_reset_and_reset_assertions() -> None:
    script = """
    (set-logic UF)
    (declare-fun P (Int) Bool)
    (assert (forall ((x Int)) (! (P x) :pattern ((P x)))))
    (check-sat)
    (reset-assertions)
    (assert (forall ((x Int)) (! (P x) :pattern ((P x)))))
    (check-sat)
    (reset)
    (set-logic UF)
    (declare-fun Q (Int) Bool)
    (assert (forall ((x Int)) (! (Q x) :pattern ((Q x)))))
    (check-sat)
    """
    outputs, _ = execute_smt2(script, max_quantifier_rounds=0)
    assert outputs == ["unknown", "unknown", "unknown"]

    # Also verify SMT2Runner preserves timeout=0.0 across resets.
    runner = SMT2Runner(timeout=0.0)
    res = runner.execute(
        "(declare-const p Bool)\n(assert p)\n(check-sat)\n"
        "(reset-assertions)\n(assert p)\n(check-sat)\n"
        "(reset)\n(declare-const q Bool)\n(assert q)\n(check-sat)\n"
    )
    assert res == ["unknown", "unknown", "unknown"]
