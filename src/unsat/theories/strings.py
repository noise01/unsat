"""Theory solver for Strings and Regular Expressions (``QF_S``, ``QF_SLIA``).

Implements incremental CDCL(T) theory solving cooperating with ``EUFSolver`` and
``LRASolver`` (LIA length/code-point constraints):
- Brzozowski derivative regular-expression membership, intersection, complement,
  bounded emptiness checks, and regex length bound extraction.
- Word-equation normal-form alignment and length-guided Nielsen case splits.
- Character-slot Union-Find for concrete ``str`` model synthesis and full validation
  of extended operators (``str.contains``, ``str.<``, ``str.<=``, ``str.to_code``,
  ``str.from_code``, ``str.to_int``, ``str.from_int``, ``str.replace_all``).

Depends on: ``syntax``, ``theories.base``, ``theories.euf``, ``theories.lra``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl
from unsat.syntax.context_strings import expr_to_re
from unsat.syntax.str_eval import (
    MAX_CHAR_CODE,
    Interval,
    ReNode,
    eval_str_from_code,
    eval_str_from_int,
    eval_str_replace_all,
    eval_str_to_code,
    eval_str_to_int,
    normalize_intervals,
    re_comp,
    re_deriv,
    re_find_word_of_length,
    re_inter,
    re_is_empty,
    re_matches,
    re_min_max_length,
    re_minterms,
    re_nullable,
)
from unsat.theories.base import StringStats, TheoryLit
from unsat.theories.euf import EUFSolver
from unsat.theories.lra import LRASolver

_MAX_SYNTHESIS_TOTAL_LEN = 4096


@dataclass(frozen=True, slots=True)
class StringBudget:
    """Budget limiting string lemma emission, Nielsen splits, and unfolding."""

    max_lemmas: int = 300
    max_splits: int = 96
    max_unfold_depth: int = 24


@dataclass(frozen=True, slots=True)
class StringLemma:
    """Conditional string theory lemma ``(reasons => formula)``."""

    formula: Expr
    reasons: tuple[TheoryLit, ...] = ()


@dataclass(frozen=True, slots=True)
class StringUnknown:
    """Indicator that string solving reached budget/decidability limits."""

    reason: str


@dataclass(frozen=True, slots=True)
class _TokChar:
    char: str


@dataclass(frozen=True, slots=True)
class _TokVar:
    term: Expr
    rep: Expr


type _Token = _TokChar | _TokVar


class StringSolver:
    """Incremental theory solver for ``String`` and ``RegLan`` constraints."""

    def __init__(
        self,
        ctx: Context,
        *,
        budget: StringBudget | None = None,
    ) -> None:
        self._ctx = ctx
        self._budget = StringBudget() if budget is None else budget
        self._stats = StringStats()

        self._registered_terms: set[Expr] = set()
        self._concat_terms: list[App] = []
        self._to_code_terms: list[App] = []
        self._from_code_terms: list[App] = []
        self._to_int_terms: list[App] = []
        self._from_int_terms: list[App] = []
        self._replace_all_terms: list[App] = []
        self._registered_atoms: set[Expr] = set()

        self._asserted_atoms: dict[Expr, bool] = {}
        self._trail: list[Expr] = []
        self._trail_marks: list[int] = []

        self._skolem_decls: set[FuncDecl] = set()
        self._skolem_seq: int = 0
        self._split_skolems: dict[tuple[object, ...], App] = {}
        self._splits_used: int = 0
        self._last_model: dict[Expr, str] = {}
        self._emitted_conditional: set[tuple[Expr, frozenset[TheoryLit]]] = set()

    @property
    def stats(self) -> StringStats:
        """Instrumentation counters accumulated across checks."""
        return self._stats

    @property
    def internal_decls(self) -> frozenset[FuncDecl]:
        """Fresh Skolem string constants created during Nielsen splits."""
        return frozenset(self._skolem_decls)

    def reset_check_state(self) -> None:
        """Reset per-``check()`` budgets while keeping incremental state."""
        self._splits_used = 0
        self._last_model.clear()
        self._emitted_conditional.clear()

    def _get_split_skolem(self, key: tuple[object, ...]) -> App:
        existing = self._split_skolems.get(key)
        if existing is not None:
            return existing
        name = f"__str_sk!{self._skolem_seq}"
        self._skolem_seq += 1
        app = self._ctx.mk_string(name)
        self._skolem_decls.add(app.decl)
        self._split_skolems[key] = app
        return app

    def push(self) -> None:
        """Save assertion trail checkpoint."""
        self._trail_marks.append(len(self._trail))

    def pop(self, num_levels: int = 1) -> None:
        """Restore asserted string predicates back ``num_levels`` frames."""
        if num_levels < 0 or num_levels > len(self._trail_marks):
            msg = f"Invalid pop level {num_levels}"
            raise ValueError(msg)
        if num_levels == 0:
            return
        target = self._trail_marks[-num_levels]
        del self._trail_marks[-num_levels:]
        while len(self._trail) > target:
            atom = self._trail.pop()
            self._asserted_atoms.pop(atom, None)

    def register_term(self, term: Expr) -> None:
        """Register a ``String`` term or string-producing/inspecting op."""
        if term in self._registered_terms:
            return
        self._registered_terms.add(term)
        if not isinstance(term, App):
            return
        kind = term.decl.kind
        if kind is DeclKind.STR_CONCAT:
            self._concat_terms.append(term)
        elif kind is DeclKind.STR_TO_CODE:
            self._to_code_terms.append(term)
        elif kind is DeclKind.STR_FROM_CODE:
            self._from_code_terms.append(term)
        elif kind is DeclKind.STR_TO_INT:
            self._to_int_terms.append(term)
        elif kind is DeclKind.STR_FROM_INT:
            self._from_int_terms.append(term)
        elif kind is DeclKind.STR_REPLACE_ALL:
            self._replace_all_terms.append(term)

    def register_atom(self, atom: Expr) -> None:
        """Register a string predicate (``str.in_re``, ``contains``, ``<``, ``<=``)."""
        if atom in self._registered_atoms:
            return
        self._registered_atoms.add(atom)
        if isinstance(atom, App):
            for arg in atom.args:
                if arg.is_string:
                    self.register_term(arg)

    def assert_atom(self, atom: Expr, polarity: bool) -> None:
        """Record an active truth assignment for ``atom``."""
        self.register_atom(atom)
        if atom in self._asserted_atoms:
            return
        self._asserted_atoms[atom] = polarity
        self._trail.append(atom)

    def concrete_values(self) -> dict[Expr, str]:
        """Return concrete ``str`` values synthesized in the latest ``check()``."""
        return dict(self._last_model)

    def _lra_int(self, lra_conc: dict[Expr, Fraction], expr: Expr) -> int | None:
        if isinstance(expr, Const) and expr.is_int:
            assert isinstance(expr.value, int)
            assert not isinstance(expr.value, bool)
            return expr.value
        val = lra_conc.get(expr)
        if val is not None and val.denominator == 1:
            return val.numerator
        return None

    def _already_emitted(
        self,
        lemma_expr: Expr,
        reasons: tuple[TheoryLit, ...],
        emitted_lemmas: set[Expr],
    ) -> bool:
        if lemma_expr is self._ctx.false_expr or reasons:
            return (
                lemma_expr,
                frozenset(dict.fromkeys(reasons)),
            ) in self._emitted_conditional
        return lemma_expr in emitted_lemmas

    def _emit(
        self,
        lemma_expr: Expr,
        reasons: tuple[TheoryLit, ...],
        emitted_lemmas: set[Expr],
        counter: str,
    ) -> list[StringLemma] | StringUnknown:
        if (
            len(emitted_lemmas) + len(self._emitted_conditional)
            >= self._budget.max_lemmas
        ):
            self._stats.unknowns += 1
            return StringUnknown("String lemma budget exhausted")
        if lemma_expr is self._ctx.true_expr:
            self._stats.unknowns += 1
            return StringUnknown("String lemma simplified to true")
        unique_rsns = tuple(dict.fromkeys(reasons))
        if lemma_expr is self._ctx.false_expr or unique_rsns:
            key = (lemma_expr, frozenset(unique_rsns))
            if key not in self._emitted_conditional:
                self._emitted_conditional.add(key)
                setattr(self._stats, counter, getattr(self._stats, counter) + 1)
                return [StringLemma(lemma_expr, unique_rsns)]
            self._stats.unknowns += 1
            return StringUnknown("Repeated string lemma loop")
        if lemma_expr not in emitted_lemmas:
            emitted_lemmas.add(lemma_expr)
            setattr(self._stats, counter, getattr(self._stats, counter) + 1)
            return [StringLemma(lemma_expr, ())]
        self._stats.unknowns += 1
        return StringUnknown("Repeated string lemma loop")

    def _flatten_term_with_reasons(
        self,
        expr: Expr,
        euf: EUFSolver,
        rep_const: dict[Expr, str],
        rep_const_expr: dict[Expr, Const],
        rep_concat: dict[Expr, App],
        visiting: set[Expr],
        *,
        expand_root: bool = False,
    ) -> tuple[list[_Token], list[TheoryLit]]:
        rep = euf.rep_expr(expr)
        if not expand_root and rep in rep_const:
            c_expr = rep_const_expr[rep]
            rsns = euf.explain_terms_equal(expr, c_expr) if expr is not c_expr else []
            return ([_TokChar(ch) for ch in rep_const[rep]], rsns)
        if isinstance(expr, App) and expr.decl.kind is DeclKind.STR_CONCAT:
            toks: list[_Token] = []
            rsns: list[TheoryLit] = []
            for arg in expr.args:
                sub_toks, sub_rsns = self._flatten_term_with_reasons(
                    arg, euf, rep_const, rep_const_expr, rep_concat, visiting
                )
                toks.extend(sub_toks)
                rsns.extend(sub_rsns)
            return toks, rsns
        cat = None if expand_root else rep_concat.get(rep)
        if cat is not None and rep not in visiting:
            visiting.add(rep)
            rsns = euf.explain_terms_equal(expr, cat) if expr is not cat else []
            sub_toks, sub_rsns = self._flatten_term_with_reasons(
                cat, euf, rep_const, rep_const_expr, rep_concat, visiting
            )
            visiting.remove(rep)
            rsns.extend(sub_rsns)
            return sub_toks, rsns
        return ([_TokVar(expr, rep)], [])

    def check(
        self,
        euf: EUFSolver,
        lra: LRASolver,
        *,
        emitted_lemmas: set[Expr],
    ) -> list[StringLemma] | StringUnknown | None:
        """Check consistency across string equations, regexes, lengths, and ops."""
        self._last_model = {}
        str_reps = euf.terms_of_sort(self._ctx.string_sort)
        if not str_reps and not self._asserted_atoms and not self._registered_terms:
            return None

        self._stats.checks += 1
        ctx = self._ctx
        lra_conc = lra.concrete_values()

        # 1. Index EUF classes, constants, and known LIA lengths for String terms.
        rep_const: dict[Expr, str] = {}
        rep_const_expr: dict[Expr, Const] = {}
        rep_len_term: dict[Expr, Expr] = {}
        rep_lengths: dict[Expr, int] = {}

        all_str_terms: list[Expr] = []
        seen_terms: set[Expr] = set()
        for rep in str_reps:
            for member in euf.eclass_members(rep):
                if member not in seen_terms:
                    seen_terms.add(member)
                    all_str_terms.append(member)
        for t in self._registered_terms:
            if t.is_string and t not in seen_terms:
                seen_terms.add(t)
                all_str_terms.append(t)

        for term in all_str_terms:
            rep = euf.rep_expr(term)
            if isinstance(term, Const) and term.is_string:
                assert isinstance(term.value, str)
                if rep in rep_const and rep_const[rep] != term.value:
                    rsns = tuple(euf.explain_terms_equal(rep_const_expr[rep], term))
                    return self._emit(
                        ctx.false_expr, rsns, emitted_lemmas, "word_splits"
                    )
                rep_const[rep] = term.value
                rep_const_expr[rep] = term
                rep_lengths[rep] = len(term.value)
                continue
            len_node = ctx.mk_str_len(term)
            lv = self._lra_int(lra_conc, len_node)
            if lv is not None:
                if lv < 0:
                    return self._emit(
                        ctx.mk_ge(len_node, ctx.mk_int_val(0)),
                        (),
                        emitted_lemmas,
                        "length_lemmas",
                    )
                if rep not in rep_len_term:
                    rep_len_term[rep] = term
                    rep_lengths[rep] = lv
                elif rep in rep_lengths and rep_lengths[rep] != lv:
                    # Sync length equality across EUF-equal members.
                    other_t = rep_len_term.get(rep)
                    if other_t is not None and not isinstance(other_t, Const):
                        rsns = tuple(euf.explain_terms_equal(term, other_t))
                        return self._emit(
                            ctx.mk_eq(len_node, ctx.mk_str_len(other_t)),
                            rsns,
                            emitted_lemmas,
                            "length_lemmas",
                        )

        # Ensure constants vs LRA lengths agree; L(x)==0 forces x==""
        for term in all_str_terms:
            if isinstance(term, Const):
                continue
            rep = euf.rep_expr(term)
            len_node = ctx.mk_str_len(term)
            lv = self._lra_int(lra_conc, len_node)
            if rep in rep_const:
                c_expr = rep_const_expr[rep]
                c_val = rep_const[rep]
                if lv is not None and lv != len(c_val):
                    rsns = tuple(euf.explain_terms_equal(term, c_expr))
                    return self._emit(
                        ctx.mk_eq(len_node, ctx.mk_int_val(len(c_val))),
                        rsns,
                        emitted_lemmas,
                        "length_lemmas",
                    )
            elif lv == 0:
                empty_e = ctx.mk_string_val("")
                if not euf.are_equal(term, empty_e):
                    eq_empty = ctx.mk_implies(
                        ctx.mk_eq(len_node, ctx.mk_int_val(0)),
                        ctx.mk_eq(term, empty_e),
                    )
                    if eq_empty not in emitted_lemmas:
                        return self._emit(eq_empty, (), emitted_lemmas, "length_lemmas")

        # Map non-const E-classes to concat members and fold identity concats.
        rep_concat: dict[Expr, App] = {}
        for rep in str_reps:
            if rep in rep_const:
                continue
            for member in euf.eclass_members(rep):
                if isinstance(member, App) and member.decl.kind is DeclKind.STR_CONCAT:
                    rep_concat[rep] = member
                    break

        for concat in self._concat_terms:
            toks, rsns = self._flatten_term_with_reasons(
                concat,
                euf,
                rep_const,
                rep_const_expr,
                rep_concat,
                set(),
                expand_root=True,
            )
            if all(isinstance(t, _TokChar) for t in toks):
                cs = "".join(t.char for t in toks if isinstance(t, _TokChar))
                rep_c = euf.rep_expr(concat)
                if rep_c in rep_const and rep_const[rep_c] != cs:
                    full_rsns = [
                        *rsns,
                        *euf.explain_terms_equal(concat, rep_const_expr[rep_c]),
                    ]
                    return self._emit(
                        ctx.false_expr, tuple(full_rsns), emitted_lemmas, "word_splits"
                    )
                c_target = ctx.mk_string_val(cs)
                if not euf.are_equal(concat, c_target):
                    eq_c = ctx.mk_eq(concat, c_target)
                    rsns_t = tuple(rsns)
                    if not self._already_emitted(eq_c, rsns_t, emitted_lemmas):
                        return self._emit(eq_c, rsns_t, emitted_lemmas, "word_splits")
            elif len(toks) == 1 and isinstance(toks[0], _TokVar):
                single_t = toks[0].term
                if not euf.are_equal(concat, single_t):
                    eq_s = ctx.mk_eq(concat, single_t)
                    rsns_t = tuple(rsns)
                    if not self._already_emitted(eq_s, rsns_t, emitted_lemmas):
                        return self._emit(eq_s, rsns_t, emitted_lemmas, "word_splits")

        # 2. Regex membership & intersection checks per String equivalence class.
        class_regex_atoms: dict[Expr, list[tuple[App, bool, ReNode]]] = {}
        for atom, pol in self._asserted_atoms.items():
            if not isinstance(atom, App) or atom.decl.kind is not DeclKind.STR_IN_RE:
                continue
            s_arg, r_arg = atom.args
            compiled = expr_to_re(r_arg)
            if compiled is None:
                continue
            eff_re = compiled if pol else re_comp(compiled)
            rep = euf.rep_expr(s_arg)
            class_regex_atoms.setdefault(rep, []).append((atom, pol, eff_re))

        class_combined_re: dict[Expr, ReNode] = {}
        class_regex_anchor: dict[Expr, Expr] = {}
        class_regex_reasons: dict[Expr, tuple[TheoryLit, ...]] = {}
        for rep, entries in class_regex_atoms.items():
            anchor = entries[0][0].args[0]
            class_regex_anchor[rep] = anchor
            rsns: list[TheoryLit] = []
            re_nodes: list[ReNode] = []
            for atom, pol, eff_re in entries:
                rsns.append(TheoryLit(atom, pol))
                if atom.args[0] is not anchor:
                    rsns.extend(euf.explain_terms_equal(atom.args[0], anchor))
                re_nodes.append(eff_re)
            class_regex_reasons[rep] = tuple(dict.fromkeys(rsns))
            comb = re_inter(*re_nodes)
            class_combined_re[rep] = comb

            if rep in rep_const:
                c_val = rep_const[rep]
                if not re_matches(comb, c_val):
                    full_rsns = [
                        *rsns,
                        *euf.explain_terms_equal(anchor, rep_const_expr[rep]),
                    ]
                    return self._emit(
                        ctx.false_expr,
                        tuple(full_rsns),
                        emitted_lemmas,
                        "regex_lemmas",
                    )

            empt = re_is_empty(comb)
            if empt is True:
                return self._emit(
                    ctx.false_expr, tuple(rsns), emitted_lemmas, "regex_lemmas"
                )

            cur_len = rep_lengths.get(rep)
            len_host = rep_len_term.get(rep, anchor)
            if cur_len is not None and not isinstance(len_host, Const):
                min_len, max_len = re_min_max_length(comb)
                len_node = ctx.mk_str_len(len_host)
                base_rsns = tuple([*rsns, *euf.explain_terms_equal(len_host, anchor)])
                if min_len is not None and cur_len < min_len:
                    return self._emit(
                        ctx.mk_ge(len_node, ctx.mk_int_val(min_len)),
                        base_rsns,
                        emitted_lemmas,
                        "regex_lemmas",
                    )
                if max_len is not None and cur_len > max_len:
                    return self._emit(
                        ctx.mk_le(len_node, ctx.mk_int_val(max_len)),
                        base_rsns,
                        emitted_lemmas,
                        "regex_lemmas",
                    )
                if cur_len <= 256 and re_find_word_of_length(comb, cur_len) is None:
                    neq_len = ctx.mk_or(
                        ctx.mk_lt(len_node, ctx.mk_int_val(cur_len)),
                        ctx.mk_gt(len_node, ctx.mk_int_val(cur_len)),
                    )
                    return self._emit(
                        neq_len, base_rsns, emitted_lemmas, "regex_lemmas"
                    )

        # 3. Word-equation alignment & length-guided Nielsen splits across E-classes.
        for rep in str_reps:
            members = euf.eclass_members(rep)
            concats = [
                m
                for m in members
                if isinstance(m, App) and m.decl.kind is DeclKind.STR_CONCAT
            ]
            if not concats:
                continue
            target_lhs: Expr | None = rep_const_expr.get(rep)
            if target_lhs is None:
                target_lhs = concats[0]
                others = [m for m in members if m is not target_lhs]
            else:
                others = concats
            for rhs_e in others:
                if rhs_e is target_lhs:
                    continue
                lhs_seq, l_rsns = self._flatten_term_with_reasons(
                    target_lhs,
                    euf,
                    rep_const,
                    rep_const_expr,
                    rep_concat,
                    set(),
                    expand_root=isinstance(target_lhs, App)
                    and target_lhs.decl.kind is DeclKind.STR_CONCAT,
                )
                rhs_seq, r_rsns = self._flatten_term_with_reasons(
                    rhs_e,
                    euf,
                    rep_const,
                    rep_const_expr,
                    rep_concat,
                    set(),
                    expand_root=isinstance(rhs_e, App)
                    and rhs_e.decl.kind is DeclKind.STR_CONCAT,
                )
                eq_rsns = tuple(
                    [*euf.explain_terms_equal(target_lhs, rhs_e), *l_rsns, *r_rsns]
                )
                res = self._align_sequences(
                    lhs_seq, rhs_seq, eq_rsns, euf, rep_lengths, emitted_lemmas
                )
                if res is not None:
                    return res

        # 4. Character-slot model synthesis across all String equivalence classes.
        synth_res = self._synthesize_and_verify(
            str_reps,
            all_str_terms,
            euf,
            lra_conc,
            rep_const,
            rep_const_expr,
            rep_lengths,
            rep_len_term,
            class_combined_re,
            class_regex_anchor,
            class_regex_reasons,
            emitted_lemmas,
        )
        if synth_res is not None:
            return synth_res

        return None

    def _toks_equal(
        self, a: _Token, b: _Token, euf: EUFSolver
    ) -> list[TheoryLit] | None:
        if isinstance(a, _TokChar) and isinstance(b, _TokChar):
            return [] if a.char == b.char else None
        if isinstance(a, _TokVar) and isinstance(b, _TokVar) and a.rep is b.rep:
            return [] if a.term is b.term else euf.explain_terms_equal(a.term, b.term)
        return None

    def _align_sequences(
        self,
        lhs: list[_Token],
        rhs: list[_Token],
        eq_rsns: tuple[TheoryLit, ...],
        euf: EUFSolver,
        rep_lengths: dict[Expr, int],
        emitted_lemmas: set[Expr],
    ) -> list[StringLemma] | StringUnknown | None:
        ctx = self._ctx
        all_rsns = list(eq_rsns)
        lo = 0
        while lo < len(lhs) and lo < len(rhs):
            eq_pref = self._toks_equal(lhs[lo], rhs[lo], euf)
            if eq_pref is None:
                break
            all_rsns.extend(eq_pref)
            lo += 1

        hi_l = len(lhs)
        hi_r = len(rhs)
        while hi_l > lo and hi_r > lo:
            eq_suf = self._toks_equal(lhs[hi_l - 1], rhs[hi_r - 1], euf)
            if eq_suf is None:
                break
            all_rsns.extend(eq_suf)
            hi_l -= 1
            hi_r -= 1

        rem_l = lhs[lo:hi_l]
        rem_r = rhs[lo:hi_r]
        if not rem_l and not rem_r:
            return None

        base_rsns = tuple(dict.fromkeys(all_rsns))
        if not rem_l or not rem_r:
            non_empty = rem_l if rem_l else rem_r
            for tok in non_empty:
                if isinstance(tok, _TokChar):
                    return self._emit(
                        ctx.false_expr, base_rsns, emitted_lemmas, "word_splits"
                    )
            empty_s = ctx.mk_string_val("")
            guards = [
                ctx.mk_eq(tok.term, empty_s)
                for tok in non_empty
                if isinstance(tok, _TokVar) and not euf.are_equal(tok.term, empty_s)
            ]
            if guards:
                guard_f = ctx.mk_and(*guards)
                if not self._already_emitted(guard_f, base_rsns, emitted_lemmas):
                    return self._emit(guard_f, base_rsns, emitted_lemmas, "word_splits")
            return None

        h_l = rem_l[0]
        h_r = rem_r[0]
        if isinstance(h_l, _TokChar) and isinstance(h_r, _TokChar):
            if h_l.char != h_r.char:
                return self._emit(
                    ctx.false_expr, base_rsns, emitted_lemmas, "word_splits"
                )
            return None

        t_l = rem_l[-1]
        t_r = rem_r[-1]
        if (
            isinstance(t_l, _TokChar)
            and isinstance(t_r, _TokChar)
            and t_l.char != t_r.char
        ):
            return self._emit(ctx.false_expr, base_rsns, emitted_lemmas, "word_splits")

        # Direct variable-to-constant and variable-to-variable equality fast-paths.
        if (
            len(rem_l) == 1
            and isinstance(rem_l[0], _TokVar)
            and all(isinstance(t, _TokChar) for t in rem_r)
        ):
            cs = "".join(t.char for t in rem_r if isinstance(t, _TokChar))
            c_expr = ctx.mk_string_val(cs)
            if not euf.are_equal(rem_l[0].term, c_expr):
                lemma = ctx.mk_eq(rem_l[0].term, c_expr)
                if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                    return self._emit(lemma, base_rsns, emitted_lemmas, "word_splits")
            return None

        if (
            len(rem_r) == 1
            and isinstance(rem_r[0], _TokVar)
            and all(isinstance(t, _TokChar) for t in rem_l)
        ):
            cs = "".join(t.char for t in rem_l if isinstance(t, _TokChar))
            c_expr = ctx.mk_string_val(cs)
            if not euf.are_equal(rem_r[0].term, c_expr):
                lemma = ctx.mk_eq(rem_r[0].term, c_expr)
                if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                    return self._emit(lemma, base_rsns, emitted_lemmas, "word_splits")
            return None

        if (
            len(rem_l) == 1
            and len(rem_r) == 1
            and isinstance(rem_l[0], _TokVar)
            and isinstance(rem_r[0], _TokVar)
        ):
            if not euf.are_equal(rem_l[0].term, rem_r[0].term):
                lemma = ctx.mk_eq(rem_l[0].term, rem_r[0].term)
                if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                    return self._emit(lemma, base_rsns, emitted_lemmas, "word_splits")
            return None

        # Conjugate equation refutation (Lyndon-Schutzenberger):
        # u ++ x == y ++ v (or x ++ v == u ++ y) with x == y implies v is a
        # cyclic rotation of u, so len(u) != len(v) or v not in (u + u) is UNSAT.
        if (
            isinstance(rem_l[-1], _TokVar)
            and isinstance(rem_r[0], _TokVar)
            and rem_l[-1].rep is rem_r[0].rep
            and all(isinstance(t, _TokChar) for t in rem_l[:-1])
            and all(isinstance(t, _TokChar) for t in rem_r[1:])
        ) or (
            isinstance(rem_r[-1], _TokVar)
            and isinstance(rem_l[0], _TokVar)
            and rem_r[-1].rep is rem_l[0].rep
            and all(isinstance(t, _TokChar) for t in rem_r[:-1])
            and all(isinstance(t, _TokChar) for t in rem_l[1:])
        ):
            if isinstance(rem_l[-1], _TokVar) and all(
                isinstance(t, _TokChar) for t in rem_l[:-1]
            ):
                var_l, var_r = rem_l[-1], rem_r[0]
                u_toks, v_toks = rem_l[:-1], rem_r[1:]
            else:
                var_l, var_r = rem_r[-1], rem_l[0]
                u_toks, v_toks = rem_r[:-1], rem_l[1:]
            assert isinstance(var_l, _TokVar)
            assert isinstance(var_r, _TokVar)
            u_str = "".join(t.char for t in u_toks if isinstance(t, _TokChar))
            v_str = "".join(t.char for t in v_toks if isinstance(t, _TokChar))
            if (
                u_str
                and v_str
                and (len(u_str) != len(v_str) or v_str not in u_str + u_str)
            ):
                conj_rsns = (
                    *base_rsns,
                    *(
                        euf.explain_terms_equal(var_l.term, var_r.term)
                        if var_l.term is not var_r.term
                        else ()
                    ),
                )
                return self._emit(
                    ctx.false_expr, conj_rsns, emitted_lemmas, "word_splits"
                )

        # Prefix split on unaligned (Var, Const...) or (Var, Var) frontier.
        if isinstance(h_l, _TokChar) and isinstance(h_r, _TokVar):
            rem_l, rem_r = rem_r, rem_l
            h_l, h_r = h_r, h_l

        if isinstance(h_l, _TokVar) and isinstance(h_r, _TokChar):
            prefix_chars: list[str] = []
            for tok in rem_r:
                if isinstance(tok, _TokChar):
                    prefix_chars.append(tok.char)
                else:
                    break
            const_prefix = "".join(prefix_chars)
            c_e = ctx.mk_string_val(const_prefix)
            len_hl = rep_lengths.get(h_l.rep, 0)
            l_node = ctx.mk_str_len(h_l.term)

            if len_hl == 0:
                empty_e = ctx.mk_string_val("")
                if not euf.are_equal(h_l.term, empty_e):
                    lemma = ctx.mk_implies(
                        ctx.mk_eq(l_node, ctx.mk_int_val(0)),
                        ctx.mk_eq(h_l.term, empty_e),
                    )
                    if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                        return self._emit(
                            lemma, base_rsns, emitted_lemmas, "word_splits"
                        )
                return None

            if len_hl == len(const_prefix):
                if not euf.are_equal(h_l.term, c_e):
                    lemma = ctx.mk_implies(
                        ctx.mk_eq(l_node, ctx.mk_int_val(len(const_prefix))),
                        ctx.mk_eq(h_l.term, c_e),
                    )
                    if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                        return self._emit(
                            lemma, base_rsns, emitted_lemmas, "word_splits"
                        )
                return None

            if len_hl < len(const_prefix):
                trunc_e = ctx.mk_string_val(const_prefix[:len_hl])
                if not euf.are_equal(h_l.term, trunc_e):
                    lemma = ctx.mk_implies(
                        ctx.mk_eq(l_node, ctx.mk_int_val(len_hl)),
                        ctx.mk_eq(h_l.term, trunc_e),
                    )
                    if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                        return self._emit(
                            lemma, base_rsns, emitted_lemmas, "word_splits"
                        )
                return None

            # len_hl > len(const_prefix)
            if (
                len(emitted_lemmas) + len(self._emitted_conditional)
                >= self._budget.max_lemmas
            ):
                self._stats.unknowns += 1
                return StringUnknown("String lemma budget exhausted")
            if self._splits_used >= self._budget.max_splits:
                self._stats.unknowns += 1
                return StringUnknown("String word-split budget exhausted")
            sk = self._get_split_skolem(("c_gt", h_l.term, const_prefix))
            cat_e = ctx.mk_str_concat(c_e, sk)
            if not euf.are_equal(h_l.term, cat_e):
                cond = ctx.mk_gt(l_node, ctx.mk_int_val(len(const_prefix)))
                body = ctx.mk_and(
                    ctx.mk_eq(h_l.term, cat_e),
                    ctx.mk_eq(
                        ctx.mk_str_len(sk),
                        ctx.mk_sub(l_node, ctx.mk_int_val(len(const_prefix))),
                    ),
                )
                lemma = ctx.mk_implies(cond, body)
                if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                    self._splits_used += 1
                    return self._emit(lemma, base_rsns, emitted_lemmas, "word_splits")
            return None

        if isinstance(h_l, _TokVar) and isinstance(h_r, _TokVar):
            l1 = rep_lengths.get(h_l.rep, 0)
            l2 = rep_lengths.get(h_r.rep, 0)
            ln1 = ctx.mk_str_len(h_l.term)
            ln2 = ctx.mk_str_len(h_r.term)
            if l1 == l2:
                if not euf.are_equal(h_l.term, h_r.term):
                    lemma = ctx.mk_implies(
                        ctx.mk_eq(ln1, ln2), ctx.mk_eq(h_l.term, h_r.term)
                    )
                    if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                        return self._emit(
                            lemma, base_rsns, emitted_lemmas, "word_splits"
                        )
                return None

            if self._splits_used >= self._budget.max_splits:
                self._stats.unknowns += 1
                return StringUnknown("String word-split budget exhausted")
            if l1 < l2:
                short_t, long_t, l_short, l_long = h_l.term, h_r.term, ln1, ln2
            else:
                short_t, long_t, l_short, l_long = h_r.term, h_l.term, ln2, ln1
            sk = self._get_split_skolem(("v_lt", short_t, long_t))
            cat_e = ctx.mk_str_concat(short_t, sk)
            if not euf.are_equal(long_t, cat_e):
                cond = ctx.mk_lt(l_short, l_long)
                body = ctx.mk_and(
                    ctx.mk_eq(long_t, cat_e),
                    ctx.mk_eq(ctx.mk_str_len(sk), ctx.mk_sub(l_long, l_short)),
                )
                lemma = ctx.mk_implies(cond, body)
                if not self._already_emitted(lemma, base_rsns, emitted_lemmas):
                    self._splits_used += 1
                    return self._emit(lemma, base_rsns, emitted_lemmas, "word_splits")

        return None

    def _synthesize_and_verify(
        self,
        str_reps: list[Expr],
        all_str_terms: list[Expr],
        euf: EUFSolver,
        lra_conc: dict[Expr, Fraction],
        rep_const: dict[Expr, str],
        rep_const_expr: dict[Expr, Const],
        rep_lengths: dict[Expr, int],
        rep_len_term: dict[Expr, Expr],
        class_combined_re: dict[Expr, ReNode],
        class_regex_anchor: dict[Expr, Expr],
        class_regex_reasons: dict[Expr, tuple[TheoryLit, ...]],
        emitted_lemmas: set[Expr],
    ) -> list[StringLemma] | StringUnknown | None:
        ctx = self._ctx

        # Determine length for each active String class rep.
        len_map: dict[Expr, int] = {}
        total_len = 0
        for rep in str_reps:
            ln = len(rep_const[rep]) if rep in rep_const else rep_lengths.get(rep, 0)
            len_map[rep] = ln
            total_len += ln
        if total_len > _MAX_SYNTHESIS_TOTAL_LEN:
            self._stats.unknowns += 1
            return StringUnknown("Synthesized string length exceeds bound")

        rep_anchor: dict[Expr, Expr] = {}
        for rep in str_reps:
            if rep in rep_const_expr:
                rep_anchor[rep] = rep_const_expr[rep]
            elif rep in rep_len_term:
                rep_anchor[rep] = rep_len_term[rep]
            else:
                rep_anchor[rep] = rep

        # Assign dense slot IDs (rep, pos) -> slot_id
        rep_slot_base: dict[Expr, int] = {}
        slot_owner: list[tuple[Expr, int]] = []
        for rep in str_reps:
            rep_slot_base[rep] = len(slot_owner)
            for pos in range(len_map[rep]):
                slot_owner.append((rep, pos))

        n_slots = len(slot_owner)
        parent = list(range(n_slots))
        slot_char: list[str | None] = [None] * n_slots
        slot_root_pin: list[int | None] = [None] * n_slots
        # Per-slot hard pin: (char, guards, euf_reasons)
        slot_pin: list[tuple[str, tuple[Expr, ...], tuple[TheoryLit, ...]] | None] = [
            None
        ] * n_slots
        # Spanning-tree edges for minimal conflict explanation on slot collisions.
        slot_edges: list[list[tuple[int, tuple[Expr, ...], tuple[TheoryLit, ...]]]] = [
            [] for _ in range(n_slots)
        ]

        def _find(x: int) -> int:
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def _collect_path(
            src: int, dst: int
        ) -> tuple[list[Expr], list[TheoryLit]] | None:
            if src == dst:
                return ([], [])
            prev_edge: dict[
                int, tuple[int, tuple[Expr, ...], tuple[TheoryLit, ...]]
            ] = {}
            queue = [src]
            seen = {src}
            idx = 0
            found = False
            while idx < len(queue):
                cur = queue[idx]
                idx += 1
                if cur == dst:
                    found = True
                    break
                for nxt, e_guards, e_rsns in slot_edges[cur]:
                    if nxt not in seen:
                        seen.add(nxt)
                        prev_edge[nxt] = (cur, e_guards, e_rsns)
                        queue.append(nxt)
            if not found:
                return None
            guards_out: list[Expr] = []
            rsns_out: list[TheoryLit] = []
            cur = dst
            while cur != src:
                p_node, e_guards, e_rsns = prev_edge[cur]
                guards_out.extend(e_guards)
                rsns_out.extend(e_rsns)
                cur = p_node
            return guards_out, rsns_out

        def _emit_slot_conflict(
            s_a: int,
            guards_a: tuple[Expr, ...],
            rsns_a: tuple[TheoryLit, ...],
            s_b: int,
            guards_b: tuple[Expr, ...],
            rsns_b: tuple[TheoryLit, ...],
            counter: str = "word_splits",
        ) -> list[StringLemma] | StringUnknown | None:
            path = _collect_path(s_a, s_b)
            if path is None:
                return None
            p_guards, p_rsns = path
            all_guards = list(dict.fromkeys([*guards_a, *guards_b, *p_guards]))
            all_rsns = tuple(dict.fromkeys([*rsns_a, *rsns_b, *p_rsns]))
            lemma = (
                ctx.false_expr
                if not all_guards
                else ctx.mk_not(ctx.mk_and(*all_guards))
            )
            if not self._already_emitted(lemma, all_rsns, emitted_lemmas):
                return self._emit(lemma, all_rsns, emitted_lemmas, counter)
            return None

        def _pin_slot(
            s_id: int,
            ch: str,
            guards: tuple[Expr, ...],
            rsns: tuple[TheoryLit, ...],
            counter: str = "word_splits",
        ) -> list[StringLemma] | StringUnknown | None:
            r = _find(s_id)
            prev_holder = slot_root_pin[r]
            if prev_holder is not None:
                prev_pin = slot_pin[prev_holder]
                assert prev_pin is not None
                prev_ch, prev_guards, prev_rsns = prev_pin
                if prev_ch != ch:
                    conf = _emit_slot_conflict(
                        s_id, guards, rsns, prev_holder, prev_guards, prev_rsns, counter
                    )
                    if conf is not None:
                        return conf
                    self._stats.unknowns += 1
                    return StringUnknown("Repeated string char conflict")
                return None
            slot_pin[s_id] = (ch, guards, rsns)
            slot_root_pin[r] = s_id
            slot_char[r] = ch
            return None

        def _union(
            x: int,
            y: int,
            guards: tuple[Expr, ...],
            rsns: tuple[TheoryLit, ...],
        ) -> list[StringLemma] | StringUnknown | None:
            rx, ry = _find(x), _find(y)
            if rx == ry:
                return None
            cx, cy = slot_char[rx], slot_char[ry]
            if cx is not None and cy is not None and cx != cy:
                hx = slot_root_pin[rx]
                hy = slot_root_pin[ry]
                assert hx is not None
                assert hy is not None
                px = slot_pin[hx]
                py = slot_pin[hy]
                assert px is not None
                assert py is not None
                slot_edges[x].append((y, guards, rsns))
                slot_edges[y].append((x, guards, rsns))
                conf = _emit_slot_conflict(
                    hx, px[1], px[2], hy, py[1], py[2], "word_splits"
                )
                if conf is not None:
                    return conf
                self._stats.unknowns += 1
                return StringUnknown("Repeated string concat char conflict")
            if rx > ry:
                rx, ry = ry, rx
            parent[ry] = rx
            slot_edges[x].append((y, guards, rsns))
            slot_edges[y].append((x, guards, rsns))
            if slot_char[rx] is None and slot_char[ry] is not None:
                slot_char[rx] = slot_char[ry]
                slot_root_pin[rx] = slot_root_pin[ry]
            return None

        # Fix constants into slots.
        for rep, c_val in rep_const.items():
            base = rep_slot_base.get(rep)
            if base is None:
                continue
            for pos, ch in enumerate(c_val):
                conf = _pin_slot(base + pos, ch, (), ())
                if conf is not None:
                    return conf

        # Merge concat slots with prefix-length / arg-length provenance.
        for concat in self._concat_terms:
            rep = euf.rep_expr(concat)
            if rep not in rep_slot_base:
                continue
            exp_len = len_map[rep]
            arg_reps = [euf.rep_expr(a) for a in concat.args]
            sum_args = sum(len_map.get(ar, 0) for ar in arg_reps)
            if sum_args != exp_len:
                # Enforce sum length equality directly if LIA lagged behind.
                ln_lhs = ctx.mk_str_len(concat)
                ln_rhs = ctx.mk_add(*(ctx.mk_str_len(a) for a in concat.args))
                return self._emit(
                    ctx.mk_eq(ln_lhs, ln_rhs), (), emitted_lemmas, "length_lemmas"
                )
            concat_rsns = tuple(euf.explain_terms_equal(concat, rep_anchor[rep]))
            cursor = 0
            for arg_idx, (arg, ar) in enumerate(
                zip(concat.args, arg_reps, strict=True)
            ):
                a_len = len_map.get(ar, 0)
                if arg_idx == 0:
                    prefix_guard: tuple[Expr, ...] = ()
                elif arg_idx == 1:
                    prefix_guard = (
                        ctx.mk_eq(
                            ctx.mk_str_len(concat.args[0]), ctx.mk_int_val(cursor)
                        ),
                    )
                else:
                    prefix_guard = (
                        ctx.mk_eq(
                            ctx.mk_add(
                                *(ctx.mk_str_len(pa) for pa in concat.args[:arg_idx])
                            ),
                            ctx.mk_int_val(cursor),
                        ),
                    )
                if isinstance(arg, Const) and arg.is_string:
                    assert isinstance(arg.value, str)
                    for p, ch in enumerate(arg.value):
                        conf = _pin_slot(
                            rep_slot_base[rep] + cursor + p,
                            ch,
                            prefix_guard,
                            concat_rsns,
                        )
                        if conf is not None:
                            return conf
                elif ar in rep_slot_base:
                    arg_rsns = tuple(euf.explain_terms_equal(arg, rep_anchor[ar]))
                    edge_rsns = tuple([*concat_rsns, *arg_rsns])
                    for p in range(a_len):
                        edge_guards = (
                            *prefix_guard,
                            ctx.mk_ge(ctx.mk_str_len(arg), ctx.mk_int_val(p + 1)),
                        )
                        conf = _union(
                            rep_slot_base[rep] + cursor + p,
                            rep_slot_base[ar] + p,
                            edge_guards,
                            edge_rsns,
                        )
                        if conf is not None:
                            return conf
                cursor += a_len

        # Enforce exact 1-char regex code-point bounds on str.to_code terms BEFORE
        # letting arbitrary LRA corner values pin slot characters.
        for tc in self._to_code_terms:
            s_arg = tc.args[0]
            rep_s = euf.rep_expr(s_arg)
            v = self._lra_int(lra_conc, tc)
            if (
                v is not None
                and 0 <= v <= MAX_CHAR_CODE
                and len_map.get(rep_s) == 1
                and rep_s in class_combined_re
            ):
                comb = class_combined_re[rep_s]
                if not re_matches(comb, chr(v)):
                    valid_1char = normalize_intervals(
                        [
                            iv
                            for iv in re_minterms(comb)
                            if re_nullable(re_deriv(comb, iv[0]))
                        ]
                    )
                    reg_rsns = tuple(
                        [
                            *class_regex_reasons[rep_s],
                            *euf.explain_terms_equal(s_arg, class_regex_anchor[rep_s]),
                        ]
                    )
                    len_1 = ctx.mk_eq(ctx.mk_str_len(s_arg), ctx.mk_int_val(1))
                    if not valid_1char:
                        return self._emit(
                            ctx.mk_not(len_1), reg_rsns, emitted_lemmas, "regex_lemmas"
                        )
                    in_bounds = [
                        ctx.mk_and(
                            ctx.mk_ge(tc, ctx.mk_int_val(lo)),
                            ctx.mk_le(tc, ctx.mk_int_val(hi)),
                        )
                        if lo < hi
                        else ctx.mk_eq(tc, ctx.mk_int_val(lo))
                        for lo, hi in valid_1char
                    ]
                    allowed_disj = (
                        in_bounds[0] if len(in_bounds) == 1 else ctx.mk_or(*in_bounds)
                    )
                    lemma = ctx.mk_implies(len_1, allowed_disj)
                    if not self._already_emitted(lemma, reg_rsns, emitted_lemmas):
                        return self._emit(
                            lemma, reg_rsns, emitted_lemmas, "regex_lemmas"
                        )

        # Propagate str.to_code(s) == v and str.from_code(n) == r into 1-char slots.
        for tc in self._to_code_terms:
            s_arg = tc.args[0]
            rep_s = euf.rep_expr(s_arg)
            v = self._lra_int(lra_conc, tc)
            if v is not None and 0 <= v <= MAX_CHAR_CODE and len_map.get(rep_s) == 1:
                ch = chr(v)
                tc_guards = (
                    ctx.mk_eq(ctx.mk_str_len(s_arg), ctx.mk_int_val(1)),
                    ctx.mk_eq(tc, ctx.mk_int_val(v)),
                )
                tc_rsns = tuple(euf.explain_terms_equal(s_arg, rep_anchor[rep_s]))
                r = _find(rep_slot_base[rep_s])
                prev = slot_char[r]
                if prev is not None and prev != ch:
                    prev_holder = slot_root_pin[r]
                    assert prev_holder is not None
                    prev_pin = slot_pin[prev_holder]
                    assert prev_pin is not None
                    path = _collect_path(rep_slot_base[rep_s], prev_holder)
                    p_guards, p_rsns = path if path is not None else ([], [])
                    ant_guards = list(
                        dict.fromkeys(
                            [
                                ctx.mk_eq(ctx.mk_str_len(s_arg), ctx.mk_int_val(1)),
                                *prev_pin[1],
                                *p_guards,
                            ]
                        )
                    )
                    eq_target = ctx.mk_eq(tc, ctx.mk_int_val(ord(prev)))
                    lemma = (
                        eq_target
                        if not ant_guards
                        else ctx.mk_implies(ctx.mk_and(*ant_guards), eq_target)
                    )
                    all_rsns = tuple(dict.fromkeys([*tc_rsns, *prev_pin[2], *p_rsns]))
                    if not self._already_emitted(lemma, all_rsns, emitted_lemmas):
                        return self._emit(lemma, all_rsns, emitted_lemmas, "ext_lemmas")
                conf = _pin_slot(
                    rep_slot_base[rep_s], ch, tc_guards, tc_rsns, "ext_lemmas"
                )
                if conf is not None:
                    return conf

        for fc in self._from_code_terms:
            n_arg = fc.args[0]
            rep_fc = euf.rep_expr(fc)
            v = self._lra_int(lra_conc, n_arg)
            if v is not None and 0 <= v <= MAX_CHAR_CODE and len_map.get(rep_fc) == 1:
                ch = chr(v)
                fc_guards = (ctx.mk_eq(n_arg, ctx.mk_int_val(v)),)
                fc_rsns = tuple(euf.explain_terms_equal(fc, rep_anchor[rep_fc]))
                conf = _pin_slot(
                    rep_slot_base[rep_fc], ch, fc_guards, fc_rsns, "ext_lemmas"
                )
                if conf is not None:
                    return conf

        for fi in self._from_int_terms:
            n_arg = fi.args[0]
            rep_fi = euf.rep_expr(fi)
            v = self._lra_int(lra_conc, n_arg)
            if v is not None and v >= 0 and rep_fi in rep_slot_base:
                expected_s = str(v)
                if len_map[rep_fi] != len(expected_s):
                    return self._emit(
                        ctx.mk_implies(
                            ctx.mk_eq(n_arg, ctx.mk_int_val(v)),
                            ctx.mk_eq(fi, ctx.mk_string_val(expected_s)),
                        ),
                        (),
                        emitted_lemmas,
                        "ext_lemmas",
                    )
                base = rep_slot_base[rep_fi]
                fi_guards = (ctx.mk_eq(n_arg, ctx.mk_int_val(v)),)
                fi_rsns = tuple(euf.explain_terms_equal(fi, rep_anchor[rep_fi]))
                for p, ch in enumerate(expected_s):
                    conf = _pin_slot(base + p, ch, fi_guards, fi_rsns, "ext_lemmas")
                    if conf is not None:
                        return conf

        # Soft digits for str.to_int targets (avoid blocking regex solutions).
        soft_to_int_slots: dict[int, str] = {}
        for ti in self._to_int_terms:
            s_arg = ti.args[0]
            rep_s = euf.rep_expr(s_arg)
            v = self._lra_int(lra_conc, ti)
            if v is not None and v >= 0 and rep_s in rep_slot_base:
                ln = len_map[rep_s]
                digits = str(v)
                if ln < len(digits):
                    return self._emit(
                        ctx.mk_implies(
                            ctx.mk_ge(ti, ctx.mk_int_val(v)),
                            ctx.mk_ge(
                                ctx.mk_str_len(s_arg), ctx.mk_int_val(len(digits))
                            ),
                        ),
                        (),
                        emitted_lemmas,
                        "ext_lemmas",
                    )
                padded = ("0" * (ln - len(digits))) + digits
                base = rep_slot_base[rep_s]
                compatible = True
                for p, ch in enumerate(padded):
                    r = _find(base + p)
                    existing_ch = slot_char[r] or soft_to_int_slots.get(r)
                    if existing_ch is not None and existing_ch != ch:
                        compatible = False
                        break
                if compatible:
                    comb_re = class_combined_re.get(rep_s)
                    if comb_re is None or re_matches(comb_re, padded):
                        for p, ch in enumerate(padded):
                            r = _find(base + p)
                            if slot_char[r] is None:
                                soft_to_int_slots[r] = ch

        # Build EUF disequality groups among String reps.
        diseq_peers: dict[Expr, set[Expr]] = {}
        diseq_atom_map: dict[tuple[Expr, Expr], Expr] = {}
        for eq_atom, lhs, rhs in euf.asserted_disequalities():
            if not lhs.is_string:
                continue
            r1 = euf.rep_expr(lhs)
            r2 = euf.rep_expr(rhs)
            if len_map.get(r1, -1) == len_map.get(r2, -2):
                diseq_peers.setdefault(r1, set()).add(r2)
                diseq_peers.setdefault(r2, set()).add(r1)
                diseq_atom_map[(r1, r2)] = eq_atom
                diseq_atom_map[(r2, r1)] = eq_atom

        # Solve regex-constrained classes first using allowed slot chars.
        rep_word: dict[Expr, str] = dict(rep_const)
        for rep in sorted(class_combined_re, key=lambda r: (len_map.get(r, 0), r.id)):
            if rep in rep_word or rep not in rep_slot_base:
                continue
            ln = len_map[rep]
            base = rep_slot_base[rep]
            hard_allowed_at: list[tuple[Interval, ...] | None] = []
            soft_allowed_at: list[tuple[Interval, ...] | None] = []
            for p in range(ln):
                r = _find(base + p)
                ch_hard = slot_char[r]
                hard_allowed_at.append(
                    ((ord(ch_hard), ord(ch_hard)),) if ch_hard is not None else None
                )
                ch_eff = ch_hard if ch_hard is not None else soft_to_int_slots.get(r)
                soft_allowed_at.append(
                    ((ord(ch_eff), ord(ch_eff)),) if ch_eff is not None else None
                )
            forbidden = {
                rep_word[peer] for peer in diseq_peers.get(rep, ()) if peer in rep_word
            }
            comb = class_combined_re[rep]
            word = re_find_word_of_length(
                comb,
                ln,
                allowed_at=soft_allowed_at,
                forbidden=forbidden,
            )
            if word is None and soft_allowed_at != hard_allowed_at:
                word = re_find_word_of_length(
                    comb,
                    ln,
                    allowed_at=hard_allowed_at,
                    forbidden=forbidden,
                )
            if word is None:
                host = rep_len_term.get(rep, rep)
                ln_node = ctx.mk_str_len(host)
                reg_anchor = class_regex_anchor[rep]
                reg_rsns = tuple(
                    [
                        *class_regex_reasons[rep],
                        *euf.explain_terms_equal(host, reg_anchor),
                    ]
                )
                word_unpinned = re_find_word_of_length(comb, ln, forbidden=forbidden)
                if word_unpinned is None:
                    word_no_forbid = (
                        re_find_word_of_length(comb, ln) if forbidden else None
                    )
                    if word_no_forbid is not None and forbidden:
                        eq_target = ctx.mk_string_val(word_no_forbid)
                        return self._emit(
                            ctx.mk_or(
                                ctx.mk_eq(host, eq_target),
                                ctx.mk_distinct(host, eq_target),
                            ),
                            (),
                            emitted_lemmas,
                            "regex_lemmas",
                        )
                    neq_l = ctx.mk_or(
                        ctx.mk_lt(ln_node, ctx.mk_int_val(ln)),
                        ctx.mk_gt(ln_node, ctx.mk_int_val(ln)),
                    )
                    return self._emit(neq_l, reg_rsns, emitted_lemmas, "regex_lemmas")

                # Hard-pinned slot chars contradicted comb; explain via provenance.
                pin_guards: list[Expr] = [ctx.mk_eq(ln_node, ctx.mk_int_val(ln))]
                pin_rsns: list[TheoryLit] = list(reg_rsns)
                for p in range(ln):
                    r = _find(base + p)
                    if slot_char[r] is not None:
                        holder = slot_root_pin[r]
                        assert holder is not None
                        p_info = slot_pin[holder]
                        assert p_info is not None
                        path = _collect_path(base + p, holder)
                        p_guards, p_rsns = path if path is not None else ([], [])
                        pin_guards.extend(p_info[1])
                        pin_guards.extend(p_guards)
                        pin_rsns.extend(p_info[2])
                        pin_rsns.extend(p_rsns)
                pin_guards = list(dict.fromkeys(pin_guards))
                pin_lemma = (
                    ctx.false_expr
                    if not pin_guards
                    else ctx.mk_not(ctx.mk_and(*pin_guards))
                )
                pin_rsns_t = tuple(dict.fromkeys(pin_rsns))
                if not self._already_emitted(pin_lemma, pin_rsns_t, emitted_lemmas):
                    return self._emit(
                        pin_lemma,
                        pin_rsns_t,
                        emitted_lemmas,
                        "regex_lemmas",
                    )
                self._stats.unknowns += 1
                return StringUnknown("Regex slot conflict exhausted")

            rep_word[rep] = word
            for p, ch in enumerate(word):
                r = _find(base + p)
                slot_char[r] = ch
                if slot_root_pin[r] is None:
                    slot_root_pin[r] = base + p
                    slot_pin[base + p] = (ch, (), ())

        # Fill free slot components (preferring any compatible soft_to_int digits)
        # while breaking same-length EUF disequalities.
        alpha = "abcdefghijklmnopqrstuvwxyz0123456789"
        for rep in str_reps:
            if rep in rep_word or rep not in rep_slot_base:
                continue
            ln = len_map[rep]
            base = rep_slot_base[rep]
            forbidden = {
                rep_word[peer] for peer in diseq_peers.get(rep, ()) if peer in rep_word
            }
            chars: list[str] = []
            for p in range(ln):
                r = _find(base + p)
                ch = slot_char[r]
                if ch is None:
                    ch = soft_to_int_slots.get(r, "a")
                chars.append(ch)
            candidate = "".join(chars)
            if candidate in forbidden:
                # Pick a different char in the first free slot to break collision.
                resolved = False
                for p_free in range(ln):
                    r_free = _find(base + p_free)
                    if slot_char[r_free] is None:
                        for ch_alt in alpha:
                            trial = (
                                candidate[:p_free] + ch_alt + candidate[p_free + 1 :]
                            )
                            if trial not in forbidden:
                                slot_char[r_free] = ch_alt
                                candidate = trial
                                resolved = True
                                break
                    if resolved:
                        break
            for p, r in enumerate(_find(base + pos) for pos in range(ln)):
                if slot_char[r] is None:
                    slot_char[r] = candidate[p]
            rep_word[rep] = "".join(
                slot_char[_find(base + pos)] or "a" for pos in range(ln)
            )

        # Recompute concrete strings for every rep after all shared slots converged.
        for rep in str_reps:
            if rep not in rep_slot_base:
                rep_word.setdefault(rep, "")
                continue
            base = rep_slot_base[rep]
            rep_word[rep] = "".join(
                slot_char[_find(base + pos)] or "a" for pos in range(len_map[rep])
            )

        # 5. Full verification against all active constraints & extended ops!
        def _val(e: Expr) -> str:
            if isinstance(e, Const) and e.is_string:
                assert isinstance(e.value, str)
                return e.value
            return rep_word.get(euf.rep_expr(e), "")

        # Verify EUF disequalities.
        for eq_atom, lhs, rhs in euf.asserted_disequalities():
            if lhs.is_string and _val(lhs) == _val(rhs):
                v_s = _val(lhs)
                ln_v = len(v_s)
                # Shared slots made lhs and rhs identical; emit separation lemma.
                if ln_v == 0:
                    return self._emit(
                        ctx.mk_implies(
                            ctx.mk_and(
                                ctx.mk_eq(ctx.mk_str_len(lhs), ctx.mk_int_val(0)),
                                ctx.mk_eq(ctx.mk_str_len(rhs), ctx.mk_int_val(0)),
                            ),
                            eq_atom,
                        ),
                        (),
                        emitted_lemmas,
                        "word_splits",
                    )
                if ln_v <= 16:
                    neq_slots = ctx.mk_or(
                        *(
                            ctx.mk_distinct(
                                ctx.mk_str_at(lhs, ctx.mk_int_val(p)),
                                ctx.mk_str_at(rhs, ctx.mk_int_val(p)),
                            )
                            for p in range(ln_v)
                        )
                    )
                    lemma = ctx.mk_implies(
                        ctx.mk_and(
                            ctx.mk_eq(ctx.mk_str_len(lhs), ctx.mk_int_val(ln_v)),
                            ctx.mk_eq(ctx.mk_str_len(rhs), ctx.mk_int_val(ln_v)),
                            ctx.mk_not(eq_atom),
                        ),
                        neq_slots,
                    )
                    if lemma not in emitted_lemmas:
                        return self._emit(lemma, (), emitted_lemmas, "word_splits")
                self._stats.unknowns += 1
                return StringUnknown("Failed to separate disequal strings")

        # Verify str.in_re.
        for rep, comb in class_combined_re.items():
            if not re_matches(comb, rep_word.get(rep, "")):
                self._stats.unknowns += 1
                return StringUnknown("Regex model verification failed")

        # Verify str.contains, str.<, str.<=
        for atom, pol in self._asserted_atoms.items():
            if not isinstance(atom, App):
                continue
            kind = atom.decl.kind
            if kind is DeclKind.STR_CONTAINS:
                vs = _val(atom.args[0])
                vt = _val(atom.args[1])
                if not pol and vt in vs:
                    idx = vs.find(vt)
                    ls, lt = len(vs), len(vt)
                    s_e, t_e = atom.args
                    if lt == 0:
                        return self._emit(atom, (), emitted_lemmas, "ext_lemmas")
                    lemma = ctx.mk_implies(
                        ctx.mk_and(
                            ctx.mk_eq(ctx.mk_str_len(s_e), ctx.mk_int_val(ls)),
                            ctx.mk_eq(ctx.mk_str_len(t_e), ctx.mk_int_val(lt)),
                            ctx.mk_not(atom),
                        ),
                        ctx.mk_distinct(
                            ctx.mk_str_substr(
                                s_e, ctx.mk_int_val(idx), ctx.mk_int_val(lt)
                            ),
                            t_e,
                        ),
                    )
                    return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")
            elif kind in (DeclKind.STR_LT, DeclKind.STR_LE):
                a_e, b_e = atom.args
                va, vb = _val(a_e), _val(b_e)
                holds = (va < vb) if kind is DeclKind.STR_LT else (va <= vb)
                if holds != pol:
                    lemma = self._lex_conflict_lemma(atom, pol, a_e, b_e, va, vb)
                    return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")

        # Verify to_code / from_code / to_int / from_int / replace_all.
        for tc in self._to_code_terms:
            s_arg = tc.args[0]
            vs = _val(s_arg)
            v = self._lra_int(lra_conc, tc)
            expected_c = eval_str_to_code(vs)
            if v is not None and v != expected_c:
                if len(vs) == 1 and expected_c >= 0:
                    lemma = ctx.mk_implies(
                        ctx.mk_eq(s_arg, ctx.mk_string_val(vs)),
                        ctx.mk_eq(tc, ctx.mk_int_val(expected_c)),
                    )
                    return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")
                if v < 0:
                    return self._emit(
                        ctx.mk_implies(
                            ctx.mk_eq(ctx.mk_str_len(s_arg), ctx.mk_int_val(len(vs))),
                            ctx.mk_ge(tc, ctx.mk_int_val(0))
                            if len(vs) == 1
                            else ctx.mk_eq(tc, ctx.mk_int_val(-1)),
                        ),
                        (),
                        emitted_lemmas,
                        "ext_lemmas",
                    )

        for fc in self._from_code_terms:
            n_arg = fc.args[0]
            v = self._lra_int(lra_conc, n_arg)
            if v is not None and _val(fc) != eval_str_from_code(v):
                lemma = ctx.mk_implies(
                    ctx.mk_eq(n_arg, ctx.mk_int_val(v)),
                    ctx.mk_eq(fc, ctx.mk_string_val(eval_str_from_code(v))),
                )
                return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")

        for ti in self._to_int_terms:
            s_arg = ti.args[0]
            vs = _val(s_arg)
            v = self._lra_int(lra_conc, ti)
            expected_i = eval_str_to_int(vs)
            if v is not None and v != expected_i:
                lemma = ctx.mk_implies(
                    ctx.mk_eq(s_arg, ctx.mk_string_val(vs)),
                    ctx.mk_eq(ti, ctx.mk_int_val(expected_i)),
                )
                return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")

        for fi in self._from_int_terms:
            n_arg = fi.args[0]
            v = self._lra_int(lra_conc, n_arg)
            if v is not None and _val(fi) != eval_str_from_int(v):
                lemma = ctx.mk_implies(
                    ctx.mk_eq(n_arg, ctx.mk_int_val(v)),
                    ctx.mk_eq(fi, ctx.mk_string_val(eval_str_from_int(v))),
                )
                return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")

        need_ra_unknown = False
        for ra in self._replace_all_terms:
            s_arg, src_arg, dst_arg = ra.args
            vs, vsrc, vdst, vr = _val(s_arg), _val(src_arg), _val(dst_arg), _val(ra)
            expected_ra = eval_str_replace_all(vs, vsrc, vdst)
            if vr != expected_ra:
                rep_s = euf.rep_expr(s_arg)
                rep_src = euf.rep_expr(src_arg)
                rep_dst = euf.rep_expr(dst_arg)
                if rep_s in rep_const and rep_src in rep_const and rep_dst in rep_const:
                    const_lemma = ctx.mk_eq(ra, ctx.mk_string_val(expected_ra))
                    c_rsns = tuple(
                        [
                            *euf.explain_terms_equal(s_arg, rep_const_expr[rep_s]),
                            *euf.explain_terms_equal(src_arg, rep_const_expr[rep_src]),
                            *euf.explain_terms_equal(dst_arg, rep_const_expr[rep_dst]),
                        ]
                    )
                    if not self._already_emitted(const_lemma, c_rsns, emitted_lemmas):
                        return self._emit(
                            const_lemma, c_rsns, emitted_lemmas, "ext_lemmas"
                        )
                if vsrc and vsrc in vs:
                    k_expr = ctx.mk_str_indexof(s_arg, src_arg, ctx.mk_int_val(0))
                    tail_start = ctx.mk_add(k_expr, ctx.mk_str_len(src_arg))
                    tail_len = ctx.mk_sub(ctx.mk_str_len(s_arg), tail_start)
                    rest_s = ctx.mk_str_substr(s_arg, tail_start, tail_len)
                    step_rhs = ctx.mk_str_concat(
                        ctx.mk_str_substr(s_arg, ctx.mk_int_val(0), k_expr),
                        dst_arg,
                        ctx.mk_str_replace_all(rest_s, src_arg, dst_arg),
                    )
                    lemma = ctx.mk_implies(
                        ctx.mk_and(
                            ctx.mk_distinct(src_arg, ctx.mk_string_val("")),
                            ctx.mk_ge(k_expr, ctx.mk_int_val(0)),
                        ),
                        ctx.mk_eq(ra, step_rhs),
                    )
                    if lemma not in emitted_lemmas:
                        return self._emit(lemma, (), emitted_lemmas, "ext_lemmas")
                need_ra_unknown = True
        if need_ra_unknown:
            self._stats.unknowns += 1
            return StringUnknown("str.replace_all refinement exhausted")

        # Save concrete model for all registered String terms.
        model_out: dict[Expr, str] = {}
        for term in all_str_terms:
            if not isinstance(term, Const):
                model_out[term] = _val(term)
        self._last_model = model_out
        return None

    def _lex_conflict_lemma(
        self,
        atom: App,
        pol: bool,
        a_e: Expr,
        b_e: Expr,
        va: str,
        vb: str,
    ) -> Expr:
        ctx = self._ctx
        la, lb = len(va), len(vb)
        m = min(la, lb)
        lcp = 0
        while lcp < m and va[lcp] == vb[lcp]:
            lcp += 1
        lit_atom = atom if pol else ctx.mk_not(atom)
        len_guards: list[Expr] = [
            ctx.mk_eq(ctx.mk_str_len(a_e), ctx.mk_int_val(la)),
            ctx.mk_eq(ctx.mk_str_len(b_e), ctx.mk_int_val(lb)),
            lit_atom,
        ]
        if lcp > 0:
            len_guards.append(
                ctx.mk_eq(
                    ctx.mk_str_substr(a_e, ctx.mk_int_val(0), ctx.mk_int_val(lcp)),
                    ctx.mk_str_substr(b_e, ctx.mk_int_val(0), ctx.mk_int_val(lcp)),
                )
            )
        cond = ctx.mk_and(*len_guards)
        want_le = atom.decl.kind is DeclKind.STR_LE
        if lcp == m:
            if pol:
                conseq = (
                    ctx.mk_bool_val(la <= lb) if want_le else ctx.mk_bool_val(la < lb)
                )
            else:
                conseq = (
                    ctx.mk_bool_val(la > lb) if want_le else ctx.mk_bool_val(la >= lb)
                )
            return ctx.mk_implies(cond, conseq)

        ca = ctx.mk_str_to_code(ctx.mk_str_at(a_e, ctx.mk_int_val(lcp)))
        cb = ctx.mk_str_to_code(ctx.mk_str_at(b_e, ctx.mk_int_val(lcp)))
        if pol:
            return ctx.mk_implies(cond, ctx.mk_le(ca, cb))
        return ctx.mk_implies(cond, ctx.mk_ge(ca, cb))
