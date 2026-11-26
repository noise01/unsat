"""Theory combination propagator coordinating EUF, LRA, LIA, Arrays, and BV."""

from collections.abc import Callable, Sequence
from typing import Protocol

from unsat.sat import Lit, SATSolver, Var, negate, pos_lit
from unsat.syntax import Const, Context, Expr, Sort
from unsat.tactics import BitBlaster
from unsat.theories import (
    ArraySolver,
    BVBlastRequest,
    BVSolver,
    EUFSolver,
    LIACutLemma,
    LIASplitLemma,
    LRASolver,
    NLALemma,
    NLASolver,
    NLAUnknown,
    StringLemma,
    StringSolver,
    StringUnknown,
    TheoryLit,
    find_lia_lemma,
)


class _LemmaEncoder(Protocol):
    def ensure_expr_var(self, expr: Expr) -> Var: ...

    def expr_var_or_none(self, expr: Expr) -> Var | None: ...

    def encode_lemma(
        self, expr: Expr, polarity: int = 1
    ) -> tuple[Lit, list[list[Lit]]]: ...

    def encode_bv_blast_lemma(self, atom: Expr, atom_lit: Lit) -> list[list[Lit]]: ...


class _CombinedPropagator:
    """Propagator coordinating ``EUF``, ``LRA``, ``LIA``, ``BV``, and ``Arrays``."""

    def __init__(
        self,
        ctx: Context,
        euf_solver: EUFSolver,
        lra_solver: LRASolver,
        array_solver: ArraySolver,
        bv_solver: BVSolver,
        nla_solver: NLASolver,
        string_solver: StringSolver,
        bitblaster: BitBlaster,
    ) -> None:
        self._ctx = ctx
        self._sat: SATSolver | None = None
        self._euf = euf_solver
        self._lra = lra_solver
        self._arrays = array_solver
        self._bv = bv_solver
        self._nla = nla_solver
        self._strings = string_solver
        self._bitblaster = bitblaster
        self._encoder: _LemmaEncoder | None = None

        self._euf_lit_to_atoms: dict[Lit, list[tuple[Expr, bool]]] = {}
        self._euf_atom_to_pos_lit: dict[Expr, Lit] = {}

        self._lra_lit_to_atoms: dict[Lit, list[tuple[Expr, bool]]] = {}
        self._lra_atom_to_pos_lit: dict[Expr, Lit] = {}

        self._bv_lit_to_atoms: dict[Lit, list[tuple[Expr, bool]]] = {}
        self._bv_atom_to_pos_lit: dict[Expr, Lit] = {}

        self._str_lit_to_atoms: dict[Lit, list[tuple[Expr, bool]]] = {}
        self._str_atom_to_pos_lit: dict[Expr, Lit] = {}

        self._shared_arith_terms: dict[Sort, list[Expr]] = {}
        self._shared_arith_set: set[Expr] = set()
        self._shared_bv_terms: dict[Sort, list[Expr]] = {}
        self._shared_bv_set: set[Expr] = set()
        self._emitted_cuts: set[Expr] = set()
        self._emitted_nla_lemmas: set[Expr] = set()
        self._emitted_str_lemmas: set[Expr] = set()
        self._nla_unknown: bool = False
        self._string_unknown: bool = False

    def attach(self, sat_solver: SATSolver, encoder: _LemmaEncoder) -> None:
        """Bind the owning ``SATSolver`` and encoder after construction."""
        self._sat = sat_solver
        self._encoder = encoder

    @property
    def nla_unknown(self) -> bool:
        """Whether ``NLASolver`` stopped conservatively with ``NLAUnknown``."""
        return self._nla_unknown

    @property
    def string_unknown(self) -> bool:
        """Whether ``StringSolver`` stopped conservatively with ``StringUnknown``."""
        return self._string_unknown

    def reset_check_state(self) -> None:
        """Clear per-solve deduplication state before a fresh ``check()``."""
        self._emitted_cuts.clear()
        self._emitted_nla_lemmas.clear()
        self._emitted_str_lemmas.clear()
        self._nla_unknown = False
        self._string_unknown = False
        self._nla.reset_check_state()
        self._strings.reset_check_state()

    def add_shared_arith_term(self, term: Expr) -> None:
        """Record an ``Int``/``Real`` term participating in EUF for MBTC."""
        if term in self._shared_arith_set or not term.is_arith:
            return
        self._shared_arith_set.add(term)
        self._shared_arith_terms.setdefault(term.sort, []).append(term)
        self._euf.register_term(term)
        self._lra.register_term(term)

    def add_shared_bv_term(self, term: Expr) -> None:
        """Record a ``BitVec`` term participating in EUF/Arrays for BV MBTC."""
        if term in self._shared_bv_set or not term.is_bv:
            return
        self._shared_bv_set.add(term)
        self._shared_bv_terms.setdefault(term.sort, []).append(term)
        self._euf.register_term(term)
        self._bv.register_term(term)

    def all_shared_arith_terms(self) -> list[Expr]:
        """Return all registered mixed EUF+arithmetic interface terms."""
        return [t for terms in self._shared_arith_terms.values() for t in terms]

    def all_shared_bv_terms(self) -> list[Expr]:
        """Return all registered mixed EUF/Array+BitVec interface terms."""
        return [t for terms in self._shared_bv_terms.values() for t in terms]

    def has_shared_term(self, term: Expr) -> bool:
        """Return whether ``term`` is an arithmetic/EUF interface term."""
        return term in self._shared_arith_set

    def bind_euf(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None:
        """Bind positive ``lit`` to EUF atom ``(atom, True)``."""
        if atom in self._euf_atom_to_pos_lit:
            return
        self._euf_atom_to_pos_lit[atom] = lit
        self._euf_lit_to_atoms.setdefault(lit, []).append((atom, True))
        self._euf_lit_to_atoms.setdefault(negate(lit), []).append((atom, False))

        if not catch_up:
            return
        assert self._sat is not None
        val = self._sat.value(lit)
        if val is None:
            return
        self._euf.assert_atom(atom, val)
        props, conflict = self._euf.propagate()
        if conflict is not None:
            self._sat.add_clause(self._euf_conflict_to_clause(conflict))
            return
        for p_atom, p_sign in props:
            p_lit = self._euf_atom_to_pos_lit.get(p_atom)
            if p_lit is None:
                continue
            sat_p_lit = p_lit if p_sign else negate(p_lit)
            if self._sat.value(sat_p_lit) is None:
                reasons = self._euf.explain_propagation(p_atom, p_sign)
                lemma = [
                    sat_p_lit,
                    *(negate(self._euf_lit_to_sat(tl)) for tl in reasons),
                ]
                self._sat.add_clause(lemma)

    def bind_lra(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None:
        """Bind positive ``lit`` to LRA comparison atom ``(atom, True)``."""
        if atom in self._lra_atom_to_pos_lit:
            return
        self._lra_atom_to_pos_lit[atom] = lit
        self._lra_lit_to_atoms.setdefault(lit, []).append((atom, True))
        self._lra_lit_to_atoms.setdefault(negate(lit), []).append((atom, False))

        if not catch_up:
            return
        assert self._sat is not None
        val = self._sat.value(lit)
        if val is None:
            return
        self._lra.assert_atom(atom, val)
        props, conflict = self._lra.propagate()
        if conflict is not None:
            self._sat.add_clause(self._lra_conflict_to_clause(conflict))
            return
        for p_atom, p_sign in props:
            p_lit = self._lra_atom_to_pos_lit.get(p_atom)
            if p_lit is None:
                continue
            sat_p_lit = p_lit if p_sign else negate(p_lit)
            if self._sat.value(sat_p_lit) is None:
                reasons = self._lra.explain_propagation(p_atom, p_sign)
                lemma = [
                    sat_p_lit,
                    *(negate(self._lra_lit_to_sat(tl)) for tl in reasons),
                ]
                self._sat.add_clause(lemma)

    def bind_bv(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None:
        """Bind positive ``lit`` to BV atom ``(atom, True)``."""
        if atom in self._bv_atom_to_pos_lit:
            return
        self._bv_atom_to_pos_lit[atom] = lit
        self._bv_lit_to_atoms.setdefault(lit, []).append((atom, True))
        self._bv_lit_to_atoms.setdefault(negate(lit), []).append((atom, False))

        if not catch_up:
            return
        assert self._sat is not None
        val = self._sat.value(lit)
        if val is None:
            return
        self._bv.assert_atom(atom, val)
        props, conflict = self._bv.propagate()
        if conflict is not None:
            self._sat.add_clause(self._bv_conflict_to_clause(conflict))
            return
        for p_atom, p_sign in props:
            p_lit = self._bv_atom_to_pos_lit.get(p_atom)
            if p_lit is None:
                continue
            sat_p_lit = p_lit if p_sign else negate(p_lit)
            if self._sat.value(sat_p_lit) is None:
                reasons = self._bv.explain_propagation(p_atom, p_sign)
                lemma = [
                    sat_p_lit,
                    *(negate(self._bv_lit_to_sat(tl)) for tl in reasons),
                ]
                self._sat.add_clause(lemma)

    def bind_string(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None:
        """Bind positive ``lit`` to String predicate atom ``(atom, True)``."""
        if atom in self._str_atom_to_pos_lit:
            return
        self._str_atom_to_pos_lit[atom] = lit
        self._str_lit_to_atoms.setdefault(lit, []).append((atom, True))
        self._str_lit_to_atoms.setdefault(negate(lit), []).append((atom, False))

        if not catch_up:
            return
        assert self._sat is not None
        val = self._sat.value(lit)
        if val is not None:
            self._strings.assert_atom(atom, val)

    def push(self) -> None:
        self._euf.push()
        self._lra.push()
        self._bv.push()
        self._strings.push()

    def pop(self, num_levels: int) -> None:
        self._euf.pop(num_levels)
        self._lra.pop(num_levels)
        self._bv.pop(num_levels)
        self._strings.pop(num_levels)

    def on_assign(self, lit: Lit) -> None:
        euf_entries = self._euf_lit_to_atoms.get(lit)
        if euf_entries is not None:
            for atom, sign in euf_entries:
                self._euf.assert_atom(atom, sign)
        lra_entries = self._lra_lit_to_atoms.get(lit)
        if lra_entries is not None:
            for atom, sign in lra_entries:
                self._lra.assert_atom(atom, sign)
        bv_entries = self._bv_lit_to_atoms.get(lit)
        if bv_entries is not None:
            for atom, sign in bv_entries:
                self._bv.assert_atom(atom, sign)
        str_entries = self._str_lit_to_atoms.get(lit)
        if str_entries is not None:
            for atom, sign in str_entries:
                self._strings.assert_atom(atom, sign)

    def propagate(self) -> tuple[Sequence[Lit], Sequence[Lit] | None]:
        euf_props, euf_conflict = self._euf.propagate()
        if euf_conflict is not None:
            return (), self._euf_conflict_to_clause(euf_conflict)

        lra_props, lra_conflict = self._lra.propagate()
        if lra_conflict is not None:
            return (), self._lra_conflict_to_clause(lra_conflict)

        bv_props, bv_conflict = self._bv.propagate()
        if bv_conflict is not None:
            return (), self._bv_conflict_to_clause(bv_conflict)

        sat_props: list[Lit] = []
        for atom, sign in euf_props:
            pos = self._euf_atom_to_pos_lit.get(atom)
            if pos is not None:
                sat_props.append(pos if sign else negate(pos))
        for atom, sign in lra_props:
            pos = self._lra_atom_to_pos_lit.get(atom)
            if pos is not None:
                sat_props.append(pos if sign else negate(pos))
        for atom, sign in bv_props:
            pos = self._bv_atom_to_pos_lit.get(atom)
            if pos is not None:
                sat_props.append(pos if sign else negate(pos))
        return sat_props, None

    def explain_propagation(self, lit: Lit) -> Sequence[Lit]:
        euf_entries = self._euf_lit_to_atoms.get(lit)
        if euf_entries:
            for atom, sign in euf_entries:
                try:
                    reasons = self._euf.explain_propagation(atom, sign)
                except KeyError, ValueError:
                    continue
                return [lit, *(negate(self._euf_lit_to_sat(tl)) for tl in reasons)]

        lra_entries = self._lra_lit_to_atoms.get(lit)
        if lra_entries:
            for atom, sign in lra_entries:
                try:
                    reasons = self._lra.explain_propagation(atom, sign)
                except KeyError, ValueError:
                    continue
                return [lit, *(negate(self._lra_lit_to_sat(tl)) for tl in reasons)]

        bv_entries = self._bv_lit_to_atoms.get(lit)
        if bv_entries:
            for atom, sign in bv_entries:
                try:
                    reasons = self._bv.explain_propagation(atom, sign)
                except KeyError, ValueError:
                    continue
                return [lit, *(negate(self._bv_lit_to_sat(tl)) for tl in reasons)]

        msg = f"SAT literal {lit} has no valid theory explanation in current state"
        raise ValueError(msg)

    def check(self) -> Sequence[Sequence[Lit]]:
        euf_lemmas = self._euf.check()
        if euf_lemmas:
            return [self._euf_conflict_to_clause(lemma) for lemma in euf_lemmas]

        lra_lemmas = self._lra.check()
        if lra_lemmas:
            return [self._lra_conflict_to_clause(lemma) for lemma in lra_lemmas]

        lia_lemma = find_lia_lemma(self._lra, emitted_cuts=self._emitted_cuts)
        if lia_lemma is not None:
            if isinstance(lia_lemma, LIACutLemma):
                base = self._lra_conflict_to_clause(lia_lemma.reasons)
                if lia_lemma.cut_atom is self._ctx.false_expr:
                    return [base]
                self._emitted_cuts.add(lia_lemma.cut_atom)
                cut_lit = self._ensure_lra_lemma_lit(lia_lemma.cut_atom)
                return [[*base, cut_lit]]
            assert isinstance(lia_lemma, LIASplitLemma)
            if lia_lemma.prefer_ge:
                lit_first = self._ensure_lra_lemma_lit(lia_lemma.ge_atom)
                lit_second = self._ensure_lra_lemma_lit(lia_lemma.le_atom)
            else:
                lit_first = self._ensure_lra_lemma_lit(lia_lemma.le_atom)
                lit_second = self._ensure_lra_lemma_lit(lia_lemma.ge_atom)
            return [[lit_first, lit_second]]

        if self._shared_arith_terms:
            mbtc_lemmas = self._check_mbtc()
            if mbtc_lemmas:
                return mbtc_lemmas

        nla_res = self._nla.check(self._lra, emitted_lemmas=self._emitted_nla_lemmas)
        if isinstance(nla_res, list) and nla_res:
            assert self._encoder is not None
            nla_out: list[list[Lit]] = []
            for nla_lemma in nla_res:
                assert isinstance(nla_lemma, NLALemma)
                base = self._lra_conflict_to_clause(nla_lemma.reasons)
                if nla_lemma.formula is self._ctx.false_expr:
                    nla_out.append(base)
                elif nla_lemma.formula is self._ctx.true_expr:
                    continue
                else:
                    f_lit, def_clauses = self._encoder.encode_lemma(
                        nla_lemma.formula, polarity=1
                    )
                    nla_out.extend(def_clauses)
                    nla_out.append([*base, f_lit])
            if nla_out:
                return nla_out
        if isinstance(nla_res, NLAUnknown):
            self._nla_unknown = True

        bv_res: BVBlastRequest | list[TheoryLit] | None = None
        if self._bv_atom_to_pos_lit or self._shared_bv_set:
            bv_res = self._bv.check(self._collect_sat_bv_values())
            if isinstance(bv_res, list):
                return [self._bv_conflict_to_clause(bv_res)]

        if bv_res is None and self._shared_bv_terms:
            bv_mbtc = self._check_mbtc_bv()
            if bv_mbtc:
                return bv_mbtc

        array_lemmas = self._arrays.check(self._euf)
        if array_lemmas:
            assert self._encoder is not None
            out: list[list[Lit]] = []
            for lemma in array_lemmas:
                base = self._euf_conflict_to_clause(lemma.reasons)
                if lemma.formula is self._ctx.true_expr:
                    continue
                if lemma.formula is self._ctx.false_expr:
                    out.append(base)
                    continue
                f_lit, def_clauses = self._encoder.encode_lemma(
                    lemma.formula, polarity=1
                )
                out.extend(def_clauses)
                out.append([*base, f_lit])
            if out:
                return out

        if isinstance(bv_res, BVBlastRequest):
            return self._blast_bv_request(bv_res)

        str_res = self._strings.check(
            self._euf, self._lra, emitted_lemmas=self._emitted_str_lemmas
        )
        if isinstance(str_res, list) and str_res:
            assert self._encoder is not None
            vars_before = self._sat.num_vars if self._sat is not None else 0
            str_out: list[list[Lit]] = []
            for str_lemma in str_res:
                assert isinstance(str_lemma, StringLemma)
                base = [negate(self._mixed_lit_to_sat(tl)) for tl in str_lemma.reasons]
                if str_lemma.formula is self._ctx.false_expr:
                    str_out.append(base)
                elif str_lemma.formula is self._ctx.true_expr:
                    continue
                else:
                    f_lit, def_clauses = self._encoder.encode_lemma(
                        str_lemma.formula, polarity=1
                    )
                    str_out.extend(def_clauses)
                    str_out.append([*base, f_lit])
            if str_out:
                if self._sat is not None and self._sat.num_vars == vars_before:
                    has_unsat_or_unassigned = any(
                        not any(self._sat.value(lit) is True for lit in clause)
                        for clause in str_out
                    )
                    if not has_unsat_or_unassigned:
                        self._string_unknown = True
                        return ()
                return str_out
        if isinstance(str_res, StringUnknown):
            self._string_unknown = True

        return ()

    def _mixed_lit_to_sat(self, tlit: TheoryLit) -> Lit:
        pos = self._str_atom_to_pos_lit.get(tlit.atom)
        if pos is None:
            pos = self._euf_atom_to_pos_lit.get(tlit.atom)
        if pos is None:
            pos = self._lra_atom_to_pos_lit.get(tlit.atom)
        if pos is None:
            assert self._encoder is not None
            lit, _ = self._encoder.encode_lemma(tlit.atom, polarity=0)
            pos = lit
        return pos if tlit.sign else negate(pos)

    def _sat_bit_lookup(self) -> Callable[[Expr], bool]:
        assert self._sat is not None
        assert self._encoder is not None
        sat = self._sat
        enc = self._encoder

        def _lookup(node: Expr) -> bool:
            var = enc.expr_var_or_none(node)
            if var is None:
                return False
            val = sat.value(pos_lit(var))
            return bool(val) if val is not None else False

        return _lookup

    def _collect_sat_bv_values(self) -> dict[Expr, int]:
        lookup = self._sat_bit_lookup()
        sat_vals: dict[Expr, int] = {}
        for term in self._bv.registered_terms():
            val = self._bitblaster.eval_blasted_term_bits(term, lookup)
            if val is not None:
                sat_vals[term] = val
        return sat_vals

    def _blast_bv_request(self, req: BVBlastRequest) -> list[list[Lit]]:
        assert self._encoder is not None
        out: list[list[Lit]] = []
        for atom in req.atoms:
            if self._bv.is_blasted(atom):
                continue
            atom_lit = self._bv_atom_to_pos_lit[atom]
            out.extend(self._encoder.encode_bv_blast_lemma(atom, atom_lit))
            self._bv.mark_blasted(atom)
            self._bv.stats.blasted_atoms += 1
        return out

    def _check_mbtc_bv(self) -> list[list[Lit]]:
        assert self._encoder is not None
        sat_vals = self._collect_sat_bv_values()
        vals = self._bv.term_values(self.all_shared_bv_terms(), sat_vals)

        # Direction 1 (EUF -> BV): force matching bit vectors on EUF-equal terms.
        sort_reps: dict[Sort, dict[Expr, Expr]] = {}
        for sort, terms in self._shared_bv_terms.items():
            groups: dict[Expr, Expr] = {}
            for term in terms:
                rep = self._euf.rep_expr(term)
                leader = groups.get(rep)
                if leader is None:
                    groups[rep] = term
                    continue
                if vals[term] != vals[leader]:
                    reasons = self._euf.explain_terms_equal(term, leader)
                    base = self._euf_conflict_to_clause(reasons)
                    eq_atom = self._ctx.mk_eq(term, leader)
                    if eq_atom is self._ctx.true_expr:
                        continue
                    if eq_atom is self._ctx.false_expr:
                        return [base]
                    lit_eq, def_clauses = self._encoder.encode_lemma(
                        eq_atom, polarity=0
                    )
                    return [*def_clauses, [*base, lit_eq]]
            sort_reps[sort] = groups

        # Direction 2 (BV -> EUF): speculate interface equalities when BV values match.
        for groups in sort_reps.values():
            seen_val: dict[int, Expr] = {}
            for leader in groups.values():
                val = vals[leader]
                other = seen_val.get(val)
                if other is None:
                    seen_val[val] = leader
                    continue
                eq_atom = self._ctx.mk_eq(leader, other)
                if eq_atom is self._ctx.false_expr or eq_atom is self._ctx.true_expr:
                    continue
                if self._encoder.expr_var_or_none(eq_atom) is not None:
                    continue
                _, def_clauses = self._encoder.encode_lemma(eq_atom, polarity=0)
                return def_clauses

        return []

    def _ensure_lra_lemma_lit(self, atom: Expr) -> Lit:
        assert self._encoder is not None
        existing = self._lra_atom_to_pos_lit.get(atom)
        if existing is not None:
            return existing
        self._lra.register_atom(atom)
        lit = pos_lit(self._encoder.ensure_expr_var(atom))
        self.bind_lra(lit, atom, catch_up=False)
        return lit

    def _ensure_euf_lemma_lit(self, eq_atom: Expr) -> Lit:
        assert self._encoder is not None
        existing = self._euf_atom_to_pos_lit.get(eq_atom)
        if existing is not None:
            return existing
        self._euf.register_eq(eq_atom)
        lit = pos_lit(self._encoder.ensure_expr_var(eq_atom))
        self.bind_euf(lit, eq_atom, catch_up=False)
        return lit

    def _check_mbtc(self) -> list[list[Lit]]:
        all_terms = self.all_shared_arith_terms()
        vals = self._lra.term_values(all_terms)

        # Direction 1 (EUF -> LRA): propagate EUF equalities into LRA bounds.
        sort_reps: dict[Sort, dict[Expr, Expr]] = {}
        for sort, terms in self._shared_arith_terms.items():
            groups: dict[Expr, Expr] = {}
            for term in terms:
                rep = self._euf.rep_expr(term)
                leader = groups.get(rep)
                if leader is None:
                    groups[rep] = term
                    continue
                if vals[term] != vals[leader]:
                    reasons = self._euf.explain_terms_equal(term, leader)
                    base = self._euf_conflict_to_clause(reasons)
                    le = self._ctx.mk_le(term, leader)
                    ge = self._ctx.mk_ge(term, leader)
                    lemmas: list[list[Lit]] = []
                    for cmp_atom in (le, ge):
                        if cmp_atom is self._ctx.true_expr:
                            continue
                        if cmp_atom is self._ctx.false_expr:
                            lemmas.append(list(base))
                        else:
                            lemmas.append([*base, self._ensure_lra_lemma_lit(cmp_atom)])
                    if lemmas:
                        return lemmas
            sort_reps[sort] = groups

        # Direction 2 (LRA -> EUF): speculate interface equalities for matching vals.
        for groups in sort_reps.values():
            seen_val: dict[object, Expr] = {}
            for leader in groups.values():
                val = vals[leader]
                other = seen_val.get(val)
                if other is None:
                    seen_val[val] = leader
                    continue
                eq_atom = self._ctx.mk_eq(leader, other)
                if eq_atom is self._ctx.false_expr or eq_atom is self._ctx.true_expr:
                    continue
                lit_eq = self._ensure_euf_lemma_lit(eq_atom)
                le = self._ctx.mk_le(leader, other)
                ge = self._ctx.mk_ge(leader, other)
                lit_le = (
                    None if isinstance(le, Const) else self._ensure_lra_lemma_lit(le)
                )
                lit_ge = (
                    None if isinstance(ge, Const) else self._ensure_lra_lemma_lit(ge)
                )

                out_lemmas: list[list[Lit]] = []
                if lit_le is not None:
                    out_lemmas.append([negate(lit_eq), lit_le])
                elif le is self._ctx.false_expr:
                    out_lemmas.append([negate(lit_eq)])

                if lit_ge is not None:
                    out_lemmas.append([negate(lit_eq), lit_ge])
                elif ge is self._ctx.false_expr:
                    out_lemmas.append([negate(lit_eq)])

                clause3: list[Lit] = [lit_eq]
                satisfied_neg = False
                for opt_atom, opt_lit in ((le, lit_le), (ge, lit_ge)):
                    if opt_atom is self._ctx.false_expr:
                        satisfied_neg = True
                        break
                    if opt_lit is not None:
                        clause3.append(negate(opt_lit))
                if not satisfied_neg:
                    out_lemmas.append(clause3)
                return out_lemmas

        return []

    def _euf_lit_to_sat(self, tlit: TheoryLit) -> Lit:
        pos = self._euf_atom_to_pos_lit[tlit.atom]
        return pos if tlit.sign else negate(pos)

    def _lra_lit_to_sat(self, tlit: TheoryLit) -> Lit:
        pos = self._lra_atom_to_pos_lit[tlit.atom]
        return pos if tlit.sign else negate(pos)

    def _euf_conflict_to_clause(self, conflict: Sequence[TheoryLit]) -> list[Lit]:
        return [negate(self._euf_lit_to_sat(tl)) for tl in conflict]

    def _lra_conflict_to_clause(self, conflict: Sequence[TheoryLit]) -> list[Lit]:
        return [negate(self._lra_lit_to_sat(tl)) for tl in conflict]

    def _bv_lit_to_sat(self, tlit: TheoryLit) -> Lit:
        pos = self._bv_atom_to_pos_lit[tlit.atom]
        return pos if tlit.sign else negate(pos)

    def _bv_conflict_to_clause(self, conflict: Sequence[TheoryLit]) -> list[Lit]:
        return [negate(self._bv_lit_to_sat(tl)) for tl in conflict]
