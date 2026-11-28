"""Polarity-aware incremental Tseitin, theory atom, BV, and quantifier encoder."""

from collections.abc import Iterable
from typing import Protocol

from unsat.sat import Lit, SATSolver, Var, negate, pos_lit
from unsat.syntax import (
    App,
    Const,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
    collect_func_decls,
    instantiate_quantifier,
    iter_subexprs,
)
from unsat.syntax.str_eval import MAX_CHAR_CODE
from unsat.tactics import BitBlaster, bv_simplify, simplify, skolemize
from unsat.theories import ArraySolver, BVSolver, EUFSolver, LRASolver, StringSolver

_CMP_KINDS = frozenset({DeclKind.LT, DeclKind.LE, DeclKind.GT, DeclKind.GE})
_ARITH_OP_KINDS = frozenset(
    {
        DeclKind.NEG,
        DeclKind.ADD,
        DeclKind.SUB,
        DeclKind.MUL,
        DeclKind.DIV,
        DeclKind.IDIV,
        DeclKind.MOD,
        DeclKind.ABS,
        DeclKind.TO_REAL,
        DeclKind.TO_INT,
        DeclKind.STR_LEN,
        DeclKind.STR_INDEXOF,
        DeclKind.STR_TO_INT,
        DeclKind.STR_TO_CODE,
    }
)
_STRING_TERM_KINDS = frozenset(
    {
        DeclKind.STR_CONCAT,
        DeclKind.STR_AT,
        DeclKind.STR_SUBSTR,
        DeclKind.STR_REPLACE,
        DeclKind.STR_REPLACE_ALL,
        DeclKind.STR_FROM_INT,
        DeclKind.STR_FROM_CODE,
    }
)
_STRING_PRED_KINDS = frozenset(
    {
        DeclKind.STR_IN_RE,
        DeclKind.STR_CONTAINS,
        DeclKind.STR_LT,
        DeclKind.STR_LE,
    }
)
_RE_OP_KINDS = frozenset(
    {
        DeclKind.STR_TO_RE,
        DeclKind.RE_NONE,
        DeclKind.RE_ALL,
        DeclKind.RE_ALLCHAR,
        DeclKind.RE_CONCAT,
        DeclKind.RE_UNION,
        DeclKind.RE_INTER,
        DeclKind.RE_STAR,
        DeclKind.RE_PLUS,
        DeclKind.RE_OPT,
        DeclKind.RE_RANGE,
        DeclKind.RE_COMP,
        DeclKind.RE_DIFF,
        DeclKind.RE_POWER,
        DeclKind.RE_LOOP,
    }
)
_BV_CMP_KINDS = frozenset(
    {
        DeclKind.BV_ULT,
        DeclKind.BV_ULE,
        DeclKind.BV_UGT,
        DeclKind.BV_UGE,
        DeclKind.BV_SLT,
        DeclKind.BV_SLE,
        DeclKind.BV_SGT,
        DeclKind.BV_SGE,
    }
)
_BV_OP_KINDS = frozenset(
    {
        DeclKind.BV_NOT,
        DeclKind.BV_AND,
        DeclKind.BV_OR,
        DeclKind.BV_XOR,
        DeclKind.BV_NEG,
        DeclKind.BV_ADD,
        DeclKind.BV_SUB,
        DeclKind.BV_MUL,
        DeclKind.BV_UDIV,
        DeclKind.BV_UREM,
        DeclKind.BV_SDIV,
        DeclKind.BV_SREM,
        DeclKind.BV_SMOD,
        DeclKind.BV_SHL,
        DeclKind.BV_LSHR,
        DeclKind.BV_ASHR,
        DeclKind.BV_CONCAT,
        DeclKind.BV_EXTRACT,
        DeclKind.BV_ZERO_EXT,
        DeclKind.BV_SIGN_EXT,
        DeclKind.BV_ROTATE_LEFT,
        DeclKind.BV_ROTATE_RIGHT,
        DeclKind.BV_REPEAT,
    }
)
_ARRAY_OP_KINDS = frozenset({DeclKind.SELECT, DeclKind.STORE, DeclKind.CONST_ARRAY})


class _PropSink(Protocol):
    def add_shared_arith_term(self, term: Expr) -> None: ...

    def add_shared_bv_term(self, term: Expr) -> None: ...

    def bind_euf(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None: ...

    def bind_lra(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None: ...

    def bind_bv(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None: ...

    def bind_string(self, lit: Lit, atom: Expr, *, catch_up: bool = True) -> None: ...


def _strip_nots(expr: Expr) -> tuple[Expr, bool]:
    flip = False
    current = expr
    while isinstance(current, App) and current.decl.kind is DeclKind.NOT:
        flip = not flip
        current = current.args[0]
    return current, flip


def _is_bool_fixed_distinct(node: Expr) -> bool:
    return (
        isinstance(node, App)
        and node.decl.kind is DeclKind.DISTINCT
        and len(node.args) != 2
        and (not node.args or node.args[0].is_bool)
    )


class _PlaistedGreenbaumEncoder:
    """Polarity-aware incremental Tseitin, EUF, LRA/LIA, BV, and Array encoder."""

    def __init__(
        self,
        ctx: Context,
        sat_solver: SATSolver,
        euf_solver: EUFSolver,
        lra_solver: LRASolver,
        array_solver: ArraySolver,
        bv_solver: BVSolver,
        string_solver: StringSolver,
        bitblaster: BitBlaster,
        prop: _PropSink,
    ) -> None:
        self._ctx = ctx
        self._sat = sat_solver
        self._euf = euf_solver
        self._lra = lra_solver
        self._arrays = array_solver
        self._bv = bv_solver
        self._strings = string_solver
        self._bitblaster = bitblaster
        self._prop = prop
        self._expr_to_var: dict[Expr, Var] = {}
        self._decl_to_var: dict[FuncDecl, Var] = {}
        self._pos_encoded: set[Expr] = set()
        self._neg_encoded: set[Expr] = set()
        self._terms_non_euf: set[Expr] = set()
        self._terms_euf: set[Expr] = set()
        self._true_lit: Lit | None = None
        self._first_lit: Lit | None = None
        self._clause_sink: list[list[Lit]] | None = None
        self._reserved_names: set[str] = set()
        self._skolem_decls: set[FuncDecl] = set()
        self._skolem_seq: int = 0
        self._universal_entries: list[tuple[Lit, Quantifier, set[Lit | None]]] = []
        self._encoding_quant_stack: list[Quantifier] = []
        self._quant_to_entry_indices: dict[Quantifier, list[int]] = {}
        self._arith_axioms_emitted: set[Expr] = set()
        self._str_axioms_emitted: set[Expr] = set()

    @property
    def internal_decls(self) -> frozenset[FuncDecl]:
        """Skolem declarations synthesized during quantifier encoding."""
        return frozenset(self._skolem_decls)

    @property
    def universal_entries(
        self,
    ) -> tuple[tuple[Lit, Quantifier, set[Lit | None]], ...]:
        """Guarded universal quantifiers ``(active_lit, norm_q, owner_lits)``."""
        return tuple(self._universal_entries)

    def mark_quantifier_owners(self, expr: Expr, owners: Lit | Iterable[Lit | None] | None) -> None:
        """Associate ``owners`` with quantifiers appearing in ``expr``."""
        owner_set = {owners} if (owners is None or isinstance(owners, int)) else set(owners)
        if not owner_set:
            return
        for node in iter_subexprs(expr):
            if isinstance(node, Quantifier):
                for idx in self._quant_to_entry_indices.get(node, ()):
                    self._universal_entries[idx][2].update(owner_set)

    def record_reserved(self, expr: Expr) -> None:
        """Record user declaration names in ``expr`` to avoid Skolem collisions."""
        for decl in collect_func_decls(expr):
            self._reserved_names.add(decl.name)

    def _alloc_skolem_const(self, sort: Sort) -> App:
        while True:
            name = f"__sk!{self._skolem_seq}"
            self._skolem_seq += 1
            if name not in self._reserved_names:
                self._reserved_names.add(name)
                app = self._ctx.mk_const(name, sort)
                self._skolem_decls.add(app.decl)
                return app

    def _emit_existential_witness(self, guard_cond_lit: Lit, node: Quantifier, *, negate_body: bool) -> None:
        sk_consts = tuple(self._alloc_skolem_const(s) for s in node.var_sorts)
        inst = instantiate_quantifier(node, sk_consts)
        target = self._ctx.mk_not(inst) if negate_body else inst
        simp = bv_simplify(simplify(target))
        if simp is self._ctx.true_expr:
            return
        if simp is self._ctx.false_expr:
            self._emit_clause([guard_cond_lit])
            return
        lit_w = self.encode(simp, polarity=1)
        self._emit_clause([guard_cond_lit, lit_w])

    def _register_universal_branch(self, active_lit: Lit, u_q: Quantifier) -> None:
        sk_expr, sk_decls = skolemize(u_q, reserved_names=self._reserved_names)
        for decl in sk_decls:
            self._skolem_decls.add(decl)
            self._reserved_names.add(decl.name)
        conjuncts = sk_expr.args if isinstance(sk_expr, App) and sk_expr.decl.kind is DeclKind.AND else (sk_expr,)
        for conj in conjuncts:
            if isinstance(conj, Quantifier) and conj.is_forall:
                idx = len(self._universal_entries)
                self._universal_entries.append((active_lit, conj, set()))
                for anc in self._encoding_quant_stack:
                    self._quant_to_entry_indices.setdefault(anc, []).append(idx)
            elif conj is self._ctx.true_expr:
                continue
            elif conj is self._ctx.false_expr:
                self._emit_clause([negate(active_lit)])
            else:
                lit_c = self.encode(conj, polarity=1)
                self._emit_clause([negate(active_lit), lit_c])

    def _encode_quantifier(self, node: Quantifier, pol: int) -> None:
        emit_pos = pol >= 0 and node not in self._pos_encoded
        emit_neg = pol <= 0 and node not in self._neg_encoded
        if not emit_pos and not emit_neg:
            return
        if pol >= 0:
            self._pos_encoded.add(node)
        if pol <= 0:
            self._neg_encoded.add(node)

        q_lit = pos_lit(self.ensure_expr_var(node))
        self._encoding_quant_stack.append(node)
        try:
            if emit_pos:
                if node.is_forall:
                    self._register_universal_branch(q_lit, node)
                else:
                    self._emit_existential_witness(negate(q_lit), node, negate_body=False)
            if emit_neg:
                if node.is_forall:
                    self._emit_existential_witness(q_lit, node, negate_body=True)
                else:
                    u_q = self._ctx.mk_quantifier(
                        True,
                        node.var_names,
                        node.var_sorts,
                        self._ctx.mk_not(node.body),
                        patterns=node.patterns,
                    )
                    if isinstance(u_q, Quantifier):
                        self._register_universal_branch(negate(q_lit), u_q)
                    elif u_q is self._ctx.false_expr:
                        self._emit_clause([q_lit])
        finally:
            self._encoding_quant_stack.pop()

    @property
    def decl_to_var(self) -> dict[FuncDecl, Var]:
        """Mapping from Boolean 0-arity declarations to SAT variable indices."""
        return self._decl_to_var

    def expr_var_or_none(self, expr: Expr) -> Var | None:
        """Return SAT variable index allocated for ``expr``, or ``None``."""
        return self._expr_to_var.get(expr)

    def _emit_clause(self, lits: list[Lit]) -> None:
        if self._clause_sink is not None:
            self._clause_sink.append(lits)
        else:
            self._sat.add_clause(lits)

    def encode_lemma(self, expr: Expr, polarity: int = 1) -> tuple[Lit, list[list[Lit]]]:
        """Encode ``expr`` during ``check()``, capturing definition clauses."""
        prev_sink = self._clause_sink
        clauses: list[list[Lit]] = []
        self._clause_sink = clauses
        try:
            lit = self.encode(expr, polarity=polarity)
        finally:
            self._clause_sink = prev_sink
        return lit, clauses

    def encode_bv_blast_lemma(self, atom: Expr, atom_lit: Lit) -> list[list[Lit]]:
        """Bit-blast a single BV atom on demand, returning SAT definition clauses."""
        assert isinstance(atom, App)
        self._bitblaster.register_reserved(atom)
        if atom.decl.kind is DeclKind.EQ:
            blasted = self._bitblaster.blast_eq(atom.args[0], atom.args[1])
        else:
            blasted = self._bitblaster.blast_bool(atom)
        if blasted is self._ctx.true_expr:
            return [[atom_lit]]
        if blasted is self._ctx.false_expr:
            return [[negate(atom_lit)]]
        lit_blast, def_clauses = self.encode_lemma(blasted, polarity=0)
        return [
            *def_clauses,
            [negate(atom_lit), lit_blast],
            [atom_lit, negate(lit_blast)],
        ]

    def any_lit(self) -> Lit | None:
        """Return an allocated SAT literal if any variable exists yet."""
        return self._first_lit

    def ensure_expr_var(self, expr: Expr) -> Var:
        """Return existing SAT variable index for ``expr`` or allocate a new one."""
        var = self._expr_to_var.get(expr)
        if var is None:
            var = self._sat.new_var()
            self._expr_to_var[expr] = var
            if self._first_lit is None:
                self._first_lit = pos_lit(var)
            if isinstance(expr, App) and expr.is_const_symbol:
                self._decl_to_var[expr.decl] = var
        return var

    def _get_true_lit(self) -> Lit:
        if self._true_lit is None:
            lit = pos_lit(self._sat.new_var())
            self._emit_clause([lit])
            self._true_lit = lit
            if self._first_lit is None:
                self._first_lit = lit
        return self._true_lit

    def _get_false_lit(self) -> Lit:
        return negate(self._get_true_lit())

    def _register_term(self, term: Expr, *, in_euf: bool = True) -> None:
        """Walk ``term`` registering EUF/LRA/Array/BV subterms and non-Bool ITEs."""
        bool_args: list[Expr] = []
        non_bool_ites: list[App] = []
        arith_axiom_nodes: list[App] = []
        str_axiom_nodes: list[Expr] = []
        stack: list[tuple[Expr, bool, bool]] = [(term, in_euf, False)]

        while stack:
            node, euf_flag, expanded = stack.pop()
            if euf_flag:
                if node in self._terms_euf:
                    continue
            elif node in self._terms_euf or node in self._terms_non_euf:
                continue

            if isinstance(node, Const):
                if euf_flag or node.is_string or node.is_reglan:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                    elif node.is_string:
                        self._strings.register_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            if isinstance(node, Quantifier):
                self._terms_euf.add(node)
                bool_args.append(node)
                continue

            if not isinstance(node, App):
                if euf_flag:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            kind = node.decl.kind
            if kind is DeclKind.ITE and not node.is_bool:
                eff_euf = euf_flag or node.is_array
                if not expanded:
                    stack.append((node, eff_euf, True))
                    stack.append((node.args[2], eff_euf, False))
                    stack.append((node.args[1], eff_euf, False))
                    continue
                if eff_euf:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                    if node.is_array:
                        self._arrays.register_term(node)
                else:
                    self._terms_non_euf.add(node)
                    if node.is_bv:
                        self._bv.register_term(node)
                if node.is_arith:
                    self._lra.register_term(node)
                if node.is_string:
                    self._strings.register_term(node)
                    if node not in self._str_axioms_emitted:
                        str_axiom_nodes.append(node)
                non_bool_ites.append(node)
                continue

            if kind in _ARITH_OP_KINDS:
                div_congruent = kind in (
                    DeclKind.IDIV,
                    DeclKind.MOD,
                    DeclKind.DIV,
                ) and (not isinstance(node.args[1], Const) or node.args[1].value == 0)
                str_arith = kind in (
                    DeclKind.STR_LEN,
                    DeclKind.STR_INDEXOF,
                    DeclKind.STR_TO_INT,
                    DeclKind.STR_TO_CODE,
                )
                eff_arith_euf = euf_flag or div_congruent or str_arith
                if not expanded:
                    stack.append((node, eff_arith_euf, True))
                    stack.extend((arg, eff_arith_euf, False) for arg in reversed(node.args))
                    continue
                if eff_arith_euf:
                    self._terms_euf.add(node)
                    if div_congruent or str_arith:
                        self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                else:
                    self._terms_non_euf.add(node)
                if str_arith:
                    self._strings.register_term(node)
                    if node not in self._str_axioms_emitted:
                        str_axiom_nodes.append(node)
                if (
                    kind
                    in (
                        DeclKind.ABS,
                        DeclKind.TO_INT,
                        DeclKind.IDIV,
                        DeclKind.MOD,
                        DeclKind.DIV,
                    )
                    and node not in self._arith_axioms_emitted
                ):
                    arith_axiom_nodes.append(node)
                continue

            if kind in _STRING_TERM_KINDS:
                if not expanded:
                    stack.append((node, True, True))
                    stack.extend((arg, True, False) for arg in reversed(node.args))
                    continue
                self._terms_euf.add(node)
                self._euf.register_term(node)
                if node.is_string:
                    self._strings.register_term(node)
                    if node not in self._str_axioms_emitted:
                        str_axiom_nodes.append(node)
                continue

            if kind in _RE_OP_KINDS:
                if not expanded and node.args:
                    stack.append((node, True, True))
                    stack.extend((arg, True, False) for arg in reversed(node.args))
                    continue
                self._terms_euf.add(node)
                self._euf.register_term(node)
                continue

            if kind in _BV_OP_KINDS:
                if not expanded:
                    stack.append((node, euf_flag, True))
                    stack.extend((arg, euf_flag, False) for arg in reversed(node.args))
                    continue
                if euf_flag:
                    self._terms_euf.add(node)
                    if node.is_bv:
                        self._prop.add_shared_bv_term(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            if kind in _ARRAY_OP_KINDS:
                if not expanded:
                    stack.append((node, True, True))
                    for arg in reversed(node.args):
                        if arg.is_bool:
                            bool_args.append(arg)
                        else:
                            stack.append((arg, True, False))
                    continue
                self._terms_euf.add(node)
                self._arrays.register_term(node)
                self._euf.register_term(node)
                if node.is_arith:
                    self._prop.add_shared_arith_term(node)
                elif node.is_bv:
                    self._prop.add_shared_bv_term(node)
                elif node.is_string:
                    self._strings.register_term(node)
                    if node not in self._str_axioms_emitted:
                        str_axiom_nodes.append(node)
                continue

            if node.decl.is_uninterpreted:
                if node.args:
                    if not expanded:
                        stack.append((node, euf_flag, True))
                        for arg in reversed(node.args):
                            if arg.is_bool:
                                bool_args.append(arg)
                            else:
                                # Arguments of an uninterpreted App always touch EUF.
                                stack.append((arg, True, False))
                        continue
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                    elif node.is_array:
                        self._arrays.register_term(node)
                    elif node.is_string:
                        self._strings.register_term(node)
                        if node not in self._str_axioms_emitted:
                            str_axiom_nodes.append(node)
                elif euf_flag or node.is_string or node.is_reglan:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
                    elif node.is_array:
                        self._arrays.register_term(node)
                    elif node.is_string:
                        self._strings.register_term(node)
                        if node not in self._str_axioms_emitted:
                            str_axiom_nodes.append(node)
                else:
                    self._terms_non_euf.add(node)
                continue

            if node.is_bool:
                self._terms_euf.add(node)
                bool_args.append(node)
                continue

            if euf_flag:
                self._terms_euf.add(node)
                self._euf.register_term(node)
            else:
                self._terms_non_euf.add(node)

        for b_arg in bool_args:
            if isinstance(b_arg, Const):
                self._euf.register_term(b_arg)
                continue
            lit_arg = self.encode(b_arg, polarity=0)
            self._euf.register_bool_term(b_arg)
            self._prop.bind_euf(lit_arg, b_arg, catch_up=(self._clause_sink is None))

        for ite_node in non_bool_ites:
            cond, then_b, else_b = ite_node.args
            lit_c = self.encode(cond, polarity=0)
            lit_then = self.encode(self._ctx.mk_eq(ite_node, then_b), polarity=1)
            lit_else = self.encode(self._ctx.mk_eq(ite_node, else_b), polarity=1)
            self._emit_clause([negate(lit_c), lit_then])
            self._emit_clause([lit_c, lit_else])

        for anode in arith_axiom_nodes:
            self._emit_arith_node_axioms(anode)

        for snode in str_axiom_nodes:
            self._emit_str_node_axioms(snode)

    def _emit_str_node_axioms(self, node: Expr) -> None:
        if node in self._str_axioms_emitted:
            return
        self._str_axioms_emitted.add(node)
        ctx = self._ctx

        if node.is_string and not isinstance(node, Const):
            len_node = ctx.mk_str_len(node)
            empty_s = ctx.mk_string_val("")
            self._emit_clause([self.encode(ctx.mk_ge(len_node, ctx.mk_int_val(0)), polarity=1)])
            self._emit_clause(
                [
                    self.encode(
                        ctx.mk_eq(
                            ctx.mk_eq(node, empty_s),
                            ctx.mk_eq(len_node, ctx.mk_int_val(0)),
                        ),
                        polarity=1,
                    )
                ]
            )
            if isinstance(node, App) and node.decl.kind is DeclKind.STR_CONCAT:
                self._emit_clause(
                    [
                        self.encode(
                            ctx.mk_eq(
                                len_node,
                                ctx.mk_add(*(ctx.mk_str_len(a) for a in node.args)),
                            ),
                            polarity=1,
                        )
                    ]
                )

        if not isinstance(node, App):
            return
        skind = node.decl.kind
        if skind is DeclKind.STR_AT:
            s, idx = node.args
            ax = ctx.mk_eq(node, ctx.mk_str_substr(s, idx, ctx.mk_int_val(1)))
            self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_SUBSTR:
            s, idx, n = node.args
            z0 = ctx.mk_int_val(0)
            len_s = ctx.mk_str_len(s)
            len_r = ctx.mk_str_len(node)
            rem = ctx.mk_sub(len_s, idx)
            valid = ctx.mk_and(ctx.mk_ge(idx, z0), ctx.mk_lt(idx, len_s), ctx.mk_gt(n, z0))
            sk_pre = self._alloc_skolem_const(ctx.string_sort)
            sk_suf = self._alloc_skolem_const(ctx.string_sort)
            exp_len = ctx.mk_ite(ctx.mk_le(n, rem), n, rem)
            ax_valid = ctx.mk_implies(
                valid,
                ctx.mk_and(
                    ctx.mk_eq(s, ctx.mk_str_concat(sk_pre, node, sk_suf)),
                    ctx.mk_eq(ctx.mk_str_len(sk_pre), idx),
                    ctx.mk_eq(len_r, exp_len),
                ),
            )
            ax_invalid = ctx.mk_implies(ctx.mk_not(valid), ctx.mk_eq(node, ctx.mk_string_val("")))
            for ax in (ax_valid, ax_invalid):
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_INDEXOF:
            s, t, i = node.args
            z0 = ctx.mk_int_val(0)
            zm1 = ctx.mk_int_val(-1)
            z1 = ctx.mk_int_val(1)
            len_s = ctx.mk_str_len(s)
            len_t = ctx.mk_str_len(t)
            in_bounds = ctx.mk_and(ctx.mk_ge(i, z0), ctx.mk_le(i, len_s))
            t_empty = ctx.mk_eq(t, ctx.mk_string_val(""))
            nonempty_t = ctx.mk_not(t_empty)
            k = node
            # Span before earliest match that cannot contain t when t != "".
            pre_span = ctx.mk_str_substr(
                s,
                i,
                ctx.mk_sub(ctx.mk_add(ctx.mk_sub(k, i), len_t), z1),
            )
            rest_span = ctx.mk_str_substr(s, i, ctx.mk_sub(len_s, i))
            axioms = (
                ctx.mk_implies(ctx.mk_not(in_bounds), ctx.mk_eq(k, zm1)),
                ctx.mk_implies(ctx.mk_and(in_bounds, t_empty), ctx.mk_eq(k, i)),
                ctx.mk_implies(
                    ctx.mk_and(in_bounds, nonempty_t),
                    ctx.mk_or(
                        ctx.mk_eq(k, zm1),
                        ctx.mk_and(
                            ctx.mk_ge(k, i),
                            ctx.mk_le(ctx.mk_add(k, len_t), len_s),
                        ),
                    ),
                ),
                ctx.mk_implies(
                    ctx.mk_and(in_bounds, nonempty_t, ctx.mk_ge(k, z0)),
                    ctx.mk_and(
                        ctx.mk_eq(ctx.mk_str_substr(s, k, len_t), t),
                        ctx.mk_not(ctx.mk_str_contains(pre_span, t)),
                    ),
                ),
                ctx.mk_implies(
                    ctx.mk_and(in_bounds, nonempty_t, ctx.mk_eq(k, zm1)),
                    ctx.mk_not(ctx.mk_str_contains(rest_span, t)),
                ),
            )
            for ax in axioms:
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_REPLACE:
            s, src, dst = node.args
            z0 = ctx.mk_int_val(0)
            src_empty = ctx.mk_eq(src, ctx.mk_string_val(""))
            k = ctx.mk_str_indexof(s, src, z0)
            tail_start = ctx.mk_add(k, ctx.mk_str_len(src))
            tail_len = ctx.mk_sub(ctx.mk_str_len(s), tail_start)
            replaced = ctx.mk_str_concat(
                ctx.mk_str_substr(s, z0, k),
                dst,
                ctx.mk_str_substr(s, tail_start, tail_len),
            )
            axioms_rep = (
                ctx.mk_implies(src_empty, ctx.mk_eq(node, ctx.mk_str_concat(dst, s))),
                ctx.mk_implies(
                    ctx.mk_and(ctx.mk_not(src_empty), ctx.mk_lt(k, z0)),
                    ctx.mk_eq(node, s),
                ),
                ctx.mk_implies(
                    ctx.mk_and(ctx.mk_not(src_empty), ctx.mk_ge(k, z0)),
                    ctx.mk_eq(node, replaced),
                ),
            )
            for ax in axioms_rep:
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_REPLACE_ALL:
            s, src, _dst = node.args
            axioms_ra = (
                ctx.mk_implies(ctx.mk_eq(src, ctx.mk_string_val("")), ctx.mk_eq(node, s)),
                ctx.mk_implies(ctx.mk_not(ctx.mk_str_contains(s, src)), ctx.mk_eq(node, s)),
            )
            for ax in axioms_ra:
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_TO_CODE:
            s = node.args[0]
            len_s = ctx.mk_str_len(s)
            z0 = ctx.mk_int_val(0)
            for ax in (
                ctx.mk_ge(node, ctx.mk_int_val(-1)),
                ctx.mk_le(node, ctx.mk_int_val(MAX_CHAR_CODE)),
                ctx.mk_eq(ctx.mk_eq(len_s, ctx.mk_int_val(1)), ctx.mk_ge(node, z0)),
            ):
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_FROM_CODE:
            n = node.args[0]
            in_rng = ctx.mk_and(
                ctx.mk_ge(n, ctx.mk_int_val(0)),
                ctx.mk_le(n, ctx.mk_int_val(MAX_CHAR_CODE)),
            )
            for ax in (
                ctx.mk_implies(
                    in_rng,
                    ctx.mk_and(
                        ctx.mk_eq(ctx.mk_str_len(node), ctx.mk_int_val(1)),
                        ctx.mk_eq(ctx.mk_str_to_code(node), n),
                    ),
                ),
                ctx.mk_implies(ctx.mk_not(in_rng), ctx.mk_eq(node, ctx.mk_string_val(""))),
            ):
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_TO_INT:
            s = node.args[0]
            digits_re = ctx.mk_re_plus(ctx.mk_re_range(ctx.mk_string_val("0"), ctx.mk_string_val("9")))
            in_digits = ctx.mk_str_in_re(s, digits_re)
            for ax in (
                ctx.mk_ge(node, ctx.mk_int_val(-1)),
                ctx.mk_eq(ctx.mk_ge(node, ctx.mk_int_val(0)), in_digits),
                ctx.mk_implies(
                    ctx.mk_and(
                        ctx.mk_eq(ctx.mk_str_len(s), ctx.mk_int_val(1)),
                        ctx.mk_ge(node, ctx.mk_int_val(0)),
                    ),
                    ctx.mk_eq(node, ctx.mk_sub(ctx.mk_str_to_code(s), ctx.mk_int_val(48))),
                ),
            ):
                self._emit_clause([self.encode(ax, polarity=1)])
        elif skind is DeclKind.STR_FROM_INT:
            n = node.args[0]
            canonical_nat = ctx.mk_re_union(
                ctx.mk_str_to_re(ctx.mk_string_val("0")),
                ctx.mk_re_concat(
                    ctx.mk_re_range(ctx.mk_string_val("1"), ctx.mk_string_val("9")),
                    ctx.mk_re_star(ctx.mk_re_range(ctx.mk_string_val("0"), ctx.mk_string_val("9"))),
                ),
            )
            z0 = ctx.mk_int_val(0)
            for ax in (
                ctx.mk_implies(ctx.mk_lt(n, z0), ctx.mk_eq(node, ctx.mk_string_val(""))),
                ctx.mk_implies(
                    ctx.mk_ge(n, z0),
                    ctx.mk_and(
                        ctx.mk_str_in_re(node, canonical_nat),
                        ctx.mk_eq(ctx.mk_str_to_int(node), n),
                    ),
                ),
            ):
                self._emit_clause([self.encode(ax, polarity=1)])

    def _emit_arith_node_axioms(self, anode: App) -> None:
        if anode in self._arith_axioms_emitted:
            return
        ctx = self._ctx
        akind = anode.decl.kind
        if akind in (DeclKind.IDIV, DeclKind.MOD):
            a, b = anode.args
            q = ctx.mk_idiv(a, b)
            r = ctx.mk_mod(a, b)
            self._arith_axioms_emitted.add(q)
            self._arith_axioms_emitted.add(r)
            if isinstance(b, Const):
                assert isinstance(b.value, int)
                assert not isinstance(b.value, bool)
                c = b.value
                if c == 0:
                    return
                axioms = (
                    ctx.mk_eq(a, ctx.mk_add(ctx.mk_mul(b, q), r)),
                    ctx.mk_ge(r, ctx.mk_int_val(0)),
                    ctx.mk_lt(r, ctx.mk_int_val(abs(c))),
                )
            else:
                z0 = ctx.mk_int_val(0)
                b0 = ctx.mk_eq(b, z0)
                axioms = (
                    ctx.mk_or(b0, ctx.mk_eq(a, ctx.mk_add(ctx.mk_mul(b, q), r))),
                    ctx.mk_or(b0, ctx.mk_ge(r, z0)),
                    ctx.mk_or(b0, ctx.mk_lt(b, z0), ctx.mk_lt(r, b)),
                    ctx.mk_or(b0, ctx.mk_gt(b, z0), ctx.mk_lt(r, ctx.mk_neg(b))),
                )
            for ax in axioms:
                self._emit_clause([self.encode(ax, polarity=1)])
            return

        self._arith_axioms_emitted.add(anode)
        if akind is DeclKind.ABS:
            x = anode.args[0]
            z0 = ctx.mk_int_val(0)
            for ax in (
                ctx.mk_implies(ctx.mk_ge(x, z0), ctx.mk_eq(anode, x)),
                ctx.mk_implies(ctx.mk_lt(x, z0), ctx.mk_eq(anode, ctx.mk_neg(x))),
            ):
                self._emit_clause([self.encode(ax, polarity=1)])
        elif akind is DeclKind.TO_INT:
            r = anode.args[0]
            tr = ctx.mk_to_real(anode)
            for ax in (
                ctx.mk_le(tr, r),
                ctx.mk_lt(r, ctx.mk_add(tr, ctx.mk_real_val(1))),
            ):
                self._emit_clause([self.encode(ax, polarity=1)])
        elif akind is DeclKind.DIV:
            num, den = anode.args
            if isinstance(den, Const):
                return
            r0 = ctx.mk_real_val(0)
            ax = ctx.mk_or(ctx.mk_eq(den, r0), ctx.mk_eq(ctx.mk_mul(anode, den), num))
            self._emit_clause([self.encode(ax, polarity=1)])

    def _is_encoded(self, node: Expr, pol: int) -> bool:
        if pol > 0:
            return node in self._pos_encoded
        if pol < 0:
            return node in self._neg_encoded
        return node in self._pos_encoded and node in self._neg_encoded

    def _get_lit(self, expr: Expr) -> Lit:
        base, flip = _strip_nots(expr)
        if isinstance(base, Const):
            lit = self._get_true_lit() if base.value else self._get_false_lit()
        elif _is_bool_fixed_distinct(base):
            assert isinstance(base, App)
            lit = self._get_true_lit() if len(base.args) <= 1 else self._get_false_lit()
        else:
            lit = pos_lit(self._expr_to_var[base])
        return negate(lit) if flip else lit

    def _distinct_eq_pairs(self, node: App) -> list[Expr]:
        args = node.args
        return [self._ctx.mk_eq(args[i], args[j]) for i in range(len(args)) for j in range(i + 1, len(args))]

    def _child_polarities(self, node: App, pol: int) -> list[tuple[Expr, int]]:
        kind = node.decl.kind
        match kind:
            case DeclKind.AND | DeclKind.OR:
                return [(arg, pol) for arg in node.args]
            case DeclKind.IMPLIES:
                neg_pol = -pol if pol != 0 else 0
                return [(node.args[0], neg_pol), (node.args[1], pol)]
            case DeclKind.XOR | DeclKind.EQ:
                return [(arg, 0) for arg in node.args]
            case DeclKind.DISTINCT:
                if node.args and not node.args[0].is_bool:
                    neg_pol = -pol if pol != 0 else 0
                    return [(eq_expr, neg_pol) for eq_expr in self._distinct_eq_pairs(node)]
                return [(arg, 0) for arg in node.args]
            case DeclKind.ITE:
                return [(node.args[0], 0), (node.args[1], pol), (node.args[2], pol)]
            case _:
                msg = f"Unsupported Boolean operator in Tseitin encoder: {kind}"
                raise TypeError(msg)

    def _emit_gate_clauses(self, node: App, pol: int) -> None:
        v = pos_lit(self.ensure_expr_var(node))
        nv = negate(v)
        emit_pos = pol >= 0 and node not in self._pos_encoded
        emit_neg = pol <= 0 and node not in self._neg_encoded

        if node.decl.kind is DeclKind.DISTINCT and node.args and not node.args[0].is_bool:
            pair_lits = [self._get_lit(eq_expr) for eq_expr in self._distinct_eq_pairs(node)]
            if emit_pos:
                for eq_lit in pair_lits:
                    self._emit_clause([nv, negate(eq_lit)])
                self._pos_encoded.add(node)
            if emit_neg:
                self._emit_clause([v, *pair_lits])
                self._neg_encoded.add(node)
            return

        lits = [self._get_lit(arg) for arg in node.args]

        match node.decl.kind:
            case DeclKind.AND:
                if emit_pos:
                    for lit in lits:
                        self._emit_clause([nv, lit])
                if emit_neg:
                    self._emit_clause([v, *(negate(lit) for lit in lits)])
            case DeclKind.OR:
                if emit_pos:
                    self._emit_clause([nv, *lits])
                if emit_neg:
                    for lit in lits:
                        self._emit_clause([v, negate(lit)])
            case DeclKind.IMPLIES:
                la, lb = lits
                if emit_pos:
                    self._emit_clause([nv, negate(la), lb])
                if emit_neg:
                    self._emit_clause([v, la])
                    self._emit_clause([v, negate(lb)])
            case DeclKind.XOR | DeclKind.DISTINCT:
                la, lb = lits
                if emit_pos:
                    self._emit_clause([nv, la, lb])
                    self._emit_clause([nv, negate(la), negate(lb)])
                if emit_neg:
                    self._emit_clause([v, negate(la), lb])
                    self._emit_clause([v, la, negate(lb)])
            case DeclKind.EQ:
                la, lb = lits
                if emit_pos:
                    self._emit_clause([nv, negate(la), lb])
                    self._emit_clause([nv, la, negate(lb)])
                if emit_neg:
                    self._emit_clause([v, la, lb])
                    self._emit_clause([v, negate(la), negate(lb)])
            case DeclKind.ITE:
                lc, lt, le = lits
                if emit_pos:
                    self._emit_clause([nv, negate(lc), lt])
                    self._emit_clause([nv, lc, le])
                if emit_neg:
                    self._emit_clause([v, negate(lc), negate(lt)])
                    self._emit_clause([v, lc, negate(le)])
            case _:
                msg = f"Unsupported Boolean operator in Tseitin encoder: {node.decl}"
                raise TypeError(msg)

        if emit_pos:
            self._pos_encoded.add(node)
        if emit_neg:
            self._neg_encoded.add(node)

    def encode(self, expr: Expr, polarity: int = 1) -> Lit:
        """Encode ``expr`` iteratively with polarity ``+1``, ``-1``, or ``0``."""
        root_base, root_flip = _strip_nots(expr)
        root_pol = -polarity if (root_flip and polarity != 0) else polarity
        stack: list[tuple[Expr, int, bool]] = [(root_base, root_pol, False)]
        catch_up = self._clause_sink is None

        while stack:
            node, pol, expanded = stack.pop()
            if self._is_encoded(node, pol):
                continue

            if isinstance(node, Const) or _is_bool_fixed_distinct(node):
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if isinstance(node, Quantifier):
                self._encode_quantifier(node, pol)
                continue

            if not isinstance(node, App):
                msg = f"Unsupported AST node in Tseitin encoder: {node!r}"
                raise TypeError(msg)

            if node.is_const_symbol:
                self.ensure_expr_var(node)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            kind = node.decl.kind
            if kind is DeclKind.IS_INT:
                arg = node.args[0]
                reduced = self._ctx.mk_eq(arg, self._ctx.mk_to_real(self._ctx.mk_to_int(arg)))
                lit_red = self.encode(reduced, polarity=0)
                lit_v = pos_lit(self.ensure_expr_var(node))
                self._emit_clause([negate(lit_v), lit_red])
                self._emit_clause([lit_v, negate(lit_red)])
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.DIVISIBLE:
                mod_n = node.decl.params[0]
                arg = node.args[0]
                reduced = self._ctx.mk_eq(
                    self._ctx.mk_mod(arg, self._ctx.mk_int_val(mod_n)),
                    self._ctx.mk_int_val(0),
                )
                lit_red = self.encode(reduced, polarity=0)
                lit_v = pos_lit(self.ensure_expr_var(node))
                self._emit_clause([negate(lit_v), lit_red])
                self._emit_clause([lit_v, negate(lit_red)])
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.STR_PREFIXOF:
                p_arg, s_arg = node.args
                lp = self._ctx.mk_str_len(p_arg)
                reduced = self._ctx.mk_and(
                    self._ctx.mk_le(lp, self._ctx.mk_str_len(s_arg)),
                    self._ctx.mk_eq(
                        self._ctx.mk_str_substr(s_arg, self._ctx.mk_int_val(0), lp),
                        p_arg,
                    ),
                )
                lit_red = self.encode(reduced, polarity=0)
                lit_v = pos_lit(self.ensure_expr_var(node))
                self._emit_clause([negate(lit_v), lit_red])
                self._emit_clause([lit_v, negate(lit_red)])
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.STR_SUFFIXOF:
                suf_arg, s_arg = node.args
                lsuf = self._ctx.mk_str_len(suf_arg)
                ls = self._ctx.mk_str_len(s_arg)
                reduced = self._ctx.mk_and(
                    self._ctx.mk_le(lsuf, ls),
                    self._ctx.mk_eq(
                        self._ctx.mk_str_substr(s_arg, self._ctx.mk_sub(ls, lsuf), lsuf),
                        suf_arg,
                    ),
                )
                lit_red = self.encode(reduced, polarity=0)
                lit_v = pos_lit(self.ensure_expr_var(node))
                self._emit_clause([negate(lit_v), lit_red])
                self._emit_clause([lit_v, negate(lit_red)])
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.STR_IS_DIGIT:
                s_arg = node.args[0]
                tc = self._ctx.mk_str_to_code(s_arg)
                reduced = self._ctx.mk_and(
                    self._ctx.mk_eq(self._ctx.mk_str_len(s_arg), self._ctx.mk_int_val(1)),
                    self._ctx.mk_ge(tc, self._ctx.mk_int_val(48)),
                    self._ctx.mk_le(tc, self._ctx.mk_int_val(57)),
                )
                lit_red = self.encode(reduced, polarity=0)
                lit_v = pos_lit(self.ensure_expr_var(node))
                self._emit_clause([negate(lit_v), lit_red])
                self._emit_clause([lit_v, negate(lit_red)])
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind in _STRING_PRED_KINDS:
                for arg in node.args:
                    self._register_term(arg, in_euf=True)
                self._strings.register_atom(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_string(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                if kind is DeclKind.STR_CONTAINS and node not in self._str_axioms_emitted:
                    self._str_axioms_emitted.add(node)
                    s_arg, t_arg = node.args
                    sk1 = self._alloc_skolem_const(self._ctx.string_sort)
                    sk2 = self._alloc_skolem_const(self._ctx.string_sort)
                    for ax in (
                        self._ctx.mk_implies(
                            node,
                            self._ctx.mk_eq(s_arg, self._ctx.mk_str_concat(sk1, t_arg, sk2)),
                        ),
                        self._ctx.mk_implies(self._ctx.mk_eq(t_arg, self._ctx.mk_string_val("")), node),
                        self._ctx.mk_implies(
                            self._ctx.mk_lt(
                                self._ctx.mk_str_len(s_arg),
                                self._ctx.mk_str_len(t_arg),
                            ),
                            self._ctx.mk_not(node),
                        ),
                    ):
                        self._emit_clause([self.encode(ax, polarity=1)])
                continue

            if kind in _CMP_KINDS:
                self._register_term(node.args[0], in_euf=False)
                self._register_term(node.args[1], in_euf=False)
                self._lra.register_atom(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_lra(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind in _BV_CMP_KINDS:
                self._register_term(node.args[0], in_euf=False)
                self._register_term(node.args[1], in_euf=False)
                self._bv.register_atom(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_bv(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.EQ and not node.args[0].is_bool:
                lhs, rhs = node.args
                if lhs.is_arith:
                    le = self._ctx.mk_le(lhs, rhs)
                    ge = self._ctx.mk_ge(lhs, rhs)
                    lit_le = self.encode(le, polarity=0)
                    lit_ge = self.encode(ge, polarity=0)
                    lit_eq = pos_lit(self.ensure_expr_var(node))
                    self._emit_clause([negate(lit_eq), lit_le])
                    self._emit_clause([negate(lit_eq), lit_ge])
                    self._emit_clause([lit_eq, negate(lit_le), negate(lit_ge)])
                    self._euf.register_eq(node)
                    self._prop.bind_euf(lit_eq, node, catch_up=catch_up)
                elif lhs.is_bv:
                    self._register_term(lhs, in_euf=False)
                    self._register_term(rhs, in_euf=False)
                    self._bv.register_atom(node)
                    lit_eq = pos_lit(self.ensure_expr_var(node))
                    self._prop.bind_bv(lit_eq, node, catch_up=catch_up)
                    self._euf.register_eq(node)
                    self._prop.bind_euf(lit_eq, node, catch_up=catch_up)
                else:
                    self._register_term(lhs, in_euf=True)
                    self._register_term(rhs, in_euf=True)
                    self._euf.register_eq(node)
                    var = self.ensure_expr_var(node)
                    self._prop.bind_euf(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if kind is DeclKind.SELECT:
                self._register_term(node, in_euf=True)
                self._euf.register_bool_term(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_euf(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if node.decl.is_uninterpreted and node.args:
                self._register_term(node, in_euf=True)
                self._euf.register_bool_term(node)
                var = self.ensure_expr_var(node)
                self._prop.bind_euf(pos_lit(var), node, catch_up=catch_up)
                self._pos_encoded.add(node)
                self._neg_encoded.add(node)
                continue

            if not expanded:
                stack.append((node, pol, True))
                for child, child_pol in reversed(self._child_polarities(node, pol)):
                    c_base, c_flip = _strip_nots(child)
                    eff_pol = -child_pol if (c_flip and child_pol != 0) else child_pol
                    if not self._is_encoded(c_base, eff_pol):
                        stack.append((c_base, eff_pol, False))
                continue

            self._emit_gate_clauses(node, pol)

        return self._get_lit(expr)
