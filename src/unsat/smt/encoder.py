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
from unsat.tactics import BitBlaster, bv_simplify, simplify, skolemize
from unsat.theories import ArraySolver, BVSolver, EUFSolver, LRASolver

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
        bitblaster: BitBlaster,
        prop: _PropSink,
    ) -> None:
        self._ctx = ctx
        self._sat = sat_solver
        self._euf = euf_solver
        self._lra = lra_solver
        self._arrays = array_solver
        self._bv = bv_solver
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

    def mark_quantifier_owners(
        self, expr: Expr, owners: Lit | Iterable[Lit | None] | None
    ) -> None:
        """Associate ``owners`` with quantifiers appearing in ``expr``."""
        owner_set = (
            {owners} if (owners is None or isinstance(owners, int)) else set(owners)
        )
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

    def _emit_existential_witness(
        self, guard_cond_lit: Lit, node: Quantifier, *, negate_body: bool
    ) -> None:
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
        conjuncts = (
            sk_expr.args
            if isinstance(sk_expr, App) and sk_expr.decl.kind is DeclKind.AND
            else (sk_expr,)
        )
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
                    self._emit_existential_witness(
                        negate(q_lit), node, negate_body=False
                    )
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

    def encode_lemma(
        self, expr: Expr, polarity: int = 1
    ) -> tuple[Lit, list[list[Lit]]]:
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
        stack: list[tuple[Expr, bool, bool]] = [(term, in_euf, False)]

        while stack:
            node, euf_flag, expanded = stack.pop()
            if euf_flag:
                if node in self._terms_euf:
                    continue
            elif node in self._terms_euf or node in self._terms_non_euf:
                continue

            if isinstance(node, Const):
                if euf_flag:
                    self._terms_euf.add(node)
                    self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                    elif node.is_bv:
                        self._prop.add_shared_bv_term(node)
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
                non_bool_ites.append(node)
                continue

            if kind in _ARITH_OP_KINDS:
                div_congruent = kind in (
                    DeclKind.IDIV,
                    DeclKind.MOD,
                    DeclKind.DIV,
                ) and (not isinstance(node.args[1], Const) or node.args[1].value == 0)
                eff_arith_euf = euf_flag or div_congruent
                if not expanded:
                    stack.append((node, eff_arith_euf, True))
                    for arg in reversed(node.args):
                        stack.append((arg, eff_arith_euf, False))
                    continue
                if eff_arith_euf:
                    self._terms_euf.add(node)
                    if div_congruent:
                        self._euf.register_term(node)
                    if node.is_arith:
                        self._prop.add_shared_arith_term(node)
                else:
                    self._terms_non_euf.add(node)
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

            if kind in _BV_OP_KINDS:
                if not expanded:
                    stack.append((node, euf_flag, True))
                    for arg in reversed(node.args):
                        stack.append((arg, euf_flag, False))
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
                else:
                    if euf_flag:
                        self._terms_euf.add(node)
                        self._euf.register_term(node)
                        if node.is_arith:
                            self._prop.add_shared_arith_term(node)
                        elif node.is_bv:
                            self._prop.add_shared_bv_term(node)
                        elif node.is_array:
                            self._arrays.register_term(node)
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
        return [
            self._ctx.mk_eq(args[i], args[j])
            for i in range(len(args))
            for j in range(i + 1, len(args))
        ]

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
                    return [
                        (eq_expr, neg_pol) for eq_expr in self._distinct_eq_pairs(node)
                    ]
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

        if (
            node.decl.kind is DeclKind.DISTINCT
            and node.args
            and not node.args[0].is_bool
        ):
            pair_lits = [
                self._get_lit(eq_expr) for eq_expr in self._distinct_eq_pairs(node)
            ]
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
                reduced = self._ctx.mk_eq(
                    arg, self._ctx.mk_to_real(self._ctx.mk_to_int(arg))
                )
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
