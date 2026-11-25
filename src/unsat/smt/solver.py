"""Incremental CDCL(T) SMT solver orchestration and quantifier loop."""

import math
import time
from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from unsat.model import Model, ProjectionModelConverter, Value
from unsat.quantifiers import (
    EMatcher,
    MBQIEngine,
    QuantifierBudget,
    QuantifierStats,
    SubSolverStatus,
)
from unsat.sat import Lit, SATSolver, SolveResult, negate, pos_lit
from unsat.smt.encoder import _PlaistedGreenbaumEncoder
from unsat.smt.propagator import _CombinedPropagator
from unsat.syntax import App, Context, DeclKind, Expr, FuncDecl, Quantifier
from unsat.tactics import BitBlaster, Tactic, bv_simplify, simplify
from unsat.theories import ArraySolver, EUFSolver, LRASolver


def _validate_timeout(timeout: float | None) -> None:
    if timeout is not None and (math.isnan(timeout) or timeout < 0):
        msg = f"timeout must be non-negative, got {timeout}"
        raise ValueError(msg)


def _validate_max_conflicts(max_conflicts: int | None) -> None:
    if max_conflicts is not None and max_conflicts < 0:
        msg = f"max_conflicts must be non-negative, got {max_conflicts}"
        raise ValueError(msg)


@dataclass
class _SearchBudget:
    deadline: float | None = None
    remaining_conflicts: int | None = None

    def timed_out(self) -> bool:
        return self.deadline is not None and time.monotonic() >= self.deadline

    def remaining_timeout(self) -> float | None:
        if self.deadline is None:
            return None
        return max(0.0, self.deadline - time.monotonic())

    def consume_conflicts(self, used: int) -> None:
        if self.remaining_conflicts is not None:
            self.remaining_conflicts = max(0, self.remaining_conflicts - used)


class _GroundSubSolver:
    """Injected quantifier-free sub-solver callback for MBQI verification."""

    def __init__(self, ctx: Context, budget: _SearchBudget | None = None) -> None:
        self._ctx = ctx
        self._budget = budget

    def check_formula(
        self, formulas: Sequence[Expr]
    ) -> tuple[SubSolverStatus, Model | None]:
        if self._budget is not None and self._budget.timed_out():
            return SubSolverStatus.UNKNOWN, None
        solver = SMTSolver(self._ctx)
        solver.add(*formulas)
        timeout = None if self._budget is None else self._budget.remaining_timeout()
        max_conflicts = (
            None if self._budget is None else self._budget.remaining_conflicts
        )
        res = solver.check(timeout=timeout, max_conflicts=max_conflicts)
        if self._budget is not None:
            self._budget.consume_conflicts(solver.statistics()["conflicts"])
        if res is SolveResult.SAT:
            return SubSolverStatus.SAT, solver.model()
        if res is SolveResult.UNSAT:
            return SubSolverStatus.UNSAT, None
        return SubSolverStatus.UNKNOWN, None


class SMTSolver:
    """Incremental CDCL(T) SMT solver over a specific :class:`Context`."""

    def __init__(
        self,
        ctx: Context,
        *,
        quantifier_budget: QuantifierBudget | None = None,
        max_quantifier_rounds: int | None = None,
        max_quantifier_matches: int | None = None,
        timeout: float | None = None,
        max_conflicts: int | None = None,
    ) -> None:
        _validate_timeout(timeout)
        _validate_max_conflicts(max_conflicts)
        self._ctx = ctx
        self._timeout = timeout
        self._max_conflicts = max_conflicts
        if quantifier_budget is not None:
            self._quant_budget = quantifier_budget
        else:
            default_b = QuantifierBudget()
            self._quant_budget = QuantifierBudget(
                max_rounds=(
                    default_b.max_rounds
                    if max_quantifier_rounds is None
                    else max_quantifier_rounds
                ),
                max_matches=(
                    default_b.max_matches
                    if max_quantifier_matches is None
                    else max_quantifier_matches
                ),
            )
        self._init_backend()
        self._scope_lits: list[Lit] = []
        self._assertions_by_scope: list[list[Expr]] = [[]]
        self._last_result: SolveResult | None = None
        self._unsat_core: list[Expr] = []
        self._verified_model: Model | None = None

    def _init_backend(self) -> None:
        self._euf = EUFSolver(self._ctx)
        self._lra = LRASolver(self._ctx)
        self._arrays = ArraySolver(self._ctx)
        self._bitblaster = BitBlaster(self._ctx)
        self._propagator = _CombinedPropagator(
            self._ctx, self._euf, self._lra, self._arrays, self._bitblaster
        )
        self._sat = SATSolver(propagator=self._propagator)
        self._encoder = _PlaistedGreenbaumEncoder(
            self._ctx,
            self._sat,
            self._euf,
            self._lra,
            self._arrays,
            self._bitblaster,
            self._propagator,
        )
        self._propagator.attach(self._sat, self._encoder)
        self._quant_stats = QuantifierStats()
        self._ematcher = EMatcher()
        self._mbqi = MBQIEngine()
        self._encoded_insts: set[tuple[Lit, Expr]] = set()
        self._verified_model = None

    @property
    def ctx(self) -> Context:
        """AST context associated with this solver."""
        return self._ctx

    @property
    def num_scopes(self) -> int:
        """Current incremental ``push`` nesting depth."""
        return len(self._scope_lits)

    def _validate_bool_expr(self, expr: Expr) -> None:
        if expr.ctx is not self._ctx:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)
        if not expr.is_bool:
            msg = f"Expected Bool expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _ensure_base_level(self) -> None:
        if self._last_result is None:
            return
        any_lit = self._encoder.any_lit()
        if any_lit is None and self._scope_lits:
            any_lit = self._scope_lits[0]
        if any_lit is not None:
            self._sat.add_clause([any_lit, negate(any_lit)])

    def add(self, *formulas: Expr) -> None:
        """Assert one or more Boolean formulas into the current scope."""
        self._ensure_base_level()
        self._verified_model = None
        for formula in formulas:
            self._validate_bool_expr(formula)
            self._assertions_by_scope[-1].append(formula)
            self._encoder.record_reserved(formula)
            simplified = bv_simplify(simplify(formula))
            conjuncts = (
                simplified.args
                if isinstance(simplified, App) and simplified.decl.kind is DeclKind.AND
                else (simplified,)
            )
            for conjunct in conjuncts:
                if conjunct is self._ctx.true_expr:
                    continue
                if conjunct is self._ctx.false_expr:
                    if not self._scope_lits:
                        self._sat.add_clause([])
                    else:
                        self._sat.add_clause([negate(self._scope_lits[-1])])
                    continue
                lit = self._encoder.encode(conjunct, polarity=1)
                owner = self._scope_lits[-1] if self._scope_lits else None
                self._encoder.mark_quantifier_owners(conjunct, owner)
                if not self._scope_lits:
                    self._sat.add_clause([lit])
                else:
                    self._sat.add_clause([negate(self._scope_lits[-1]), lit])
        self._last_result = None

    def push(self) -> None:
        """Push a new incremental assertion scope."""
        self._ensure_base_level()
        act_lit = pos_lit(self._sat.new_var())
        self._scope_lits.append(act_lit)
        self._assertions_by_scope.append([])
        self._last_result = None
        self._verified_model = None

    def pop(self, levels: int = 1) -> None:
        """Pop ``levels`` incremental scopes, retracting their assertions."""
        if levels < 0 or levels > len(self._scope_lits):
            msg = f"Cannot pop {levels} scopes (current depth: {len(self._scope_lits)})"
            raise ValueError(msg)
        self._ensure_base_level()
        for _ in range(levels):
            act_lit = self._scope_lits.pop()
            self._sat.add_clause([negate(act_lit)])
            self._assertions_by_scope.pop()
        self._ematcher.clear_emitted()
        self._last_result = None
        self._verified_model = None

    def reset(self) -> None:
        """Reset all assertions, scopes, and learned state."""
        self._init_backend()
        self._scope_lits.clear()
        self._assertions_by_scope = [[]]
        self._last_result = None
        self._unsat_core = []

    def _add_guarded_instantiation(
        self,
        guard_lit: Lit,
        inst_expr: Expr,
        owners: Iterable[Lit | None] = (None,),
    ) -> None:
        simp = bv_simplify(simplify(inst_expr))
        owner_tuple = tuple(owners)
        key = (guard_lit, simp)
        if key in self._encoded_insts:
            self._encoder.mark_quantifier_owners(simp, owner_tuple)
            return
        self._encoded_insts.add(key)
        conjuncts = (
            simp.args
            if isinstance(simp, App) and simp.decl.kind is DeclKind.AND
            else (simp,)
        )
        for conj in conjuncts:
            if conj is self._ctx.true_expr:
                continue
            if conj is self._ctx.false_expr:
                self._sat.add_clause([negate(guard_lit)])
                continue
            self._encoder.record_reserved(conj)
            lit_inst = self._encoder.encode(conj, polarity=1)
            self._encoder.mark_quantifier_owners(conj, owner_tuple)
            self._sat.add_clause([negate(guard_lit), lit_inst])

    def check(
        self,
        *assumptions: Expr,
        timeout: float | None = None,
        max_conflicts: int | None = None,
    ) -> SolveResult:
        """Check satisfiability of asserted formulas under ``assumptions``."""
        _validate_timeout(timeout)
        _validate_max_conflicts(max_conflicts)
        eff_timeout = self._timeout if timeout is None else timeout
        eff_max_conflicts = (
            self._max_conflicts if max_conflicts is None else max_conflicts
        )
        deadline = None if eff_timeout is None else time.monotonic() + eff_timeout
        budget = _SearchBudget(deadline=deadline, remaining_conflicts=eff_max_conflicts)

        self._ensure_base_level()
        self._verified_model = None
        sat_assumptions = list(self._scope_lits)
        lit_to_exprs: dict[Lit, list[Expr]] = {}

        for assumption in assumptions:
            self._validate_bool_expr(assumption)
            self._encoder.record_reserved(assumption)
            simplified = bv_simplify(simplify(assumption))
            lit = self._encoder.encode(simplified, polarity=1)
            self._encoder.mark_quantifier_owners(simplified, lit)
            sat_assumptions.append(lit)
            lit_to_exprs.setdefault(lit, []).append(assumption)

        live_owner_lits: set[Lit | None] = {None, *sat_assumptions}
        sub_solver = _GroundSubSolver(self._ctx, budget=budget)
        total_rounds = 0
        mbqi_rounds = 0

        while True:
            if budget.timed_out():
                self._last_result = SolveResult.UNKNOWN
                self._unsat_core = []
                return SolveResult.UNKNOWN

            self._propagator.reset_check_state()
            conflicts_before = self._sat.statistics()["conflicts"]
            result = self._sat.solve(
                sat_assumptions,
                max_conflicts=budget.remaining_conflicts,
                deadline=budget.deadline,
            )
            budget.consume_conflicts(
                self._sat.statistics()["conflicts"] - conflicts_before
            )
            if result is SolveResult.UNSAT:
                self._last_result = SolveResult.UNSAT
                core: list[Expr] = []
                for lit in self._sat.unsat_core():
                    mapped = lit_to_exprs.get(lit)
                    if mapped:
                        core.append(mapped[0])
                self._unsat_core = list(dict.fromkeys(core))
                return SolveResult.UNSAT
            if result is SolveResult.UNKNOWN:
                self._last_result = SolveResult.UNKNOWN
                self._unsat_core = []
                return SolveResult.UNKNOWN

            self._unsat_core = []
            entries = self._encoder.universal_entries
            if not entries:
                self._last_result = SolveResult.SAT
                return SolveResult.SAT

            active_entries = [
                (u_lit, norm_q, {ol for ol in owners if ol in live_owner_lits})
                for u_lit, norm_q, owners in entries
                if any(ol in live_owner_lits for ol in owners)
                and self._sat.value(u_lit) is True
            ]
            if not active_entries:
                self._last_result = SolveResult.SAT
                return SolveResult.SAT

            q_to_guards: dict[Quantifier, list[tuple[Lit, frozenset[Lit | None]]]] = {}
            for u_lit, norm_q, live_q_owners in active_entries:
                q_to_guards.setdefault(norm_q, []).append(
                    (u_lit, frozenset(live_q_owners))
                )
            active_quants = list(q_to_guards)

            if total_rounds >= self._quant_budget.max_rounds:
                self._quant_stats.budget_exhausted += 1
                self._last_result = SolveResult.UNKNOWN
                return SolveResult.UNKNOWN
            if budget.timed_out():
                self._last_result = SolveResult.UNKNOWN
                return SolveResult.UNKNOWN

            ematch_res = self._ematcher.match_round(
                self._euf, active_quants, self._quant_budget, self._quant_stats
            )
            if ematch_res.instantiations:
                to_encode: list[tuple[Lit, Expr, frozenset[Lit | None]]] = []
                for q, _, inst_expr in ematch_res.instantiations:
                    for guard_lit, guard_owners in q_to_guards[q]:
                        to_encode.append((guard_lit, inst_expr, guard_owners))
                self._last_result = SolveResult.SAT
                self._ensure_base_level()
                for guard_lit, inst_expr, guard_owners in to_encode:
                    self._add_guarded_instantiation(guard_lit, inst_expr, guard_owners)
                total_rounds += 1
                continue

            if mbqi_rounds >= self._quant_budget.max_mbqi_rounds:
                self._quant_stats.budget_exhausted += 1
                self._last_result = SolveResult.UNKNOWN
                return SolveResult.UNKNOWN
            if budget.timed_out():
                self._last_result = SolveResult.UNKNOWN
                return SolveResult.UNKNOWN

            ground_model = self._build_model(strip_internal=False)
            mbqi_res = self._mbqi.check_and_refine(
                active_quants,
                ground_model,
                self._euf,
                sub_solver,
                self._quant_budget,
                self._quant_stats,
                already_emitted=self._ematcher.emitted,
            )
            if mbqi_res.verified:
                if mbqi_res.model is not None:
                    projector = ProjectionModelConverter(self._all_internal_decls())
                    self._verified_model = projector.convert(mbqi_res.model)
                else:
                    self._verified_model = self._build_model(strip_internal=True)
                self._last_result = SolveResult.SAT
                return SolveResult.SAT

            if mbqi_res.instantiations:
                mbqi_to_encode: list[tuple[Lit, Expr, frozenset[Lit | None]]] = []
                for q, args, inst_expr in mbqi_res.instantiations:
                    self._ematcher.record_emitted(q, self._euf, args)
                    for guard_lit, guard_owners in q_to_guards[q]:
                        mbqi_to_encode.append((guard_lit, inst_expr, guard_owners))
                self._last_result = SolveResult.SAT
                self._ensure_base_level()
                for guard_lit, inst_expr, guard_owners in mbqi_to_encode:
                    self._add_guarded_instantiation(guard_lit, inst_expr, guard_owners)
                mbqi_rounds += 1
                total_rounds += 1
                continue

            self._last_result = SolveResult.UNKNOWN
            return SolveResult.UNKNOWN

    def _all_internal_decls(self) -> frozenset[FuncDecl]:
        return frozenset(
            self._bitblaster.internal_decls
            | self._arrays.internal_decls
            | self._encoder.internal_decls
            | self._mbqi.internal_decls
        )

    def _build_model(self, *, strip_internal: bool) -> Model:
        sat_model = self._sat.model()
        internal_decls = (
            self._all_internal_decls()
            if strip_internal
            else (self._bitblaster.internal_decls | self._arrays.internal_decls)
        )
        lra_conc = self._lra.concrete_values()
        shared_terms = self._propagator.all_shared_arith_terms()
        shared_conc = self._lra.term_values(shared_terms) if shared_terms else {}

        external_vals: dict[Expr, Expr] = {}
        for expr, frac in {**lra_conc, **shared_conc}.items():
            if expr.is_int:
                assert frac.denominator == 1
                external_vals[expr] = self._ctx.mk_int_val(frac.numerator)
            elif expr.is_real:
                external_vals[expr] = self._ctx.mk_real_val(frac)

        def _bit_lookup(node: Expr) -> bool:
            var = self._encoder.expr_var_or_none(node)
            return sat_model[var] if var is not None else False

        bv_decl_vals: dict[FuncDecl, int] = {}
        for bv_decl, bits in self._bitblaster.bv_const_bits.items():
            if bv_decl not in internal_decls:
                bv_decl_vals[bv_decl] = self._bitblaster.eval_bits(bits, _bit_lookup)
        for bv_term in self._propagator.all_shared_bv_terms():
            bv_int = self._bitblaster.eval_term_bits(bv_term, _bit_lookup)
            external_vals[bv_term] = self._ctx.mk_bv_val(bv_int, bv_term.bv_size)

        for decl, var in self._encoder.decl_to_var.items():
            if decl not in internal_decls:
                external_vals[decl()] = self._ctx.mk_bool_val(sat_model[var])

        scalar_vals = self._euf.resolve_scalar_values(external_values=external_vals)
        array_input = {**scalar_vals, **external_vals}
        array_vals = self._arrays.build_array_values(self._euf, array_input)
        all_external = {**external_vals, **array_vals}

        euf_model = self._euf.build_model(external_values=all_external)
        values: dict[FuncDecl, Value] = {
            decl: val for decl, val in euf_model.items() if decl not in internal_decls
        }
        for expr, frac in lra_conc.items():
            if (
                isinstance(expr, App)
                and expr.is_const_symbol
                and expr.decl not in internal_decls
            ):
                if expr.is_int:
                    assert frac.denominator == 1
                    values[expr.decl] = frac.numerator
                elif expr.is_real:
                    values[expr.decl] = frac
        values.update(bv_decl_vals)
        for decl, var in self._encoder.decl_to_var.items():
            if decl not in internal_decls:
                values[decl] = sat_model[var]
        for term, arr_val in array_vals.items():
            if (
                isinstance(term, App)
                and term.is_const_symbol
                and term.decl not in internal_decls
            ):
                values[term.decl] = arr_val

        functions = {
            decl: euf_model.func_interp(decl)
            for decl in euf_model.func_decls()
            if decl not in internal_decls
        }
        universes = {sort: euf_model.universe(sort) for sort in euf_model.sorts()}
        return Model(self._ctx, values, functions=functions, universes=universes)

    def model(self) -> Model:
        """Return a satisfying :class:`Model` from the latest ``check()`` call."""
        if self._last_result is not SolveResult.SAT:
            msg = "Model is only available after check() returns SolveResult.SAT"
            raise ValueError(msg)
        if self._verified_model is not None:
            return self._verified_model
        return self._build_model(strip_internal=True)

    def unsat_core(self) -> list[Expr]:
        """Return the assumption subset responsible for the last ``UNSAT``."""
        return list(self._unsat_core)

    def assertions(self) -> list[Expr]:
        """Return all currently active asserted formulas in insertion order."""
        return [formula for scope in self._assertions_by_scope for formula in scope]

    def statistics(self) -> dict[str, int]:
        """Return merged SAT, EUF, LRA/LIA, Array, and Quantifier counters."""
        stats: dict[str, int] = {
            k: v for k, v in self._sat.statistics().items() if isinstance(v, int)
        }
        stats.update(self._euf.stats.to_dict())
        stats.update(self._lra.stats.to_dict())
        stats.update(self._arrays.stats.to_dict())
        stats.update(self._quant_stats.to_dict())
        return stats


def solve_with_tactic(
    formulas: Sequence[Expr],
    tactic: Tactic,
    *,
    ctx: Context | None = None,
    quantifier_budget: QuantifierBudget | None = None,
    max_quantifier_rounds: int | None = None,
    max_quantifier_matches: int | None = None,
    timeout: float | None = None,
    max_conflicts: int | None = None,
) -> tuple[SolveResult, Model | None]:
    """Preprocess ``formulas`` with ``tactic``, solve, and convert any ``Model``."""
    _validate_timeout(timeout)
    _validate_max_conflicts(max_conflicts)

    formula_list = list(formulas)
    target_ctx = ctx
    if target_ctx is None:
        if not formula_list:
            msg = "ctx is required when formulas is empty"
            raise ValueError(msg)
        target_ctx = formula_list[0].ctx

    for formula in formula_list:
        if formula.ctx is not target_ctx:
            msg = f"Expr '{formula}' belongs to a different Context"
            raise ValueError(msg)
        if not formula.is_bool:
            msg = f"Expected Bool expression, got sort '{formula.sort}'"
            raise TypeError(msg)

    deadline = None if timeout is None else time.monotonic() + timeout
    tactic_result = tactic.apply(formula_list)
    if deadline is not None and time.monotonic() >= deadline:
        return SolveResult.UNKNOWN, None

    rem_timeout = None if deadline is None else max(0.0, deadline - time.monotonic())
    solver = SMTSolver(
        target_ctx,
        quantifier_budget=quantifier_budget,
        max_quantifier_rounds=max_quantifier_rounds,
        max_quantifier_matches=max_quantifier_matches,
        timeout=rem_timeout,
        max_conflicts=max_conflicts,
    )
    solver.add(*tactic_result.formulas)
    res = solver.check()
    if res is SolveResult.SAT:
        return SolveResult.SAT, tactic_result.converter.convert(solver.model())
    return res, None
