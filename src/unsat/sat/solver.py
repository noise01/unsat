"""Incremental CDCL SAT solver core with lazy-explanation theory hooks."""

from collections.abc import Sequence

from unsat.sat.heap import VarMaxHeap
from unsat.sat.trail import THEORY_REASON, Trail
from unsat.sat.types import (
    L_FALSE,
    L_TRUE,
    L_UNDEF,
    Clause,
    Lit,
    SATStats,
    SolveResult,
    TheoryPropagator,
    Var,
    neg_lit,
    pos_lit,
)


class SATSolver:
    """Standalone incremental CDCL SAT solver operating on integer literals."""

    def __init__(self, propagator: TheoryPropagator | None = None) -> None:
        self._propagator = propagator
        self._trail = Trail()
        self._clauses: list[Clause] = []
        self._learned: list[Clause] = []
        self._watches: list[list[tuple[Lit, Clause]]] = []
        self._bin_watches: list[list[tuple[Lit, Clause]]] = []

        self._qhead = 0
        self._theory_qhead = 0
        self._ok = True
        self._last_result: SolveResult | None = None
        self._unsat_core: list[Lit] = []

        # EVSIDS branching heuristic.
        self._activities: list[float] = []
        self._heap = VarMaxHeap(self._activities)
        self._var_inc = 1.0
        self._var_decay = 0.95

        # Learned-clause DB & Glucose LBD restarts.
        self._clause_inc = 1.0
        self._clause_decay = 0.999
        self._reduce_threshold = 2000
        self._reduce_inc = 500

        self._seen: list[bool] = []
        self._seen_level: list[bool] = [False]

        self._conflicts = 0
        self._conflicts_since_restart = 0
        self._lbd_queue_size = 50
        self._lbd_queue = [0] * self._lbd_queue_size
        self._lbd_queue_pos = 0
        self._lbd_queue_sum = 0
        self._global_lbd_sum = 0
        self._restart_margin = 1.25
        self._restart_cooldown = 50

        self._stats: SATStats = {
            "conflicts": 0,
            "decisions": 0,
            "propagations": 0,
            "restarts": 0,
            "learned_clauses": 0,
            "deleted_clauses": 0,
            "theory_propagations": 0,
            "theory_conflicts": 0,
            "theory_lemmas": 0,
        }

    @property
    def num_vars(self) -> int:
        """Number of variables currently registered in the solver."""
        return self._trail.num_vars

    @property
    def ok(self) -> bool:
        """``False`` once top-level (decision level 0) inconsistency is derived."""
        return self._ok

    def new_var(self) -> Var:
        """Allocate and return a fresh 0-indexed SAT variable."""
        var = self._trail.add_variable()
        self._watches.extend(([], []))
        self._bin_watches.extend(([], []))
        self._activities.append(0.0)
        self._seen.append(False)
        self._seen_level.append(False)
        self._heap.insert(var)
        return var

    def ensure_vars(self, count: int) -> None:
        """Ensure at least ``count`` variables exist."""
        while self._trail.num_vars < count:
            self.new_var()

    def _ensure_lits_vars(self, literals: Sequence[Lit]) -> None:
        max_var = -1
        for lit in literals:
            if lit < 0:
                msg = f"Literal must be non-negative, got {lit}"
                raise ValueError(msg)
            var = lit >> 1
            if var > max_var:
                max_var = var
        if max_var >= self._trail.num_vars:
            self.ensure_vars(max_var + 1)

    def add_clause(self, literals: Sequence[Lit]) -> bool:
        """Assert a clause at decision level 0.

        Returns ``False`` if the clause database is immediately inconsistent.
        """
        self._ensure_lits_vars(literals)
        self._last_result = None

        if not self._ok:
            return False

        if self._trail.decision_level > 0:
            self._backtrack(0)

        normalized: list[Lit] = []
        seen_lits: set[Lit] = set()
        for lit in literals:
            if (lit ^ 1) in seen_lits:
                return True  # Tautology.
            val = self._trail.eval_lit(lit)
            if val == L_TRUE:
                return True  # Already satisfied at level 0.
            if val == L_FALSE:
                continue
            if lit not in seen_lits:
                seen_lits.add(lit)
                normalized.append(lit)

        if not normalized:
            self._ok = False
            return False

        if len(normalized) == 1:
            self._trail.assign(normalized[0], reason=None)
            if self._propagate() is not None:
                self._ok = False
                return False
            return True

        clause = Clause(normalized, learned=False)
        self._clauses.append(clause)
        self._attach_clause(clause)
        return True

    def solve(self, assumptions: Sequence[Lit] | None = None) -> SolveResult:
        """Solve the current formula under optional ``assumptions``."""
        assumption_list = list(assumptions) if assumptions is not None else []
        self._ensure_lits_vars(assumption_list)

        self._unsat_core = []
        if not self._ok:
            self._last_result = SolveResult.UNSAT
            return SolveResult.UNSAT

        self._backtrack(0)
        assumption_set = set(assumption_list)
        pending_conflict: Clause | None = None

        while True:
            conflict = (
                pending_conflict if pending_conflict is not None else self._propagate()
            )
            pending_conflict = None

            if conflict is not None:
                if self._handle_conflict(conflict) is SolveResult.UNSAT:
                    self._ok = False
                    self._unsat_core = []
                    self._last_result = SolveResult.UNSAT
                    return SolveResult.UNSAT
                continue

            next_assumption = self._next_assumption(assumption_list)
            if next_assumption is not None:
                if self._trail.eval_lit(next_assumption) == L_FALSE:
                    self._unsat_core = self._analyze_final(
                        next_assumption, assumption_set
                    )
                    self._last_result = SolveResult.UNSAT
                    return SolveResult.UNSAT

                self._stats["decisions"] += 1
                self._trail.push()
                if self._propagator is not None:
                    self._propagator.push()
                self._trail.assign(next_assumption, reason=None)
                continue

            if self._trail.all_assigned:
                if self._propagator is not None:
                    lemmas = self._propagator.check()
                    if lemmas:
                        self._stats["theory_lemmas"] += len(lemmas)
                        progressed = False
                        for raw_lemma in lemmas:
                            lemma_conflict, added_progress = self._add_theory_lemma(
                                raw_lemma
                            )
                            progressed = progressed or added_progress
                            if lemma_conflict is not None:
                                pending_conflict = lemma_conflict
                                progressed = True
                                break
                        if progressed:
                            continue

                self._last_result = SolveResult.SAT
                return SolveResult.SAT

            decision_lit = self._pick_branch_lit()
            self._stats["decisions"] += 1
            self._trail.push()
            if self._propagator is not None:
                self._propagator.push()
            self._trail.assign(decision_lit, reason=None)

    def model(self) -> dict[Var, bool]:
        """Return the variable assignment from the most recent ``SAT`` result."""
        if self._last_result is not SolveResult.SAT:
            msg = "Model is only available after solve() returns SolveResult.SAT"
            raise ValueError(msg)
        return {
            var: self._trail.assignment[var] == L_TRUE
            for var in range(self._trail.num_vars)
        }

    def value(self, lit: Lit) -> bool | None:
        """Return the truth value of ``lit`` on the current trail, or ``None``."""
        if lit < 0 or (lit >> 1) >= self._trail.num_vars:
            msg = f"Literal {lit} is out of range for {self._trail.num_vars} variables"
            raise ValueError(msg)
        val = self._trail.eval_lit(lit)
        if val == L_TRUE:
            return True
        if val == L_FALSE:
            return False
        return None

    def unsat_core(self) -> list[Lit]:
        """Return the assumption subset responsible for the last ``UNSAT``."""
        return list(self._unsat_core)

    def statistics(self) -> SATStats:
        """Return a snapshot of SAT search counters."""
        return {
            "conflicts": self._stats["conflicts"],
            "decisions": self._stats["decisions"],
            "propagations": self._stats["propagations"],
            "restarts": self._stats["restarts"],
            "learned_clauses": self._stats["learned_clauses"],
            "deleted_clauses": self._stats["deleted_clauses"],
            "theory_propagations": self._stats["theory_propagations"],
            "theory_conflicts": self._stats["theory_conflicts"],
            "theory_lemmas": self._stats["theory_lemmas"],
        }

    def _attach_clause(self, clause: Clause) -> None:
        lits = clause.literals
        if len(lits) == 2:
            self._bin_watches[lits[0]].append((lits[1], clause))
            self._bin_watches[lits[1]].append((lits[0], clause))
        else:
            self._watches[lits[0]].append((lits[1], clause))
            self._watches[lits[1]].append((lits[0], clause))

    def _backtrack(self, target_level: int) -> None:
        curr_level = self._trail.decision_level
        if target_level >= curr_level:
            return
        if self._propagator is not None:
            self._propagator.pop(curr_level - target_level)
        unassigned = self._trail.backtrack(target_level)
        for var in unassigned:
            self._heap.insert(var)
        self._qhead = len(self._trail.stack)
        if self._theory_qhead > self._qhead:
            self._theory_qhead = self._qhead

    def _next_assumption(self, assumptions: list[Lit]) -> Lit | None:
        for lit in assumptions:
            val = self._trail.eval_lit(lit)
            if val != L_TRUE:
                return lit
        return None

    def _pick_branch_lit(self) -> Lit:
        while not self._heap.empty():
            var = self._heap.pop_max()
            if self._trail.assignment[var] == L_UNDEF:
                if self._trail.phase[var] == L_FALSE:
                    return neg_lit(var)
                return pos_lit(var)
        msg = "No unassigned variable available for branching"
        raise RuntimeError(msg)

    def _handle_conflict(self, conflict: Clause) -> SolveResult | None:
        self._conflicts += 1
        self._stats["conflicts"] += 1

        max_level = max(
            (self._trail.level[lit >> 1] for lit in conflict.literals),
            default=0,
        )
        if self._trail.decision_level == 0 or max_level == 0:
            return SolveResult.UNSAT

        if max_level < self._trail.decision_level:
            self._backtrack(max_level)

        learned_lits, bt_level = self._analyze_conflict(conflict)
        self._backtrack(bt_level)

        if not learned_lits:
            return SolveResult.UNSAT

        if len(learned_lits) == 1:
            lbd = 1
            self._trail.assign(learned_lits[0], reason=None)
        else:
            lbd = self._compute_lbd(learned_lits)
            learned_clause = Clause(learned_lits, learned=True, lbd=lbd)
            self._learned.append(learned_clause)
            self._stats["learned_clauses"] += 1
            self._attach_clause(learned_clause)
            self._trail.assign(learned_lits[0], reason=learned_clause)

        self._conflicts_since_restart += 1
        self._global_lbd_sum += lbd
        old_lbd = self._lbd_queue[self._lbd_queue_pos]
        self._lbd_queue[self._lbd_queue_pos] = lbd
        self._lbd_queue_sum += lbd - old_lbd
        self._lbd_queue_pos = (self._lbd_queue_pos + 1) % self._lbd_queue_size

        if self._conflicts >= self._reduce_threshold:
            self._reduce_db()
            self._reduce_threshold += self._reduce_inc

        if (
            self._conflicts >= self._lbd_queue_size
            and self._conflicts_since_restart >= self._restart_cooldown
        ):
            short_avg = self._lbd_queue_sum / self._lbd_queue_size
            global_avg = self._global_lbd_sum / self._conflicts
            if short_avg > global_avg * self._restart_margin:
                self._backtrack(0)
                self._conflicts_since_restart = 0
                self._stats["restarts"] += 1

        return None

    def _propagate(self) -> Clause | None:
        while True:
            conflict = self._propagate_sat()
            if conflict is not None:
                return conflict

            if self._propagator is None:
                return None

            stack = self._trail.stack
            while self._theory_qhead < len(stack):
                self._propagator.on_assign(stack[self._theory_qhead])
                self._theory_qhead += 1

            prop_lits, conflict_lits = self._propagator.propagate()
            if conflict_lits is not None:
                self._stats["theory_conflicts"] += 1
                return self._make_theory_clause(conflict_lits)

            propagated_any = False
            lit_eval = self._trail.lit_eval
            for p_lit in prop_lits:
                val = lit_eval[p_lit]
                if val == L_UNDEF:
                    self._trail.assign(p_lit, reason=THEORY_REASON)
                    self._stats["theory_propagations"] += 1
                    propagated_any = True
                elif val == L_FALSE:
                    self._stats["theory_conflicts"] += 1
                    raw_reason = self._propagator.explain_propagation(p_lit)
                    return self._make_theory_clause(raw_reason, must_contain=p_lit)

            if not propagated_any:
                return None

    def _propagate_sat(self) -> Clause | None:
        lit_eval = self._trail.lit_eval
        watches = self._watches
        bin_watches = self._bin_watches
        stack = self._trail.stack

        while self._qhead < len(stack):
            self._stats["propagations"] += 1
            p = stack[self._qhead]
            self._qhead += 1
            false_lit = p ^ 1

            for implied_lit, clause in bin_watches[false_lit]:
                if clause.deleted:
                    continue
                val = lit_eval[implied_lit]
                if val == L_FALSE:
                    return clause
                if val == L_UNDEF:
                    self._trail.assign(implied_lit, reason=clause)

            watchers = watches[false_lit]
            i = 0
            j = 0
            n_watchers = len(watchers)
            while i < n_watchers:
                blocker, clause = watchers[i]
                i += 1

                if clause.deleted:
                    continue

                if lit_eval[blocker] == L_TRUE:
                    watchers[j] = (blocker, clause)
                    j += 1
                    continue

                lits = clause.literals
                if lits[0] == false_lit:
                    lits[0], lits[1] = lits[1], lits[0]

                first_watch = lits[0]
                if lit_eval[first_watch] == L_TRUE:
                    watchers[j] = (first_watch, clause)
                    j += 1
                    continue

                found_new_watch = False
                for k in range(2, len(lits)):
                    lit_k = lits[k]
                    if lit_eval[lit_k] != L_FALSE:
                        lits[1], lits[k] = lits[k], lits[1]
                        watches[lits[1]].append((first_watch, clause))
                        found_new_watch = True
                        break

                if found_new_watch:
                    continue

                watchers[j] = (first_watch, clause)
                j += 1

                if lit_eval[first_watch] == L_FALSE:
                    while i < n_watchers:
                        watchers[j] = watchers[i]
                        i += 1
                        j += 1
                    del watchers[j:]
                    return clause

                self._trail.assign(first_watch, reason=clause)

            del watchers[j:]

        return None

    def _make_theory_clause(
        self, raw_lits: Sequence[Lit], must_contain: Lit | None = None
    ) -> Clause:
        self._ensure_lits_vars(raw_lits)
        deduped = list(dict.fromkeys(raw_lits))
        if must_contain is not None:
            if must_contain not in deduped:
                msg = (
                    f"Theory explanation must contain propagated literal {must_contain}"
                )
                raise ValueError(msg)
            if deduped[0] != must_contain:
                idx = deduped.index(must_contain)
                deduped[0], deduped[idx] = deduped[idx], deduped[0]
        return Clause(deduped, learned=True)

    def _resolve_reason(self, assigned_lit: Lit) -> Clause | None:
        var = assigned_lit >> 1
        reason = self._trail.reason[var]
        if reason is None:
            return None
        if isinstance(reason, Clause):
            return reason
        if reason is THEORY_REASON:
            if self._propagator is None:
                msg = "THEORY_REASON recorded without a TheoryPropagator"
                raise RuntimeError(msg)
            raw = self._propagator.explain_propagation(assigned_lit)
            clause = self._make_theory_clause(raw, must_contain=assigned_lit)
            self._trail.reason[var] = clause
            return clause
        msg = f"Unexpected trail reason object: {reason!r}"
        raise RuntimeError(msg)

    def _analyze_conflict(self, conflict: Clause) -> tuple[list[Lit], int]:
        stack = self._trail.stack
        curr_level = self._trail.decision_level
        learned: list[Lit] = [-1]
        clear_seen: list[Var] = []
        path_c = 0
        trail_idx = len(stack) - 1
        clause: Clause | None = conflict
        p = -1

        try:
            while True:
                if clause is not None:
                    self._bump_clause_activity(clause)
                    skip_var = p >> 1 if p >= 0 else -1
                    for lit in clause.literals:
                        var = lit >> 1
                        if var == skip_var:
                            continue
                        lvl = self._trail.level[var]
                        if not self._seen[var] and lvl > 0:
                            self._seen[var] = True
                            clear_seen.append(var)
                            self._bump_var_activity(var)
                            if lvl >= curr_level:
                                path_c += 1
                            else:
                                learned.append(lit)

                while not self._seen[stack[trail_idx] >> 1]:
                    trail_idx -= 1

                p = stack[trail_idx]
                trail_idx -= 1
                path_c -= 1
                if path_c == 0:
                    break

                self._seen[p >> 1] = False
                clause = self._resolve_reason(p)

            learned[0] = p ^ 1
            learned = self._minimize_learned(learned, clear_seen)
        finally:
            for var in clear_seen:
                self._seen[var] = False

        if len(learned) == 1:
            bt_level = 0
        else:
            max_i = 1
            max_lvl = self._trail.level[learned[1] >> 1]
            for i in range(2, len(learned)):
                lvl = self._trail.level[learned[i] >> 1]
                if lvl > max_lvl:
                    max_lvl = lvl
                    max_i = i
            learned[1], learned[max_i] = learned[max_i], learned[1]
            bt_level = max_lvl

        self._decay_var_activity()
        self._decay_clause_activity()
        return learned, bt_level

    def _minimize_learned(self, learned: list[Lit], clear_seen: list[Var]) -> list[Lit]:
        if len(learned) <= 2:
            return learned

        abstract_levels = 0
        for lit in learned[1:]:
            abstract_levels |= 1 << (self._trail.level[lit >> 1] & 63)

        kept = [learned[0]]
        for lit in learned[1:]:
            var = lit >> 1
            if self._trail.reason[var] is None or not self._lit_redundant(
                lit, abstract_levels, clear_seen
            ):
                kept.append(lit)
        return kept

    def _lit_redundant(
        self, start_lit: Lit, abstract_levels: int, clear_seen: list[Var]
    ) -> bool:
        work = [start_lit]
        added: list[Var] = []
        while work:
            curr_lit = work.pop()
            curr_var = curr_lit >> 1
            reason = self._resolve_reason(curr_lit ^ 1)
            if reason is None:
                for var in added:
                    self._seen[var] = False
                return False

            for r_lit in reason.literals:
                r_var = r_lit >> 1
                if r_var == curr_var or self._seen[r_var]:
                    continue
                r_lvl = self._trail.level[r_var]
                if r_lvl == 0:
                    continue
                if self._trail.reason[r_var] is None or not (
                    abstract_levels & (1 << (r_lvl & 63))
                ):
                    for var in added:
                        self._seen[var] = False
                    return False
                self._seen[r_var] = True
                added.append(r_var)
                work.append(r_lit)

        clear_seen.extend(added)
        return True

    def _analyze_final(self, conflict_lit: Lit, assumption_set: set[Lit]) -> list[Lit]:
        core = [conflict_lit]
        if self._trail.level[conflict_lit >> 1] == 0:
            return core

        seen = [False] * self._trail.num_vars
        seen[conflict_lit >> 1] = True

        for lit in reversed(self._trail.stack):
            var = lit >> 1
            if self._trail.level[var] == 0:
                break
            if not seen[var]:
                continue
            reason = self._resolve_reason(lit)
            if reason is None:
                if lit in assumption_set:
                    core.append(lit)
            else:
                for r_lit in reason.literals:
                    r_var = r_lit >> 1
                    if r_var != var and self._trail.level[r_var] > 0:
                        seen[r_var] = True

        return list(dict.fromkeys(core))

    def _add_theory_lemma(self, raw_lits: Sequence[Lit]) -> tuple[Clause | None, bool]:
        self._ensure_lits_vars(raw_lits)
        deduped: list[Lit] = []
        seen_lits: set[Lit] = set()
        for lit in raw_lits:
            if (lit ^ 1) in seen_lits:
                return None, False  # Tautological lemma.
            if lit not in seen_lits:
                seen_lits.add(lit)
                deduped.append(lit)

        if not deduped:
            return Clause([], learned=True), True

        if len(deduped) == 1:
            lit = deduped[0]
            val = self._trail.eval_lit(lit)
            if val == L_FALSE:
                return Clause([lit], learned=True), True
            if val == L_UNDEF or self._trail.level[lit >> 1] > 0:
                self._backtrack(0)
                if self._trail.eval_lit(lit) == L_FALSE:
                    return Clause([lit], learned=True), True
                if self._trail.eval_lit(lit) == L_UNDEF:
                    self._trail.assign(lit, reason=None)
                return None, True
            return None, False

        # Place the two best watched literals at indices 0 and 1.
        def watch_rank(idx: int) -> tuple[int, int]:
            lit = deduped[idx]
            val = self._trail.eval_lit(lit)
            lvl = self._trail.level[lit >> 1] if val == L_FALSE else 0
            return (val, lvl)

        best1 = 0 if watch_rank(0) >= watch_rank(1) else 1
        best2 = 1 - best1
        rank1 = watch_rank(best1)
        rank2 = watch_rank(best2)
        for k in range(2, len(deduped)):
            rk = watch_rank(k)
            if rk > rank1:
                best2, rank2 = best1, rank1
                best1, rank1 = k, rk
            elif rk > rank2:
                best2, rank2 = k, rk

        deduped[0], deduped[best1] = deduped[best1], deduped[0]
        if best2 == 0:
            best2 = best1
        deduped[1], deduped[best2] = deduped[best2], deduped[1]

        lbd = self._compute_lbd(deduped)
        clause = Clause(deduped, learned=True, lbd=lbd)
        self._learned.append(clause)
        self._stats["learned_clauses"] += 1
        self._attach_clause(clause)

        v0 = self._trail.eval_lit(deduped[0])
        v1 = self._trail.eval_lit(deduped[1])
        if v0 == L_FALSE:
            return clause, True
        if v0 == L_UNDEF and v1 == L_FALSE:
            target_lvl = self._trail.level[deduped[1] >> 1]
            if target_lvl < self._trail.decision_level:
                self._backtrack(target_lvl)
            self._trail.assign(deduped[0], reason=clause)
            return None, True
        return None, v0 == L_UNDEF

    def _compute_lbd(self, lits: Sequence[Lit]) -> int:
        lbd = 0
        for lit in lits:
            lvl = self._trail.level[lit >> 1]
            if lvl > 0 and not self._seen_level[lvl]:
                self._seen_level[lvl] = True
                lbd += 1
        for lit in lits:
            lvl = self._trail.level[lit >> 1]
            if lvl > 0:
                self._seen_level[lvl] = False
        return lbd

    def _bump_var_activity(self, var: Var) -> None:
        self._activities[var] += self._var_inc
        self._heap.increase(var)
        if self._activities[var] > 1e100:
            for i in range(len(self._activities)):
                self._activities[i] *= 1e-100
            self._var_inc *= 1e-100
            self._heap.rebuild()

    def _decay_var_activity(self) -> None:
        self._var_inc /= self._var_decay

    def _bump_clause_activity(self, clause: Clause) -> None:
        if not clause.learned:
            return
        clause.activity += self._clause_inc
        if clause.activity > 1e20:
            for learned in self._learned:
                learned.activity *= 1e-20
            self._clause_inc *= 1e-20

    def _decay_clause_activity(self) -> None:
        self._clause_inc /= self._clause_decay

    def _reduce_db(self) -> None:
        locked_ids = {
            id(reason) for reason in self._trail.reason if isinstance(reason, Clause)
        }
        self._learned.sort(key=lambda c: (c.lbd, -c.activity))

        half = len(self._learned) // 2
        deleted_any = False
        for clause in self._learned[half:]:
            if clause.lbd <= 2 or id(clause) in locked_ids:
                continue
            clause.deleted = True
            deleted_any = True
            self._stats["deleted_clauses"] += 1

        if not deleted_any:
            return

        self._learned = [c for c in self._learned if not c.deleted]
        for watch_list in self._watches:
            if any(clause.deleted for _, clause in watch_list):
                watch_list[:] = [entry for entry in watch_list if not entry[1].deleted]
        for bin_list in self._bin_watches:
            if any(clause.deleted for _, clause in bin_list):
                bin_list[:] = [entry for entry in bin_list if not entry[1].deleted]
