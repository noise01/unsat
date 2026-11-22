"""Pattern extraction and congruence-aware E-matching over the EUF E-graph.

Depends on: ``syntax``, ``theories``, ``quantifiers.base``.
"""

from collections.abc import Iterator, Sequence
from dataclasses import dataclass

from unsat.quantifiers.base import QuantifierBudget, QuantifierStats
from unsat.syntax import (
    App,
    BoundVar,
    Const,
    DeclKind,
    Expr,
    Quantifier,
    free_bound_var_indices,
    instantiate_quantifier,
)
from unsat.theories import EUFSolver

_TRIGGER_DECL_KINDS = frozenset(
    {
        DeclKind.UNINTERPRETED,
        DeclKind.SELECT,
        DeclKind.STORE,
    }
)


@dataclass(frozen=True, slots=True)
class EMatchResult:
    """Result of one E-matching round across active universal quantifiers."""

    instantiations: tuple[tuple[Quantifier, tuple[Expr, ...], Expr], ...]
    truncated: bool = False


def _collect_trigger_candidates(
    quantifier: Quantifier,
) -> list[tuple[App, frozenset[int], int]]:
    """Collect quantifier-body ``App`` triggers referencing ``0..k-1``."""
    k = quantifier.num_vars
    target_vars = set(range(k))
    body = quantifier.body

    size_memo: dict[Expr, int] = {}
    post: list[Expr] = []
    seen: set[Expr] = set()
    stack: list[tuple[Expr, bool]] = [(body, False)]
    while stack:
        node, expanded = stack.pop()
        if node in seen:
            continue
        if isinstance(node, Quantifier):
            # Do not cross nested quantifier scopes when collecting triggers.
            seen.add(node)
            size_memo[node] = 1
            continue
        if expanded:
            seen.add(node)
            size_memo[node] = 1 + sum(size_memo.get(ch, 1) for ch in node.children)
            post.append(node)
            continue
        stack.append((node, True))
        for ch in reversed(node.children):
            if ch not in seen:
                stack.append((ch, False))

    candidates: list[tuple[App, frozenset[int], int]] = []
    for node in post:
        if (
            isinstance(node, App)
            and node.decl.kind in _TRIGGER_DECL_KINDS
            and node.args
        ):
            free = free_bound_var_indices(node)
            cov = frozenset(idx for idx in free if idx in target_vars)
            if cov:
                candidates.append((node, cov, size_memo[node]))
    return candidates


def extract_patterns(quantifier: Quantifier) -> tuple[tuple[Expr, ...], ...]:
    """Return explicit patterns on ``quantifier`` or synthesize default triggers."""
    if quantifier.patterns:
        return quantifier.patterns

    k = quantifier.num_vars
    target = frozenset(range(k))
    candidates = _collect_trigger_candidates(quantifier)
    if not candidates:
        return ()

    # Prefer smaller single-term triggers covering all quantified variables.
    singles = [(term, cov, sz) for term, cov, sz in candidates if cov == target]
    singles.sort(
        key=lambda item: (
            0 if item[0].decl.is_uninterpreted else 1,
            item[2],
            item[0].id,
        )
    )
    if singles:
        chosen: list[tuple[Expr, ...]] = []
        seen_terms: set[Expr] = set()
        for term, _, _ in singles:
            if term in seen_terms:
                continue
            seen_terms.add(term)
            chosen.append((term,))
            if len(chosen) >= 4:
                break
        return tuple(chosen)

    # Greedily build multi-patterns when no single term covers every variable.
    ordered = sorted(
        candidates,
        key=lambda item: (
            -len(item[1]),
            0 if item[0].decl.is_uninterpreted else 1,
            item[2],
            item[0].id,
        ),
    )
    all_covered: frozenset[int] = frozenset().union(*(cov for _, cov, _ in ordered))
    if all_covered != target:
        return ()

    multi_pats: list[tuple[Expr, ...]] = []
    used_starts: set[Expr] = set()
    for start_term, start_cov, _ in ordered:
        if start_term in used_starts:
            continue
        pat: list[Expr] = [start_term]
        cov = set(start_cov)
        while cov != target:
            best_next: tuple[App, frozenset[int], int] | None = None
            best_gain = 0
            for cand_term, cand_cov, cand_sz in ordered:
                if cand_term in pat:
                    continue
                gain = len(cand_cov - cov)
                if gain > best_gain:
                    best_gain = gain
                    best_next = (cand_term, cand_cov, cand_sz)
            if best_next is None:
                break
            pat.append(best_next[0])
            cov.update(best_next[1])
        if cov == target:
            used_starts.add(start_term)
            multi_pats.append(tuple(pat))
            if len(multi_pats) >= 4:
                break
    return tuple(multi_pats)


class EMatcher:
    """Modulo-EUF pattern matcher with generation bounds and deduplication."""

    def __init__(self) -> None:
        self._patterns: dict[Quantifier, tuple[tuple[Expr, ...], ...]] = {}
        self._emitted: set[tuple[Quantifier, tuple[Expr, ...]]] = set()
        self._term_gen: dict[Expr, int] = {}

    @property
    def emitted(self) -> frozenset[tuple[Quantifier, tuple[Expr, ...]]]:
        """All ``(quantifier, rep_args)`` instantiations already emitted."""
        return frozenset(self._emitted)

    def get_patterns(self, quantifier: Quantifier) -> tuple[tuple[Expr, ...], ...]:
        """Return matcher-owned pattern list for ``quantifier`` without mutation."""
        cached = self._patterns.get(quantifier)
        if cached is not None:
            return cached
        extracted = extract_patterns(quantifier)
        self._patterns[quantifier] = extracted
        return extracted

    def record_emitted(
        self, quantifier: Quantifier, euf: EUFSolver, args: tuple[Expr, ...]
    ) -> None:
        """Record an instantiation (e.g. from MBQI) to prevent re-emission."""
        key = (quantifier, tuple(euf.rep_expr(arg) for arg in args))
        self._emitted.add(key)

    def clear_emitted(self) -> None:
        """Clear scope-sensitive E-class deduplication keys (e.g. after ``pop``)."""
        self._emitted.clear()

    def _preferred_member(self, euf: EUFSolver, term: Expr) -> Expr:
        rep = euf.rep_expr(term)
        members = euf.eclass_members(rep)
        if not members:
            return term
        return min(
            members,
            key=lambda m: (
                self._term_gen.get(m, 0),
                0
                if isinstance(m, Const)
                else 1
                if (isinstance(m, App) and not m.args)
                else 2,
                m.id,
            ),
        )

    def _match_subterm(
        self,
        euf: EUFSolver,
        pat: Expr,
        target: Expr,
        env: tuple[Expr | None, ...],
        k: int,
    ) -> Iterator[tuple[tuple[Expr | None, ...], tuple[Expr, ...]]]:
        if isinstance(pat, BoundVar):
            if pat.index >= k:
                return
            pos = k - 1 - pat.index
            bound = env[pos]
            if bound is None:
                nxt = list(env)
                nxt[pos] = self._preferred_member(euf, target)
                yield tuple(nxt), ()
            elif euf.are_equal(bound, target):
                yield env, ()
            return

        if isinstance(pat, Const):
            if euf.are_equal(pat, target):
                yield env, ()
            return

        if isinstance(pat, App):
            if not pat.args:
                if euf.are_equal(pat, target):
                    yield env, ()
                return
            for member in euf.eclass_members(target):
                if (
                    isinstance(member, App)
                    and member.decl is pat.decl
                    and len(member.args) == len(pat.args)
                ):
                    for out_env, sub_matched in self._match_args(
                        euf, pat.args, member.args, env, k
                    ):
                        yield out_env, (member, *sub_matched)

    def _match_args(
        self,
        euf: EUFSolver,
        pat_args: tuple[Expr, ...],
        term_args: tuple[Expr, ...],
        env: tuple[Expr | None, ...],
        k: int,
    ) -> Iterator[tuple[tuple[Expr | None, ...], tuple[Expr, ...]]]:
        if not pat_args:
            yield env, ()
            return
        for env1, matched1 in self._match_subterm(
            euf, pat_args[0], term_args[0], env, k
        ):
            for env2, matched2 in self._match_args(
                euf, pat_args[1:], term_args[1:], env1, k
            ):
                yield env2, (*matched1, *matched2)

    def _match_pattern_tuple(
        self,
        euf: EUFSolver,
        pat_terms: tuple[Expr, ...],
        env: tuple[Expr | None, ...],
        k: int,
    ) -> Iterator[tuple[tuple[Expr, ...], tuple[Expr, ...]]]:
        if not pat_terms:
            if all(item is not None for item in env):
                yield tuple(item for item in env if item is not None), ()
            return
        head_pat = pat_terms[0]
        if not isinstance(head_pat, App) or not head_pat.args:
            return
        for cand in euf.apps_by_decl(head_pat.decl):
            if cand.sort is not head_pat.sort or len(cand.args) != len(head_pat.args):
                continue
            for env1, matched1 in self._match_args(
                euf, head_pat.args, cand.args, env, k
            ):
                for full_env, matched_rest in self._match_pattern_tuple(
                    euf, pat_terms[1:], env1, k
                ):
                    yield full_env, (cand, *matched1, *matched_rest)

    def match_round(
        self,
        euf: EUFSolver,
        quantifiers: Sequence[Quantifier],
        budget: QuantifierBudget,
        stats: QuantifierStats,
    ) -> EMatchResult:
        """Run one bounded E-matching round across ``quantifiers``."""
        if not quantifiers:
            return EMatchResult((), False)

        # Ensure all existing E-graph members are seeded at generation 0.
        for rep in euf.eclasses():
            for member in euf.eclass_members(rep):
                self._term_gen.setdefault(member, 0)

        results: list[tuple[Quantifier, tuple[Expr, ...], Expr]] = []
        truncated = False
        stats.ematch_rounds += 1

        for q in quantifiers:
            if len(results) >= budget.max_instantiations:
                truncated = True
                break
            pats = self.get_patterns(q)
            if not pats:
                continue
            k = q.num_vars
            init_env: tuple[Expr | None, ...] = (None,) * k
            q_matches = 0
            for pat_tuple in pats:
                if (
                    q_matches >= budget.max_matches
                    or len(results) >= budget.max_instantiations
                ):
                    truncated = True
                    break
                for args, matched_apps in self._match_pattern_tuple(
                    euf, pat_tuple, init_env, k
                ):
                    if (
                        q_matches >= budget.max_matches
                        or len(results) >= budget.max_instantiations
                    ):
                        truncated = True
                        break
                    rep_key = (q, tuple(euf.rep_expr(arg) for arg in args))
                    if rep_key in self._emitted:
                        continue
                    match_gen = max(
                        (
                            *(self._term_gen.get(arg, 0) for arg in args),
                            *(self._term_gen.get(app, 0) for app in matched_apps),
                        ),
                        default=0,
                    )
                    if match_gen >= budget.max_ematch_depth:
                        truncated = True
                        continue

                    self._emitted.add(rep_key)
                    inst_expr = instantiate_quantifier(q, args)
                    nxt_gen = match_gen + 1
                    stack: list[Expr] = [inst_expr]
                    visited: set[Expr] = set()
                    while stack:
                        sub = stack.pop()
                        if sub in visited:
                            continue
                        visited.add(sub)
                        if isinstance(sub, App) and sub.args:
                            self._term_gen.setdefault(sub, nxt_gen)
                        stack.extend(sub.children)

                    results.append((q, args, inst_expr))
                    q_matches += 1
                    stats.ematch_instantiations += 1

        if truncated:
            stats.budget_exhausted += 1
        return EMatchResult(tuple(results), truncated=truncated)
