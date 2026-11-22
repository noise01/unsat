"""Gaussian elimination and bound-propagation tactics for SMT formulas."""

import math
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction

from unsat.model import IdentityModelConverter, SubstitutionModelConverter
from unsat.syntax import (
    App,
    Const,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Sort,
    has_bound_vars,
    has_quantifiers,
    iter_subexprs,
    substitute,
)
from unsat.tactics.base import TacticResult
from unsat.tactics.simplify import simplify


def _split_conjuncts(formulas: Sequence[Expr]) -> list[Expr]:
    out: list[Expr] = []
    stack: list[Expr] = [simplify(f) for f in reversed(formulas)]
    while stack:
        item = stack.pop()
        if isinstance(item, App) and item.decl.kind is DeclKind.AND:
            stack.extend(reversed(item.args))
        else:
            out.append(item)
    return out


def _linearize_ground(expr: Expr) -> tuple[dict[App, Fraction], Fraction] | None:
    """Extract ``(coeffs, const)`` for pure linear combinations of 0-arity vars."""
    if has_quantifiers(expr) or has_bound_vars(expr):
        return None
    memo: dict[Expr, tuple[dict[App, Fraction], Fraction]] = {}
    for node in iter_subexprs(expr):
        if isinstance(node, Const):
            if node.is_int:
                assert isinstance(node.value, int)
                assert not isinstance(node.value, bool)
                memo[node] = ({}, Fraction(node.value))
            elif node.is_real:
                assert isinstance(node.value, Fraction)
                memo[node] = ({}, node.value)
            else:
                return None
            continue
        if not isinstance(node, App):
            return None
        if node.is_const_symbol:
            if not node.is_arith:
                return None
            memo[node] = ({node: Fraction(1)}, Fraction(0))
            continue
        kind = node.decl.kind
        if kind is DeclKind.NEG:
            cm, k = memo[node.args[0]]
            memo[node] = ({v: -c for v, c in cm.items()}, -k)
        elif kind is DeclKind.ADD:
            acc: dict[App, Fraction] = {}
            acc_k = Fraction(0)
            for arg in node.args:
                cm, k = memo[arg]
                acc_k += k
                for v, c in cm.items():
                    nxt = acc.get(v, Fraction(0)) + c
                    if nxt == 0:
                        acc.pop(v, None)
                    else:
                        acc[v] = nxt
            memo[node] = (acc, acc_k)
        elif kind is DeclKind.SUB:
            lm, lk = memo[node.args[0]]
            rm, rk = memo[node.args[1]]
            sub_m = dict(lm)
            for v, c in rm.items():
                nxt = sub_m.get(v, Fraction(0)) - c
                if nxt == 0:
                    sub_m.pop(v, None)
                else:
                    sub_m[v] = nxt
            memo[node] = (sub_m, lk - rk)
        elif kind is DeclKind.MUL:
            const_f = Fraction(1)
            var_part: tuple[dict[App, Fraction], Fraction] | None = None
            for arg in node.args:
                cm, k = memo[arg]
                if not cm:
                    const_f *= k
                elif var_part is None:
                    var_part = (cm, k)
                else:
                    return None
            if const_f == 0 or var_part is None:
                memo[node] = ({}, const_f if var_part is None else Fraction(0))
            else:
                vm, vk = var_part
                memo[node] = (
                    {v: c * const_f for v, c in vm.items()},
                    vk * const_f,
                )
        elif kind is DeclKind.DIV:
            lm, lk = memo[node.args[0]]
            rm, rk = memo[node.args[1]]
            if rm or rk == 0:
                return None
            memo[node] = ({v: c / rk for v, c in lm.items()}, lk / rk)
        else:
            return None
    return memo[expr]


def _build_linear_rhs(
    ctx: Context,
    sort: Sort,
    coeffs: dict[App, Fraction],
    piv_var: App,
    piv_coeff: Fraction,
    const_val: Fraction,
) -> Expr:
    terms: list[Expr] = []
    for var, coef in sorted(coeffs.items(), key=lambda kv: kv[0].id):
        if var is piv_var:
            continue
        ratio = -coef / piv_coeff
        if sort.is_int:
            assert ratio.denominator == 1
            if ratio == 1:
                terms.append(var)
            elif ratio == -1:
                terms.append(ctx.mk_neg(var))
            else:
                terms.append(ctx.mk_mul(ctx.mk_int_val(ratio.numerator), var))
        else:
            if ratio == 1:
                terms.append(var)
            elif ratio == -1:
                terms.append(ctx.mk_neg(var))
            else:
                terms.append(ctx.mk_mul(ctx.mk_real_val(ratio), var))

    k_term = -const_val / piv_coeff
    if k_term != 0 or not terms:
        if sort.is_int:
            assert k_term.denominator == 1
            terms.append(ctx.mk_int_val(k_term.numerator))
        else:
            terms.append(ctx.mk_real_val(k_term))
    return terms[0] if len(terms) == 1 else ctx.mk_add(*terms)


def _solve_defining_eq(
    ctx: Context, conjunct: Expr
) -> tuple[str, App | None, Expr | None]:
    """Classify a conjunct as conflict, trivial, or substitution ``(var, rhs)``."""
    if conjunct is ctx.false_expr:
        return ("conflict", None, None)
    if conjunct is ctx.true_expr:
        return ("trivial", None, None)

    if isinstance(conjunct, App):
        if conjunct.is_const_symbol:
            return ("subst", conjunct, ctx.true_expr)
        if conjunct.decl.kind is DeclKind.NOT and isinstance(conjunct.args[0], App):
            inner = conjunct.args[0]
            if inner.is_const_symbol:
                return ("subst", inner, ctx.false_expr)
        if conjunct.decl.kind is DeclKind.EQ:
            lhs, rhs = conjunct.args
            if lhs is rhs:
                return ("trivial", None, None)
            if lhs.is_arith:
                l_lin = _linearize_ground(lhs)
                r_lin = _linearize_ground(rhs)
                if l_lin is not None and r_lin is not None:
                    diff_m = dict(l_lin[0])
                    for v, c in r_lin[0].items():
                        nxt = diff_m.get(v, Fraction(0)) - c
                        if nxt == 0:
                            diff_m.pop(v, None)
                        else:
                            diff_m[v] = nxt
                    diff_k = l_lin[1] - r_lin[1]
                    if not diff_m:
                        return ("trivial" if diff_k == 0 else "conflict", None, None)
                    if lhs.is_int:
                        g = math.gcd(*(abs(c.numerator) for c in diff_m.values()))
                        assert diff_k.denominator == 1
                        if diff_k.numerator % g != 0:
                            return ("conflict", None, None)
                        piv = next(
                            (
                                v
                                for v in sorted(diff_m, key=lambda t: t.id)
                                if abs(diff_m[v]) == 1
                            ),
                            None,
                        )
                        if piv is not None:
                            sol = _build_linear_rhs(
                                ctx, lhs.sort, diff_m, piv, diff_m[piv], diff_k
                            )
                            return ("subst", piv, sol)
                    else:
                        piv = min(diff_m, key=lambda t: t.id)
                        sol = _build_linear_rhs(
                            ctx, lhs.sort, diff_m, piv, diff_m[piv], diff_k
                        )
                        return ("subst", piv, sol)

            # Non-linear or non-arithmetic syntactic defining equality
            if (
                isinstance(lhs, App)
                and lhs.is_const_symbol
                and not has_quantifiers(rhs)
                and not has_bound_vars(rhs)
                and lhs not in set(iter_subexprs(rhs))
            ):
                return ("subst", lhs, rhs)
            if (
                isinstance(rhs, App)
                and rhs.is_const_symbol
                and not has_quantifiers(lhs)
                and not has_bound_vars(lhs)
                and rhs not in set(iter_subexprs(lhs))
            ):
                return ("subst", rhs, lhs)

    return ("keep", None, None)


def gaussian_elim(formulas: Sequence[Expr]) -> TacticResult:
    """Eliminate unit Bool, linear arithmetic, and explicit equalities."""
    if not formulas:
        return TacticResult((), IdentityModelConverter())
    ctx = formulas[0].ctx
    work = _split_conjuncts(formulas)
    eliminated: list[tuple[FuncDecl, Expr]] = []

    changed = True
    while changed:
        changed = False
        next_work: list[Expr] = []
        chosen: tuple[int, App, Expr] | None = None
        for item in work:
            s_item = simplify(item)
            status, var_app, rhs_expr = _solve_defining_eq(ctx, s_item)
            if status == "conflict":
                return TacticResult((ctx.false_expr,), IdentityModelConverter())
            if status == "trivial":
                changed = True
                continue
            if chosen is None and status == "subst":
                assert var_app is not None
                assert rhs_expr is not None
                chosen = (len(next_work), var_app, rhs_expr)
            next_work.append(s_item)

        if chosen is not None:
            idx, var_app, rhs_expr = chosen
            eliminated.append((var_app.decl, rhs_expr))
            mapping: dict[Expr, Expr] = {var_app: rhs_expr}
            rebuilt: list[Expr] = []
            for j, item in enumerate(next_work):
                if j == idx:
                    continue
                sub = simplify(substitute(item, mapping))
                if sub is ctx.false_expr:
                    return TacticResult((ctx.false_expr,), IdentityModelConverter())
                if sub is not ctx.true_expr:
                    rebuilt.append(sub)
            work = _split_conjuncts(rebuilt)
            changed = True
        else:
            work = next_work

    deduped = tuple(dict.fromkeys(work))
    converter = (
        SubstitutionModelConverter(dict(reversed(eliminated)))
        if eliminated
        else IdentityModelConverter()
    )
    return TacticResult(deduped, converter)


class GaussianElimTactic:
    """Performs variable elimination via defining equalities & linear equations."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Eliminate solved variables and return remaining goal + model converter."""
        return gaussian_elim(formulas)


@dataclass(slots=True)
class _Interval:
    lower: Fraction | None = None
    lower_strict: bool = False
    upper: Fraction | None = None
    upper_strict: bool = False

    def tighten_lower(self, val: Fraction, strict: bool, *, is_int: bool) -> bool:
        if is_int:
            if strict:
                bound = Fraction(math.floor(val) + 1)
            else:
                bound = Fraction(math.ceil(val))
            eff_strict = False
        else:
            bound = val
            eff_strict = strict

        if self.lower is None or bound > self.lower:
            self.lower = bound
            self.lower_strict = eff_strict
        elif bound == self.lower and eff_strict:
            self.lower_strict = True
        return self.is_consistent()

    def tighten_upper(self, val: Fraction, strict: bool, *, is_int: bool) -> bool:
        if is_int:
            if strict:
                bound = Fraction(math.ceil(val) - 1)
            else:
                bound = Fraction(math.floor(val))
            eff_strict = False
        else:
            bound = val
            eff_strict = strict

        if self.upper is None or bound < self.upper:
            self.upper = bound
            self.upper_strict = eff_strict
        elif bound == self.upper and eff_strict:
            self.upper_strict = True
        return self.is_consistent()

    def is_consistent(self) -> bool:
        if self.lower is None or self.upper is None:
            return True
        if self.lower > self.upper:
            return False
        return not (
            self.lower == self.upper and (self.lower_strict or self.upper_strict)
        )

    def pinned_value(self) -> Fraction | None:
        if (
            self.lower is not None
            and self.lower == self.upper
            and not self.lower_strict
            and not self.upper_strict
        ):
            return self.lower
        return None


_FLIPPED_CMP = {
    DeclKind.LT: DeclKind.GT,
    DeclKind.LE: DeclKind.GE,
    DeclKind.GT: DeclKind.LT,
    DeclKind.GE: DeclKind.LE,
}


def _extract_cmp_linear(
    conjunct: Expr,
) -> tuple[DeclKind, dict[App, Fraction], Fraction] | None:
    if not isinstance(conjunct, App):
        return None
    kind = conjunct.decl.kind
    if kind in (DeclKind.LT, DeclKind.LE, DeclKind.GT, DeclKind.GE, DeclKind.EQ):
        lhs, rhs = conjunct.args
        if not lhs.is_arith:
            return None
        l_lin = _linearize_ground(lhs)
        r_lin = _linearize_ground(rhs)
        if l_lin is None or r_lin is None:
            return None
        diff_m = dict(l_lin[0])
        for v, c in r_lin[0].items():
            nxt = diff_m.get(v, Fraction(0)) - c
            if nxt == 0:
                diff_m.pop(v, None)
            else:
                diff_m[v] = nxt
        return (kind, diff_m, l_lin[1] - r_lin[1])
    if kind is DeclKind.NOT and isinstance(conjunct.args[0], App):
        inner = conjunct.args[0]
        if inner.decl.kind in (DeclKind.LT, DeclKind.LE, DeclKind.GT, DeclKind.GE):
            neg_map = {
                DeclKind.LT: DeclKind.GE,
                DeclKind.LE: DeclKind.GT,
                DeclKind.GT: DeclKind.LE,
                DeclKind.GE: DeclKind.LT,
            }
            extracted = _extract_cmp_linear(inner)
            if extracted is not None:
                return (neg_map[extracted[0]], extracted[1], extracted[2])
    return None


def _apply_cmp_bound(
    bounds: dict[App, _Interval],
    kind: DeclKind,
    coeffs: dict[App, Fraction],
    const_k: Fraction,
) -> bool:
    if len(coeffs) != 1:
        return True
    var, coef = next(iter(coeffs.items()))
    target = -const_k / coef
    eff_kind = kind if coef > 0 or kind is DeclKind.EQ else _FLIPPED_CMP[kind]
    iv = bounds.setdefault(var, _Interval())
    is_int = var.is_int
    if eff_kind is DeclKind.EQ:
        return iv.tighten_lower(target, False, is_int=is_int) and iv.tighten_upper(
            target, False, is_int=is_int
        )
    if eff_kind is DeclKind.LE:
        return iv.tighten_upper(target, False, is_int=is_int)
    if eff_kind is DeclKind.LT:
        return iv.tighten_upper(target, True, is_int=is_int)
    if eff_kind is DeclKind.GE:
        return iv.tighten_lower(target, False, is_int=is_int)
    return iv.tighten_lower(target, True, is_int=is_int)


def _eval_cmp_under_bounds(
    bounds: dict[App, _Interval],
    kind: DeclKind,
    coeffs: dict[App, Fraction],
    const_k: Fraction,
) -> bool | None:
    if kind is DeclKind.EQ:
        return None
    min_sum: Fraction | None = const_k
    min_strict = False
    max_sum: Fraction | None = const_k
    max_strict = False
    for var, coef in coeffs.items():
        iv = bounds.get(var)
        if iv is None:
            return None
        if coef > 0:
            if iv.lower is None or min_sum is None:
                min_sum = None
            else:
                min_sum += coef * iv.lower
                min_strict = min_strict or iv.lower_strict
            if iv.upper is None or max_sum is None:
                max_sum = None
            else:
                max_sum += coef * iv.upper
                max_strict = max_strict or iv.upper_strict
        else:
            if iv.upper is None or min_sum is None:
                min_sum = None
            else:
                min_sum += coef * iv.upper
                min_strict = min_strict or iv.upper_strict
            if iv.lower is None or max_sum is None:
                max_sum = None
            else:
                max_sum += coef * iv.lower
                max_strict = max_strict or iv.lower_strict

    if kind is DeclKind.LE:
        if max_sum is not None and (max_sum < 0 or (max_sum == 0)):
            return True
        if min_sum is not None and (min_sum > 0 or (min_sum == 0 and min_strict)):
            return False
    elif kind is DeclKind.LT:
        if max_sum is not None and (max_sum < 0 or (max_sum == 0 and max_strict)):
            return True
        if min_sum is not None and min_sum >= 0:
            return False
    elif kind is DeclKind.GE:
        if min_sum is not None and min_sum >= 0:
            return True
        if max_sum is not None and (max_sum < 0 or (max_sum == 0 and max_strict)):
            return False
    elif kind is DeclKind.GT:
        if min_sum is not None and (min_sum > 0 or (min_sum == 0 and min_strict)):
            return True
        if max_sum is not None and max_sum <= 0:
            return False
    return None


def propagate_bounds(formulas: Sequence[Expr]) -> TacticResult:
    """Tighten arithmetic bounds, substitute pinned vars, and fold implied cmps."""
    if not formulas:
        return TacticResult((), IdentityModelConverter())
    ctx = formulas[0].ctx
    work = _split_conjuncts(formulas)
    eliminated: list[tuple[FuncDecl, Expr]] = []

    while True:
        bounds: dict[App, _Interval] = {}
        parsed = [_extract_cmp_linear(item) for item in work]
        for idx, info in enumerate(parsed):
            if work[idx] is ctx.false_expr:
                return TacticResult((ctx.false_expr,), IdentityModelConverter())
            if info is not None and not _apply_cmp_bound(
                bounds, info[0], info[1], info[2]
            ):
                return TacticResult((ctx.false_expr,), IdentityModelConverter())

        pinned: dict[Expr, Expr] = {}
        for var, iv in sorted(bounds.items(), key=lambda kv: kv[0].id):
            pval = iv.pinned_value()
            if pval is not None:
                c_expr = (
                    ctx.mk_int_val(pval.numerator)
                    if var.is_int
                    else ctx.mk_real_val(pval)
                )
                pinned[var] = c_expr
                eliminated.append((var.decl, c_expr))

        if pinned:
            subbed: list[Expr] = []
            for item in work:
                rew = simplify(substitute(item, pinned))
                if rew is ctx.false_expr:
                    return TacticResult((ctx.false_expr,), IdentityModelConverter())
                if rew is not ctx.true_expr:
                    subbed.append(rew)
            work = _split_conjuncts(subbed)
            continue

        # Fold comparisons implied or refuted solely by remaining OTHER conjuncts.
        work = list(dict.fromkeys(work))
        parsed = [_extract_cmp_linear(item) for item in work]
        kept_flags = [True] * len(work)
        pruned_any = False
        next_work: list[Expr] = []
        for idx, item in enumerate(work):
            if item is ctx.true_expr:
                kept_flags[idx] = False
                pruned_any = True
                continue
            info = parsed[idx]
            if info is not None and len(info[1]) >= 1:
                other_bounds: dict[App, _Interval] = {}
                for j, other_info in enumerate(parsed):
                    if j != idx and kept_flags[j] and other_info is not None:
                        _apply_cmp_bound(
                            other_bounds, other_info[0], other_info[1], other_info[2]
                        )
                verdict = _eval_cmp_under_bounds(
                    other_bounds, info[0], info[1], info[2]
                )
                if verdict is False:
                    return TacticResult((ctx.false_expr,), IdentityModelConverter())
                if verdict is True:
                    kept_flags[idx] = False
                    pruned_any = True
                    continue
            next_work.append(item)

        work = next_work
        if not pruned_any:
            break

    converter = (
        SubstitutionModelConverter(dict(reversed(eliminated)))
        if eliminated
        else IdentityModelConverter()
    )
    return TacticResult(tuple(work), converter)


class PropagateBoundsTactic:
    """Propagates unary linear bounds, fixes pinned vars, and drops tautologies."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Apply :func:`propagate_bounds` across ``formulas``."""
        return propagate_bounds(formulas)
