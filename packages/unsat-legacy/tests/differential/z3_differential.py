"""Z3 differential oracle for the frozen endoxa SMT solver.

Renders one backend-neutral :mod:`differential.formula` AST into both the
legacy solver (``unsat_legacy``) and Z3, checks satisfiability with
each, and compares the verdicts. On the quantifier-free propositional fragment both
solvers are complete, so the contract is strict: verdicts must both be decisive
(SAT/UNSAT) and equal. An unsat_legacy UNKNOWN is recorded as an *incompleteness*
(``agree=False``) rather than silently tolerated -- that too is a signal worth a red.

Only the SAT/UNSAT *verdict* is compared, never the satisfying model: distinct
solvers legitimately return different models for the same SAT formula.

This module discharges the commitment that the frozen solver's reliability
is guarded by a Z3 differential oracle.
"""

from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal

import z3
from unsat_legacy import And, Bool, Eq, Function, Implies, Not, Or, Solver, USort

from .formula import And as NAnd
from .formula import Apply as NApply
from .formula import Atom as NAtom
from .formula import Equal as NEqual
from .formula import Formula, Term, format_formula
from .formula import Implies as NImplies
from .formula import Not as NNot
from .formula import Or as NOr
from .formula import Var as NVar

if TYPE_CHECKING:
    from unsat_legacy import Expr

Verdict = Literal["SAT", "UNSAT", "UNKNOWN"]

#: The one uninterpreted sort the EUF fragment is written over, on each side. A
#: declared sort rather than a built-in one: an Int would give Z3 a domain it knows
#: is infinite and knows arithmetic about, and the point is to ask both solvers the
#: same question about equality alone.
_U = USort("U")
_Z3_U = z3.DeclareSort("U")


def _declaration_key(fn: str, arity: int) -> str:
    """Name a function by its arity as well.

    The generator reuses a name at more than one arity, and both solvers treat
    those as different declarations. Keying on the pair here is what keeps the two
    renderings in step -- otherwise one side would silently merge what the other
    kept apart, and the disagreement would be the harness's, not the solver's.
    """
    return f"{fn}/{arity}"


def render_legacy_term(node: Term) -> Expr:
    """Render a neutral term AST into an unsat_legacy expression."""
    match node:
        case NAtom(name):
            return Function(name, _U)()
        case NApply(fn, args):
            rendered = [render_legacy_term(a) for a in args]
            decl = Function(
                _declaration_key(fn, len(rendered)), *([_U] * (len(rendered) + 1))
            )
            return decl(*rendered)
    msg = f"Unknown term node: {node!r}"
    raise TypeError(msg)


def render_legacy(node: Formula) -> Expr:
    """Render a neutral formula AST into an unsat_legacy expression."""
    match node:
        case NVar(name):
            return Bool(name)
        case NEqual(left, right):
            return Eq(render_legacy_term(left), render_legacy_term(right))
        case NNot(child):
            return Not(render_legacy(child))
        case NImplies(left, right):
            return Implies(render_legacy(left), render_legacy(right))
        case NAnd(children):
            return And(*(render_legacy(c) for c in children))
        case NOr(children):
            return Or(*(render_legacy(c) for c in children))
    msg = f"Unknown formula node: {node!r}"
    raise TypeError(msg)


def render_z3_term(node: Term) -> z3.ExprRef:
    """Render the same neutral term AST into a Z3 expression."""
    match node:
        case NAtom(name):
            return z3.Const(name, _Z3_U)
        case NApply(fn, args):
            rendered = [render_z3_term(a) for a in args]
            decl = z3.Function(
                _declaration_key(fn, len(rendered)), *([_Z3_U] * (len(rendered) + 1))
            )
            return decl(*rendered)
    msg = f"Unknown term node: {node!r}"
    raise TypeError(msg)


def render_z3(node: Formula) -> z3.BoolRef:
    """Render the same neutral formula AST into a Z3 expression."""
    match node:
        case NVar(name):
            return z3.Bool(name)
        case NEqual(left, right):
            return render_z3_term(left) == render_z3_term(right)
        case NNot(child):
            return z3.Not(render_z3(child))
        case NImplies(left, right):
            return z3.Implies(render_z3(left), render_z3(right))
        case NAnd(children):
            return z3.And(*(render_z3(c) for c in children))
        case NOr(children):
            return z3.Or(*(render_z3(c) for c in children))
    msg = f"Unknown formula node: {node!r}"
    raise TypeError(msg)


def _z3_verdict(node: Formula) -> Verdict:
    solver = z3.Solver()
    solver.add(render_z3(node))
    result = solver.check()
    if result == z3.sat:
        return "SAT"
    if result == z3.unsat:
        return "UNSAT"
    return "UNKNOWN"


def _legacy_verdict(node: Formula) -> Verdict:
    solver = Solver()
    solver.add(render_legacy(node))
    return solver.check()


@dataclass(frozen=True, slots=True)
class DifferentialResult:
    """Outcome of checking one formula against both solvers."""

    formula_repr: str
    legacy: Verdict
    z3: Verdict
    agree: bool


def differential_check(node: Formula) -> DifferentialResult:
    """Check ``node`` with both solvers and compare their SAT/UNSAT verdicts.

    ``agree`` is True only when both verdicts are decisive (SAT/UNSAT) and equal.
    An unsat_legacy UNKNOWN on this complete fragment counts as a disagreement.
    """
    legacy = _legacy_verdict(node)
    z3_result = _z3_verdict(node)
    agree = legacy == z3_result and legacy in ("SAT", "UNSAT")
    return DifferentialResult(
        formula_repr=format_formula(node),
        legacy=legacy,
        z3=z3_result,
        agree=agree,
    )
