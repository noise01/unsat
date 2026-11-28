"""Word-level lazy Bit-Vector theory solver with known-bits & interval domains.

Performs incremental word-level domain narrowing (known zero/one bit masks plus
synchronized unsigned and signed intervals), online theory propagation/conflicts
with exact reason sets, lightweight concrete model synthesis, and on-demand
bit-blasting escalation requests handled by ``unsat.smt``.

Depends on: ``syntax``, ``model``, ``theories.base``.
"""

from collections.abc import Sequence
from dataclasses import dataclass

from unsat.syntax import App, Const, Context, DeclKind, Expr, FuncDecl
from unsat.theories.base import BVStats, TheoryLit

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

# Undo opcodes for copy-free backtracking.
_OP_ASSERT = 0
_OP_DOMAIN = 1
_OP_PROP_REASON = 2
_OP_LAST_CONCRETE = 3


def _dedup_lits(lits: Sequence[TheoryLit]) -> list[TheoryLit]:
    return list(dict.fromkeys(lits))


def _bv_mask(width: int) -> int:
    return (1 << width) - 1


def _bv_to_signed(val: int, width: int) -> int:
    sign_bit = 1 << (width - 1)
    return val - (1 << width) if (val & sign_bit) else val


def _bv_udiv(a: int, b: int, mask: int) -> int:
    return mask if b == 0 else a // b


def _bv_urem(a: int, b: int) -> int:
    return a if b == 0 else a % b


def _bv_sdiv(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    neg_a = (-a) & mask
    neg_b = (-b) & mask
    if not ma and not mb:
        return _bv_udiv(a, b, mask)
    if ma and not mb:
        return (-_bv_udiv(neg_a, b, mask)) & mask
    if not ma and mb:
        return (-_bv_udiv(a, neg_b, mask)) & mask
    return _bv_udiv(neg_a, neg_b, mask)


def _bv_srem(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    neg_a = (-a) & mask
    neg_b = (-b) & mask
    if not ma and not mb:
        return _bv_urem(a, b)
    if ma and not mb:
        return (-_bv_urem(neg_a, b)) & mask
    if not ma and mb:
        return _bv_urem(a, neg_b)
    return (-_bv_urem(neg_a, neg_b)) & mask


def _bv_smod(a: int, b: int, width: int, mask: int) -> int:
    sign_bit = 1 << (width - 1)
    ma = bool(a & sign_bit)
    mb = bool(b & sign_bit)
    abs_a = (-a) & mask if ma else a
    abs_b = (-b) & mask if mb else b
    u = _bv_urem(abs_a, abs_b)
    if u == 0:
        return 0
    if not ma and not mb:
        return u
    if ma and not mb:
        return ((-u) + b) & mask
    if not ma and mb:
        return (u + b) & mask
    return (-u) & mask


def _min_matching(low: int, zeros: int, ones: int, width: int) -> int | None:
    """Return smallest ``v >= low`` in ``[0, mask]`` matching ``(zeros, ones)``."""
    if zeros & ones:
        return None
    mask = (1 << width) - 1
    if low > mask:
        return None
    if low <= 0:
        return ones
    last_bump = -1
    for k in range(width - 1, -1, -1):
        bit_mask = 1 << k
        l_bit = low & bit_mask
        z_bit = zeros & bit_mask
        o_bit = ones & bit_mask
        if l_bit:
            if z_bit:
                if last_bump < 0:
                    return None
                keep = ~((1 << (last_bump + 1)) - 1)
                return (low & keep) | (1 << last_bump) | (ones & ((1 << last_bump) - 1))
        else:
            if o_bit:
                return (low & ~((1 << k) - 1)) | bit_mask | (ones & (bit_mask - 1))
            if not z_bit:
                last_bump = k
    return low


def _max_matching(high: int, zeros: int, ones: int, width: int) -> int | None:
    """Return largest ``v <= high`` in ``[0, mask]`` matching ``(zeros, ones)``."""
    if zeros & ones:
        return None
    if high < 0:
        return None
    mask = (1 << width) - 1
    max_fill = mask & ~zeros
    if high >= mask:
        return max_fill
    last_drop = -1
    for k in range(width - 1, -1, -1):
        bit_mask = 1 << k
        h_bit = high & bit_mask
        z_bit = zeros & bit_mask
        o_bit = ones & bit_mask
        if not h_bit:
            if o_bit:
                if last_drop < 0:
                    return None
                keep = ~((1 << (last_drop + 1)) - 1)
                return (high & keep) | (max_fill & ((1 << last_drop) - 1))
        else:
            if z_bit:
                return (high & ~((1 << (k + 1)) - 1)) | (max_fill & (bit_mask - 1))
            if not o_bit:
                last_drop = k
    return high


def _add_known_bits(za: int, oa: int, zb: int, ob: int, width: int) -> tuple[int, int]:
    """Compute sound known zero/one masks for ``a + b``."""
    rz = 0
    ro = 0
    cz = 1  # carry-in into bit 0 is known 0
    co = 0
    for k in range(width):
        a0 = bool((za >> k) & 1)
        a1 = bool((oa >> k) & 1)
        b0 = bool((zb >> k) & 1)
        b1 = bool((ob >> k) & 1)
        c0 = bool(cz)
        c1 = bool(co)

        if (a0 or a1) and (b0 or b1) and (c0 or c1):
            ones_cnt = int(a1) + int(b1) + int(c1)
            if ones_cnt & 1:
                ro |= 1 << k
            else:
                rz |= 1 << k
            cz = 1 if ones_cnt < 2 else 0
            co = 1 if ones_cnt >= 2 else 0
        else:
            # Determine next carry whenever two inputs force 0 or 1.
            num_zeros = int(a0) + int(b0) + int(c0)
            num_ones = int(a1) + int(b1) + int(c1)
            cz = 1 if num_zeros >= 2 else 0
            co = 1 if num_ones >= 2 else 0
    return rz, ro


def _rotate_left_mask(val: int, shift: int, width: int) -> int:
    s = shift % width
    if s == 0:
        return val
    mask = (1 << width) - 1
    return ((val << s) | (val >> (width - s))) & mask


def _rotate_right_mask(val: int, shift: int, width: int) -> int:
    s = shift % width
    if s == 0:
        return val
    return _rotate_left_mask(val, width - s, width)


def _repeat_mask(val: int, elem_width: int, count: int) -> int:
    out = 0
    for idx in range(count):
        out |= val << (idx * elem_width)
    return out


@dataclass(frozen=True, slots=True)
class BVBlastRequest:
    """Request emitted by :class:`BVSolver.check` to bit-blast violated atoms."""

    atoms: tuple[Expr, ...]


@dataclass(frozen=True, slots=True)
class BVDomain:
    """Combined known-bits and unsigned/signed interval domain for ``BitVec(w)``."""

    width: int
    zeros: int
    ones: int
    umin: int
    umax: int
    smin: int
    smax: int

    @classmethod
    def top(cls, width: int) -> BVDomain:
        """Return the unconstrained full domain for a bit-vector of ``width``."""
        mask = (1 << width) - 1
        sign_bit = 1 << (width - 1)
        return cls(
            width=width,
            zeros=0,
            ones=0,
            umin=0,
            umax=mask,
            smin=-sign_bit,
            smax=sign_bit - 1,
        )

    @classmethod
    def singleton(cls, value: int, width: int) -> BVDomain:
        """Return an exact singleton domain representing concrete ``value``."""
        mask = (1 << width) - 1
        u = value & mask
        s = _bv_to_signed(u, width)
        return cls(
            width=width,
            zeros=mask ^ u,
            ones=u,
            umin=u,
            umax=u,
            smin=s,
            smax=s,
        )

    @property
    def is_singleton(self) -> bool:
        """Return whether this domain permits exactly one concrete value."""
        return self.umin == self.umax

    def contains(self, value: int) -> bool:
        """Return whether ``value`` satisfies known-bits and both interval bounds."""
        mask = (1 << self.width) - 1
        u = value & mask
        if (u & self.ones) != self.ones or (u & self.zeros) != 0:
            return False
        if u < self.umin or u > self.umax:
            return False
        s = _bv_to_signed(u, self.width)
        return self.smin <= s <= self.smax

    def normalize(self) -> BVDomain | None:
        """Mutually tighten known-bits, unsigned bounds, and signed bounds."""
        width = self.width
        mask = (1 << width) - 1
        sign_bit = 1 << (width - 1)
        mod = 1 << width

        zeros = self.zeros & mask
        ones = self.ones & mask
        umin = max(0, self.umin)
        umax = min(mask, self.umax)
        smin = max(-sign_bit, self.smin)
        smax = min(sign_bit - 1, self.smax)

        for _ in range(3):
            if (zeros & ones) != 0 or umin > umax or smin > smax:
                return None

            new_umin = _min_matching(umin, zeros, ones, width)
            new_umax = _max_matching(umax, zeros, ones, width)
            if new_umin is None or new_umax is None or new_umin > new_umax:
                return None
            umin, umax = new_umin, new_umax

            # Common high prefix between umin and umax forces known prefix bits.
            diff = umin ^ umax
            suffix_bits = diff.bit_length()
            prefix_mask = mask ^ ((1 << suffix_bits) - 1)
            if prefix_mask:
                ones |= umin & prefix_mask
                zeros |= (~umin) & prefix_mask
                if zeros & ones:
                    return None

            # Cross-tighten unsigned and signed ranges across sign bit.
            if smax < 0 or umin >= sign_bit or (smax >= 0 and umin > smax):
                ones |= sign_bit
            if smin >= 0 or umax < sign_bit or (smin < 0 and umax >= sign_bit and (umax - mod) < smin):
                zeros |= sign_bit

            if zeros & ones:
                return None

            if ones & sign_bit:
                umin = max(umin, sign_bit)
                smax = min(smax, -1)
                if smin > smax:
                    return None
                umin = max(umin, smin + mod)
                umax = min(umax, smax + mod)
                smin = max(smin, umin - mod)
                smax = min(smax, umax - mod)
            elif zeros & sign_bit:
                umax = min(umax, sign_bit - 1)
                smin = max(smin, 0)
                if smin > smax:
                    return None
                umin = max(umin, smin)
                umax = min(umax, smax)
                smin = max(smin, umin)
                smax = min(smax, umax)

            if umin > umax or smin > smax:
                return None

            if (zeros | ones) == mask and umin == umax:
                break

        if (zeros & ones) != 0 or umin > umax or smin > smax:
            return None

        return BVDomain(
            width=width,
            zeros=zeros,
            ones=ones,
            umin=umin,
            umax=umax,
            smin=smin,
            smax=smax,
        )

    def intersect(self, other: BVDomain) -> BVDomain | None:
        """Return normalized intersection with ``other``, or ``None`` if empty."""
        return BVDomain(
            width=self.width,
            zeros=self.zeros | other.zeros,
            ones=self.ones | other.ones,
            umin=max(self.umin, other.umin),
            umax=min(self.umax, other.umax),
            smin=max(self.smin, other.smin),
            smax=min(self.smax, other.smax),
        ).normalize()

    def pick_value(self, preferred: int | None = None) -> int:
        """Choose a concrete value contained in this domain."""
        if preferred is not None and self.contains(preferred):
            return preferred & ((1 << self.width) - 1)
        if self.contains(self.umin):
            return self.umin
        if self.contains(self.umax):
            return self.umax
        sign_bit = 1 << (self.width - 1)
        mod = 1 << self.width
        cand_s = (self.smin + mod) if self.smin < 0 else self.smin
        if self.contains(cand_s):
            return cand_s
        if self.contains(self.ones):
            return self.ones
        # Signed wrap case: signed interval splits unsigned domain into [umin, smax]
        # and [smin + mod, umax]. Search both segments cleanly via bit-matching.
        if not (self.ones & sign_bit) and self.smax >= 0:
            low_seg = _min_matching(self.umin, self.zeros | sign_bit, self.ones, self.width)
            if low_seg is not None and self.contains(low_seg):
                return low_seg
        if not (self.zeros & sign_bit) and self.smin < 0:
            hi_seg = _min_matching(
                max(self.umin, self.smin + mod),
                self.zeros,
                self.ones | sign_bit,
                self.width,
            )
            if hi_seg is not None and self.contains(hi_seg):
                return hi_seg
        return self.umin


def _normalize_cmp(lhs: Expr, rhs: Expr, kind: DeclKind, polarity: bool) -> tuple[Expr, Expr, bool, bool]:
    """Normalize BV comparison ``(atom, pol)`` to ``(x, y, is_signed, strict)``."""
    match kind:
        case DeclKind.BV_ULT:
            return (lhs, rhs, False, True) if polarity else (rhs, lhs, False, False)
        case DeclKind.BV_ULE:
            return (lhs, rhs, False, False) if polarity else (rhs, lhs, False, True)
        case DeclKind.BV_UGT:
            return (rhs, lhs, False, True) if polarity else (lhs, rhs, False, False)
        case DeclKind.BV_UGE:
            return (rhs, lhs, False, False) if polarity else (lhs, rhs, False, True)
        case DeclKind.BV_SLT:
            return (lhs, rhs, True, True) if polarity else (rhs, lhs, True, False)
        case DeclKind.BV_SLE:
            return (lhs, rhs, True, False) if polarity else (rhs, lhs, True, True)
        case DeclKind.BV_SGT:
            return (rhs, lhs, True, True) if polarity else (lhs, rhs, True, False)
        case DeclKind.BV_SGE:
            return (rhs, lhs, True, False) if polarity else (lhs, rhs, True, True)
        case _:
            msg = f"Expected BV comparison DeclKind, got {kind}"
            raise TypeError(msg)


class BVSolver:
    """Lazy word-level Bit-Vector theory solver cooperating with CDCL(T)."""

    def __init__(self, ctx: Context) -> None:
        self._ctx = ctx
        self._stats = BVStats()

        self._trail_marks: list[int] = []
        self._history: list[tuple[object, ...]] = []

        self._domains: dict[Expr, BVDomain] = {}
        self._reasons: dict[Expr, frozenset[TheoryLit]] = {}
        self._asserted_atoms: dict[Expr, bool] = {}
        self._registered_atoms: set[Expr] = set()
        self._term_atoms: dict[Expr, list[Expr]] = {}
        self._term_users: dict[Expr, list[Expr]] = {}
        self._registered_terms: list[Expr] = []
        self._registered_term_set: set[Expr] = set()
        self._blasted_atoms: set[Expr] = set()

        self._pending_props: list[tuple[Expr, bool]] = []
        self._prop_reasons: dict[tuple[Expr, bool], tuple[TheoryLit, ...]] = {}
        self._conflict: list[TheoryLit] | None = None
        self._dirty_terms: set[Expr] = set()
        self._last_concrete: dict[Expr, int] = {}

    @property
    def ctx(self) -> Context:
        """AST context targeted by this BV solver."""
        return self._ctx

    @property
    def stats(self) -> BVStats:
        """Instrumentation counters for word-level BV solving."""
        return self._stats

    def push(self) -> None:
        """Save current trail position onto the incremental undo stack."""
        self._trail_marks.append(len(self._history))

    def pop(self, num_levels: int = 1) -> None:
        """Restore domain, reason, and assertion state across ``num_levels`` frames."""
        if num_levels <= 0:
            return
        if num_levels > len(self._trail_marks):
            msg = f"Cannot pop {num_levels} levels from depth {len(self._trail_marks)}"
            raise ValueError(msg)

        target = self._trail_marks[-num_levels]
        del self._trail_marks[-num_levels:]

        history = self._history
        while len(history) > target:
            entry = history.pop()
            op = entry[0]
            if op == _OP_ASSERT:
                atom = entry[1]
                assert isinstance(atom, Expr)
                self._asserted_atoms.pop(atom, None)
            elif op == _OP_DOMAIN:
                term = entry[1]
                old_dom = entry[2]
                old_rsn = entry[3]
                assert isinstance(term, Expr)
                assert isinstance(old_dom, BVDomain)
                assert isinstance(old_rsn, frozenset)
                self._domains[term] = old_dom
                self._reasons[term] = old_rsn
            elif op == _OP_PROP_REASON:
                prop_key = entry[1]
                assert isinstance(prop_key, tuple)
                self._prop_reasons.pop(prop_key, None)
            elif op == _OP_LAST_CONCRETE:
                old_conc = entry[1]
                assert isinstance(old_conc, dict)
                self._last_concrete = old_conc

        self._conflict = None
        self._pending_props.clear()
        self._dirty_terms.clear()

    def registered_terms(self) -> Sequence[Expr]:
        """Return all registered BitVec terms in bottom-up registration order."""
        return self._registered_terms

    def is_blasted(self, atom: Expr) -> bool:
        """Return whether ``atom`` has already been bit-blasted permanently."""
        return atom in self._blasted_atoms

    def mark_blasted(self, atom: Expr) -> None:
        """Mark ``atom`` as bit-blasted so future checks rely on SAT bits."""
        self._blasted_atoms.add(atom)

    def register_term(self, term: Expr) -> None:
        """Register ``term`` and BV subterms (treating UF/Array/ITE as leaves)."""
        if term.ctx is not self._ctx:
            msg = f"Expr '{term}' belongs to a different Context"
            raise ValueError(msg)
        if not term.is_bv:
            return
        if term in self._registered_term_set:
            return

        stack: list[tuple[Expr, bool]] = [(term, False)]
        while stack:
            node, expanded = stack.pop()
            if node in self._registered_term_set or not node.is_bv:
                continue

            if isinstance(node, App) and node.decl.kind in _BV_OP_KINDS:
                if not expanded:
                    stack.append((node, True))
                    stack.extend(
                        (arg, False)
                        for arg in reversed(node.args)
                        if arg not in self._registered_term_set and arg.is_bv
                    )
                    continue
                for arg in node.args:
                    users = self._term_users.setdefault(arg, [])
                    if node not in users:
                        users.append(node)
                self._registered_term_set.add(node)
                self._registered_terms.append(node)
                self._domains[node] = BVDomain.top(node.bv_size)
                self._reasons[node] = frozenset()
                self._dirty_terms.add(node)
                continue

            self._registered_term_set.add(node)
            self._registered_terms.append(node)
            if isinstance(node, Const):
                assert isinstance(node.value, int)
                assert not isinstance(node.value, bool)
                self._domains[node] = BVDomain.singleton(node.value, node.bv_size)
            else:
                self._domains[node] = BVDomain.top(node.bv_size)
            self._reasons[node] = frozenset()

    def register_atom(self, atom: Expr) -> None:
        """Register a BV equality or comparison atom for propagation and checking."""
        if atom.ctx is not self._ctx:
            msg = f"Expr '{atom}' belongs to a different Context"
            raise ValueError(msg)
        if atom in self._registered_atoms:
            return
        if not isinstance(atom, App):
            return
        kind = atom.decl.kind
        if kind is DeclKind.EQ:
            if len(atom.args) != 2 or not atom.args[0].is_bv:
                return
        elif kind not in _BV_CMP_KINDS:
            return

        lhs, rhs = atom.args
        self.register_term(lhs)
        self.register_term(rhs)
        self._registered_atoms.add(atom)
        self._term_atoms.setdefault(lhs, []).append(atom)
        if rhs is not lhs:
            self._term_atoms.setdefault(rhs, []).append(atom)
        self._check_atom_subsumed(atom)

    def assert_atom(self, atom: Expr, polarity: bool) -> None:
        """Assert ``atom`` with ``polarity`` at the current trail level."""
        self.register_atom(atom)
        existing = self._asserted_atoms.get(atom)
        if existing is not None:
            if existing == polarity:
                return
            if self._conflict is None:
                self._conflict = [TheoryLit(atom, True), TheoryLit(atom, False)]
                self._stats.conflicts += 1
            return

        self._asserted_atoms[atom] = polarity
        if self._trail_marks:
            self._history.append((_OP_ASSERT, atom))

        if self._conflict is None and atom in self._registered_atoms:
            self._apply_atom_constraint(atom, polarity)

    def propagate(
        self,
    ) -> tuple[Sequence[tuple[Expr, bool]], Sequence[TheoryLit] | None]:
        """Run bounded word-level fixpoint propagation, returning props or conflict."""
        if self._conflict is not None:
            return (), list(self._conflict)

        if self._dirty_terms:
            self._run_fixpoint()
            if self._conflict is not None:
                return (), list(self._conflict)

        if not self._pending_props:
            return (), None
        props = list(self._pending_props)
        self._pending_props.clear()
        self._stats.propagations += len(props)
        return props, None

    def explain_propagation(self, atom: Expr, polarity: bool) -> Sequence[TheoryLit]:
        """Return asserted ``TheoryLit`` reasons entailing ``(atom, polarity)``."""
        reasons = self._prop_reasons.get((atom, polarity))
        if reasons is None:
            msg = f"No BV propagation reason recorded for ({atom}, {polarity})"
            raise KeyError(msg)
        return reasons

    def explain_conflict(self) -> Sequence[TheoryLit]:
        """Return asserted ``TheoryLit`` reasons for the current BV conflict."""
        if self._conflict is None:
            msg = "No active BV theory conflict to explain"
            raise ValueError(msg)
        return list(self._conflict)

    def _update_domain(
        self,
        term: Expr,
        candidate: BVDomain,
        new_reasons: frozenset[TheoryLit],
    ) -> bool:
        """Intersect ``term`` domain with ``candidate``; return False on conflict."""
        cur = self._domains[term]
        merged = cur.intersect(candidate)
        if merged is None:
            if self._conflict is None:
                combined = _dedup_lits(
                    sorted(
                        self._reasons[term] | new_reasons,
                        key=lambda tl: (tl.atom.id, tl.sign),
                    )
                )
                self._conflict = combined
                self._stats.conflicts += 1
            return False
        if merged == cur:
            return True

        if self._trail_marks:
            self._history.append((_OP_DOMAIN, term, cur, self._reasons[term]))
        self._domains[term] = merged
        self._reasons[term] = self._reasons[term] | new_reasons
        self._dirty_terms.add(term)
        for user in self._term_users.get(term, ()):
            self._dirty_terms.add(user)
        return True

    def _apply_atom_constraint(self, atom: Expr, polarity: bool) -> bool:
        assert isinstance(atom, App)
        lit = TheoryLit(atom, polarity)
        lhs, rhs = atom.args
        dl = self._domains[lhs]
        dr = self._domains[rhs]
        rl = self._reasons[lhs]
        rr = self._reasons[rhs]

        if atom.decl.kind is DeclKind.EQ:
            if polarity:
                if not self._update_domain(lhs, dr, rr | {lit}):
                    return False
                if rhs is lhs:
                    return True
                return self._update_domain(rhs, self._domains[lhs], self._reasons[lhs] | {lit})

            # Disequality: lhs != rhs
            if dl.is_singleton and dr.is_singleton and dl.umin == dr.umin:
                if self._conflict is None:
                    self._conflict = _dedup_lits(
                        sorted(
                            rl | rr | {lit},
                            key=lambda tl: (tl.atom.id, tl.sign),
                        )
                    )
                    self._stats.conflicts += 1
                return False
            if dl.is_singleton and not dr.is_singleton:
                val = dl.umin
                mask = _bv_mask(rhs.bv_size)
                sval = _bv_to_signed(val, rhs.bv_size)
                new_umin = val + 1 if dr.umin == val else dr.umin
                new_umax = val - 1 if dr.umax == val else dr.umax
                new_smin = sval + 1 if dr.smin == sval else dr.smin
                new_smax = sval - 1 if dr.smax == sval else dr.smax
                if new_umin != dr.umin or new_umax != dr.umax or new_smin != dr.smin or new_smax != dr.smax:
                    cand = BVDomain(
                        width=dr.width,
                        zeros=dr.zeros,
                        ones=dr.ones,
                        umin=max(0, new_umin),
                        umax=min(mask, new_umax),
                        smin=new_smin,
                        smax=new_smax,
                    )
                    return self._update_domain(rhs, cand, rl | {lit})
            elif dr.is_singleton and not dl.is_singleton:
                val = dr.umin
                mask = _bv_mask(lhs.bv_size)
                sval = _bv_to_signed(val, lhs.bv_size)
                new_umin = val + 1 if dl.umin == val else dl.umin
                new_umax = val - 1 if dl.umax == val else dl.umax
                new_smin = sval + 1 if dl.smin == sval else dl.smin
                new_smax = sval - 1 if dl.smax == sval else dl.smax
                if new_umin != dl.umin or new_umax != dl.umax or new_smin != dl.smin or new_smax != dl.smax:
                    cand = BVDomain(
                        width=dl.width,
                        zeros=dl.zeros,
                        ones=dl.ones,
                        umin=max(0, new_umin),
                        umax=min(mask, new_umax),
                        smin=new_smin,
                        smax=new_smax,
                    )
                    return self._update_domain(lhs, cand, rr | {lit})
            return True

        x, y, is_signed, strict = _normalize_cmp(lhs, rhs, atom.decl.kind, polarity)
        dx = self._domains[x]
        dy = self._domains[y]
        self._reasons[x]
        ry = self._reasons[y]
        step = 1 if strict else 0

        if is_signed:
            x_cand = BVDomain(
                width=dx.width,
                zeros=dx.zeros,
                ones=dx.ones,
                umin=dx.umin,
                umax=dx.umax,
                smin=dx.smin,
                smax=dy.smax - step,
            )
            if not self._update_domain(x, x_cand, ry | {lit}):
                return False
            dx_now = self._domains[x]
            rx_now = self._reasons[x]
            y_cand = BVDomain(
                width=dy.width,
                zeros=dy.zeros,
                ones=dy.ones,
                umin=dy.umin,
                umax=dy.umax,
                smin=dx_now.smin + step,
                smax=dy.smax,
            )
            return self._update_domain(y, y_cand, rx_now | {lit})

        x_cand = BVDomain(
            width=dx.width,
            zeros=dx.zeros,
            ones=dx.ones,
            umin=dx.umin,
            umax=dy.umax - step,
            smin=dx.smin,
            smax=dx.smax,
        )
        if not self._update_domain(x, x_cand, ry | {lit}):
            return False
        dx_now = self._domains[x]
        rx_now = self._reasons[x]
        y_cand = BVDomain(
            width=dy.width,
            zeros=dy.zeros,
            ones=dy.ones,
            umin=dx_now.umin + step,
            umax=dy.umax,
            smin=dy.smin,
            smax=dy.smax,
        )
        return self._update_domain(y, y_cand, rx_now | {lit})

    def _enqueue_prop(self, atom: Expr, polarity: bool, reasons: frozenset[TheoryLit]) -> None:
        if atom in self._asserted_atoms:
            return
        key = (atom, polarity)
        if key in self._prop_reasons:
            return
        ordered = tuple(sorted(reasons, key=lambda tl: (tl.atom.id, tl.sign)))
        self._prop_reasons[key] = ordered
        if self._trail_marks:
            self._history.append((_OP_PROP_REASON, key))
        self._pending_props.append(key)

    def _check_atom_subsumed(self, atom: Expr) -> None:
        if atom in self._asserted_atoms or not isinstance(atom, App):
            return
        lhs, rhs = atom.args
        dl = self._domains[lhs]
        dr = self._domains[rhs]
        reasons = self._reasons[lhs] | self._reasons[rhs]

        if atom.decl.kind is DeclKind.EQ:
            if lhs is rhs or (dl.is_singleton and dr.is_singleton and dl.umin == dr.umin):
                self._enqueue_prop(atom, True, reasons)
            elif dl.intersect(dr) is None:
                self._enqueue_prop(atom, False, reasons)
            return

        for pol in (True, False):
            x, y, is_signed, strict = _normalize_cmp(lhs, rhs, atom.decl.kind, pol)
            dx = self._domains[x]
            dy = self._domains[y]
            if is_signed:
                holds = dx.smax < dy.smin if strict else dx.smax <= dy.smin
            else:
                holds = dx.umax < dy.umin if strict else dx.umax <= dy.umin
            if holds:
                self._enqueue_prop(atom, pol, self._reasons[x] | self._reasons[y])
                return

    def _propagate_app(self, node: App) -> bool:
        """Apply forward and backward transfer rules on BV operator ``node``."""
        kind = node.decl.kind
        args = node.args
        width = node.bv_size
        mask = (1 << width) - 1
        self._domains[node]
        self._reasons[node]
        all_arg_reasons = frozenset().union(*(self._reasons[a] for a in args))

        # Constant-fold when every operand is singleton.
        if all(self._domains[a].is_singleton for a in args):
            vals = {a: self._domains[a].umin for a in args}
            exact = self._eval_bv_app(node, vals)
            return self._update_domain(node, BVDomain.singleton(exact, width), all_arg_reasons)

        match kind:
            case DeclKind.BV_NOT:
                a = args[0]
                da = self._domains[a]
                fwd = BVDomain(
                    width=width,
                    zeros=da.ones,
                    ones=da.zeros,
                    umin=mask - da.umax,
                    umax=mask - da.umin,
                    smin=-da.smax - 1,
                    smax=-da.smin - 1,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                bwd = BVDomain(
                    width=width,
                    zeros=dn.ones,
                    ones=dn.zeros,
                    umin=mask - dn.umax,
                    umax=mask - dn.umin,
                    smin=-dn.smax - 1,
                    smax=-dn.smin - 1,
                )
                return self._update_domain(a, bwd, self._reasons[node])

            case DeclKind.BV_NEG:
                a = args[0]
                da = self._domains[a]
                sign_bit = 1 << (width - 1)
                mod = 1 << width
                # Trailing zeros of a stay zero in -a.
                tz = (da.zeros & -da.zeros) - 1 if (da.zeros & 1) else 0
                if tz == 0 and (da.ones & 1):
                    lo_z, lo_o = 0, 1
                else:
                    # Find longest contiguous trailing-zero prefix starting at bit 0.
                    tz_mask = 0
                    bit = 1
                    while (da.zeros & bit) and (bit <= mask):
                        tz_mask |= bit
                        bit <<= 1
                    lo_z = tz_mask
                    lo_o = bit if (bit <= mask and (da.ones & bit)) else 0
                f_umin = (mod - da.umax) if da.umin > 0 else 0
                f_umax = (mod - da.umin) if da.umin > 0 else mask
                f_smin = -da.smax if da.smin > -sign_bit else -sign_bit
                f_smax = -da.smin if da.smin > -sign_bit else sign_bit - 1
                fwd = BVDomain(
                    width=width,
                    zeros=lo_z,
                    ones=lo_o,
                    umin=f_umin,
                    umax=f_umax,
                    smin=f_smin,
                    smax=f_smax,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                b_umin = (mod - dn.umax) if dn.umin > 0 else 0
                b_umax = (mod - dn.umin) if dn.umin > 0 else mask
                b_smin = -dn.smax if dn.smin > -sign_bit else -sign_bit
                b_smax = -dn.smin if dn.smin > -sign_bit else sign_bit - 1
                bwd = BVDomain(
                    width=width,
                    zeros=dn.zeros & (lo_z if lo_o == 0 else (lo_z | lo_o)),
                    ones=0,
                    umin=b_umin,
                    umax=b_umax,
                    smin=b_smin,
                    smax=b_smax,
                )
                return self._update_domain(a, bwd, self._reasons[node])

            case DeclKind.BV_AND:
                rz = 0
                ro = mask
                umax_cap = mask
                for a in args:
                    da = self._domains[a]
                    rz |= da.zeros
                    ro &= da.ones
                    umax_cap = min(umax_cap, da.umax)
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=rz,
                    ones=ro,
                    umin=0,
                    umax=umax_cap,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, all_arg_reasons):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                # Backward: node bit=1 forces every arg bit=1; umin >= dn.umin.
                if dn.ones or dn.umin > 0:
                    for a in args:
                        bwd = BVDomain(
                            width=width,
                            zeros=0,
                            ones=dn.ones,
                            umin=dn.umin,
                            umax=mask,
                            smin=top.smin,
                            smax=top.smax,
                        )
                        if not self._update_domain(a, bwd, rn):
                            return False
                # If node bit=0 and all other args have bit=1, arg[i] must have bit=0.
                if dn.zeros:
                    for idx, a in enumerate(args):
                        other_ones = mask
                        other_reasons = rn
                        for j, other in enumerate(args):
                            if j != idx:
                                other_ones &= self._domains[other].ones
                                other_reasons |= self._reasons[other]
                        forced_z = dn.zeros & other_ones
                        if forced_z:
                            bwd = BVDomain(
                                width=width,
                                zeros=forced_z,
                                ones=0,
                                umin=0,
                                umax=mask,
                                smin=top.smin,
                                smax=top.smax,
                            )
                            if not self._update_domain(a, bwd, other_reasons):
                                return False
                return True

            case DeclKind.BV_OR:
                ro = 0
                rz = mask
                umin_floor = 0
                for a in args:
                    da = self._domains[a]
                    ro |= da.ones
                    rz &= da.zeros
                    umin_floor = max(umin_floor, da.umin)
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=rz,
                    ones=ro,
                    umin=umin_floor,
                    umax=mask,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, all_arg_reasons):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                if dn.zeros or dn.umax < mask:
                    for a in args:
                        bwd = BVDomain(
                            width=width,
                            zeros=dn.zeros,
                            ones=0,
                            umin=0,
                            umax=dn.umax,
                            smin=top.smin,
                            smax=top.smax,
                        )
                        if not self._update_domain(a, bwd, rn):
                            return False
                if dn.ones:
                    for idx, a in enumerate(args):
                        other_zeros = mask
                        other_reasons = rn
                        for j, other in enumerate(args):
                            if j != idx:
                                other_zeros &= self._domains[other].zeros
                                other_reasons |= self._reasons[other]
                        forced_o = dn.ones & other_zeros
                        if forced_o:
                            bwd = BVDomain(
                                width=width,
                                zeros=0,
                                ones=forced_o,
                                umin=0,
                                umax=mask,
                                smin=top.smin,
                                smax=top.smax,
                            )
                            if not self._update_domain(a, bwd, other_reasons):
                                return False
                return True

            case DeclKind.BV_XOR:
                cur_z = mask
                cur_o = 0
                for a in args:
                    da = self._domains[a]
                    cur_z, cur_o = (
                        (cur_z & da.zeros) | (cur_o & da.ones),
                        (cur_z & da.ones) | (cur_o & da.zeros),
                    )
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=cur_z,
                    ones=cur_o,
                    umin=0,
                    umax=mask,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, all_arg_reasons):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                for idx, a in enumerate(args):
                    oz = dn.zeros
                    oo = dn.ones
                    other_reasons = rn
                    for j, other in enumerate(args):
                        if j != idx:
                            dj = self._domains[other]
                            other_reasons |= self._reasons[other]
                            oz, oo = (
                                (oz & dj.zeros) | (oo & dj.ones),
                                (oz & dj.ones) | (oo & dj.zeros),
                            )
                    if oz or oo:
                        bwd = BVDomain(
                            width=width,
                            zeros=oz,
                            ones=oo,
                            umin=0,
                            umax=mask,
                            smin=top.smin,
                            smax=top.smax,
                        )
                        if not self._update_domain(a, bwd, other_reasons):
                            return False
                return True

            case DeclKind.BV_ADD:
                z_acc = mask
                o_acc = 0
                sum_umin = 0
                sum_umax = 0
                sum_smin = 0
                sum_smax = 0
                for a in args:
                    da = self._domains[a]
                    z_acc, o_acc = _add_known_bits(z_acc, o_acc, da.zeros, da.ones, width)
                    sum_umin += da.umin
                    sum_umax += da.umax
                    sum_smin += da.smin
                    sum_smax += da.smax
                mod = 1 << width
                sign_bit = 1 << (width - 1)
                top = BVDomain.top(width)
                f_umin = (sum_umin & mask) if (sum_umin >> width) == (sum_umax >> width) else 0
                f_umax = (sum_umax & mask) if (sum_umin >> width) == (sum_umax >> width) else mask
                f_smin = sum_smin if -sign_bit <= sum_smin and sum_smax < sign_bit else top.smin
                f_smax = sum_smax if -sign_bit <= sum_smin and sum_smax < sign_bit else top.smax
                fwd = BVDomain(
                    width=width,
                    zeros=z_acc,
                    ones=o_acc,
                    umin=f_umin,
                    umax=f_umax,
                    smin=f_smin,
                    smax=f_smax,
                )
                if not self._update_domain(node, fwd, all_arg_reasons):
                    return False

                dn = self._domains[node]
                rn = self._reasons[node]
                # Backward when two operands or others sum without wrap ambiguity.
                for idx, a in enumerate(args):
                    other_umin = 0
                    other_umax = 0
                    other_smin = 0
                    other_smax = 0
                    oz = mask
                    oo = 0
                    other_reasons = rn
                    for j, other in enumerate(args):
                        if j != idx:
                            dj = self._domains[other]
                            other_reasons |= self._reasons[other]
                            other_umin += dj.umin
                            other_umax += dj.umax
                            other_smin += dj.smin
                            other_smax += dj.smax
                            oz, oo = _add_known_bits(oz, oo, dj.zeros, dj.ones, width)
                    # Candidate a = node - other: check non-wrapping subtraction
                    if other_umax < mod:
                        diff_lo = dn.umin - other_umax
                        diff_hi = dn.umax - other_umin
                        if diff_lo >= 0 or diff_hi < 0:
                            b_umin = diff_lo & mask
                            b_umax = diff_hi & mask
                        else:
                            b_umin, b_umax = 0, mask
                    else:
                        b_umin, b_umax = 0, mask
                    s_lo = dn.smin - other_smax
                    s_hi = dn.smax - other_smin
                    b_smin = s_lo if -sign_bit <= s_lo and s_hi < sign_bit else top.smin
                    b_smax = s_hi if -sign_bit <= s_lo and s_hi < sign_bit else top.smax
                    # Known bits of a = node + (~other + 1) if other trailing known
                    neg_oz = mask if (oz & 1) and ((oz + oo) & mask) == mask else 0
                    if neg_oz == mask:
                        pass
                    if b_umin > 0 or b_umax < mask or b_smin > top.smin or b_smax < top.smax:
                        bwd = BVDomain(
                            width=width,
                            zeros=0,
                            ones=0,
                            umin=b_umin,
                            umax=b_umax,
                            smin=b_smin,
                            smax=b_smax,
                        )
                        if not self._update_domain(a, bwd, other_reasons):
                            return False
                return True

            case DeclKind.BV_SUB:
                a, b = args
                da = self._domains[a]
                db = self._domains[b]
                sign_bit = 1 << (width - 1)
                top = BVDomain.top(width)
                diff_lo = da.umin - db.umax
                diff_hi = da.umax - db.umin
                if diff_lo >= 0 or diff_hi < 0:
                    f_umin, f_umax = diff_lo & mask, diff_hi & mask
                else:
                    f_umin, f_umax = 0, mask
                s_lo = da.smin - db.smax
                s_hi = da.smax - db.smin
                f_smin = s_lo if -sign_bit <= s_lo and s_hi < sign_bit else top.smin
                f_smax = s_hi if -sign_bit <= s_lo and s_hi < sign_bit else top.smax
                fwd = BVDomain(
                    width=width,
                    zeros=0,
                    ones=0,
                    umin=f_umin,
                    umax=f_umax,
                    smin=f_smin,
                    smax=f_smax,
                )
                if not self._update_domain(node, fwd, all_arg_reasons):
                    return False

                dn = self._domains[node]
                rn = self._reasons[node]
                # a = node + b
                a_sum_lo = dn.umin + db.umin
                a_sum_hi = dn.umax + db.umax
                a_umin = (a_sum_lo & mask) if (a_sum_lo >> width) == (a_sum_hi >> width) else 0
                a_umax = (a_sum_hi & mask) if (a_sum_lo >> width) == (a_sum_hi >> width) else mask
                a_slo = dn.smin + db.smin
                a_shi = dn.smax + db.smax
                a_smin = a_slo if -sign_bit <= a_slo and a_shi < sign_bit else top.smin
                a_smax = a_shi if -sign_bit <= a_slo and a_shi < sign_bit else top.smax
                if (a_umin > 0 or a_umax < mask or a_smin > top.smin or a_smax < top.smax) and not self._update_domain(
                    a,
                    BVDomain(
                        width=width,
                        zeros=0,
                        ones=0,
                        umin=a_umin,
                        umax=a_umax,
                        smin=a_smin,
                        smax=a_smax,
                    ),
                    rn | self._reasons[b],
                ):
                    return False
                # b = a - node
                da_now = self._domains[a]
                b_lo = da_now.umin - dn.umax
                b_hi = da_now.umax - dn.umin
                b_umin, b_umax = (b_lo & mask, b_hi & mask) if (b_lo >= 0 or b_hi < 0) else (0, mask)
                b_slo = da_now.smin - dn.smax
                b_shi = da_now.smax - dn.smin
                b_smin = b_slo if -sign_bit <= b_slo and b_shi < sign_bit else top.smin
                b_smax = b_shi if -sign_bit <= b_slo and b_shi < sign_bit else top.smax
                if b_umin > 0 or b_umax < mask or b_smin > top.smin or b_smax < top.smax:
                    return self._update_domain(
                        b,
                        BVDomain(
                            width=width,
                            zeros=0,
                            ones=0,
                            umin=b_umin,
                            umax=b_umax,
                            smin=b_smin,
                            smax=b_smax,
                        ),
                        rn | self._reasons[a],
                    )
                return True

            case DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                a = args[0]
                da = self._domains[a]
                hi_mask = (1 << (hi + 1)) - 1
                f_umin, f_umax = 0, mask
                if (da.umin >> (hi + 1)) == (da.umax >> (hi + 1)):
                    f_umin = (da.umin & hi_mask) >> lo
                    f_umax = (da.umax & hi_mask) >> lo
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=(da.zeros >> lo) & mask,
                    ones=(da.ones >> lo) & mask,
                    umin=f_umin,
                    umax=f_umax,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                b_top = BVDomain.top(a.bv_size)
                return self._update_domain(
                    a,
                    BVDomain(
                        width=a.bv_size,
                        zeros=dn.zeros << lo,
                        ones=dn.ones << lo,
                        umin=0,
                        umax=b_top.umax,
                        smin=b_top.smin,
                        smax=b_top.smax,
                    ),
                    rn,
                )

            case DeclKind.BV_CONCAT:
                rz = 0
                ro = 0
                f_umin = 0
                f_umax = 0
                for a in args:
                    da = self._domains[a]
                    aw = a.bv_size
                    rz = (rz << aw) | da.zeros
                    ro = (ro << aw) | da.ones
                    f_umin = (f_umin << aw) | da.umin
                    f_umax = (f_umax << aw) | da.umax
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=rz,
                    ones=ro,
                    umin=f_umin,
                    umax=f_umax,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, all_arg_reasons):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                lo = width
                for a in args:
                    aw = a.bv_size
                    lo -= aw
                    amask = (1 << aw) - 1
                    atop = BVDomain.top(aw)
                    b_umin, b_umax = 0, amask
                    if (dn.umin >> (lo + aw)) == (dn.umax >> (lo + aw)):
                        b_umin = (dn.umin >> lo) & amask
                        b_umax = (dn.umax >> lo) & amask
                    bwd = BVDomain(
                        width=aw,
                        zeros=(dn.zeros >> lo) & amask,
                        ones=(dn.ones >> lo) & amask,
                        umin=b_umin,
                        umax=b_umax,
                        smin=atop.smin,
                        smax=atop.smax,
                    )
                    if not self._update_domain(a, bwd, rn):
                        return False
                return True

            case DeclKind.BV_ZERO_EXT:
                n = node.decl.params[0]
                a = args[0]
                aw = a.bv_size
                amask = (1 << aw) - 1
                ext_zeros = ((1 << n) - 1) << aw
                da = self._domains[a]
                fwd = BVDomain(
                    width=width,
                    zeros=da.zeros | ext_zeros,
                    ones=da.ones,
                    umin=da.umin,
                    umax=da.umax,
                    smin=da.umin,
                    smax=da.umax,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                if dn.ones & ext_zeros:
                    # Incompatible upper non-zero bit -> conflict.
                    if self._conflict is None:
                        self._conflict = _dedup_lits(
                            sorted(
                                rn | self._reasons[a],
                                key=lambda tl: (tl.atom.id, tl.sign),
                            )
                        )
                        self._stats.conflicts += 1
                    return False
                atop = BVDomain.top(aw)
                return self._update_domain(
                    a,
                    BVDomain(
                        width=aw,
                        zeros=dn.zeros & amask,
                        ones=dn.ones & amask,
                        umin=dn.umin,
                        umax=min(amask, dn.umax),
                        smin=atop.smin,
                        smax=atop.smax,
                    ),
                    rn,
                )

            case DeclKind.BV_SIGN_EXT:
                a = args[0]
                aw = a.bv_size
                amask = (1 << aw) - 1
                asign = 1 << (aw - 1)
                ext_mask = mask ^ amask
                da = self._domains[a]
                ext_z = ext_mask if (da.zeros & asign) else 0
                ext_o = ext_mask if (da.ones & asign) else 0
                fwd = BVDomain(
                    width=width,
                    zeros=da.zeros | ext_z,
                    ones=da.ones | ext_o,
                    umin=0,
                    umax=mask,
                    smin=da.smin,
                    smax=da.smax,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                rn = self._reasons[node]
                if (dn.zeros & ext_mask) and (dn.ones & ext_mask):
                    if self._conflict is None:
                        self._conflict = _dedup_lits(
                            sorted(
                                rn | self._reasons[a],
                                key=lambda tl: (tl.atom.id, tl.sign),
                            )
                        )
                        self._stats.conflicts += 1
                    return False
                bz = dn.zeros & amask
                bo = dn.ones & amask
                if dn.zeros & ext_mask:
                    bz |= asign
                if dn.ones & ext_mask:
                    bo |= asign
                return self._update_domain(
                    a,
                    BVDomain(
                        width=aw,
                        zeros=bz,
                        ones=bo,
                        umin=0,
                        umax=amask,
                        smin=max(-asign, dn.smin),
                        smax=min(asign - 1, dn.smax),
                    ),
                    rn,
                )

            case DeclKind.BV_ROTATE_LEFT | DeclKind.BV_ROTATE_RIGHT:
                shift = node.decl.params[0]
                a = args[0]
                da = self._domains[a]
                rot = _rotate_left_mask if kind is DeclKind.BV_ROTATE_LEFT else _rotate_right_mask
                inv_rot = _rotate_right_mask if kind is DeclKind.BV_ROTATE_LEFT else _rotate_left_mask
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=rot(da.zeros, shift, width),
                    ones=rot(da.ones, shift, width),
                    umin=0,
                    umax=mask,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                return self._update_domain(
                    a,
                    BVDomain(
                        width=width,
                        zeros=inv_rot(dn.zeros, shift, width),
                        ones=inv_rot(dn.ones, shift, width),
                        umin=0,
                        umax=mask,
                        smin=top.smin,
                        smax=top.smax,
                    ),
                    self._reasons[node],
                )

            case DeclKind.BV_REPEAT:
                count = node.decl.params[0]
                a = args[0]
                aw = a.bv_size
                amask = (1 << aw) - 1
                da = self._domains[a]
                top = BVDomain.top(width)
                fwd = BVDomain(
                    width=width,
                    zeros=_repeat_mask(da.zeros, aw, count),
                    ones=_repeat_mask(da.ones, aw, count),
                    umin=0,
                    umax=mask,
                    smin=top.smin,
                    smax=top.smax,
                )
                if not self._update_domain(node, fwd, self._reasons[a]):
                    return False
                dn = self._domains[node]
                bz = 0
                bo = 0
                for idx in range(count):
                    bz |= (dn.zeros >> (idx * aw)) & amask
                    bo |= (dn.ones >> (idx * aw)) & amask
                atop = BVDomain.top(aw)
                return self._update_domain(
                    a,
                    BVDomain(
                        width=aw,
                        zeros=bz,
                        ones=bo,
                        umin=0,
                        umax=amask,
                        smin=atop.smin,
                        smax=atop.smax,
                    ),
                    self._reasons[node],
                )

            case DeclKind.BV_SHL:
                a, s = args
                da = self._domains[a]
                ds = self._domains[s]
                top = BVDomain.top(width)
                if ds.is_singleton:
                    k = ds.umin
                    if k >= width:
                        return self._update_domain(node, BVDomain.singleton(0, width), all_arg_reasons)
                    lo_mask = (1 << k) - 1
                    f_umin = da.umin << k if (da.umax << k) <= mask else 0
                    f_umax = min(da.umax << k, mask)
                    fwd = BVDomain(
                        width=width,
                        zeros=((da.zeros << k) & mask) | lo_mask,
                        ones=(da.ones << k) & mask,
                        umin=f_umin,
                        umax=f_umax,
                        smin=top.smin,
                        smax=top.smax,
                    )
                    if not self._update_domain(node, fwd, all_arg_reasons):
                        return False
                    dn = self._domains[node]
                    if dn.ones & lo_mask:
                        if self._conflict is None:
                            self._conflict = _dedup_lits(
                                sorted(
                                    self._reasons[node] | all_arg_reasons,
                                    key=lambda tl: (tl.atom.id, tl.sign),
                                )
                            )
                            self._stats.conflicts += 1
                        return False
                    return self._update_domain(
                        a,
                        BVDomain(
                            width=width,
                            zeros=dn.zeros >> k,
                            ones=dn.ones >> k,
                            umin=0,
                            umax=mask,
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        self._reasons[node] | self._reasons[s],
                    )
                if ds.umin > 0:
                    lo_z = (1 << min(ds.umin, width)) - 1
                    return self._update_domain(
                        node,
                        BVDomain(
                            width=width,
                            zeros=lo_z,
                            ones=0,
                            umin=0,
                            umax=0 if ds.umin >= width else mask,
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        self._reasons[s],
                    )
                return True

            case DeclKind.BV_LSHR:
                a, s = args
                da = self._domains[a]
                ds = self._domains[s]
                top = BVDomain.top(width)
                if ds.is_singleton:
                    k = ds.umin
                    if k >= width:
                        return self._update_domain(node, BVDomain.singleton(0, width), all_arg_reasons)
                    hi_mask = mask ^ ((1 << (width - k)) - 1)
                    fwd = BVDomain(
                        width=width,
                        zeros=(da.zeros >> k) | hi_mask,
                        ones=da.ones >> k,
                        umin=da.umin >> k,
                        umax=da.umax >> k,
                        smin=top.smin,
                        smax=top.smax,
                    )
                    if not self._update_domain(node, fwd, all_arg_reasons):
                        return False
                    dn = self._domains[node]
                    if dn.ones & hi_mask:
                        if self._conflict is None:
                            self._conflict = _dedup_lits(
                                sorted(
                                    self._reasons[node] | all_arg_reasons,
                                    key=lambda tl: (tl.atom.id, tl.sign),
                                )
                            )
                            self._stats.conflicts += 1
                        return False
                    return self._update_domain(
                        a,
                        BVDomain(
                            width=width,
                            zeros=(dn.zeros << k) & mask,
                            ones=(dn.ones << k) & mask,
                            umin=0,
                            umax=mask,
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        self._reasons[node] | self._reasons[s],
                    )
                f_umin = 0 if ds.umax >= width else (da.umin >> ds.umax)
                f_umax = 0 if ds.umin >= width else (da.umax >> ds.umin)
                hi_z = mask ^ ((1 << max(0, width - ds.umin)) - 1)
                return self._update_domain(
                    node,
                    BVDomain(
                        width=width,
                        zeros=hi_z,
                        ones=0,
                        umin=f_umin,
                        umax=f_umax,
                        smin=top.smin,
                        smax=top.smax,
                    ),
                    all_arg_reasons,
                )

            case DeclKind.BV_ASHR:
                a, s = args
                da = self._domains[a]
                ds = self._domains[s]
                sign_bit = 1 << (width - 1)
                top = BVDomain.top(width)
                if ds.is_singleton:
                    k = min(ds.umin, width)
                    if k >= width:
                        if da.zeros & sign_bit:
                            return self._update_domain(node, BVDomain.singleton(0, width), all_arg_reasons)
                        if da.ones & sign_bit:
                            return self._update_domain(node, BVDomain.singleton(mask, width), all_arg_reasons)
                        return True
                    hi_mask = mask ^ ((1 << (width - k)) - 1)
                    fz = (da.zeros >> k) | (hi_mask if (da.zeros & sign_bit) else 0)
                    fo = (da.ones >> k) | (hi_mask if (da.ones & sign_bit) else 0)
                    return self._update_domain(
                        node,
                        BVDomain(
                            width=width,
                            zeros=fz,
                            ones=fo,
                            umin=0,
                            umax=mask,
                            smin=da.smin >> k,
                            smax=da.smax >> k,
                        ),
                        all_arg_reasons,
                    )
                lo_shift = min(ds.umin, width)
                hi_shift = min(ds.umax, width)
                candidates = (
                    da.smin >> lo_shift,
                    da.smin >> hi_shift,
                    da.smax >> lo_shift,
                    da.smax >> hi_shift,
                )
                return self._update_domain(
                    node,
                    BVDomain(
                        width=width,
                        zeros=0,
                        ones=0,
                        umin=0,
                        umax=mask,
                        smin=min(candidates),
                        smax=max(candidates),
                    ),
                    all_arg_reasons,
                )

            case DeclKind.BV_MUL:
                min_prod = 1
                max_prod = 1
                for a in args:
                    da = self._domains[a]
                    min_prod *= da.umin
                    max_prod *= da.umax
                top = BVDomain.top(width)
                if (min_prod >> width) == (max_prod >> width):
                    return self._update_domain(
                        node,
                        BVDomain(
                            width=width,
                            zeros=0,
                            ones=0,
                            umin=min_prod & mask,
                            umax=max_prod & mask,
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        all_arg_reasons,
                    )
                # Preserve guaranteed common trailing zero bits.
                tz_sum = 0
                for a in args:
                    za = self._domains[a].zeros
                    tz = 0
                    while tz < width and ((za >> tz) & 1):
                        tz += 1
                    tz_sum += tz
                tz_clamped = min(tz_sum, width)
                if tz_clamped:
                    return self._update_domain(
                        node,
                        BVDomain(
                            width=width,
                            zeros=(1 << tz_clamped) - 1,
                            ones=0,
                            umin=0,
                            umax=mask,
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        all_arg_reasons,
                    )
                return True

            case DeclKind.BV_UDIV:
                a, b = args
                da = self._domains[a]
                db = self._domains[b]
                if db.umin > 0:
                    top = BVDomain.top(width)
                    return self._update_domain(
                        node,
                        BVDomain(
                            width=width,
                            zeros=0,
                            ones=0,
                            umin=da.umin // db.umax,
                            umax=da.umax // db.umin,
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        all_arg_reasons,
                    )
                return True

            case DeclKind.BV_UREM:
                a, b = args
                da = self._domains[a]
                db = self._domains[b]
                if db.umin > 0:
                    top = BVDomain.top(width)
                    return self._update_domain(
                        node,
                        BVDomain(
                            width=width,
                            zeros=0,
                            ones=0,
                            umin=0,
                            umax=min(da.umax, db.umax - 1),
                            smin=top.smin,
                            smax=top.smax,
                        ),
                        all_arg_reasons,
                    )
                return True

            case _:
                return True

    def _run_fixpoint(self) -> None:
        max_steps = max(64, len(self._registered_terms) * 8)
        steps = 0
        touched: set[Expr] = set()

        # Re-evaluate all asserted atoms over currently dirty terms too.
        while self._dirty_terms and steps < max_steps:
            steps += 1
            term = self._dirty_terms.pop()
            touched.add(term)

            if isinstance(term, App) and term.decl.kind in _BV_OP_KINDS and not self._propagate_app(term):
                return

            for atom in self._term_atoms.get(term, ()):
                pol = self._asserted_atoms.get(atom)
                if pol is not None and not self._apply_atom_constraint(atom, pol):
                    return

        # Re-check subsumption for unasserted atoms touching updated terms.
        seen_atoms: set[Expr] = set()
        for term in touched:
            for atom in self._term_atoms.get(term, ()):
                if atom not in seen_atoms and atom not in self._asserted_atoms:
                    seen_atoms.add(atom)
                    self._check_atom_subsumed(atom)

    @staticmethod
    def _eval_bv_app(node: App, arg_vals: dict[Expr, int]) -> int:
        kind = node.decl.kind
        args = node.args
        width = node.bv_size
        mask = (1 << width) - 1
        match kind:
            case DeclKind.BV_NOT:
                return (~arg_vals[args[0]]) & mask
            case DeclKind.BV_NEG:
                return (-arg_vals[args[0]]) & mask
            case DeclKind.BV_AND:
                res = mask
                for a in args:
                    res &= arg_vals[a]
                return res
            case DeclKind.BV_OR:
                res = 0
                for a in args:
                    res |= arg_vals[a]
                return res
            case DeclKind.BV_XOR:
                res = 0
                for a in args:
                    res ^= arg_vals[a]
                return res
            case DeclKind.BV_ADD:
                res = 0
                for a in args:
                    res += arg_vals[a]
                return res & mask
            case DeclKind.BV_SUB:
                return (arg_vals[args[0]] - arg_vals[args[1]]) & mask
            case DeclKind.BV_MUL:
                res = 1
                for a in args:
                    res = (res * arg_vals[a]) & mask
                return res
            case DeclKind.BV_UDIV:
                return _bv_udiv(arg_vals[args[0]], arg_vals[args[1]], mask)
            case DeclKind.BV_UREM:
                return _bv_urem(arg_vals[args[0]], arg_vals[args[1]])
            case DeclKind.BV_SDIV:
                return _bv_sdiv(arg_vals[args[0]], arg_vals[args[1]], width, mask)
            case DeclKind.BV_SREM:
                return _bv_srem(arg_vals[args[0]], arg_vals[args[1]], width, mask)
            case DeclKind.BV_SMOD:
                return _bv_smod(arg_vals[args[0]], arg_vals[args[1]], width, mask)
            case DeclKind.BV_SHL:
                a_v = arg_vals[args[0]]
                b_v = arg_vals[args[1]]
                return 0 if b_v >= width else ((a_v << b_v) & mask)
            case DeclKind.BV_LSHR:
                a_v = arg_vals[args[0]]
                b_v = arg_vals[args[1]]
                return 0 if b_v >= width else (a_v >> b_v)
            case DeclKind.BV_ASHR:
                a_v = arg_vals[args[0]]
                b_v = arg_vals[args[1]]
                sign_bit = 1 << (width - 1)
                if b_v >= width:
                    return mask if (a_v & sign_bit) else 0
                return (_bv_to_signed(a_v, width) >> b_v) & mask
            case DeclKind.BV_CONCAT:
                res = 0
                for part in args:
                    res = (res << part.bv_size) | arg_vals[part]
                return res
            case DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                return (arg_vals[args[0]] >> lo) & ((1 << (hi - lo + 1)) - 1)
            case DeclKind.BV_ZERO_EXT:
                return arg_vals[args[0]]
            case DeclKind.BV_SIGN_EXT:
                src = args[0]
                return _bv_to_signed(arg_vals[src], src.bv_size) & mask
            case DeclKind.BV_ROTATE_LEFT:
                return _rotate_left_mask(arg_vals[args[0]], node.decl.params[0], width)
            case DeclKind.BV_ROTATE_RIGHT:
                return _rotate_right_mask(arg_vals[args[0]], node.decl.params[0], width)
            case DeclKind.BV_REPEAT:
                src = args[0]
                return _repeat_mask(arg_vals[src], src.bv_size, node.decl.params[0])
            case _:
                msg = f"Unsupported BV operator in BVSolver: {kind}"
                raise TypeError(msg)

    @staticmethod
    def _eval_atom(atom: App, vals: dict[Expr, int]) -> bool:
        lhs, rhs = atom.args
        a = vals[lhs]
        b = vals[rhs]
        kind = atom.decl.kind
        match kind:
            case DeclKind.EQ:
                return a == b
            case DeclKind.BV_ULT:
                return a < b
            case DeclKind.BV_ULE:
                return a <= b
            case DeclKind.BV_UGT:
                return a > b
            case DeclKind.BV_UGE:
                return a >= b
            case DeclKind.BV_SLT:
                w = lhs.bv_size
                return _bv_to_signed(a, w) < _bv_to_signed(b, w)
            case DeclKind.BV_SLE:
                w = lhs.bv_size
                return _bv_to_signed(a, w) <= _bv_to_signed(b, w)
            case DeclKind.BV_SGT:
                w = lhs.bv_size
                return _bv_to_signed(a, w) > _bv_to_signed(b, w)
            case DeclKind.BV_SGE:
                w = lhs.bv_size
                return _bv_to_signed(a, w) >= _bv_to_signed(b, w)
            case _:
                msg = f"Unsupported BV atom in BVSolver: {kind}"
                raise TypeError(msg)

    def _synthesize_concrete(self, sat_bit_values: dict[Expr, int] | None = None) -> dict[Expr, int]:
        """Construct concrete integer assignments bottom-up over registered terms."""
        sat_vals = sat_bit_values or {}
        concrete: dict[Expr, int] = {}

        # Group BV leaf terms linked by asserted equalities `Eq(u, v) = True`.
        leaves = [t for t in self._registered_terms if not (isinstance(t, App) and t.decl.kind in _BV_OP_KINDS)]
        parent: dict[Expr, Expr] = {t: t for t in leaves}

        def _find(x: Expr) -> Expr:
            while parent[x] is not x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for atom, pol in self._asserted_atoms.items():
            if (
                pol
                and isinstance(atom, App)
                and atom.decl.kind is DeclKind.EQ
                and atom.args[0] in parent
                and atom.args[1] in parent
            ):
                ra, rb = _find(atom.args[0]), _find(atom.args[1])
                if ra is not rb:
                    parent[rb] = ra

        groups: dict[Expr, list[Expr]] = {}
        for leaf in leaves:
            groups.setdefault(_find(leaf), []).append(leaf)

        # Track asserted disequalities between leaves to avoid trivial collisions.
        neq_neighbors: dict[Expr, list[Expr]] = {}
        for atom, pol in self._asserted_atoms.items():
            if not pol and isinstance(atom, App) and atom.decl.kind is DeclKind.EQ:
                lhs, rhs = atom.args
                if lhs in parent and rhs in parent:
                    neq_neighbors.setdefault(lhs, []).append(rhs)
                    neq_neighbors.setdefault(rhs, []).append(lhs)

        for members in groups.values():
            dom = BVDomain.top(members[0].bv_size)
            preferred_fixed: int | None = None
            for member in members:
                if isinstance(member, Const):
                    assert isinstance(member.value, int)
                    assert not isinstance(member.value, bool)
                    concrete[member] = member.value
                    preferred_fixed = member.value
                elif member in sat_vals:
                    concrete[member] = sat_vals[member]
                    if preferred_fixed is None:
                        preferred_fixed = sat_vals[member]
                inter = dom.intersect(self._domains[member])
                if inter is not None:
                    dom = inter

            unfixed = [m for m in members if m not in concrete]
            if not unfixed:
                continue

            forbidden = {
                concrete[nbr] for member in unfixed for nbr in neq_neighbors.get(member, ()) if nbr in concrete
            }
            chosen = dom.pick_value(preferred_fixed)
            if chosen in forbidden:
                candidates = [dom.umin, dom.umax]
                hi_probe = min(dom.umax, dom.umin + 16)
                candidates.extend(range(dom.umin, hi_probe + 1))
                for cand in candidates:
                    if cand not in forbidden and dom.contains(cand):
                        chosen = cand
                        break
            for member in unfixed:
                concrete[member] = chosen

        # Evaluate compound BV operator nodes bottom-up.
        for term in self._registered_terms:
            if term in sat_vals:
                concrete[term] = sat_vals[term]
            elif isinstance(term, App) and term.decl.kind in _BV_OP_KINDS:
                concrete[term] = self._eval_bv_app(term, concrete)

        return concrete

    def check(self, sat_bit_values: dict[Expr, int] | None = None) -> BVBlastRequest | list[TheoryLit] | None:
        """Validate asserted BV atoms or request on-demand bit-blasting."""
        self._stats.checks += 1
        if self._conflict is not None:
            return list(self._conflict)

        if self._dirty_terms:
            self._run_fixpoint()
            if self._conflict is not None:
                return list(self._conflict)

        concrete = self._synthesize_concrete(sat_bit_values)
        to_blast: list[Expr] = []
        for atom, pol in self._asserted_atoms.items():
            if atom in self._blasted_atoms or not isinstance(atom, App):
                continue
            if self._eval_atom(atom, concrete) != pol:
                to_blast.append(atom)

        if to_blast:
            return BVBlastRequest(tuple(to_blast))

        if self._trail_marks:
            self._history.append((_OP_LAST_CONCRETE, self._last_concrete))
        self._last_concrete = concrete
        self._stats.word_models += 1
        return None

    def _matching_concrete(
        self, sat_bit_values: dict[Expr, int] | None = None
    ) -> tuple[dict[Expr, int], dict[Expr, int]]:
        sat_vals = sat_bit_values or {}
        if self._last_concrete and all(self._last_concrete.get(k) == v for k, v in sat_vals.items()):
            return self._last_concrete, sat_vals
        return self._synthesize_concrete(sat_vals), sat_vals

    def concrete_values(self, sat_bit_values: dict[Expr, int] | None = None) -> dict[FuncDecl, int]:
        """Return concrete integer values for all uninterpreted BV 0-arity constants."""
        concrete, sat_vals = self._matching_concrete(sat_bit_values)
        out: dict[FuncDecl, int] = {}
        for term in self._registered_terms:
            if isinstance(term, App) and term.is_const_symbol:
                out[term.decl] = sat_vals.get(term, concrete.get(term, self._domains[term].pick_value()))
        return out

    def term_values(
        self,
        terms: Sequence[Expr],
        sat_bit_values: dict[Expr, int] | None = None,
    ) -> dict[Expr, int]:
        """Return concrete integer values for requested BV terms (used by MBTC)."""
        concrete, sat_vals = self._matching_concrete(sat_bit_values)
        out: dict[Expr, int] = {}
        for term in terms:
            if not term.is_bv:
                continue
            if term in sat_vals:
                out[term] = sat_vals[term]
            elif term in concrete:
                out[term] = concrete[term]
            elif isinstance(term, Const):
                assert isinstance(term.value, int)
                assert not isinstance(term.value, bool)
                out[term] = term.value
            elif term in self._domains:
                out[term] = self._domains[term].pick_value()
            else:
                out[term] = 0
        return out
