"""Pure SMT-LIB2 string semantics, Unicode escaping, and Brzozowski regex engine.

Depends on: stdlib only.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Sequence
from dataclasses import dataclass

MAX_CHAR_CODE = 0x2FFFF
_HEX_DIGITS = frozenset("0123456789abcdefABCDEF")
_PREFERRED_ASCII = (
    tuple(range(ord("a"), ord("z") + 1))
    + tuple(range(ord("0"), ord("9") + 1))
    + tuple(range(ord("A"), ord("Z") + 1))
    + (ord(" "), ord("_"), ord("-"))
)


def validate_smt2_string(value: str) -> None:
    """Validate that ``value`` is a ``str`` within the SMT-LIB2 code-point range."""
    if not isinstance(value, str):
        msg = f"String constant value must be str, got {type(value).__name__}"
        raise TypeError(msg)
    for ch in value:
        code = ord(ch)
        if code > MAX_CHAR_CODE:
            msg = f"Character code point U+{code:X} exceeds SMT-LIB2 Unicode limit U+{MAX_CHAR_CODE:X}"
            raise ValueError(msg)


def unescape_smt2_string(raw: str) -> str:
    r"""Decode SMT-LIB2 2.6 ``\\u{...}`` and ``\\uHHHH`` Unicode escape sequences."""
    if "\\" not in raw:
        return raw
    out: list[str] = []
    n = len(raw)
    i = 0
    while i < n:
        if raw[i] == "\\" and i + 1 < n and raw[i + 1] == "u":
            if i + 2 < n and raw[i + 2] == "{":
                close = raw.find("}", i + 3)
                if close != -1 and 1 <= close - (i + 3) <= 5:
                    hex_part = raw[i + 3 : close]
                    if all(ch in _HEX_DIGITS for ch in hex_part):
                        code = int(hex_part, 16)
                        if code <= MAX_CHAR_CODE:
                            out.append(chr(code))
                            i = close + 1
                            continue
            elif i + 6 <= n:
                hex_part = raw[i + 2 : i + 6]
                if all(ch in _HEX_DIGITS for ch in hex_part):
                    code = int(hex_part, 16)
                    if code <= MAX_CHAR_CODE:
                        out.append(chr(code))
                        i += 6
                        continue
        out.append(raw[i])
        i += 1
    return "".join(out)


def format_smt2_string(value: str) -> str:
    """Render ``value`` as a quoted SMT-LIB2 2.6 string literal."""
    out: list[str] = ['"']
    n = len(value)
    for i, ch in enumerate(value):
        code = ord(ch)
        if ch == '"':
            out.append('""')
        elif ch == "\\" and i + 1 < n and value[i + 1] == "u":
            # Prevent unescaping ambiguity when literal '\u...' appears in value.
            out.append("\\u{5c}")
        elif 0x20 <= code <= 0x7E:
            out.append(ch)
        else:
            out.append(f"\\u{{{code:x}}}")
    out.append('"')
    return "".join(out)


def eval_str_at(s: str, index: int) -> str:
    """SMT-LIB2 ``(str.at s i)``: single-character substring or ``""``."""
    if 0 <= index < len(s):
        return s[index]
    return ""


def eval_str_substr(s: str, offset: int, length: int) -> str:
    """SMT-LIB2 ``(str.substr s i n)``."""
    if 0 <= offset < len(s) and length > 0:
        return s[offset : offset + length]
    return ""


def eval_str_indexof(s: str, needle: str, offset: int) -> int:
    """SMT-LIB2 ``(str.indexof s t i)``."""
    if offset < 0 or offset > len(s):
        return -1
    if not needle:
        return offset
    return s.find(needle, offset)


def eval_str_replace(s: str, src: str, dst: str) -> str:
    """SMT-LIB2 ``(str.replace s src dst)`` (first occurrence only)."""
    if not src:
        return dst + s
    return s.replace(src, dst, 1)


def eval_str_replace_all(s: str, src: str, dst: str) -> str:
    """SMT-LIB2 ``(str.replace_all s src dst)`` (identity when ``src == ""``)."""
    if not src:
        return s
    return s.replace(src, dst)


def eval_str_to_int(s: str) -> int:
    """SMT-LIB2 ``(str.to_int s)`` (non-empty ASCII digits or ``-1``)."""
    if s and all("0" <= ch <= "9" for ch in s):
        return int(s)
    return -1


def eval_str_from_int(n: int) -> str:
    """SMT-LIB2 ``(str.from_int n)`` (decimal for ``n >= 0``, else ``""``)."""
    if n < 0:
        return ""
    return str(n)


def eval_str_to_code(s: str) -> int:
    """SMT-LIB2 ``(str.to_code s)`` (code point for 1-char strings, else ``-1``)."""
    if len(s) == 1:
        code = ord(s[0])
        if code <= MAX_CHAR_CODE:
            return code
    return -1


def eval_str_from_code(n: int) -> str:
    """SMT-LIB2 ``(str.from_code n)`` (1-char string if in range, else ``""``)."""
    if 0 <= n <= MAX_CHAR_CODE:
        return chr(n)
    return ""


def eval_str_is_digit(s: str) -> bool:
    """SMT-LIB2 ``(str.is_digit s)`` (single ASCII digit character)."""
    return len(s) == 1 and "0" <= s[0] <= "9"


# ------------------------------------------------------------------
# Canonical Regular Expressions & Brzozowski Derivative Engine
# ------------------------------------------------------------------


type Interval = tuple[int, int]


def normalize_intervals(intervals: Sequence[Interval]) -> tuple[Interval, ...]:
    """Clamp intervals to ``[0, MAX_CHAR_CODE]``, sort, and merge overlaps."""
    valid = [
        (max(0, lo), min(MAX_CHAR_CODE, hi)) for lo, hi in intervals if lo <= MAX_CHAR_CODE and hi >= 0 and lo <= hi
    ]
    if not valid:
        return ()
    valid.sort()
    merged: list[Interval] = [valid[0]]
    for lo, hi in valid[1:]:
        p_lo, p_hi = merged[-1]
        if lo <= p_hi + 1:
            merged[-1] = (p_lo, max(p_hi, hi))
        else:
            merged.append((lo, hi))
    return tuple(merged)


def intervals_contain(intervals: tuple[Interval, ...], code: int) -> bool:
    """Return whether ``code`` falls inside normalized sorted ``intervals``."""
    lo_idx = 0
    hi_idx = len(intervals) - 1
    while lo_idx <= hi_idx:
        mid = (lo_idx + hi_idx) // 2
        a, b = intervals[mid]
        if code < a:
            hi_idx = mid - 1
        elif code > b:
            lo_idx = mid + 1
        else:
            return True
    return False


def intervals_intersect(a: tuple[Interval, ...], b: tuple[Interval, ...]) -> tuple[Interval, ...]:
    """Return the normalized intersection of two interval sets."""
    out: list[Interval] = []
    i = 0
    j = 0
    while i < len(a) and j < len(b):
        lo = max(a[i][0], b[j][0])
        hi = min(a[i][1], b[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return tuple(out)


def intervals_complement(intervals: tuple[Interval, ...]) -> tuple[Interval, ...]:
    """Return complement of ``intervals`` within ``[0, MAX_CHAR_CODE]``."""
    out: list[Interval] = []
    cur = 0
    for lo, hi in intervals:
        if cur < lo:
            out.append((cur, lo - 1))
        cur = max(cur, hi + 1)
    if cur <= MAX_CHAR_CODE:
        out.append((cur, MAX_CHAR_CODE))
    return tuple(out)


@dataclass(frozen=True, slots=True)
class ReEmpty:
    """Empty language ``re.none``."""


@dataclass(frozen=True, slots=True)
class ReEps:
    """Singleton empty-string language ``(str.to_re "")``."""


@dataclass(frozen=True, slots=True)
class ReChars:
    """Single-character class over disjoint inclusive code-point intervals."""

    intervals: tuple[Interval, ...]


@dataclass(frozen=True, slots=True)
class ReConcat:
    """Regular-expression concatenation ``(re.++ ...)``."""

    parts: tuple[ReNode, ...]


@dataclass(frozen=True, slots=True)
class ReUnion:
    """Regular-expression union ``(re.union ...)``."""

    alts: tuple[ReNode, ...]


@dataclass(frozen=True, slots=True)
class ReInter:
    """Regular-expression intersection ``(re.inter ...)``."""

    parts: tuple[ReNode, ...]


@dataclass(frozen=True, slots=True)
class ReComp:
    """Regular-expression complement ``(re.comp r)``."""

    inner: ReNode


@dataclass(frozen=True, slots=True)
class ReStar:
    """Kleene closure ``(re.* r)``."""

    inner: ReNode


type ReNode = ReEmpty | ReEps | ReChars | ReConcat | ReUnion | ReInter | ReComp | ReStar

RE_EMPTY = ReEmpty()
RE_EPS = ReEps()
RE_ALLCHAR = ReChars(((0, MAX_CHAR_CODE),))
RE_ALL = ReStar(RE_ALLCHAR)


def re_chars(intervals: Sequence[Interval]) -> ReNode:
    """Construct a normalized character-class regex node."""
    norm = normalize_intervals(intervals)
    if not norm:
        return RE_EMPTY
    if norm == RE_ALLCHAR.intervals:
        return RE_ALLCHAR
    return ReChars(norm)


def re_from_str(s: str) -> ReNode:
    """Construct a regex matching exactly string ``s``."""
    if not s:
        return RE_EPS
    if len(s) == 1:
        code = ord(s[0])
        return ReChars(((code, code),))
    return ReConcat(tuple(ReChars(((ord(ch), ord(ch)),)) for ch in s))


def re_range(lo: str, hi: str) -> ReNode:
    """SMT-LIB2 ``(re.range lo hi)``."""
    if len(lo) != 1 or len(hi) != 1 or ord(lo[0]) > ord(hi[0]):
        return RE_EMPTY
    return re_chars(((ord(lo[0]), ord(hi[0])),))


def re_concat(*parts: ReNode) -> ReNode:
    """Smart concatenation constructor with identity/absorbing normalization."""
    flat: list[ReNode] = []
    for part in parts:
        if isinstance(part, ReEmpty):
            return RE_EMPTY
        if isinstance(part, ReEps):
            continue
        if isinstance(part, ReConcat):
            flat.extend(part.parts)
        else:
            flat.append(part)
    if not flat:
        return RE_EPS
    if len(flat) == 1:
        return flat[0]
    return ReConcat(tuple(flat))


def _sort_key_re(node: ReNode) -> tuple[str, int, str]:
    return (type(node).__name__, hash(node), repr(node))


def re_union(*alts: ReNode) -> ReNode:
    """Smart union constructor merging character classes and flattening."""
    unique: list[ReNode] = []
    seen: set[ReNode] = set()
    char_intervals: list[Interval] = []
    for alt in alts:
        items = alt.alts if isinstance(alt, ReUnion) else (alt,)
        for item in items:
            if item == RE_ALL:
                return RE_ALL
            if isinstance(item, ReEmpty):
                continue
            if isinstance(item, ReChars):
                char_intervals.extend(item.intervals)
                continue
            if item not in seen:
                seen.add(item)
                unique.append(item)
    if char_intervals:
        cnode = re_chars(char_intervals)
        if not isinstance(cnode, ReEmpty) and cnode not in seen:
            seen.add(cnode)
            unique.append(cnode)
    if not unique:
        return RE_EMPTY
    if len(unique) == 1:
        return unique[0]
    unique.sort(key=_sort_key_re)
    return ReUnion(tuple(unique))


def re_inter(*parts: ReNode) -> ReNode:
    """Smart intersection constructor with identity/character folding."""
    unique: list[ReNode] = []
    seen: set[ReNode] = set()
    char_class: ReChars | None = None
    for part in parts:
        items = part.parts if isinstance(part, ReInter) else (part,)
        for item in items:
            if isinstance(item, ReEmpty):
                return RE_EMPTY
            if item == RE_ALL:
                continue
            if isinstance(item, ReChars):
                if char_class is None:
                    char_class = item
                else:
                    merged = intervals_intersect(char_class.intervals, item.intervals)
                    if not merged:
                        return RE_EMPTY
                    char_class = ReChars(merged)
                continue
            if item not in seen:
                seen.add(item)
                unique.append(item)
    if char_class is not None:
        if unique:
            # Intersection with a length-1 class forces length == 1.
            pass
        if char_class not in seen:
            unique.append(char_class)
    if not unique:
        return RE_ALL
    if len(unique) == 1:
        return unique[0]
    unique.sort(key=_sort_key_re)
    return ReInter(tuple(unique))


def re_comp(inner: ReNode) -> ReNode:
    """Smart complement constructor."""
    if isinstance(inner, ReEmpty):
        return RE_ALL
    if inner == RE_ALL:
        return RE_EMPTY
    if isinstance(inner, ReComp):
        return inner.inner
    return ReComp(inner)


def re_diff(lhs: ReNode, rhs: ReNode) -> ReNode:
    """SMT-LIB2 ``(re.diff lhs rhs)``."""
    return re_inter(lhs, re_comp(rhs))


def re_star(inner: ReNode) -> ReNode:
    """Smart Kleene star constructor."""
    if isinstance(inner, (ReEmpty, ReEps)):
        return RE_EPS
    if isinstance(inner, ReStar):
        return inner
    return ReStar(inner)


def re_plus(inner: ReNode) -> ReNode:
    """SMT-LIB2 ``(re.+ r)``."""
    return re_concat(inner, re_star(inner))


def re_opt(inner: ReNode) -> ReNode:
    """SMT-LIB2 ``(re.opt r)``."""
    return re_union(RE_EPS, inner)


def re_power(inner: ReNode, n: int) -> ReNode:
    """SMT-LIB2 ``((_ re.^ n) r)``."""
    if n < 0:
        msg = f"Regex power must be non-negative, got {n}"
        raise ValueError(msg)
    if n == 0:
        return RE_EPS
    return re_concat(*(inner for _ in range(n)))


def re_loop(inner: ReNode, lo: int, hi: int) -> ReNode:
    """SMT-LIB2 ``((_ re.loop lo hi) r)``."""
    if lo < 0:
        msg = f"Regex loop lower bound must be non-negative, got {lo}"
        raise ValueError(msg)
    if hi < lo:
        return RE_EMPTY
    if lo == hi:
        return re_power(inner, lo)
    base = re_power(inner, lo)
    opt_tail = RE_EPS
    for _ in range(hi - lo):
        opt_tail = re_opt(re_concat(inner, opt_tail))
    return re_concat(base, opt_tail)


def re_nullable(node: ReNode) -> bool:
    """Return whether ``node`` accepts the empty string ``""``."""
    match node:
        case ReEmpty() | ReChars():
            return False
        case ReEps() | ReStar():
            return True
        case ReConcat(parts=parts):
            return all(re_nullable(p) for p in parts)
        case ReUnion(alts=alts):
            return any(re_nullable(a) for a in alts)
        case ReInter(parts=parts):
            return all(re_nullable(p) for p in parts)
        case ReComp(inner=inner):
            return not re_nullable(inner)


def re_deriv(node: ReNode, code: int, memo: dict[tuple[ReNode, int], ReNode] | None = None) -> ReNode:
    """Compute the Brzozowski derivative of ``node`` with respect to ``chr(code)``."""
    if memo is not None:
        cached = memo.get((node, code))
        if cached is not None:
            return cached
    res: ReNode
    match node:
        case ReEmpty() | ReEps():
            res = RE_EMPTY
        case ReChars(intervals=intervals):
            res = RE_EPS if intervals_contain(intervals, code) else RE_EMPTY
        case ReConcat(parts=parts):
            head = parts[0]
            tail = ReConcat(parts[1:]) if len(parts) > 2 else parts[1]
            d_head = re_concat(re_deriv(head, code, memo), tail)
            res = re_union(d_head, re_deriv(tail, code, memo)) if re_nullable(head) else d_head
        case ReUnion(alts=alts):
            res = re_union(*(re_deriv(alt, code, memo) for alt in alts))
        case ReInter(parts=parts):
            res = re_inter(*(re_deriv(part, code, memo) for part in parts))
        case ReComp(inner=inner):
            res = re_comp(re_deriv(inner, code, memo))
        case ReStar(inner=inner):
            res = re_concat(re_deriv(inner, code, memo), node)
    if memo is not None:
        memo[(node, code)] = res
    return res


def re_matches(node: ReNode, s: str) -> bool:
    """Return whether string ``s`` belongs to the language of ``node``."""
    cur = node
    memo: dict[tuple[ReNode, int], ReNode] = {}
    for ch in s:
        cur = re_deriv(cur, ord(ch), memo)
        if isinstance(cur, ReEmpty):
            return False
    return re_nullable(cur)


def _collect_char_boundaries(node: ReNode, boundaries: set[int]) -> None:
    stack: list[ReNode] = [node]
    visited: set[ReNode] = set()
    while stack:
        cur = stack.pop()
        if cur in visited:
            continue
        visited.add(cur)
        match cur:
            case ReChars(intervals=intervals):
                for lo, hi in intervals:
                    boundaries.add(lo)
                    if hi + 1 <= MAX_CHAR_CODE:
                        boundaries.add(hi + 1)
            case ReConcat(parts=parts) | ReInter(parts=parts):
                stack.extend(parts)
            case ReUnion(alts=alts):
                stack.extend(alts)
            case ReComp(inner=inner) | ReStar(inner=inner):
                stack.append(inner)
            case _:
                pass


def re_minterms(node: ReNode) -> tuple[Interval, ...]:
    """Partition ``[0, MAX_CHAR_CODE]`` into derivative-equivalent character ranges."""
    boundaries: set[int] = {0}
    _collect_char_boundaries(node, boundaries)
    pts = sorted(boundaries)
    out: list[Interval] = []
    for idx, start in enumerate(pts):
        end = pts[idx + 1] - 1 if idx + 1 < len(pts) else MAX_CHAR_CODE
        out.append((start, end))
    return tuple(out)


def _pick_rep_in_interval(lo: int, hi: int, offset: int = 0) -> int:
    for code in _PREFERRED_ASCII:
        if lo <= code <= hi:
            if offset == 0:
                return code
            offset -= 1
    span = hi - lo + 1
    return lo + (offset % span)


def re_is_empty(node: ReNode, *, max_states: int = 256) -> bool | None:
    """Decide language emptiness via bounded BFS over Brzozowski derivative states.

    Returns ``True`` if provably empty, ``False`` if non-empty, or ``None`` if
    ``max_states`` is reached before exploration finishes.
    """
    if isinstance(node, ReEmpty):
        return True
    if re_nullable(node):
        return False
    visited: set[ReNode] = {node}
    queue: deque[ReNode] = deque([node])
    while queue:
        cur = queue.popleft()
        if re_nullable(cur):
            return False
        for lo, _hi in re_minterms(cur):
            nxt = re_deriv(cur, lo)
            if isinstance(nxt, ReEmpty) or nxt in visited:
                continue
            if re_nullable(nxt):
                return False
            if len(visited) >= max_states:
                return None
            visited.add(nxt)
            queue.append(nxt)
    return True


def re_min_max_length(node: ReNode) -> tuple[int | None, int | None]:
    """Return sound ``(min_len, max_len)`` bounds; ``None`` means unbounded/unknown."""
    match node:
        case ReEmpty():
            return (None, None)
        case ReEps():
            return (0, 0)
        case ReChars():
            return (1, 1)
        case ReConcat(parts=parts):
            total_min = 0
            total_max: int | None = 0
            for part in parts:
                p_min, p_max = re_min_max_length(part)
                if p_min is None:
                    return (None, None)
                total_min += p_min
                if p_max is None or total_max is None:
                    total_max = None
                else:
                    total_max += p_max
            return (total_min, total_max)
        case ReUnion(alts=alts):
            mins: list[int] = []
            maxes: list[int | None] = []
            for alt in alts:
                a_min, a_max = re_min_max_length(alt)
                if a_min is not None:
                    mins.append(a_min)
                    maxes.append(a_max)
            if not mins:
                return (None, None)
            u_min = min(mins)
            u_max = None if any(m is None for m in maxes) else max(m for m in maxes if m is not None)
            return (u_min, u_max)
        case ReInter(parts=parts):
            cur_min = 0
            cur_max: int | None = None
            for part in parts:
                p_min, p_max = re_min_max_length(part)
                if p_min is not None and p_min > cur_min:
                    cur_min = p_min
                if p_max is not None and (cur_max is None or p_max < cur_max):
                    cur_max = p_max
            if cur_max is not None and cur_min > cur_max:
                return (None, None)
            return (cur_min, cur_max)
        case ReStar(inner=inner):
            _, inner_max = re_min_max_length(inner)
            if inner_max == 0:
                return (0, 0)
            return (0, None)
        case ReComp():
            return (0, None)


def re_allowed_intervals_at(node: ReNode, length: int) -> tuple[tuple[Interval, ...] | None, ...] | None:
    """Return per-position allowed char intervals for fixed ``length``, if simple."""
    if length < 0:
        return None
    if length == 0:
        return () if re_nullable(node) else None
    if isinstance(node, ReChars):
        return (node.intervals,) if length == 1 else None
    if isinstance(node, ReConcat) and all(isinstance(p, ReChars) for p in node.parts):
        if len(node.parts) != length:
            return None
        return tuple(p.intervals for p in node.parts if isinstance(p, ReChars))
    return (None,) * length


def re_find_word_of_length(
    node: ReNode,
    length: int,
    *,
    allowed_at: Sequence[tuple[Interval, ...] | None] | None = None,
    forbidden: set[str] | None = None,
    max_steps: int = 2000,
) -> str | None:
    """Find a word of exact ``length`` matching ``node`` avoiding ``forbidden``."""
    if length < 0:
        return None
    dead: set[tuple[ReNode, int]] = set()
    steps = 0

    def _search(state: ReNode, pos: int, chars: list[str]) -> str | None:
        nonlocal steps
        rem = length - pos
        if isinstance(state, ReEmpty) or (state, rem) in dead:
            return None
        if rem == 0:
            if not re_nullable(state):
                return None
            word = "".join(chars)
            if forbidden is not None and word in forbidden:
                return None
            return word

        steps += 1
        if steps > max_steps:
            return None

        pos_allowed = allowed_at[pos] if allowed_at is not None else None
        mt = re_minterms(state)
        candidate_ranges = intervals_intersect(mt, pos_allowed) if pos_allowed is not None else mt
        # Try alternative characters in the interval when avoiding forbidden words.
        for lo, hi in candidate_ranges:
            rep = _pick_rep_in_interval(lo, hi, 0)
            nxt = re_deriv(state, rep)
            if isinstance(nxt, ReEmpty):
                continue
            chars.append(chr(rep))
            found = _search(nxt, pos + 1, chars)
            chars.pop()
            if found is not None:
                return found
            # Same derivative class holds for every code point in [lo, hi].
            span = hi - lo + 1
            if span > 1 and forbidden:
                for off in range(1, min(span, len(forbidden) + 2)):
                    alt_code = _pick_rep_in_interval(lo, hi, off)
                    chars.append(chr(alt_code))
                    found_alt = _search(nxt, pos + 1, chars)
                    chars.pop()
                    if found_alt is not None:
                        return found_alt
        if not forbidden:
            dead.add((state, rem))
        return None

    return _search(node, 0, [])
