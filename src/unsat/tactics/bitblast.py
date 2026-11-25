"""Word-level bit-vector simplification and eager bit-blasting tactics.

Transforms fixed-width bit-vector formulas into pure Boolean SAT problems paired
with a :class:`BitVecModelConverter` to reconstruct bit-vector models.

Depends on: ``syntax``, ``model``, ``tactics.base``.
"""

from collections.abc import Callable, Sequence

from unsat.model import IdentityModelConverter, Model
from unsat.syntax import (
    App,
    BoundVar,
    Const,
    Context,
    DeclKind,
    Expr,
    FuncDecl,
    Quantifier,
    collect_func_decls,
    iter_subexprs,
)
from unsat.tactics.base import TacticResult

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

_BOOL_CONN_KINDS = frozenset(
    {
        DeclKind.NOT,
        DeclKind.AND,
        DeclKind.OR,
        DeclKind.IMPLIES,
        DeclKind.XOR,
        DeclKind.EQ,
        DeclKind.DISTINCT,
        DeclKind.ITE,
    }
)


def _bv_mask(width: int) -> int:
    return (1 << width) - 1


def _bv_to_signed(val: int, width: int) -> int:
    sign_bit = 1 << (width - 1)
    return val - (1 << width) if (val & sign_bit) else val


def _is_not_of_bv(candidate: Expr, target: Expr) -> bool:
    return (
        isinstance(candidate, App)
        and candidate.decl.kind is DeclKind.BV_NOT
        and candidate.args[0] is target
    )


def _simplify_extract(ctx: Context, hi: int, lo: int, arg: Expr) -> Expr:
    if isinstance(arg, App):
        kind = arg.decl.kind
        if kind is DeclKind.BV_EXTRACT:
            lo2 = arg.decl.params[1]
            return _simplify_extract(ctx, lo2 + hi, lo2 + lo, arg.args[0])
        if kind is DeclKind.BV_ZERO_EXT:
            inner = arg.args[0]
            iw = inner.bv_size
            if hi < iw:
                return _simplify_extract(ctx, hi, lo, inner)
            if lo >= iw:
                return ctx.mk_bv_val(0, hi - lo + 1)
            return ctx.mk_zero_ext(
                hi - iw + 1, _simplify_extract(ctx, iw - 1, lo, inner)
            )
        if kind is DeclKind.BV_SIGN_EXT:
            inner = arg.args[0]
            iw = inner.bv_size
            if hi < iw:
                return _simplify_extract(ctx, hi, lo, inner)
            if lo >= iw:
                msb = _simplify_extract(ctx, iw - 1, iw - 1, inner)
                return ctx.mk_repeat(hi - lo + 1, msb)
            return ctx.mk_sign_ext(
                hi - iw + 1, _simplify_extract(ctx, iw - 1, lo, inner)
            )
        if kind is DeclKind.BV_CONCAT:
            pieces: list[Expr] = []
            offset = 0
            for part in reversed(arg.args):
                pw = part.bv_size
                part_lo = offset
                part_hi = offset + pw - 1
                offset += pw
                ov_lo = max(lo, part_lo)
                ov_hi = min(hi, part_hi)
                if ov_lo <= ov_hi:
                    pieces.append(
                        _simplify_extract(ctx, ov_hi - part_lo, ov_lo - part_lo, part)
                    )
            pieces.reverse()
            return ctx.mk_concat(*pieces)
    return ctx.mk_extract(hi, lo, arg)


def _simplify_concat(ctx: Context, args: Sequence[Expr]) -> Expr:
    flat: list[Expr] = []
    for part in args:
        if isinstance(part, App) and part.decl.kind is DeclKind.BV_CONCAT:
            flat.extend(part.args)
        else:
            flat.append(part)
    coalesced: list[Expr] = []
    for part in flat:
        if (
            coalesced
            and isinstance(coalesced[-1], App)
            and coalesced[-1].decl.kind is DeclKind.BV_EXTRACT
            and isinstance(part, App)
            and part.decl.kind is DeclKind.BV_EXTRACT
            and coalesced[-1].args[0] is part.args[0]
            and coalesced[-1].decl.params[1] == part.decl.params[0] + 1
        ):
            prev = coalesced.pop()
            assert isinstance(prev, App)
            coalesced.append(
                ctx.mk_extract(prev.decl.params[0], part.decl.params[1], part.args[0])
            )
        else:
            coalesced.append(part)
    return ctx.mk_concat(*coalesced)


def _simplify_bv_eq(ctx: Context, lhs: Expr, rhs: Expr) -> Expr:
    while lhs is not rhs:
        if isinstance(lhs, Const) and not isinstance(rhs, Const):
            lhs, rhs = rhs, lhs
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            return ctx.mk_bool_val(lhs is rhs)

        if isinstance(rhs, Const):
            assert isinstance(rhs.value, int)
            assert not isinstance(rhs.value, bool)
            c2 = rhs.value
            w = rhs.sort.size
            mask = _bv_mask(w)
            if isinstance(lhs, App):
                k = lhs.decl.kind
                if k is DeclKind.BV_NOT:
                    lhs = lhs.args[0]
                    rhs = ctx.mk_bv_val((~c2) & mask, w)
                    continue
                if k is DeclKind.BV_NEG:
                    lhs = lhs.args[0]
                    rhs = ctx.mk_bv_val((-c2) & mask, w)
                    continue
                if (
                    k is DeclKind.BV_ADD
                    and len(lhs.args) >= 2
                    and isinstance(lhs.args[-1], Const)
                ):
                    c1 = lhs.args[-1].value
                    assert isinstance(c1, int)
                    assert not isinstance(c1, bool)
                    lhs = (
                        lhs.args[0]
                        if len(lhs.args) == 2
                        else ctx.mk_bv_add(*lhs.args[:-1])
                    )
                    rhs = ctx.mk_bv_val((c2 - c1) & mask, w)
                    continue
                if k is DeclKind.BV_SUB and isinstance(lhs.args[1], Const):
                    c1 = lhs.args[1].value
                    assert isinstance(c1, int)
                    assert not isinstance(c1, bool)
                    lhs = lhs.args[0]
                    rhs = ctx.mk_bv_val((c2 + c1) & mask, w)
                    continue
                if k is DeclKind.BV_SUB and isinstance(lhs.args[0], Const):
                    c1 = lhs.args[0].value
                    assert isinstance(c1, int)
                    assert not isinstance(c1, bool)
                    lhs = lhs.args[1]
                    rhs = ctx.mk_bv_val((c1 - c2) & mask, w)
                    continue
                if (
                    k is DeclKind.BV_XOR
                    and len(lhs.args) >= 2
                    and isinstance(lhs.args[-1], Const)
                ):
                    c1 = lhs.args[-1].value
                    assert isinstance(c1, int)
                    assert not isinstance(c1, bool)
                    lhs = (
                        lhs.args[0]
                        if len(lhs.args) == 2
                        else ctx.mk_bv_xor(*lhs.args[:-1])
                    )
                    rhs = ctx.mk_bv_val(c2 ^ c1, w)
                    continue
                if k is DeclKind.BV_ZERO_EXT:
                    inner = lhs.args[0]
                    iw = inner.bv_size
                    if (c2 >> iw) != 0:
                        return ctx.mk_false()
                    lhs = inner
                    rhs = ctx.mk_bv_val(c2, iw)
                    continue
                if k is DeclKind.BV_SIGN_EXT:
                    inner = lhs.args[0]
                    iw = inner.bv_size
                    lo = c2 & _bv_mask(iw)
                    if c2 != (_bv_to_signed(lo, iw) & mask):
                        return ctx.mk_false()
                    lhs = inner
                    rhs = ctx.mk_bv_val(lo, iw)
                    continue
                if k is DeclKind.BV_CONCAT:
                    eqs: list[Expr] = []
                    shift = 0
                    for part in reversed(lhs.args):
                        pw = part.bv_size
                        chunk = (c2 >> shift) & _bv_mask(pw)
                        eqs.append(_simplify_bv_eq(ctx, part, ctx.mk_bv_val(chunk, pw)))
                        shift += pw
                    eqs.reverse()
                    return ctx.mk_and(*eqs)

        if (
            isinstance(lhs, App)
            and isinstance(rhs, App)
            and lhs.decl.kind is DeclKind.BV_CONCAT
            and rhs.decl.kind is DeclKind.BV_CONCAT
            and len(lhs.args) == len(rhs.args)
            and all(a.sort is b.sort for a, b in zip(lhs.args, rhs.args, strict=True))
        ):
            return ctx.mk_and(
                *(
                    _simplify_bv_eq(ctx, a, b)
                    for a, b in zip(lhs.args, rhs.args, strict=True)
                )
            )
        break

    return ctx.mk_eq(lhs, rhs)


def _simplify_bv_cmp(ctx: Context, kind: DeclKind, lhs: Expr, rhs: Expr) -> Expr:
    rebuilt = ctx.mk_app(
        ctx.mk_decl(kind.value, (lhs.sort, rhs.sort), ctx.bool_sort, kind=kind),
        lhs,
        rhs,
    )
    if not isinstance(rebuilt, App):
        return rebuilt
    width = lhs.bv_size
    mask = _bv_mask(width)
    smin = 1 << (width - 1)
    smax = smin - 1

    if isinstance(rhs, Const):
        assert isinstance(rhs.value, int)
        assert not isinstance(rhs.value, bool)
        c = rhs.value
        if kind is DeclKind.BV_ULT and c == 0:
            return ctx.mk_false()
        if kind is DeclKind.BV_ULE and c == mask:
            return ctx.mk_true()
        if kind is DeclKind.BV_UGT and c == mask:
            return ctx.mk_false()
        if kind is DeclKind.BV_UGE and c == 0:
            return ctx.mk_true()
        if kind is DeclKind.BV_SLT and c == smin:
            return ctx.mk_false()
        if kind is DeclKind.BV_SLE and c == smax:
            return ctx.mk_true()
        if kind is DeclKind.BV_SGT and c == smax:
            return ctx.mk_false()
        if kind is DeclKind.BV_SGE and c == smin:
            return ctx.mk_true()

    if isinstance(lhs, Const):
        assert isinstance(lhs.value, int)
        assert not isinstance(lhs.value, bool)
        c = lhs.value
        if kind is DeclKind.BV_ULE and c == 0:
            return ctx.mk_true()
        if kind is DeclKind.BV_UGT and c == 0:
            return ctx.mk_false()
        if kind is DeclKind.BV_UGE and c == mask:
            return ctx.mk_true()
        if kind is DeclKind.BV_ULT and c == mask:
            return ctx.mk_false()
        if kind is DeclKind.BV_SLE and c == smin:
            return ctx.mk_true()
        if kind is DeclKind.BV_SGT and c == smin:
            return ctx.mk_false()
        if kind is DeclKind.BV_SGE and c == smax:
            return ctx.mk_true()
        if kind is DeclKind.BV_SLT and c == smax:
            return ctx.mk_false()

    return rebuilt


def bv_simplify(expr: Expr) -> Expr:
    """Apply word-level bit-vector simplification iteratively bottom-up."""
    ctx = expr.ctx
    memo: dict[Expr, Expr] = {}

    for node in iter_subexprs(expr):
        if isinstance(node, Quantifier):
            new_body = memo[node.body]
            new_pats = tuple(tuple(memo[term] for term in pat) for pat in node.patterns)
            memo[node] = ctx.mk_quantifier(
                node.is_forall,
                node.var_names,
                node.var_sorts,
                new_body,
                patterns=new_pats,
            )
            continue
        if (
            isinstance(node, (Const, BoundVar))
            or not isinstance(node, App)
            or node.is_const_symbol
        ):
            memo[node] = node
            continue

        args = [memo[arg] for arg in node.args]
        kind = node.decl.kind

        match kind:
            case DeclKind.BV_AND:
                arg_set = set(args)
                if any(
                    isinstance(a, App)
                    and a.decl.kind is DeclKind.BV_NOT
                    and a.args[0] in arg_set
                    for a in args
                ):
                    memo[node] = ctx.mk_bv_val(0, node.bv_size)
                else:
                    memo[node] = ctx.mk_bv_and(*args)
            case DeclKind.BV_OR:
                arg_set = set(args)
                if any(
                    isinstance(a, App)
                    and a.decl.kind is DeclKind.BV_NOT
                    and a.args[0] in arg_set
                    for a in args
                ):
                    w = node.bv_size
                    memo[node] = ctx.mk_bv_val(_bv_mask(w), w)
                else:
                    memo[node] = ctx.mk_bv_or(*args)
            case DeclKind.BV_XOR:
                res = ctx.mk_bv_xor(*args)
                w = node.bv_size
                mask = _bv_mask(w)
                if (
                    isinstance(res, App)
                    and res.decl.kind is DeclKind.BV_XOR
                    and len(res.args) == 2
                    and isinstance(res.args[1], Const)
                    and res.args[1].value == mask
                ):
                    res = ctx.mk_bv_not(res.args[0])
                elif (
                    isinstance(res, App)
                    and res.decl.kind is DeclKind.BV_XOR
                    and len(res.args) == 2
                    and _is_not_of_bv(res.args[0], res.args[1])
                ) or (
                    isinstance(res, App)
                    and res.decl.kind is DeclKind.BV_XOR
                    and len(res.args) == 2
                    and _is_not_of_bv(res.args[1], res.args[0])
                ):
                    res = ctx.mk_bv_val(mask, w)
                memo[node] = res
            case DeclKind.BV_UDIV:
                lhs, rhs = args
                w = lhs.bv_size
                if isinstance(rhs, Const) and rhs.value == 1:
                    memo[node] = lhs
                elif isinstance(rhs, Const) and rhs.value == 0:
                    memo[node] = ctx.mk_bv_val(_bv_mask(w), w)
                else:
                    memo[node] = ctx.mk_bv_udiv(lhs, rhs)
            case DeclKind.BV_UREM:
                lhs, rhs = args
                w = lhs.bv_size
                if isinstance(rhs, Const) and rhs.value == 1:
                    memo[node] = ctx.mk_bv_val(0, w)
                elif isinstance(rhs, Const) and rhs.value == 0:
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_urem(lhs, rhs)
            case DeclKind.BV_SDIV:
                lhs, rhs = args
                if isinstance(rhs, Const) and rhs.value == 1:
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_sdiv(lhs, rhs)
            case DeclKind.BV_SREM:
                lhs, rhs = args
                w = lhs.bv_size
                if isinstance(rhs, Const) and rhs.value == 1:
                    memo[node] = ctx.mk_bv_val(0, w)
                elif isinstance(rhs, Const) and rhs.value == 0:
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_srem(lhs, rhs)
            case DeclKind.BV_SMOD:
                lhs, rhs = args
                w = lhs.bv_size
                if isinstance(rhs, Const) and rhs.value == 1:
                    memo[node] = ctx.mk_bv_val(0, w)
                elif isinstance(rhs, Const) and rhs.value == 0:
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_smod(lhs, rhs)
            case DeclKind.BV_SHL:
                lhs, rhs = args
                w = lhs.bv_size
                if isinstance(rhs, Const):
                    assert isinstance(rhs.value, int)
                    assert not isinstance(rhs.value, bool)
                    if rhs.value == 0:
                        memo[node] = lhs
                    elif rhs.value >= w:
                        memo[node] = ctx.mk_bv_val(0, w)
                    else:
                        memo[node] = ctx.mk_bv_shl(lhs, rhs)
                elif isinstance(lhs, Const) and lhs.value == 0:
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_shl(lhs, rhs)
            case DeclKind.BV_LSHR:
                lhs, rhs = args
                w = lhs.bv_size
                if isinstance(rhs, Const):
                    assert isinstance(rhs.value, int)
                    assert not isinstance(rhs.value, bool)
                    if rhs.value == 0:
                        memo[node] = lhs
                    elif rhs.value >= w:
                        memo[node] = ctx.mk_bv_val(0, w)
                    else:
                        memo[node] = ctx.mk_bv_lshr(lhs, rhs)
                elif isinstance(lhs, Const) and lhs.value == 0:
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_lshr(lhs, rhs)
            case DeclKind.BV_ASHR:
                lhs, rhs = args
                w = lhs.bv_size
                if (isinstance(rhs, Const) and rhs.value == 0) or (
                    isinstance(lhs, Const) and lhs.value in (0, _bv_mask(w))
                ):
                    memo[node] = lhs
                else:
                    memo[node] = ctx.mk_bv_ashr(lhs, rhs)
            case DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                memo[node] = _simplify_extract(ctx, hi, lo, args[0])
            case DeclKind.BV_CONCAT:
                memo[node] = _simplify_concat(ctx, args)
            case (
                DeclKind.BV_ULT
                | DeclKind.BV_ULE
                | DeclKind.BV_UGT
                | DeclKind.BV_UGE
                | DeclKind.BV_SLT
                | DeclKind.BV_SLE
                | DeclKind.BV_SGT
                | DeclKind.BV_SGE
            ):
                memo[node] = _simplify_bv_cmp(ctx, kind, args[0], args[1])
            case DeclKind.EQ:
                if args[0].is_bv:
                    memo[node] = _simplify_bv_eq(ctx, args[0], args[1])
                else:
                    memo[node] = ctx.mk_eq(args[0], args[1])
            case _:
                memo[node] = ctx.mk_app(node.decl, *args)

    return memo[expr]


class BVSimplifyTactic:
    """Applies word-level :func:`bv_simplify` rewriting across a goal."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Simplify ``formulas`` using word-level bit-vector rewrites."""
        if not formulas:
            return TacticResult((), IdentityModelConverter())
        ctx = formulas[0].ctx
        kept: list[Expr] = []
        seen: set[Expr] = set()
        for formula in formulas:
            simplified = bv_simplify(formula)
            if simplified is ctx.false_expr:
                return TacticResult((ctx.false_expr,), IdentityModelConverter())
            if simplified is ctx.true_expr or simplified in seen:
                continue
            seen.add(simplified)
            kept.append(simplified)
        return TacticResult(tuple(kept), IdentityModelConverter())


class BitVecModelConverter:
    """Reconstructs eliminated ``BitVec`` declarations from blasted Boolean bits."""

    def __init__(
        self,
        ctx: Context,
        bv_const_bits: dict[FuncDecl, tuple[Expr, ...]],
        internal_decls: frozenset[FuncDecl],
    ) -> None:
        self._ctx = ctx
        self._bv_const_bits = dict(bv_const_bits)
        self._internal_decls = internal_decls

    def convert(self, model: Model) -> Model:
        """Rebuild bit-vector constant assignments and hide internal bit symbols."""
        if model.ctx is not self._ctx:
            msg = "Model belongs to a different Context than BitVecModelConverter"
            raise ValueError(msg)

        values = {
            decl: val for decl, val in model.items() if decl not in self._internal_decls
        }
        for bv_decl, bits in self._bv_const_bits.items():
            word_val = 0
            for idx, bit_expr in enumerate(bits):
                if model.eval_bool(bit_expr, model_completion=True):
                    word_val |= 1 << idx
            values[bv_decl] = word_val

        functions = {decl: model.func_interp(decl) for decl in model.func_decls()}
        universes = {sort: model.universe(sort) for sort in model.sorts()}
        return Model(self._ctx, values, functions=functions, universes=universes)


class BitBlaster:
    """Eager/on-demand bit-blaster translating ``BitVec`` terms & atoms to ``Bool``."""

    def __init__(
        self,
        ctx: Context,
        reserved_names: set[str] | None = None,
    ) -> None:
        self._ctx = ctx
        self._reserved_names: set[str] = (
            set(reserved_names) if reserved_names is not None else set()
        )
        self._term_bits: dict[Expr, tuple[Expr, ...]] = {}
        self._formula_cache: dict[Expr, Expr] = {}
        self._bv_const_bits: dict[FuncDecl, tuple[Expr, ...]] = {}
        self._internal_decls: set[FuncDecl] = set()
        self._udiv_cache: dict[
            tuple[Expr, Expr], tuple[tuple[Expr, ...], tuple[Expr, ...]]
        ] = {}
        self._sdiv_cache: dict[
            tuple[Expr, Expr], tuple[tuple[Expr, ...], tuple[Expr, ...]]
        ] = {}
        self._and_cache: dict[tuple[int, int], Expr] = {}
        self._or_cache: dict[tuple[int, int], Expr] = {}
        self._xor_cache: dict[tuple[int, int], Expr] = {}
        self._ite_cache: dict[tuple[int, int, int], Expr] = {}
        self._fa_cache: dict[tuple[int, int, int], tuple[Expr, Expr]] = {}

    @property
    def ctx(self) -> Context:
        """AST context targeted by this bit-blaster."""
        return self._ctx

    @property
    def bv_const_bits(self) -> dict[FuncDecl, tuple[Expr, ...]]:
        """Mapping from blasted 0-arity ``BitVec`` symbols to LSB-first bit exprs."""
        return self._bv_const_bits

    @property
    def internal_decls(self) -> set[FuncDecl]:
        """Fresh Boolean bit declarations synthesized for bit-vector leaves."""
        return self._internal_decls

    def register_reserved(self, expr: Expr) -> None:
        """Record user declaration names appearing in ``expr`` to avoid collisions."""
        for decl in collect_func_decls(expr):
            self._reserved_names.add(decl.name)

    def _alloc_leaf_bits(self, term: Expr) -> tuple[Expr, ...]:
        width = term.bv_size
        bits: list[Expr] = []
        for idx in range(width):
            name = f"__bv!{term.id}!{idx}"
            suffix = 0
            while name in self._reserved_names:
                suffix += 1
                name = f"__bv!{term.id}_{suffix}!{idx}"
            self._reserved_names.add(name)
            bit_app = self._ctx.mk_bool(name)
            self._internal_decls.add(bit_app.decl)
            bits.append(bit_app)
        result = tuple(bits)
        if isinstance(term, App) and term.is_const_symbol:
            self._bv_const_bits[term.decl] = result
        return result

    def _is_blasted_bool_node(self, node: Expr) -> bool:
        if not isinstance(node, App):
            return False
        kind = node.decl.kind
        if kind in _BV_CMP_KINDS:
            return True
        if (
            kind in (DeclKind.EQ, DeclKind.DISTINCT)
            and node.args
            and node.args[0].is_bv
        ):
            return True
        return bool(
            kind in _BOOL_CONN_KINDS
            and not (
                kind in (DeclKind.EQ, DeclKind.DISTINCT)
                and node.args
                and not node.args[0].is_bool
            )
        )

    def _ensure(self, root: Expr) -> None:
        stack: list[tuple[Expr, bool]] = [(root, False)]
        while stack:
            node, expanded = stack.pop()
            if node.is_bv:
                if node in self._term_bits:
                    continue
                if isinstance(node, Const):
                    assert isinstance(node.value, int)
                    assert not isinstance(node.value, bool)
                    val = node.value
                    self._term_bits[node] = tuple(
                        self._ctx.mk_bool_val(bool((val >> i) & 1))
                        for i in range(node.bv_size)
                    )
                    continue
                if not isinstance(node, App) or not (
                    node.decl.kind in _BV_OP_KINDS or node.decl.kind is DeclKind.ITE
                ):
                    self._term_bits[node] = self._alloc_leaf_bits(node)
                    continue
                if not expanded:
                    stack.append((node, True))
                    for arg in reversed(node.args):
                        stack.append((arg, False))
                    continue
                self._term_bits[node] = self._build_bv_node(node)
                continue

            if not node.is_bool:
                continue
            if node in self._formula_cache:
                continue
            if not self._is_blasted_bool_node(node):
                self._formula_cache[node] = node
                continue
            assert isinstance(node, App)
            if not expanded:
                stack.append((node, True))
                for arg in reversed(node.args):
                    stack.append((arg, False))
                continue
            self._formula_cache[node] = self._build_bool_node(node)

    def blast_term(self, term: Expr) -> tuple[Expr, ...]:
        """Return LSB-first Boolean AST bit tuple representing ``term``."""
        if term.ctx is not self._ctx:
            msg = f"Expr '{term}' belongs to a different Context"
            raise ValueError(msg)
        if not term.is_bv:
            msg = f"Expected BitVec term, got sort '{term.sort}'"
            raise TypeError(msg)
        self._ensure(term)
        return self._term_bits[term]

    def blast_bool(self, atom: Expr) -> Expr:
        """Blast a single ``BitVec`` comparison, equality, or disequality atom."""
        if atom.ctx is not self._ctx:
            msg = f"Expr '{atom}' belongs to a different Context"
            raise ValueError(msg)
        if not atom.is_bool:
            msg = f"Expected Bool atom, got sort '{atom.sort}'"
            raise TypeError(msg)
        return self.blast_formula(atom)

    def blast_eq(self, lhs: Expr, rhs: Expr) -> Expr:
        """Blast ``lhs == rhs`` between two ``BitVec`` terms into Boolean AST."""
        bl = self.blast_term(lhs)
        br = self.blast_term(rhs)
        return self._bits_eq(bl, br)

    def blast_formula(self, formula: Expr) -> Expr:
        """Blast all bit-vector subterms and atoms in Boolean formula ``formula``."""
        if formula.ctx is not self._ctx:
            msg = f"Expr '{formula}' belongs to a different Context"
            raise ValueError(msg)
        if not formula.is_bool:
            msg = f"Expected Bool formula, got sort '{formula.sort}'"
            raise TypeError(msg)
        self._ensure(formula)
        return self._formula_cache[formula]

    def eval_term_bits(
        self,
        term: Expr,
        bit_lookup: Callable[[Expr], bool],
    ) -> int:
        """Evaluate ``term`` under ``bit_lookup`` on leaf Bool atoms."""
        return self.eval_bits(self.blast_term(term), bit_lookup)

    def eval_bits(
        self,
        bits: Sequence[Expr],
        bit_lookup: Callable[[Expr], bool],
    ) -> int:
        """Evaluate an LSB-first bit-vector tuple under ``bit_lookup``."""
        memo: dict[Expr, bool] = {}
        stack: list[tuple[Expr, bool]] = [(bit, False) for bit in bits]

        while stack:
            node, expanded = stack.pop()
            if node in memo:
                continue
            if isinstance(node, Const):
                memo[node] = bool(node.value)
                continue
            if not isinstance(node, App) or not self._is_eval_connective(node):
                memo[node] = bit_lookup(node)
                continue
            if not expanded:
                stack.append((node, True))
                for arg in reversed(node.args):
                    if arg not in memo:
                        stack.append((arg, False))
                continue
            vals = [memo[arg] for arg in node.args]
            kind = node.decl.kind
            if kind is DeclKind.NOT:
                memo[node] = not vals[0]
            elif kind is DeclKind.AND:
                memo[node] = all(vals)
            elif kind is DeclKind.OR:
                memo[node] = any(vals)
            elif kind is DeclKind.IMPLIES:
                memo[node] = (not vals[0]) or vals[1]
            elif kind is DeclKind.XOR:
                memo[node] = vals[0] != vals[1]
            elif kind is DeclKind.EQ:
                memo[node] = vals[0] == vals[1]
            elif kind is DeclKind.DISTINCT:
                memo[node] = len(vals) <= 1 or (len(vals) == 2 and vals[0] != vals[1])
            elif kind is DeclKind.ITE:
                memo[node] = vals[1] if vals[0] else vals[2]

        out = 0
        for idx, bit in enumerate(bits):
            if memo[bit]:
                out |= 1 << idx
        return out

    @staticmethod
    def _is_eval_connective(node: App) -> bool:
        kind = node.decl.kind
        if kind in (
            DeclKind.NOT,
            DeclKind.AND,
            DeclKind.OR,
            DeclKind.IMPLIES,
            DeclKind.XOR,
        ):
            return True
        if kind in (DeclKind.EQ, DeclKind.DISTINCT, DeclKind.ITE):
            return not node.args or node.args[0].is_bool
        return False

    # ------------------------------------------------------------------
    # Gate-level bit-vector circuits (LSB-first)
    # ------------------------------------------------------------------

    def _const_bits(self, value: int, width: int) -> tuple[Expr, ...]:
        return tuple(
            self._ctx.mk_bool_val(bool((value >> i) & 1)) for i in range(width)
        )

    def _gate_not(self, a: Expr) -> Expr:
        ctx = self._ctx
        if a is ctx.false_expr:
            return ctx.true_expr
        if a is ctx.true_expr:
            return ctx.false_expr
        if isinstance(a, App) and a.decl.kind is DeclKind.NOT:
            return a.args[0]
        return ctx.mk_not(a)

    def _gate_and(self, a: Expr, b: Expr) -> Expr:
        ctx = self._ctx
        f = ctx.false_expr
        t = ctx.true_expr
        if a is f or b is f:
            return f
        if a is t:
            return b
        if b is t or a is b:
            return a
        if (isinstance(a, App) and a.decl.kind is DeclKind.NOT and a.args[0] is b) or (
            isinstance(b, App) and b.decl.kind is DeclKind.NOT and b.args[0] is a
        ):
            return f
        key = (a.id, b.id) if a.id <= b.id else (b.id, a.id)
        cached = self._and_cache.get(key)
        if cached is not None:
            return cached
        res = ctx.mk_and(a, b)
        self._and_cache[key] = res
        return res

    def _gate_or(self, a: Expr, b: Expr) -> Expr:
        ctx = self._ctx
        f = ctx.false_expr
        t = ctx.true_expr
        if a is t or b is t:
            return t
        if a is f:
            return b
        if b is f or a is b:
            return a
        if (isinstance(a, App) and a.decl.kind is DeclKind.NOT and a.args[0] is b) or (
            isinstance(b, App) and b.decl.kind is DeclKind.NOT and b.args[0] is a
        ):
            return t
        key = (a.id, b.id) if a.id <= b.id else (b.id, a.id)
        cached = self._or_cache.get(key)
        if cached is not None:
            return cached
        res = ctx.mk_or(a, b)
        self._or_cache[key] = res
        return res

    def _gate_xor(self, a: Expr, b: Expr) -> Expr:
        ctx = self._ctx
        f = ctx.false_expr
        t = ctx.true_expr
        if a is f:
            return b
        if b is f:
            return a
        if a is t:
            return self._gate_not(b)
        if b is t:
            return self._gate_not(a)
        if a is b:
            return f
        if (isinstance(a, App) and a.decl.kind is DeclKind.NOT and a.args[0] is b) or (
            isinstance(b, App) and b.decl.kind is DeclKind.NOT and b.args[0] is a
        ):
            return t
        key = (a.id, b.id) if a.id <= b.id else (b.id, a.id)
        cached = self._xor_cache.get(key)
        if cached is not None:
            return cached
        res = ctx.mk_xor(a, b)
        self._xor_cache[key] = res
        return res

    def _gate_ite(self, cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr:
        ctx = self._ctx
        f = ctx.false_expr
        t = ctx.true_expr
        if cond is t:
            return then_expr
        if cond is f:
            return else_expr
        if then_expr is else_expr:
            return then_expr
        if then_expr is t and else_expr is f:
            return cond
        if then_expr is f and else_expr is t:
            return self._gate_not(cond)
        if then_expr is f:
            return self._gate_and(self._gate_not(cond), else_expr)
        if else_expr is f:
            return self._gate_and(cond, then_expr)
        if then_expr is t:
            return self._gate_or(cond, else_expr)
        if else_expr is t:
            return self._gate_or(self._gate_not(cond), then_expr)
        key = (cond.id, then_expr.id, else_expr.id)
        cached = self._ite_cache.get(key)
        if cached is not None:
            return cached
        res = ctx.mk_ite(cond, then_expr, else_expr)
        self._ite_cache[key] = res
        return res

    def _half_adder(self, a: Expr, b: Expr) -> tuple[Expr, Expr]:
        f = self._ctx.false_expr
        t = self._ctx.true_expr
        if a is f:
            return b, f
        if b is f:
            return a, f
        if a is t:
            return self._gate_not(b), b
        if b is t:
            return self._gate_not(a), a
        if a is b:
            return f, a
        return self._gate_xor(a, b), self._gate_and(a, b)

    def _full_adder(self, a: Expr, b: Expr, cin: Expr) -> tuple[Expr, Expr]:
        f = self._ctx.false_expr
        if cin is f:
            return self._half_adder(a, b)
        if a is f:
            return self._half_adder(b, cin)
        if b is f:
            return self._half_adder(a, cin)
        if a is b:
            return cin, a
        if b is cin:
            return a, b
        if a is cin:
            return b, a
        ia, ib, ic = a.id, b.id, cin.id
        if ia > ib:
            ia, ib = ib, ia
        if ib > ic:
            ib, ic = ic, ib
        if ia > ib:
            ia, ib = ib, ia
        key = (ia, ib, ic)
        cached = self._fa_cache.get(key)
        if cached is not None:
            return cached
        ab_xor = self._gate_xor(a, b)
        s = self._gate_xor(ab_xor, cin)
        cout = self._gate_or(self._gate_and(a, b), self._gate_and(ab_xor, cin))
        res = (s, cout)
        self._fa_cache[key] = res
        return res

    def _mux_bits(
        self, cond: Expr, then_bits: Sequence[Expr], else_bits: Sequence[Expr]
    ) -> tuple[Expr, ...]:
        return tuple(
            self._gate_ite(cond, t_bit, e_bit)
            for t_bit, e_bit in zip(then_bits, else_bits, strict=True)
        )

    def _add_bits(
        self, a_bits: Sequence[Expr], b_bits: Sequence[Expr], carry_in: Expr
    ) -> tuple[tuple[Expr, ...], Expr]:
        sums: list[Expr] = []
        carry = carry_in
        for ai, bi in zip(a_bits, b_bits, strict=True):
            s, carry = self._full_adder(ai, bi, carry)
            sums.append(s)
        return tuple(sums), carry

    def _neg_bits(self, a_bits: Sequence[Expr]) -> tuple[Expr, ...]:
        if not a_bits:
            return ()
        ctx = self._ctx
        f = ctx.false_expr
        t = ctx.true_expr
        out: list[Expr] = [a_bits[0]]
        seen = a_bits[0]
        for bit in a_bits[1:]:
            if seen is f:
                out.append(bit)
                seen = bit
            elif seen is t:
                out.append(self._gate_not(bit))
            else:
                out.append(self._gate_xor(bit, seen))
                seen = self._gate_or(bit, seen)
        return tuple(out)

    def _sub_bits(
        self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]
    ) -> tuple[Expr, ...]:
        ctx = self._ctx
        return self._add_bits(
            a_bits, [self._gate_not(b) for b in b_bits], ctx.true_expr
        )[0]

    def _mul_bits(
        self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]
    ) -> tuple[Expr, ...]:
        f = self._ctx.false_expr
        width = len(a_bits)
        a_active = sum(1 for bit in a_bits if bit is not f)
        b_active = sum(1 for bit in b_bits if bit is not f)
        if a_active == 0 or b_active == 0:
            return (f,) * width
        if a_active < b_active:
            a_bits, b_bits = b_bits, a_bits

        acc: list[Expr] | None = None
        for i, bi in enumerate(b_bits):
            if bi is f:
                continue
            row = [self._gate_and(a_bits[j], bi) for j in range(width - i)]
            if acc is None:
                acc = [f] * i + row
                continue
            if not row:
                continue
            sum_slice, _ = self._add_bits(acc[i:], row, f)
            acc[i:] = sum_slice
        assert acc is not None
        return tuple(acc)

    def _shl_bits(
        self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]
    ) -> tuple[Expr, ...]:
        ctx = self._ctx
        f = ctx.false_expr
        width = len(a_bits)
        stages = (width - 1).bit_length()
        cur = list(a_bits)
        for stage in range(stages):
            shift = 1 << stage
            ctrl = b_bits[stage]
            if ctrl is f:
                continue
            cur = [
                self._gate_ite(
                    ctrl,
                    cur[idx - shift] if idx >= shift else f,
                    cur[idx],
                )
                for idx in range(width)
            ]
        if stages < width:
            high_or = ctx.mk_or(*b_bits[stages:])
            if high_or is not f:
                not_high = self._gate_not(high_or)
                cur = [self._gate_and(not_high, bit) for bit in cur]
        return tuple(cur)

    def _shr_bits(
        self, a_bits: Sequence[Expr], b_bits: Sequence[Expr], *, arithmetic: bool
    ) -> tuple[Expr, ...]:
        ctx = self._ctx
        f = ctx.false_expr
        width = len(a_bits)
        stages = (width - 1).bit_length()
        fill = a_bits[-1] if arithmetic else f
        cur = list(a_bits)
        for stage in range(stages):
            shift = 1 << stage
            ctrl = b_bits[stage]
            if ctrl is f:
                continue
            cur = [
                self._gate_ite(
                    ctrl,
                    cur[idx + shift] if idx + shift < width else fill,
                    cur[idx],
                )
                for idx in range(width)
            ]
        if stages < width:
            high_or = ctx.mk_or(*b_bits[stages:])
            if high_or is not f:
                cur = [self._gate_ite(high_or, fill, bit) for bit in cur]
        return tuple(cur)

    def _udiv_urem_bits(
        self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]
    ) -> tuple[tuple[Expr, ...], tuple[Expr, ...]]:
        ctx = self._ctx
        f = ctx.false_expr
        t = ctx.true_expr
        width = len(a_bits)
        b_is_zero = self._gate_not(ctx.mk_or(*b_bits))
        neg_b_ext = (*(self._gate_not(b) for b in b_bits), t)

        rem: list[Expr] = [f] * width
        quot: list[Expr] = [f] * width
        for step in range(width - 1, -1, -1):
            rem_ext = [a_bits[step], *rem]
            diff, borrow_inv = self._add_bits(rem_ext, neg_b_ext, t)
            quot[step] = borrow_inv
            rem = [
                self._gate_ite(borrow_inv, diff[k], rem_ext[k]) for k in range(width)
            ]

        quot_final = tuple(self._gate_ite(b_is_zero, t, q) for q in quot)
        rem_final = tuple(
            self._gate_ite(b_is_zero, a_bit, r_bit)
            for a_bit, r_bit in zip(a_bits, rem, strict=True)
        )
        return quot_final, rem_final

    def _udiv_rem_for_pair(
        self, lhs: Expr, rhs: Expr
    ) -> tuple[tuple[Expr, ...], tuple[Expr, ...]]:
        key = (lhs, rhs)
        cached = self._udiv_cache.get(key)
        if cached is not None:
            return cached
        res = self._udiv_urem_bits(self._term_bits[lhs], self._term_bits[rhs])
        self._udiv_cache[key] = res
        return res

    def _sdiv_rem_for_pair(
        self, lhs: Expr, rhs: Expr
    ) -> tuple[tuple[Expr, ...], tuple[Expr, ...], tuple[Expr, ...], Expr, Expr]:
        a_bits = self._term_bits[lhs]
        b_bits = self._term_bits[rhs]
        ma, mb = a_bits[-1], b_bits[-1]
        key = (lhs, rhs)
        cached = self._sdiv_cache.get(key)
        if cached is not None:
            u_q, u_r = cached
            return u_q, u_r, b_bits, ma, mb
        abs_a = self._mux_bits(ma, self._neg_bits(a_bits), a_bits)
        abs_b = self._mux_bits(mb, self._neg_bits(b_bits), b_bits)
        u_q, u_r = self._udiv_urem_bits(abs_a, abs_b)
        self._sdiv_cache[key] = (u_q, u_r)
        return u_q, u_r, b_bits, ma, mb

    def _ult_bits(self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]) -> Expr:
        borrow = self._ctx.false_expr
        for ai, bi in zip(a_bits, b_bits, strict=True):
            if ai is bi:
                continue
            na = self._gate_not(ai)
            borrow = self._gate_or(
                self._gate_and(na, bi),
                self._gate_and(self._gate_or(na, bi), borrow),
            )
        return borrow

    def _slt_bits(self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]) -> Expr:
        ctx = self._ctx
        a_flipped = [*a_bits[:-1], ctx.mk_not(a_bits[-1])]
        b_flipped = [*b_bits[:-1], ctx.mk_not(b_bits[-1])]
        return self._ult_bits(a_flipped, b_flipped)

    def _bits_eq(self, a_bits: Sequence[Expr], b_bits: Sequence[Expr]) -> Expr:
        ctx = self._ctx
        return ctx.mk_and(
            *(ctx.mk_eq(a, b) for a, b in zip(a_bits, b_bits, strict=True))
        )

    def _build_bv_node(self, node: App) -> tuple[Expr, ...]:
        ctx = self._ctx
        kind = node.decl.kind
        args = node.args
        match kind:
            case DeclKind.BV_NOT:
                return tuple(ctx.mk_not(b) for b in self._term_bits[args[0]])
            case DeclKind.BV_AND:
                tuples = [self._term_bits[arg] for arg in args]
                return tuple(ctx.mk_and(*col) for col in zip(*tuples, strict=True))
            case DeclKind.BV_OR:
                tuples = [self._term_bits[arg] for arg in args]
                return tuple(ctx.mk_or(*col) for col in zip(*tuples, strict=True))
            case DeclKind.BV_XOR:
                acc = self._term_bits[args[0]]
                for arg in args[1:]:
                    nxt = self._term_bits[arg]
                    acc = tuple(ctx.mk_xor(a, b) for a, b in zip(acc, nxt, strict=True))
                return acc
            case DeclKind.BV_NEG:
                return self._neg_bits(self._term_bits[args[0]])
            case DeclKind.BV_ADD:
                acc = self._term_bits[args[0]]
                for arg in args[1:]:
                    acc, _ = self._add_bits(acc, self._term_bits[arg], ctx.mk_false())
                return acc
            case DeclKind.BV_SUB:
                return self._sub_bits(
                    self._term_bits[args[0]], self._term_bits[args[1]]
                )
            case DeclKind.BV_MUL:
                acc = self._term_bits[args[0]]
                for arg in args[1:]:
                    acc = self._mul_bits(acc, self._term_bits[arg])
                return acc
            case DeclKind.BV_UDIV:
                return self._udiv_rem_for_pair(args[0], args[1])[0]
            case DeclKind.BV_UREM:
                return self._udiv_rem_for_pair(args[0], args[1])[1]
            case DeclKind.BV_SDIV:
                u_q, _, _, ma, mb = self._sdiv_rem_for_pair(args[0], args[1])
                return self._mux_bits(self._gate_xor(ma, mb), self._neg_bits(u_q), u_q)
            case DeclKind.BV_SREM:
                _, u_r, _, ma, _ = self._sdiv_rem_for_pair(args[0], args[1])
                return self._mux_bits(ma, self._neg_bits(u_r), u_r)
            case DeclKind.BV_SMOD:
                _, u_r, b_bits, ma, mb = self._sdiv_rem_for_pair(args[0], args[1])
                signed_u = self._mux_bits(ma, self._neg_bits(u_r), u_r)
                with_b = self._add_bits(signed_u, b_bits, ctx.false_expr)[0]
                adj = self._mux_bits(self._gate_xor(ma, mb), with_b, signed_u)
                u_nz = ctx.mk_or(*u_r)
                return tuple(self._gate_and(u_nz, bit) for bit in adj)
            case DeclKind.BV_SHL:
                return self._shl_bits(
                    self._term_bits[args[0]], self._term_bits[args[1]]
                )
            case DeclKind.BV_LSHR:
                return self._shr_bits(
                    self._term_bits[args[0]],
                    self._term_bits[args[1]],
                    arithmetic=False,
                )
            case DeclKind.BV_ASHR:
                return self._shr_bits(
                    self._term_bits[args[0]],
                    self._term_bits[args[1]],
                    arithmetic=True,
                )
            case DeclKind.BV_CONCAT:
                return tuple(
                    bit for part in reversed(args) for bit in self._term_bits[part]
                )
            case DeclKind.BV_EXTRACT:
                hi, lo = node.decl.params
                return self._term_bits[args[0]][lo : hi + 1]
            case DeclKind.BV_ZERO_EXT:
                n = node.decl.params[0]
                return self._term_bits[args[0]] + (ctx.mk_false(),) * n
            case DeclKind.BV_SIGN_EXT:
                n = node.decl.params[0]
                bits = self._term_bits[args[0]]
                return bits + (bits[-1],) * n
            case DeclKind.BV_ROTATE_LEFT:
                bits = self._term_bits[args[0]]
                width = len(bits)
                shift = node.decl.params[0] % width
                return tuple(bits[(i - shift) % width] for i in range(width))
            case DeclKind.BV_ROTATE_RIGHT:
                bits = self._term_bits[args[0]]
                width = len(bits)
                shift = node.decl.params[0] % width
                return tuple(bits[(i + shift) % width] for i in range(width))
            case DeclKind.BV_REPEAT:
                n = node.decl.params[0]
                return self._term_bits[args[0]] * n
            case DeclKind.ITE:
                cond_b = self._formula_cache[args[0]]
                return self._mux_bits(
                    cond_b, self._term_bits[args[1]], self._term_bits[args[2]]
                )
            case _:
                msg = f"Unsupported BV operator in BitBlaster: {kind}"
                raise TypeError(msg)

    def _build_bool_node(self, node: App) -> Expr:
        ctx = self._ctx
        kind = node.decl.kind
        args = node.args
        match kind:
            case DeclKind.NOT:
                return ctx.mk_not(self._formula_cache[args[0]])
            case DeclKind.AND:
                return ctx.mk_and(*(self._formula_cache[a] for a in args))
            case DeclKind.OR:
                return ctx.mk_or(*(self._formula_cache[a] for a in args))
            case DeclKind.IMPLIES:
                return ctx.mk_implies(
                    self._formula_cache[args[0]], self._formula_cache[args[1]]
                )
            case DeclKind.XOR:
                return ctx.mk_xor(
                    self._formula_cache[args[0]], self._formula_cache[args[1]]
                )
            case DeclKind.EQ:
                if args[0].is_bv:
                    return self._bits_eq(
                        self._term_bits[args[0]], self._term_bits[args[1]]
                    )
                return ctx.mk_eq(
                    self._formula_cache[args[0]], self._formula_cache[args[1]]
                )
            case DeclKind.DISTINCT:
                if args and args[0].is_bv:
                    diffs: list[Expr] = []
                    for i in range(len(args)):
                        for j in range(i + 1, len(args)):
                            diffs.append(
                                ctx.mk_not(
                                    self._bits_eq(
                                        self._term_bits[args[i]],
                                        self._term_bits[args[j]],
                                    )
                                )
                            )
                    return ctx.mk_and(*diffs)
                return ctx.mk_distinct(*(self._formula_cache[a] for a in args))
            case DeclKind.ITE:
                return ctx.mk_ite(
                    self._formula_cache[args[0]],
                    self._formula_cache[args[1]],
                    self._formula_cache[args[2]],
                )
            case DeclKind.BV_ULT:
                return self._ult_bits(
                    self._term_bits[args[0]], self._term_bits[args[1]]
                )
            case DeclKind.BV_ULE:
                return ctx.mk_not(
                    self._ult_bits(self._term_bits[args[1]], self._term_bits[args[0]])
                )
            case DeclKind.BV_UGT:
                return self._ult_bits(
                    self._term_bits[args[1]], self._term_bits[args[0]]
                )
            case DeclKind.BV_UGE:
                return ctx.mk_not(
                    self._ult_bits(self._term_bits[args[0]], self._term_bits[args[1]])
                )
            case DeclKind.BV_SLT:
                return self._slt_bits(
                    self._term_bits[args[0]], self._term_bits[args[1]]
                )
            case DeclKind.BV_SLE:
                return ctx.mk_not(
                    self._slt_bits(self._term_bits[args[1]], self._term_bits[args[0]])
                )
            case DeclKind.BV_SGT:
                return self._slt_bits(
                    self._term_bits[args[1]], self._term_bits[args[0]]
                )
            case DeclKind.BV_SGE:
                return ctx.mk_not(
                    self._slt_bits(self._term_bits[args[0]], self._term_bits[args[1]])
                )
            case _:
                msg = f"Unsupported Boolean node in BitBlaster: {kind}"
                raise TypeError(msg)


def bitblast(expr: Expr) -> TacticResult:
    """Bit-blast a single ``Bool`` formula, returning blasted formula & converter."""
    return BitBlastTactic().apply((expr,))


class BitBlastTactic:
    """Eagerly bit-blasts bit-vector formulas into pure Boolean formulas."""

    def apply(self, formulas: Sequence[Expr]) -> TacticResult:
        """Transform ``formulas`` into pure ``Bool`` formulas + BV model converter."""
        if not formulas:
            return TacticResult((), IdentityModelConverter())
        ctx = formulas[0].ctx
        blaster = BitBlaster(ctx)
        for formula in formulas:
            blaster.register_reserved(formula)
        blasted = tuple(blaster.blast_formula(formula) for formula in formulas)
        converter = BitVecModelConverter(
            ctx,
            blaster.bv_const_bits,
            frozenset(blaster.internal_decls),
        )
        return TacticResult(blasted, converter)
