"""Explicit hash-consed AST :class:`Context` managing sorts, decls, and terms."""

import weakref
from collections.abc import Sequence
from fractions import Fraction

import unsat.syntax.expr as _expr_mod
from unsat.syntax.bv_eval import _bv_mask
from unsat.syntax.context_arith import (
    build_abs,
    build_add,
    build_arith_cmp,
    build_div,
    build_divisible,
    build_idiv,
    build_is_int,
    build_mod,
    build_mul,
    build_neg,
    build_sub,
    build_to_int,
    build_to_real,
)
from unsat.syntax.context_bv import (
    build_bv_add,
    build_bv_and,
    build_bv_bin,
    build_bv_cmp,
    build_bv_mul,
    build_bv_neg,
    build_bv_not,
    build_bv_or,
    build_bv_sub,
    build_bv_xor,
    build_concat,
    build_const_array,
    build_extract,
    build_repeat,
    build_rotate_left,
    build_rotate_right,
    build_select,
    build_sign_ext,
    build_store,
    build_zero_ext,
)
from unsat.syntax.context_strings import (
    build_re_all,
    build_re_allchar,
    build_re_comp,
    build_re_concat,
    build_re_diff,
    build_re_inter,
    build_re_loop,
    build_re_none,
    build_re_opt,
    build_re_plus,
    build_re_power,
    build_re_range,
    build_re_star,
    build_re_union,
    build_str_at,
    build_str_cmp,
    build_str_concat,
    build_str_contains,
    build_str_from_code,
    build_str_from_int,
    build_str_in_re,
    build_str_indexof,
    build_str_is_digit,
    build_str_len,
    build_str_prefixof,
    build_str_replace,
    build_str_replace_all,
    build_str_substr,
    build_str_suffixof,
    build_str_to_code,
    build_str_to_int,
    build_str_to_re,
)
from unsat.syntax.expr import (
    App,
    BoundVar,
    Const,
    Expr,
    FuncDecl,
    Quantifier,
    Sort,
    _abstract_vars_impl,
    _is_not_of,
)
from unsat.syntax.kinds import DeclKind, SortKind
from unsat.syntax.str_eval import validate_smt2_string


class Context:
    """Explicit AST arena managing hash-consed sorts, declarations, and terms."""

    def __init__(self) -> None:
        self._next_id = 0
        self._sorts: weakref.WeakValueDictionary[tuple[object, ...], Sort] = weakref.WeakValueDictionary()
        self._decls: weakref.WeakValueDictionary[
            tuple[DeclKind, str, tuple[Sort, ...], Sort, tuple[int, ...]],
            FuncDecl,
        ] = weakref.WeakValueDictionary()
        self._exprs: weakref.WeakValueDictionary[tuple[object, ...], Expr] = weakref.WeakValueDictionary()
        self._bound_vars: weakref.WeakValueDictionary[tuple[int, int], BoundVar] = weakref.WeakValueDictionary()
        self._quantifiers: weakref.WeakValueDictionary[
            tuple[
                bool,
                tuple[str, ...],
                tuple[int, ...],
                int,
                tuple[tuple[int, ...], ...],
            ],
            Quantifier,
        ] = weakref.WeakValueDictionary()

        # Keep strong references to built-in sorts & Boolean singletons.
        self.bool_sort = self._intern_sort(SortKind.BOOL, "Bool")
        self.int_sort = self._intern_sort(SortKind.INT, "Int")
        self.real_sort = self._intern_sort(SortKind.REAL, "Real")
        self.string_sort = self._intern_sort(SortKind.STRING, "String")
        self.reglan_sort = self._intern_sort(SortKind.REGLAN, "RegLan")
        self.true_expr = self._intern_const(True, self.bool_sort)
        self.false_expr = self._intern_const(False, self.bool_sort)

    def _alloc_id(self) -> int:
        node_id = self._next_id
        self._next_id += 1
        return node_id

    def _intern_sort(
        self,
        kind: SortKind,
        name: str,
        *,
        bv_width: int | None = None,
        array_index: Sort | None = None,
        array_element: Sort | None = None,
    ) -> Sort:
        if kind is SortKind.BITVEC:
            key: tuple[object, ...] = (kind, bv_width)
        elif kind is SortKind.ARRAY:
            assert array_index is not None
            assert array_element is not None
            key = (kind, array_index.id, array_element.id)
        else:
            key = (kind, name)
        existing = self._sorts.get(key)
        if existing is not None:
            return existing
        sort = Sort(
            self._alloc_id(),
            self,
            name,
            kind,
            bv_width=bv_width,
            array_index=array_index,
            array_element=array_element,
        )
        self._sorts[key] = sort
        return sort

    def _intern_decl(
        self,
        kind: DeclKind,
        name: str,
        domain: tuple[Sort, ...],
        range_sort: Sort,
        params: tuple[int, ...] = (),
    ) -> FuncDecl:
        key = (kind, name, domain, range_sort, params)
        existing = self._decls.get(key)
        if existing is not None:
            return existing
        decl = FuncDecl(self._alloc_id(), self, name, domain, range_sort, kind, params=params)
        self._decls[key] = decl
        return decl

    def _intern_const(self, value: bool | int | Fraction | str, sort: Sort) -> Const:
        key: tuple[object, ...] = (Const, sort.id, type(value), value)
        existing = self._exprs.get(key)
        if existing is not None:
            assert isinstance(existing, Const)
            return existing
        expr = Const(self._alloc_id(), self, sort, value)
        self._exprs[key] = expr
        return expr

    def _intern_app(self, decl: FuncDecl, args: tuple[Expr, ...]) -> App:
        key: tuple[object, ...] = (App, decl.id, *(arg.id for arg in args))
        existing = self._exprs.get(key)
        if existing is not None:
            assert isinstance(existing, App)
            return existing
        expr = App(self._alloc_id(), self, decl.range_sort, decl, args)
        self._exprs[key] = expr
        return expr

    def _check_sort(self, sort: Sort) -> None:
        if sort.ctx is not self:
            msg = f"Sort '{sort}' belongs to a different Context"
            raise ValueError(msg)

    def _check_expr(self, expr: Expr) -> None:
        if expr.ctx is not self:
            msg = f"Expr '{expr}' belongs to a different Context"
            raise ValueError(msg)

    def _check_bool(self, expr: Expr) -> None:
        self._check_expr(expr)
        if not expr.is_bool:
            msg = f"Expected Bool expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _check_int(self, expr: Expr) -> None:
        self._check_expr(expr)
        if not expr.is_int:
            msg = f"Expected Int expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _check_real(self, expr: Expr) -> None:
        self._check_expr(expr)
        if not expr.is_real:
            msg = f"Expected Real expression, got sort '{expr.sort}'"
            raise TypeError(msg)

    def _check_arith(self, expr: Expr) -> Sort:
        self._check_expr(expr)
        if not expr.is_arith:
            msg = f"Expected Int or Real expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        return expr.sort

    def _check_bv(self, expr: Expr) -> int:
        self._check_expr(expr)
        if not expr.is_bv:
            msg = f"Expected BitVec expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        return expr.sort.size

    def _check_bv_pair(self, lhs: Expr, rhs: Expr, op_name: str) -> int:
        width = self._check_bv(lhs)
        self._check_expr(rhs)
        if lhs.sort is not rhs.sort:
            msg = f"Sort mismatch in {op_name}: '{lhs.sort}' vs '{rhs.sort}'"
            raise TypeError(msg)
        return width

    def _check_array(self, expr: Expr) -> Sort:
        self._check_expr(expr)
        if not expr.is_array:
            msg = f"Expected Array expression, got sort '{expr.sort}'"
            raise TypeError(msg)
        return expr.sort

    def mk_bool_sort(self) -> Sort:
        """Return this context's canonical ``Bool`` sort."""
        return self.bool_sort

    def mk_int_sort(self) -> Sort:
        """Return this context's canonical ``Int`` sort."""
        return self.int_sort

    def mk_real_sort(self) -> Sort:
        """Return this context's canonical ``Real`` sort."""
        return self.real_sort

    def mk_string_sort(self) -> Sort:
        """Return this context's canonical ``String`` sort."""
        return self.string_sort

    def mk_reglan_sort(self) -> Sort:
        """Return this context's canonical ``RegLan`` sort."""
        return self.reglan_sort

    def mk_bv_sort(self, width: int) -> Sort:
        """Create or retrieve the fixed-width ``(_ BitVec width)`` sort."""
        if isinstance(width, bool) or not isinstance(width, int) or width < 1:
            msg = f"BitVec width must be a positive int, got {width!r}"
            raise ValueError(msg)
        return self._intern_sort(SortKind.BITVEC, f"(_ BitVec {width})", bv_width=width)

    def mk_array_sort(self, index_sort: Sort, element_sort: Sort) -> Sort:
        """Create or retrieve ``(Array index_sort element_sort)``."""
        self._check_sort(index_sort)
        self._check_sort(element_sort)
        return self._intern_sort(
            SortKind.ARRAY,
            f"(Array {index_sort.name} {element_sort.name})",
            array_index=index_sort,
            array_element=element_sort,
        )

    def mk_uninterpreted_sort(self, name: str) -> Sort:
        """Create or retrieve a hash-consed uninterpreted sort."""
        if not name:
            msg = "Sort name cannot be empty"
            raise ValueError(msg)
        return self._intern_sort(SortKind.UNINTERPRETED, name)

    def mk_domain_val(self, sort: Sort, index: int) -> Const:
        """Create or retrieve a distinct domain-element constant for ``sort``."""
        self._check_sort(sort)
        if sort.kind is not SortKind.UNINTERPRETED:
            msg = f"Expected uninterpreted sort for domain value, got '{sort}'"
            raise TypeError(msg)
        if isinstance(index, bool) or index < 0:
            msg = f"Domain value index must be a non-negative int, got {index!r}"
            raise ValueError(msg)
        return self._intern_const(index, sort)

    def mk_int_val(self, value: int) -> Const:
        """Create or retrieve a hash-consed integer literal constant."""
        if isinstance(value, bool) or not isinstance(value, int):
            msg = f"Int constant value must be int, got {type(value).__name__}"
            raise TypeError(msg)
        return self._intern_const(value, self.int_sort)

    def mk_real_val(self, value: int | Fraction | str) -> Const:
        """Create or retrieve a hash-consed exact rational ``Real`` constant."""
        if isinstance(value, bool):
            msg = "Real constant value cannot be bool"
            raise TypeError(msg)
        if not isinstance(value, (int, Fraction, str)):
            msg = f"Real constant value must be int, Fraction, or str, got {type(value).__name__}"
            raise TypeError(msg)
        frac = Fraction(value)
        return self._intern_const(frac, self.real_sort)

    def mk_bv_val(self, value: int, width: int) -> Const:
        """Create or retrieve a hash-consed ``width``-bit ``BitVec`` constant."""
        if isinstance(value, bool) or not isinstance(value, int):
            msg = f"BitVec constant value must be int, got {type(value).__name__}"
            raise TypeError(msg)
        sort = self.mk_bv_sort(width)
        return self._intern_const(value & _bv_mask(width), sort)

    def mk_string_val(self, value: str) -> Const:
        """Create or retrieve a hash-consed ``String`` literal constant."""
        validate_smt2_string(value)
        return self._intern_const(value, self.string_sort)

    def mk_true(self) -> Const:
        """Return this context's canonical ``true`` literal."""
        return self.true_expr

    def mk_false(self) -> Const:
        """Return this context's canonical ``false`` literal."""
        return self.false_expr

    def mk_bool_val(self, value: bool) -> Const:
        """Return this context's canonical Boolean constant for ``value``."""
        return self.true_expr if value else self.false_expr

    def mk_decl(
        self,
        name: str,
        domain: Sequence[Sort],
        range_sort: Sort,
        *,
        kind: DeclKind = DeclKind.UNINTERPRETED,
    ) -> FuncDecl:
        """Create or retrieve a hash-consed function declaration."""
        if not name:
            msg = "Declaration name cannot be empty"
            raise ValueError(msg)
        for sort in domain:
            self._check_sort(sort)
        self._check_sort(range_sort)
        return self._intern_decl(kind, name, tuple(domain), range_sort)

    def mk_const(self, name: str, sort: Sort) -> App:
        """Create or retrieve a 0-arity symbolic constant of ``sort``."""
        self._check_sort(sort)
        decl = self.mk_decl(name, (), sort, kind=DeclKind.UNINTERPRETED)
        return self._intern_app(decl, ())

    def mk_bool(self, name: str) -> App:
        """Create or retrieve a 0-arity Boolean symbolic constant."""
        return self.mk_const(name, self.bool_sort)

    def mk_int(self, name: str) -> App:
        """Create or retrieve a 0-arity integer symbolic constant."""
        return self.mk_const(name, self.int_sort)

    def mk_real(self, name: str) -> App:
        """Create or retrieve a 0-arity real symbolic constant."""
        return self.mk_const(name, self.real_sort)

    def mk_bv(self, name: str, width: int) -> App:
        """Create or retrieve a 0-arity ``width``-bit bit-vector constant."""
        return self.mk_const(name, self.mk_bv_sort(width))

    def mk_array(self, name: str, index_sort: Sort, element_sort: Sort) -> App:
        """Create or retrieve a 0-arity array symbolic constant."""
        return self.mk_const(name, self.mk_array_sort(index_sort, element_sort))

    def mk_string(self, name: str) -> App:
        """Create or retrieve a 0-arity ``String`` symbolic constant."""
        return self.mk_const(name, self.string_sort)

    def mk_reglan(self, name: str) -> App:
        """Create or retrieve a 0-arity ``RegLan`` symbolic constant."""
        return self.mk_const(name, self.reglan_sort)

    def mk_app(self, decl: FuncDecl, *args: Expr) -> Expr:
        """Apply ``decl`` to ``args``, validating sorts and normalizing built-ins."""
        if decl.ctx is not self:
            msg = f"FuncDecl '{decl}' belongs to a different Context"
            raise ValueError(msg)
        if len(args) != decl.arity:
            msg = f"Arity mismatch for '{decl}': expected {decl.arity}, got {len(args)}"
            raise ValueError(msg)
        for i, (arg, expected_sort) in enumerate(zip(args, decl.domain, strict=True)):
            self._check_expr(arg)
            if arg.sort is not expected_sort:
                msg = f"Sort mismatch in argument {i} of '{decl}': expected '{expected_sort}', got '{arg.sort}'"
                raise TypeError(msg)

        match decl.kind:
            case DeclKind.NOT:
                return self.mk_not(args[0])
            case DeclKind.AND:
                return self.mk_and(*args)
            case DeclKind.OR:
                return self.mk_or(*args)
            case DeclKind.IMPLIES:
                return self.mk_implies(args[0], args[1])
            case DeclKind.XOR:
                return self.mk_xor(args[0], args[1])
            case DeclKind.EQ:
                return self.mk_eq(args[0], args[1])
            case DeclKind.DISTINCT:
                return self.mk_distinct(*args)
            case DeclKind.ITE:
                return self.mk_ite(args[0], args[1], args[2])
            case DeclKind.NEG:
                return self.mk_neg(args[0])
            case DeclKind.ADD:
                return self.mk_add(*args)
            case DeclKind.SUB:
                return self.mk_sub(args[0], args[1])
            case DeclKind.MUL:
                return self.mk_mul(*args)
            case DeclKind.DIV:
                return self.mk_div(args[0], args[1])
            case DeclKind.IDIV:
                return self.mk_idiv(args[0], args[1])
            case DeclKind.MOD:
                return self.mk_mod(args[0], args[1])
            case DeclKind.ABS:
                return self.mk_abs(args[0])
            case DeclKind.LT:
                return self.mk_lt(args[0], args[1])
            case DeclKind.LE:
                return self.mk_le(args[0], args[1])
            case DeclKind.GT:
                return self.mk_gt(args[0], args[1])
            case DeclKind.GE:
                return self.mk_ge(args[0], args[1])
            case DeclKind.TO_REAL:
                return self.mk_to_real(args[0])
            case DeclKind.TO_INT:
                return self.mk_to_int(args[0])
            case DeclKind.IS_INT:
                return self.mk_is_int(args[0])
            case DeclKind.DIVISIBLE:
                return self.mk_divisible(decl.params[0], args[0])
            case DeclKind.BV_NOT:
                return self.mk_bv_not(args[0])
            case DeclKind.BV_AND:
                return self.mk_bv_and(*args)
            case DeclKind.BV_OR:
                return self.mk_bv_or(*args)
            case DeclKind.BV_XOR:
                return self.mk_bv_xor(*args)
            case DeclKind.BV_NEG:
                return self.mk_bv_neg(args[0])
            case DeclKind.BV_ADD:
                return self.mk_bv_add(*args)
            case DeclKind.BV_SUB:
                return self.mk_bv_sub(args[0], args[1])
            case DeclKind.BV_MUL:
                return self.mk_bv_mul(*args)
            case DeclKind.BV_UDIV:
                return self.mk_bv_udiv(args[0], args[1])
            case DeclKind.BV_UREM:
                return self.mk_bv_urem(args[0], args[1])
            case DeclKind.BV_SDIV:
                return self.mk_bv_sdiv(args[0], args[1])
            case DeclKind.BV_SREM:
                return self.mk_bv_srem(args[0], args[1])
            case DeclKind.BV_SMOD:
                return self.mk_bv_smod(args[0], args[1])
            case DeclKind.BV_SHL:
                return self.mk_bv_shl(args[0], args[1])
            case DeclKind.BV_LSHR:
                return self.mk_bv_lshr(args[0], args[1])
            case DeclKind.BV_ASHR:
                return self.mk_bv_ashr(args[0], args[1])
            case DeclKind.BV_ULT:
                return self.mk_bv_ult(args[0], args[1])
            case DeclKind.BV_ULE:
                return self.mk_bv_ule(args[0], args[1])
            case DeclKind.BV_UGT:
                return self.mk_bv_ugt(args[0], args[1])
            case DeclKind.BV_UGE:
                return self.mk_bv_uge(args[0], args[1])
            case DeclKind.BV_SLT:
                return self.mk_bv_slt(args[0], args[1])
            case DeclKind.BV_SLE:
                return self.mk_bv_sle(args[0], args[1])
            case DeclKind.BV_SGT:
                return self.mk_bv_sgt(args[0], args[1])
            case DeclKind.BV_SGE:
                return self.mk_bv_sge(args[0], args[1])
            case DeclKind.BV_CONCAT:
                return self.mk_concat(*args)
            case DeclKind.BV_EXTRACT:
                return self.mk_extract(decl.params[0], decl.params[1], args[0])
            case DeclKind.BV_ZERO_EXT:
                return self.mk_zero_ext(decl.params[0], args[0])
            case DeclKind.BV_SIGN_EXT:
                return self.mk_sign_ext(decl.params[0], args[0])
            case DeclKind.BV_ROTATE_LEFT:
                return self.mk_rotate_left(decl.params[0], args[0])
            case DeclKind.BV_ROTATE_RIGHT:
                return self.mk_rotate_right(decl.params[0], args[0])
            case DeclKind.BV_REPEAT:
                return self.mk_repeat(decl.params[0], args[0])
            case DeclKind.SELECT:
                return self.mk_select(args[0], args[1])
            case DeclKind.STORE:
                return self.mk_store(args[0], args[1], args[2])
            case DeclKind.CONST_ARRAY:
                return self.mk_const_array(decl.range_sort.index_sort, args[0])
            case DeclKind.STR_CONCAT:
                return self.mk_str_concat(*args)
            case DeclKind.STR_LEN:
                return self.mk_str_len(args[0])
            case DeclKind.STR_AT:
                return self.mk_str_at(args[0], args[1])
            case DeclKind.STR_SUBSTR:
                return self.mk_str_substr(args[0], args[1], args[2])
            case DeclKind.STR_INDEXOF:
                return self.mk_str_indexof(args[0], args[1], args[2])
            case DeclKind.STR_REPLACE:
                return self.mk_str_replace(args[0], args[1], args[2])
            case DeclKind.STR_REPLACE_ALL:
                return self.mk_str_replace_all(args[0], args[1], args[2])
            case DeclKind.STR_CONTAINS:
                return self.mk_str_contains(args[0], args[1])
            case DeclKind.STR_PREFIXOF:
                return self.mk_str_prefixof(args[0], args[1])
            case DeclKind.STR_SUFFIXOF:
                return self.mk_str_suffixof(args[0], args[1])
            case DeclKind.STR_LT:
                return self.mk_str_lt(args[0], args[1])
            case DeclKind.STR_LE:
                return self.mk_str_le(args[0], args[1])
            case DeclKind.STR_TO_INT:
                return self.mk_str_to_int(args[0])
            case DeclKind.STR_FROM_INT:
                return self.mk_str_from_int(args[0])
            case DeclKind.STR_TO_CODE:
                return self.mk_str_to_code(args[0])
            case DeclKind.STR_FROM_CODE:
                return self.mk_str_from_code(args[0])
            case DeclKind.STR_IS_DIGIT:
                return self.mk_str_is_digit(args[0])
            case DeclKind.STR_IN_RE:
                return self.mk_str_in_re(args[0], args[1])
            case DeclKind.STR_TO_RE:
                return self.mk_str_to_re(args[0])
            case DeclKind.RE_NONE:
                return self.mk_re_none()
            case DeclKind.RE_ALL:
                return self.mk_re_all()
            case DeclKind.RE_ALLCHAR:
                return self.mk_re_allchar()
            case DeclKind.RE_CONCAT:
                return self.mk_re_concat(*args)
            case DeclKind.RE_UNION:
                return self.mk_re_union(*args)
            case DeclKind.RE_INTER:
                return self.mk_re_inter(*args)
            case DeclKind.RE_STAR:
                return self.mk_re_star(args[0])
            case DeclKind.RE_PLUS:
                return self.mk_re_plus(args[0])
            case DeclKind.RE_OPT:
                return self.mk_re_opt(args[0])
            case DeclKind.RE_RANGE:
                return self.mk_re_range(args[0], args[1])
            case DeclKind.RE_COMP:
                return self.mk_re_comp(args[0])
            case DeclKind.RE_DIFF:
                return self.mk_re_diff(args[0], args[1])
            case DeclKind.RE_POWER:
                return self.mk_re_power(decl.params[0], args[0])
            case DeclKind.RE_LOOP:
                return self.mk_re_loop(decl.params[0], decl.params[1], args[0])
            case DeclKind.UNINTERPRETED:
                return self._intern_app(decl, tuple(args))

    # ------------------------------------------------------------------
    # Boolean constructors
    # ------------------------------------------------------------------

    def mk_not(self, arg: Expr) -> Expr:
        """Build a normalized logical negation."""
        self._check_bool(arg)
        if isinstance(arg, Const):
            return self.mk_bool_val(not arg.value)
        if isinstance(arg, App) and arg.decl.kind is DeclKind.NOT:
            return arg.args[0]
        decl = self._intern_decl(DeclKind.NOT, "not", (self.bool_sort,), self.bool_sort)
        return self._intern_app(decl, (arg,))

    def mk_and(self, *args: Expr) -> Expr:
        """Build a normalized logical conjunction."""
        flattened: list[Expr] = []
        for arg in args:
            self._check_bool(arg)
            if isinstance(arg, App) and arg.decl.kind is DeclKind.AND:
                flattened.extend(arg.args)
            else:
                flattened.append(arg)

        if any(arg is self.false_expr for arg in flattened):
            return self.false_expr

        unique = list(dict.fromkeys(arg for arg in flattened if arg is not self.true_expr))
        unique_set = set(unique)
        for item in unique:
            if isinstance(item, App) and item.decl.kind is DeclKind.NOT and item.args[0] in unique_set:
                return self.false_expr

        if not unique:
            return self.true_expr
        if len(unique) == 1:
            return unique[0]

        decl = self._intern_decl(
            DeclKind.AND,
            "and",
            (self.bool_sort,) * len(unique),
            self.bool_sort,
        )
        return self._intern_app(decl, tuple(unique))

    def mk_or(self, *args: Expr) -> Expr:
        """Build a normalized logical disjunction."""
        flattened: list[Expr] = []
        for arg in args:
            self._check_bool(arg)
            if isinstance(arg, App) and arg.decl.kind is DeclKind.OR:
                flattened.extend(arg.args)
            else:
                flattened.append(arg)

        if any(arg is self.true_expr for arg in flattened):
            return self.true_expr

        unique = list(dict.fromkeys(arg for arg in flattened if arg is not self.false_expr))
        unique_set = set(unique)
        for item in unique:
            if isinstance(item, App) and item.decl.kind is DeclKind.NOT and item.args[0] in unique_set:
                return self.true_expr

        if not unique:
            return self.false_expr
        if len(unique) == 1:
            return unique[0]

        decl = self._intern_decl(
            DeclKind.OR,
            "or",
            (self.bool_sort,) * len(unique),
            self.bool_sort,
        )
        return self._intern_app(decl, tuple(unique))

    def mk_implies(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized logical implication ``lhs => rhs``."""
        self._check_bool(lhs)
        self._check_bool(rhs)
        if lhs is self.false_expr or rhs is self.true_expr or lhs is rhs:
            return self.true_expr
        if lhs is self.true_expr:
            return rhs
        if rhs is self.false_expr:
            return self.mk_not(lhs)
        decl = self._intern_decl(
            DeclKind.IMPLIES,
            "=>",
            (self.bool_sort, self.bool_sort),
            self.bool_sort,
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_xor(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized exclusive-OR expression."""
        self._check_bool(lhs)
        self._check_bool(rhs)
        if lhs is rhs:
            return self.false_expr
        if _is_not_of(lhs, rhs) or _is_not_of(rhs, lhs):
            return self.true_expr
        if lhs is self.false_expr:
            return rhs
        if rhs is self.false_expr:
            return lhs
        if lhs is self.true_expr:
            return self.mk_not(rhs)
        if rhs is self.true_expr:
            return self.mk_not(lhs)
        decl = self._intern_decl(
            DeclKind.XOR,
            "xor",
            (self.bool_sort, self.bool_sort),
            self.bool_sort,
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_eq(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized equality expression ``lhs = rhs``."""
        self._check_expr(lhs)
        self._check_expr(rhs)
        if lhs.sort is not rhs.sort:
            msg = f"Sort mismatch in Eq: cannot compare '{lhs.sort}' and '{rhs.sort}'"
            raise TypeError(msg)
        if lhs is rhs:
            return self.true_expr
        if isinstance(lhs, Const) and isinstance(rhs, Const):
            return self.mk_bool_val(lhs.value == rhs.value)
        if _is_not_of(lhs, rhs) or _is_not_of(rhs, lhs):
            return self.false_expr
        decl = self._intern_decl(
            DeclKind.EQ,
            "=",
            (lhs.sort, rhs.sort),
            self.bool_sort,
        )
        return self._intern_app(decl, (lhs, rhs))

    def mk_distinct(self, *args: Expr) -> Expr:
        """Build a normalized pairwise-distinct constraint."""
        if not args:
            return self.true_expr
        first_sort = args[0].sort
        for i, arg in enumerate(args):
            self._check_expr(arg)
            if arg.sort is not first_sort:
                msg = f"Sort mismatch in argument {i} of Distinct: expected '{first_sort}', got '{arg.sort}'"
                raise TypeError(msg)
        if len(args) == 1:
            return self.true_expr
        if len(set(args)) < len(args):
            return self.false_expr
        if all(isinstance(arg, Const) for arg in args):
            return self.true_expr

        decl = self._intern_decl(
            DeclKind.DISTINCT,
            "distinct",
            (first_sort,) * len(args),
            self.bool_sort,
        )
        return self._intern_app(decl, tuple(args))

    def mk_ite(self, cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr:
        """Build a normalized if-then-else expression."""
        self._check_bool(cond)
        self._check_expr(then_branch)
        self._check_expr(else_branch)
        if then_branch.sort is not else_branch.sort:
            msg = f"Sort mismatch in Ite branches: '{then_branch.sort}' vs '{else_branch.sort}'"
            raise TypeError(msg)
        if cond is self.true_expr:
            return then_branch
        if cond is self.false_expr:
            return else_branch
        if then_branch is else_branch:
            return then_branch
        branch_sort = then_branch.sort
        decl = self._intern_decl(
            DeclKind.ITE,
            "ite",
            (self.bool_sort, branch_sort, branch_sort),
            branch_sort,
        )
        return self._intern_app(decl, (cond, then_branch, else_branch))

    # ------------------------------------------------------------------
    # Arithmetic constructors
    # ------------------------------------------------------------------

    def mk_to_real(self, arg: Expr) -> Expr:
        """Convert an ``Int`` expression to ``Real`` via ``to_real``."""
        return build_to_real(self, arg)

    def mk_to_int(self, arg: Expr) -> Expr:
        """Convert a ``Real`` expression to ``Int`` via ``to_int``."""
        return build_to_int(self, arg)

    def mk_is_int(self, arg: Expr) -> Expr:
        """Build integrality predicate ``(is_int arg)``."""
        return build_is_int(self, arg)

    def mk_abs(self, arg: Expr) -> Expr:
        """Build integer absolute value ``(abs arg)``."""
        return build_abs(self, arg)

    def mk_idiv(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build Euclidean integer division ``(div lhs rhs)``."""
        return build_idiv(self, lhs, rhs)

    def mk_mod(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build Euclidean integer remainder ``(mod lhs rhs)``."""
        return build_mod(self, lhs, rhs)

    def mk_divisible(self, n: int, arg: Expr) -> Expr:
        """Build divisibility predicate ``((_ divisible n) arg)``."""
        return build_divisible(self, n, arg)

    def mk_neg(self, arg: Expr) -> Expr:
        """Build a normalized arithmetic negation."""
        return build_neg(self, arg)

    def mk_add(self, *args: Expr) -> Expr:
        """Build a normalized n-ary arithmetic sum."""
        return build_add(self, *args)

    def mk_sub(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized arithmetic difference ``lhs - rhs``."""
        return build_sub(self, lhs, rhs)

    def mk_mul(self, *args: Expr) -> Expr:
        """Build a normalized arithmetic product."""
        return build_mul(self, *args)

    def mk_div(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized ``Real`` division ``lhs / rhs``."""
        return build_div(self, lhs, rhs)

    def mk_lt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized strict less-than inequality ``lhs < rhs``."""
        return build_arith_cmp(self, DeclKind.LT, lhs, rhs)

    def mk_le(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized less-than-or-equal inequality ``lhs <= rhs``."""
        return build_arith_cmp(self, DeclKind.LE, lhs, rhs)

    def mk_gt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized strict greater-than inequality ``lhs > rhs``."""
        return build_arith_cmp(self, DeclKind.GT, lhs, rhs)

    def mk_ge(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build a normalized greater-than-or-equal inequality ``lhs >= rhs``."""
        return build_arith_cmp(self, DeclKind.GE, lhs, rhs)

    # ------------------------------------------------------------------
    # Bit-vector & Array constructors
    # ------------------------------------------------------------------

    def mk_bv_not(self, arg: Expr) -> Expr:
        """Build bitwise negation ``(bvnot arg)``."""
        return build_bv_not(self, arg)

    def mk_bv_neg(self, arg: Expr) -> Expr:
        """Build two's-complement negation ``(bvneg arg)``."""
        return build_bv_neg(self, arg)

    def mk_bv_and(self, *args: Expr) -> Expr:
        """Build bitwise conjunction ``(bvand ...)``."""
        return build_bv_and(self, *args)

    def mk_bv_or(self, *args: Expr) -> Expr:
        """Build bitwise disjunction ``(bvor ...)``."""
        return build_bv_or(self, *args)

    def mk_bv_xor(self, *args: Expr) -> Expr:
        """Build bitwise exclusive-OR ``(bvxor ...)``."""
        return build_bv_xor(self, *args)

    def mk_bv_add(self, *args: Expr) -> Expr:
        """Build modular bit-vector addition ``(bvadd ...)``."""
        return build_bv_add(self, *args)

    def mk_bv_sub(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build modular bit-vector subtraction ``(bvsub lhs rhs)``."""
        return build_bv_sub(self, lhs, rhs)

    def mk_bv_mul(self, *args: Expr) -> Expr:
        """Build modular bit-vector multiplication ``(bvmul ...)``."""
        return build_bv_mul(self, *args)

    def mk_bv_udiv(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned bit-vector division ``(bvudiv lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_UDIV, lhs, rhs)

    def mk_bv_urem(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned bit-vector remainder ``(bvurem lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_UREM, lhs, rhs)

    def mk_bv_sdiv(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed two's-complement division ``(bvsdiv lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_SDIV, lhs, rhs)

    def mk_bv_srem(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed truncation remainder ``(bvsrem lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_SREM, lhs, rhs)

    def mk_bv_smod(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed floor-divisor modulo ``(bvsmod lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_SMOD, lhs, rhs)

    def mk_bv_shl(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build logical left shift ``(bvshl lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_SHL, lhs, rhs)

    def mk_bv_lshr(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build logical right shift ``(bvlshr lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_LSHR, lhs, rhs)

    def mk_bv_ashr(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build arithmetic right shift ``(bvashr lhs rhs)``."""
        return build_bv_bin(self, DeclKind.BV_ASHR, lhs, rhs)

    def mk_bv_ult(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned less-than comparison ``(bvult lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_ULT, lhs, rhs)

    def mk_bv_ule(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned less-or-equal comparison ``(bvule lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_ULE, lhs, rhs)

    def mk_bv_ugt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned greater-than comparison ``(bvugt lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_UGT, lhs, rhs)

    def mk_bv_uge(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build unsigned greater-or-equal comparison ``(bvuge lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_UGE, lhs, rhs)

    def mk_bv_slt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed less-than comparison ``(bvslt lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_SLT, lhs, rhs)

    def mk_bv_sle(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed less-or-equal comparison ``(bvsle lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_SLE, lhs, rhs)

    def mk_bv_sgt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed greater-than comparison ``(bvsgt lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_SGT, lhs, rhs)

    def mk_bv_sge(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build signed greater-or-equal comparison ``(bvsge lhs rhs)``."""
        return build_bv_cmp(self, DeclKind.BV_SGE, lhs, rhs)

    def mk_concat(self, *args: Expr) -> Expr:
        """Concatenate bit-vectors from most-significant to least-significant."""
        return build_concat(self, *args)

    def mk_extract(self, high: int, low: int, arg: Expr) -> Expr:
        """Extract bits ``[high:low]`` (inclusive, 0 = LSB) from ``arg``."""
        return build_extract(self, high, low, arg)

    def mk_zero_ext(self, n: int, arg: Expr) -> Expr:
        """Zero-extend bit-vector ``arg`` by ``n`` high-order zero bits."""
        return build_zero_ext(self, n, arg)

    def mk_sign_ext(self, n: int, arg: Expr) -> Expr:
        """Sign-extend bit-vector ``arg`` by ``n`` high-order copies of its MSB."""
        return build_sign_ext(self, n, arg)

    def mk_rotate_left(self, n: int, arg: Expr) -> Expr:
        """Rotate bit-vector ``arg`` left by ``n`` bits."""
        return build_rotate_left(self, n, arg)

    def mk_rotate_right(self, n: int, arg: Expr) -> Expr:
        """Rotate bit-vector ``arg`` right by ``n`` bits."""
        return build_rotate_right(self, n, arg)

    def mk_repeat(self, n: int, arg: Expr) -> Expr:
        """Concatenate ``n >= 1`` copies of bit-vector ``arg``."""
        return build_repeat(self, n, arg)

    def mk_select(self, array: Expr, index: Expr) -> Expr:
        """Read element at ``index`` from ``array``."""
        return build_select(self, array, index)

    def mk_store(self, array: Expr, index: Expr, value: Expr) -> Expr:
        """Write ``value`` at ``index`` in ``array``, returning a new array."""
        return build_store(self, array, index, value)

    def mk_const_array(self, index_sort: Sort, value: Expr) -> App:
        """Construct constant array mapping every ``index_sort`` key to ``value``."""
        return build_const_array(self, index_sort, value)

    # ------------------------------------------------------------------
    # String & Regular-Expression constructors
    # ------------------------------------------------------------------

    def mk_str_concat(self, *args: Expr) -> Expr:
        """Build normalized string concatenation ``(str.++ ...)``."""
        return build_str_concat(self, *args)

    def mk_str_len(self, arg: Expr) -> Expr:
        """Build ``(str.len arg)``."""
        return build_str_len(self, arg)

    def mk_str_at(self, s: Expr, idx: Expr) -> Expr:
        """Build ``(str.at s idx)``."""
        return build_str_at(self, s, idx)

    def mk_str_substr(self, s: Expr, offset: Expr, length: Expr) -> Expr:
        """Build ``(str.substr s offset length)``."""
        return build_str_substr(self, s, offset, length)

    def mk_str_indexof(self, s: Expr, needle: Expr, offset: Expr) -> Expr:
        """Build ``(str.indexof s needle offset)``."""
        return build_str_indexof(self, s, needle, offset)

    def mk_str_replace(self, s: Expr, src: Expr, dst: Expr) -> Expr:
        """Build ``(str.replace s src dst)``."""
        return build_str_replace(self, s, src, dst)

    def mk_str_replace_all(self, s: Expr, src: Expr, dst: Expr) -> Expr:
        """Build ``(str.replace_all s src dst)``."""
        return build_str_replace_all(self, s, src, dst)

    def mk_str_contains(self, s: Expr, needle: Expr) -> Expr:
        """Build ``(str.contains s needle)``."""
        return build_str_contains(self, s, needle)

    def mk_str_prefixof(self, prefix: Expr, s: Expr) -> Expr:
        """Build ``(str.prefixof prefix s)``."""
        return build_str_prefixof(self, prefix, s)

    def mk_str_suffixof(self, suffix: Expr, s: Expr) -> Expr:
        """Build ``(str.suffixof suffix s)``."""
        return build_str_suffixof(self, suffix, s)

    def mk_str_lt(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build lexicographic strict less-than ``(str.< lhs rhs)``."""
        return build_str_cmp(self, DeclKind.STR_LT, lhs, rhs)

    def mk_str_le(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build lexicographic less-or-equal ``(str.<= lhs rhs)``."""
        return build_str_cmp(self, DeclKind.STR_LE, lhs, rhs)

    def mk_str_to_int(self, s: Expr) -> Expr:
        """Build ``(str.to_int s)``."""
        return build_str_to_int(self, s)

    def mk_str_from_int(self, n: Expr) -> Expr:
        """Build ``(str.from_int n)``."""
        return build_str_from_int(self, n)

    def mk_str_to_code(self, s: Expr) -> Expr:
        """Build ``(str.to_code s)``."""
        return build_str_to_code(self, s)

    def mk_str_from_code(self, n: Expr) -> Expr:
        """Build ``(str.from_code n)``."""
        return build_str_from_code(self, n)

    def mk_str_is_digit(self, s: Expr) -> Expr:
        """Build ``(str.is_digit s)``."""
        return build_str_is_digit(self, s)

    def mk_str_in_re(self, s: Expr, reg: Expr) -> Expr:
        """Build regex membership ``(str.in_re s reg)``."""
        return build_str_in_re(self, s, reg)

    def mk_str_to_re(self, s: Expr) -> Expr:
        """Build singleton regex ``(str.to_re s)``."""
        return build_str_to_re(self, s)

    def mk_re_none(self) -> Expr:
        """Return the empty regular language ``re.none``."""
        return build_re_none(self)

    def mk_re_all(self) -> Expr:
        """Return the universal regular language ``re.all``."""
        return build_re_all(self)

    def mk_re_allchar(self) -> Expr:
        """Return the single-character wildcard regex ``re.allchar``."""
        return build_re_allchar(self)

    def mk_re_concat(self, *args: Expr) -> Expr:
        """Build regex concatenation ``(re.++ ...)``."""
        return build_re_concat(self, *args)

    def mk_re_union(self, *args: Expr) -> Expr:
        """Build regex union ``(re.union ...)``."""
        return build_re_union(self, *args)

    def mk_re_inter(self, *args: Expr) -> Expr:
        """Build regex intersection ``(re.inter ...)``."""
        return build_re_inter(self, *args)

    def mk_re_star(self, arg: Expr) -> Expr:
        """Build Kleene star ``(re.* arg)``."""
        return build_re_star(self, arg)

    def mk_re_plus(self, arg: Expr) -> Expr:
        """Build Kleene plus ``(re.+ arg)``."""
        return build_re_plus(self, arg)

    def mk_re_opt(self, arg: Expr) -> Expr:
        """Build optional regex ``(re.opt arg)``."""
        return build_re_opt(self, arg)

    def mk_re_range(self, lo: Expr, hi: Expr) -> Expr:
        """Build character-range regex ``(re.range lo hi)``."""
        return build_re_range(self, lo, hi)

    def mk_re_comp(self, arg: Expr) -> Expr:
        """Build regex complement ``(re.comp arg)``."""
        return build_re_comp(self, arg)

    def mk_re_diff(self, lhs: Expr, rhs: Expr) -> Expr:
        """Build regex difference ``(re.diff lhs rhs)``."""
        return build_re_diff(self, lhs, rhs)

    def mk_re_power(self, n: int, arg: Expr) -> Expr:
        """Build bounded regex repetition ``((_ re.^ n) arg)``."""
        return build_re_power(self, n, arg)

    def mk_re_loop(self, lo: int, hi: int, arg: Expr) -> Expr:
        """Build bounded regex loop ``((_ re.loop lo hi) arg)``."""
        return build_re_loop(self, lo, hi, arg)

    # ------------------------------------------------------------------
    # Quantifier constructors
    # ------------------------------------------------------------------

    def mk_bound_var(self, index: int, sort: Sort) -> BoundVar:
        """Create or retrieve a hash-consed De Bruijn bound variable."""
        if isinstance(index, bool) or not isinstance(index, int) or index < 0:
            msg = f"BoundVar index must be a non-negative int, got {index!r}"
            raise ValueError(msg)
        self._check_sort(sort)
        key = (index, sort.id)
        existing = self._bound_vars.get(key)
        if existing is not None:
            return existing
        bvar = BoundVar(self._alloc_id(), self, sort, index)
        self._bound_vars[key] = bvar
        return bvar

    def mk_quantifier(
        self,
        is_forall: bool,
        var_names: Sequence[str],
        var_sorts: Sequence[Sort],
        body: Expr,
        *,
        patterns: Sequence[Sequence[Expr]] = (),
    ) -> Expr:
        """Create or retrieve a hash-consed quantifier with explicit De Bruijn body."""
        if not var_sorts:
            msg = "Quantifier must bind at least one variable"
            raise ValueError(msg)
        if len(var_names) != len(var_sorts):
            msg = f"Quantifier name/sort count mismatch: {len(var_names)} names vs {len(var_sorts)} sorts"
            raise ValueError(msg)
        for name in var_names:
            if not name:
                msg = "Bound variable name cannot be empty"
                raise ValueError(msg)
        for sort in var_sorts:
            self._check_sort(sort)
        self._check_bool(body)

        norm_patterns: list[tuple[Expr, ...]] = []
        for pat in patterns:
            if not pat:
                msg = "Quantifier pattern cannot be empty"
                raise ValueError(msg)
            for term in pat:
                self._check_expr(term)
            norm_patterns.append(tuple(pat))

        if isinstance(body, Const):
            return body

        names_t = tuple(var_names)
        sorts_t = tuple(var_sorts)
        pats_t = tuple(norm_patterns)
        key = (
            is_forall,
            names_t,
            tuple(sort.id for sort in sorts_t),
            body.id,
            tuple(tuple(term.id for term in pat) for pat in pats_t),
        )
        existing = self._quantifiers.get(key)
        if existing is not None:
            return existing
        quant = Quantifier(
            self._alloc_id(),
            self,
            self.bool_sort,
            is_forall,
            names_t,
            sorts_t,
            body,
            pats_t,
        )
        self._quantifiers[key] = quant
        return quant

    def _mk_binder(
        self,
        is_forall: bool,
        bound_vars: Sequence[Expr],
        body: Expr,
        patterns: Sequence[Expr | Sequence[Expr]] = (),
    ) -> Expr:
        if not bound_vars:
            msg = "Quantifier must bind at least one variable"
            raise ValueError(msg)
        seen_decls: set[FuncDecl] = set()
        bound_apps: list[App] = []
        var_names: list[str] = []
        var_sorts: list[Sort] = []
        for var in bound_vars:
            self._check_expr(var)
            if not isinstance(var, App) or not var.is_const_symbol:
                msg = f"Bound quantifier variable must be a 0-arity constant, got '{var}'"
                raise TypeError(msg)
            if var.decl in seen_decls:
                msg = f"Duplicate bound variable '{var.name}' in quantifier binder"
                raise ValueError(msg)
            seen_decls.add(var.decl)
            bound_apps.append(var)
            var_names.append(var.name)
            var_sorts.append(var.sort)

        self._check_bool(body)
        norm_pats: list[tuple[Expr, ...]] = []
        for item in patterns:
            if isinstance(item, Expr):
                self._check_expr(item)
                norm_pats.append((item,))
            else:
                if not item:
                    msg = "Quantifier pattern cannot be empty"
                    raise ValueError(msg)
                for term in item:
                    self._check_expr(term)
                norm_pats.append(tuple(item))

        if isinstance(body, Const):
            return body

        abs_body = _abstract_vars_impl(self, body, bound_apps)
        abs_pats = tuple(tuple(_abstract_vars_impl(self, term, bound_apps) for term in pat) for pat in norm_pats)
        return self.mk_quantifier(is_forall, var_names, var_sorts, abs_body, patterns=abs_pats)

    def mk_forall(
        self,
        bound_vars: Sequence[Expr],
        body: Expr,
        *,
        patterns: Sequence[Expr | Sequence[Expr]] = (),
    ) -> Expr:
        """Bind ``bound_vars`` universally across ``body`` and optional ``patterns``."""
        return self._mk_binder(True, bound_vars, body, patterns)

    def mk_exists(
        self,
        bound_vars: Sequence[Expr],
        body: Expr,
        *,
        patterns: Sequence[Expr | Sequence[Expr]] = (),
    ) -> Expr:
        """Bind ``bound_vars`` existentially across ``body`` and ``patterns``."""
        return self._mk_binder(False, bound_vars, body, patterns)


_expr_mod.Context = Context
