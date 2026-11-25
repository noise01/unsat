"""SMT-LIB2 command runner and script execution helpers."""

from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from unsat.parser.smt2.format import format_smt2_model
from unsat.parser.smt2.lexer import (
    SExpr,
    _BVLiteral,
    _Keyword,
    _parse_sexprs,
    _StringLit,
    _Symbol,
    tokenize_smt2,
)
from unsat.sat import SolveResult
from unsat.smt import SMTSolver
from unsat.syntax import (
    App,
    Const,
    Context,
    Expr,
    FuncDecl,
    Sort,
    abstract_vars,
    format_expr,
    quote_smt2_symbol,
    substitute,
)

_SUPPORTED_LOGICS = frozenset(
    {
        "QF_BOOL",
        "QF_UF",
        "QF_LRA",
        "QF_LIA",
        "QF_UFLRA",
        "QF_UFLIA",
        "QF_LIRA",
        "QF_NRA",
        "QF_NIA",
        "QF_NIRA",
        "QF_UFNRA",
        "QF_UFNIA",
        "QF_UFNIRA",
        "QF_BV",
        "QF_UFBV",
        "QF_AX",
        "QF_ABV",
        "QF_AUFBV",
        "QF_ALIA",
        "QF_ALRA",
        "QF_ANRA",
        "QF_ANIA",
        "QF_AUFLIA",
        "QF_AUFLRA",
        "QF_AUFLIRA",
        "QF_AUFNRA",
        "QF_AUFNIA",
        "QF_AUFNIRA",
        "UF",
        "LIA",
        "LRA",
        "LIRA",
        "NRA",
        "NIA",
        "NIRA",
        "UFLIA",
        "UFLRA",
        "UFLIRA",
        "UFNRA",
        "UFNIA",
        "UFNIRA",
        "BV",
        "UFBV",
        "AX",
        "ABV",
        "AUFBV",
        "ALIA",
        "ALRA",
        "AUFLIA",
        "AUFLRA",
        "AUFLIRA",
        "AUFNRA",
        "AUFNIA",
        "AUFNIRA",
        "ALL",
    }
)


def _is_decimal_token(name: str) -> bool:
    parts = name.split(".")
    return len(parts) == 2 and parts[0].isdigit() and parts[1].isdigit()


@dataclass(frozen=True, slots=True)
class _FuncDef:
    params: tuple[App, ...]
    param_sorts: tuple[Sort, ...]
    return_sort: Sort
    body: Expr


@dataclass(frozen=True, slots=True)
class _SortDef:
    params: tuple[str, ...]
    body: SExpr


class SMT2Runner:
    """Stateful SMT-LIB2 command executor for core & combined SMT logics."""

    def __init__(
        self,
        *,
        timeout: float | None = None,
        max_conflicts: int | None = None,
        max_quantifier_rounds: int | None = None,
        max_quantifier_matches: int | None = None,
    ) -> None:
        self._timeout = timeout
        self._max_conflicts = max_conflicts
        self._max_quantifier_rounds = max_quantifier_rounds
        self._max_quantifier_matches = max_quantifier_matches
        self.ctx = Context()
        self.solver = self._make_solver()
        self._sorts_stack: list[dict[str, Sort]] = [{}]
        self._sort_defs_stack: list[dict[str, _SortDef]] = [{}]
        self._decls_stack: list[dict[str, FuncDecl]] = [{}]
        self._defs_stack: list[dict[str, _FuncDef]] = [{}]
        self._declared_order: list[list[FuncDecl]] = [[]]
        self._named_stack: list[list[tuple[App, str]]] = [[]]
        self._assertions_stack: list[list[Expr]] = [[]]
        self._logic: str | None = None
        self._qvar_seq = 0
        self._named_seq = 0
        self._last_check_result: SolveResult | None = None
        self._last_named_map: dict[Expr, str] = {}

    def _make_solver(self) -> SMTSolver:
        return SMTSolver(
            self.ctx,
            timeout=self._timeout,
            max_conflicts=self._max_conflicts,
            max_quantifier_rounds=self._max_quantifier_rounds,
            max_quantifier_matches=self._max_quantifier_matches,
        )

    def declared_decls(self) -> list[FuncDecl]:
        """Return currently active declarations in declaration order."""
        return [decl for scope in self._declared_order for decl in scope]

    def execute(self, text: str) -> list[str]:
        """Execute all SMT-LIB2 commands in ``text`` and return output lines."""
        tokens = tokenize_smt2(text)
        commands = _parse_sexprs(tokens)
        outputs: list[str] = []
        for cmd in commands:
            done, reply = self._run_command(cmd)
            if reply is not None:
                outputs.append(reply)
            if done:
                break
        return outputs

    def statistics(self) -> dict[str, int]:
        """Return underlying solver statistics."""
        return self.solver.statistics()

    def _lookup_sort_entry(self, name: str) -> Sort | _SortDef | None:
        for sort_scope, def_scope in zip(
            reversed(self._sorts_stack), reversed(self._sort_defs_stack), strict=True
        ):
            if name in def_scope:
                return def_scope[name]
            if name in sort_scope:
                return sort_scope[name]
        return None

    def _lookup_callable(self, name: str) -> FuncDecl | _FuncDef | None:
        for decl_scope, def_scope in zip(
            reversed(self._decls_stack), reversed(self._defs_stack), strict=True
        ):
            if name in def_scope:
                return def_scope[name]
            if name in decl_scope:
                return decl_scope[name]
        return None

    def _alloc_placeholder(self, prefix: str, sort: Sort) -> App:
        while True:
            self._qvar_seq += 1
            ph_name = f"{prefix}!{self._qvar_seq}"
            if self._lookup_callable(ph_name) is None:
                return self.ctx.mk_const(ph_name, sort)

    def _alloc_named_indicator(self) -> App:
        while True:
            self._named_seq += 1
            ind_name = f"__smt2_named!{self._named_seq}"
            if self._lookup_callable(ind_name) is None:
                return self.ctx.mk_const(ind_name, self.ctx.bool_sort)

    def _expect_symbol(self, sexpr: SExpr, context_desc: str) -> _Symbol:
        if not isinstance(sexpr, _Symbol):
            msg = f"Expected symbol in {context_desc}, got {sexpr!r}"
            raise ValueError(msg)
        return sexpr

    def _resolve_sort(
        self,
        sexpr: SExpr,
        context_desc: str,
        sort_env: Mapping[str, Sort] | None = None,
        resolving: frozenset[str] = frozenset(),
    ) -> Sort:
        if isinstance(sexpr, tuple) and sexpr:
            head = self._expect_symbol(sexpr[0], context_desc)
            if not head.quoted and head.name == "_" and len(sexpr) == 3:
                tag = self._expect_symbol(sexpr[1], context_desc)
                if not tag.quoted and tag.name == "BitVec":
                    width = self._parse_nonneg_int(sexpr[2], context_desc)
                    return self.ctx.mk_bv_sort(width)
            if not head.quoted and head.name == "Array" and len(sexpr) == 3:
                idx_sort = self._resolve_sort(
                    sexpr[1], context_desc, sort_env=sort_env, resolving=resolving
                )
                elem_sort = self._resolve_sort(
                    sexpr[2], context_desc, sort_env=sort_env, resolving=resolving
                )
                return self.ctx.mk_array_sort(idx_sort, elem_sort)
            if head.name in resolving:
                msg = (
                    f"Cyclic sort definition involving {head.name!r} in {context_desc}"
                )
                raise ValueError(msg)
            entry = self._lookup_sort_entry(head.name)
            if isinstance(entry, _SortDef):
                if len(sexpr) - 1 != len(entry.params):
                    msg = (
                        f"Sort {head.name!r} expects {len(entry.params)} arguments, "
                        f"got {len(sexpr) - 1}"
                    )
                    raise ValueError(msg)
                resolved_args = [
                    self._resolve_sort(
                        arg, context_desc, sort_env=sort_env, resolving=resolving
                    )
                    for arg in sexpr[1:]
                ]
                next_env = dict(zip(entry.params, resolved_args, strict=True))
                return self._resolve_sort(
                    entry.body,
                    context_desc,
                    sort_env=next_env,
                    resolving=resolving | {head.name},
                )
            msg = f"Invalid compound sort {sexpr!r} in {context_desc}"
            raise ValueError(msg)

        sym = self._expect_symbol(sexpr, context_desc)
        if not sym.quoted:
            if sym.name == "Bool":
                return self.ctx.bool_sort
            if sym.name == "Int":
                return self.ctx.int_sort
            if sym.name == "Real":
                return self.ctx.real_sort
        if sort_env is not None and sym.name in sort_env:
            return sort_env[sym.name]
        if sym.name in resolving:
            msg = f"Cyclic sort definition involving {sym.name!r} in {context_desc}"
            raise ValueError(msg)
        entry = self._lookup_sort_entry(sym.name)
        if isinstance(entry, Sort):
            return entry
        if isinstance(entry, _SortDef):
            if entry.params:
                msg = (
                    f"Parameterized sort {sym.name!r} expects "
                    f"{len(entry.params)} arguments"
                )
                raise ValueError(msg)
            return self._resolve_sort(
                entry.body,
                context_desc,
                sort_env=None,
                resolving=resolving | {sym.name},
            )
        msg = f"Unknown sort {sym.name!r} in {context_desc}"
        raise ValueError(msg)

    def _parse_nonneg_int(self, sexpr: SExpr, context_desc: str) -> int:
        sym = self._expect_symbol(sexpr, context_desc)
        if sym.quoted or not sym.name.isdigit():
            msg = f"Expected non-negative integer in {context_desc}, got {sym.name!r}"
            raise ValueError(msg)
        return int(sym.name)

    def _run_command(self, cmd: SExpr) -> tuple[bool, str | None]:
        if not isinstance(cmd, tuple) or not cmd:
            msg = f"Expected command S-expression list, got {cmd!r}"
            raise ValueError(msg)
        head = self._expect_symbol(cmd[0], "command name")
        if head.quoted:
            msg = f"Unknown quoted command {head.name!r}"
            raise ValueError(msg)
        name = head.name
        args = cmd[1:]

        match name:
            case "set-logic":
                if len(args) != 1:
                    msg = "set-logic expects exactly 1 argument"
                    raise ValueError(msg)
                logic = self._expect_symbol(args[0], "set-logic").name
                if logic not in _SUPPORTED_LOGICS:
                    msg = (
                        f"Unsupported logic {logic!r}; supported logics are: "
                        f"{', '.join(sorted(_SUPPORTED_LOGICS))}"
                    )
                    raise ValueError(msg)
                self._logic = logic
                return False, None
            case "set-option" | "set-info":
                return False, None
            case "declare-sort":
                if len(args) != 2:
                    msg = "declare-sort expects <symbol> <numeral>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "declare-sort")
                arity = self._parse_nonneg_int(args[1], "declare-sort")
                if arity != 0:
                    msg = (
                        f"Parameterized sort '{sym.name}' (arity {arity}) is not "
                        "supported"
                    )
                    raise ValueError(msg)
                if not sym.quoted and sym.name in ("Bool", "Int", "Real"):
                    msg = f"Cannot redeclare built-in sort '{sym.name}'"
                    raise ValueError(msg)
                if (
                    sym.name in self._sorts_stack[-1]
                    or sym.name in self._sort_defs_stack[-1]
                ):
                    msg = f"Sort {sym.name!r} already declared in current scope"
                    raise ValueError(msg)
                self._sorts_stack[-1][sym.name] = self.ctx.mk_uninterpreted_sort(
                    sym.name
                )
                return False, None
            case "define-sort":
                if len(args) != 3:
                    msg = "define-sort expects <symbol> (<symbol>*) <sort>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "define-sort")
                if not sym.quoted and sym.name in (
                    "Bool",
                    "Int",
                    "Real",
                    "BitVec",
                    "Array",
                ):
                    msg = f"Cannot redefine built-in sort '{sym.name}'"
                    raise ValueError(msg)
                if (
                    sym.name in self._sorts_stack[-1]
                    or sym.name in self._sort_defs_stack[-1]
                ):
                    msg = f"Sort {sym.name!r} already defined in current scope"
                    raise ValueError(msg)
                if not isinstance(args[1], tuple):
                    msg = "define-sort parameter list must be a list"
                    raise ValueError(msg)
                param_names: list[str] = []
                seen_params: set[str] = set()
                for param_sexpr in args[1]:
                    param_sym = self._expect_symbol(
                        param_sexpr, "define-sort parameter"
                    )
                    if not param_sym.quoted and param_sym.name in (
                        "Bool",
                        "Int",
                        "Real",
                    ):
                        msg = (
                            f"Cannot use built-in sort '{param_sym.name}' as "
                            "define-sort parameter"
                        )
                        raise ValueError(msg)
                    if param_sym.name in seen_params:
                        msg = f"Duplicate parameter {param_sym.name!r} in define-sort"
                        raise ValueError(msg)
                    seen_params.add(param_sym.name)
                    param_names.append(param_sym.name)
                dummy_env = {pname: self.ctx.bool_sort for pname in param_names}
                self._resolve_sort(
                    args[2],
                    "define-sort body",
                    sort_env=dummy_env,
                    resolving=frozenset({sym.name}),
                )
                self._sort_defs_stack[-1][sym.name] = _SortDef(
                    params=tuple(param_names), body=args[2]
                )
                return False, None
            case "declare-const":
                if len(args) != 2:
                    msg = "declare-const expects <symbol> <sort>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "declare-const")
                sort = self._resolve_sort(args[1], "declare-const")
                self._register_decl(sym.name, (), sort)
                return False, None
            case "declare-fun":
                if len(args) != 3:
                    msg = "declare-fun expects <symbol> (<sort>*) <sort>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "declare-fun")
                if not isinstance(args[1], tuple):
                    msg = "declare-fun domain must be a sort list"
                    raise ValueError(msg)
                domain = tuple(
                    self._resolve_sort(sort_sexpr, "declare-fun domain")
                    for sort_sexpr in args[1]
                )
                range_sort = self._resolve_sort(args[2], "declare-fun range")
                self._register_decl(sym.name, domain, range_sort)
                return False, None
            case "define-fun":
                if len(args) != 4:
                    msg = "define-fun expects <symbol> (<sorted-var>*) <sort> <term>"
                    raise ValueError(msg)
                sym = self._expect_symbol(args[0], "define-fun")
                if not isinstance(args[1], tuple):
                    msg = "define-fun parameter list must be a list"
                    raise ValueError(msg)
                if (
                    sym.name in self._decls_stack[-1]
                    or sym.name in self._defs_stack[-1]
                ):
                    msg = f"Symbol {sym.name!r} already defined in current scope"
                    raise ValueError(msg)
                param_env: dict[str, Expr] = {}
                param_placeholders: list[App] = []
                param_sorts: list[Sort] = []
                for binding in args[1]:
                    if not isinstance(binding, tuple) or len(binding) != 2:
                        msg = f"Malformed define-fun parameter {binding!r}"
                        raise ValueError(msg)
                    p_sym = self._expect_symbol(binding[0], "define-fun parameter")
                    if p_sym.name in param_env:
                        msg = f"Duplicate parameter {p_sym.name!r} in define-fun"
                        raise ValueError(msg)
                    p_sort = self._resolve_sort(binding[1], "define-fun parameter sort")
                    placeholder = self._alloc_placeholder("__smt2_param", p_sort)
                    param_env[p_sym.name] = placeholder
                    param_placeholders.append(placeholder)
                    param_sorts.append(p_sort)
                expected_sort = self._resolve_sort(args[2], "define-fun")
                body = self._parse_term(args[3], param_env)
                if expected_sort.is_real and isinstance(body, Const) and body.is_int:
                    body = self.ctx.mk_to_real(body)
                if body.sort is not expected_sort:
                    msg = (
                        f"define-fun '{sym.name}' body sort '{body.sort}' does not "
                        f"match declared sort '{expected_sort}'"
                    )
                    raise TypeError(msg)
                self._defs_stack[-1][sym.name] = _FuncDef(
                    params=tuple(param_placeholders),
                    param_sorts=tuple(param_sorts),
                    return_sort=expected_sort,
                    body=body,
                )
                return False, None
            case "assert":
                if len(args) != 1:
                    msg = "assert expects exactly 1 formula"
                    raise ValueError(msg)
                inner_sexpr, named_sym = self._unwrap_assert_named(args[0])
                if named_sym is not None and any(
                    existing == named_sym
                    for scope in self._named_stack
                    for _, existing in scope
                ):
                    msg = f"Duplicate assertion name {named_sym!r}"
                    raise ValueError(msg)
                formula = self._parse_term(inner_sexpr, {})
                if named_sym is not None:
                    ind = self._alloc_named_indicator()
                    self.solver.add(self.ctx.mk_implies(ind, formula))
                    self._named_stack[-1].append((ind, named_sym))
                else:
                    self.solver.add(formula)
                self._assertions_stack[-1].append(formula)
                self._last_check_result = None
                self._last_named_map = {}
                return False, None
            case "check-sat":
                if args:
                    msg = "check-sat takes no arguments"
                    raise ValueError(msg)
                return False, self._run_check(())
            case "check-sat-assuming":
                if len(args) != 1 or not isinstance(args[0], tuple):
                    msg = "check-sat-assuming expects a list of assumptions"
                    raise ValueError(msg)
                assumps = tuple(self._parse_term(item, {}) for item in args[0])
                return False, self._run_check(assumps)
            case "get-unsat-core":
                if args:
                    msg = "get-unsat-core takes no arguments"
                    raise ValueError(msg)
                if self._last_check_result is not SolveResult.UNSAT:
                    msg = "Unsat core is only available after check-sat returns unsat"
                    raise ValueError(msg)
                core_names = [
                    quote_smt2_symbol(self._last_named_map[expr])
                    for expr in self.solver.unsat_core()
                    if expr in self._last_named_map
                ]
                return False, "(" + " ".join(core_names) + ")"
            case "get-assertions":
                if args:
                    msg = "get-assertions takes no arguments"
                    raise ValueError(msg)
                rendered = [
                    format_expr(expr)
                    for scope in self._assertions_stack
                    for expr in scope
                ]
                return False, "(" + " ".join(rendered) + ")"
            case "echo":
                if len(args) != 1 or not isinstance(args[0], _StringLit):
                    msg = "echo expects exactly 1 string literal"
                    raise ValueError(msg)
                escaped = args[0].value.replace('"', '""')
                return False, f'"{escaped}"'
            case "get-model":
                if args:
                    msg = "get-model takes no arguments"
                    raise ValueError(msg)
                return False, format_smt2_model(
                    self.solver.model(), decls=self.declared_decls()
                )
            case "get-value":
                if len(args) != 1 or not isinstance(args[0], tuple) or not args[0]:
                    msg = "get-value expects a non-empty list of terms"
                    raise ValueError(msg)
                model = self.solver.model()
                pairs = []
                for item in args[0]:
                    term = self._parse_term(item, {})
                    val = model.eval(term, model_completion=True)
                    pairs.append(f"({format_expr(term)} {format_expr(val)})")
                return False, "(" + " ".join(pairs) + ")"
            case "push":
                levels = 1 if not args else self._parse_nonneg_int(args[0], "push")
                if len(args) > 1:
                    msg = "push accepts at most 1 argument"
                    raise ValueError(msg)
                for _ in range(levels):
                    self.solver.push()
                    self._sorts_stack.append({})
                    self._sort_defs_stack.append({})
                    self._decls_stack.append({})
                    self._defs_stack.append({})
                    self._declared_order.append([])
                    self._named_stack.append([])
                    self._assertions_stack.append([])
                self._last_check_result = None
                self._last_named_map = {}
                return False, None
            case "pop":
                levels = 1 if not args else self._parse_nonneg_int(args[0], "pop")
                if len(args) > 1:
                    msg = "pop accepts at most 1 argument"
                    raise ValueError(msg)
                self.solver.pop(levels)
                for _ in range(levels):
                    self._sorts_stack.pop()
                    self._sort_defs_stack.pop()
                    self._decls_stack.pop()
                    self._defs_stack.pop()
                    self._declared_order.pop()
                    self._named_stack.pop()
                    self._assertions_stack.pop()
                self._last_check_result = None
                self._last_named_map = {}
                return False, None
            case "reset":
                if args:
                    msg = "reset takes no arguments"
                    raise ValueError(msg)
                self.ctx = Context()
                self.solver = self._make_solver()
                self._sorts_stack = [{}]
                self._sort_defs_stack = [{}]
                self._decls_stack = [{}]
                self._defs_stack = [{}]
                self._declared_order = [[]]
                self._named_stack = [[]]
                self._assertions_stack = [[]]
                self._logic = None
                self._last_check_result = None
                self._last_named_map = {}
                return False, None
            case "reset-assertions":
                if args:
                    msg = "reset-assertions takes no arguments"
                    raise ValueError(msg)
                self.solver.reset()
                self._sorts_stack = [self._sorts_stack[0]]
                self._sort_defs_stack = [self._sort_defs_stack[0]]
                self._decls_stack = [self._decls_stack[0]]
                self._defs_stack = [self._defs_stack[0]]
                self._declared_order = [self._declared_order[0]]
                self._named_stack = [[]]
                self._assertions_stack = [[]]
                self._last_check_result = None
                self._last_named_map = {}
                return False, None
            case "exit":
                if args:
                    msg = "exit takes no arguments"
                    raise ValueError(msg)
                return True, None
            case _:
                msg = f"Unsupported SMT-LIB2 command: {name!r}"
                raise ValueError(msg)

    def _register_decl(
        self,
        name: str,
        domain: tuple[Sort, ...],
        range_sort: Sort,
    ) -> FuncDecl:
        if name in self._decls_stack[-1] or name in self._defs_stack[-1]:
            msg = f"Symbol {name!r} already declared in current scope"
            raise ValueError(msg)
        decl = self.ctx.mk_decl(name, domain, range_sort)
        self._decls_stack[-1][name] = decl
        self._declared_order[-1].append(decl)
        return decl

    def _format_verdict(self, verdict: SolveResult) -> str:
        if verdict is SolveResult.SAT:
            return "sat"
        if verdict is SolveResult.UNSAT:
            return "unsat"
        return "unknown"

    def _unwrap_assert_named(self, sexpr: SExpr) -> tuple[SExpr, str | None]:
        cur = sexpr
        named_sym: str | None = None
        while (
            isinstance(cur, tuple)
            and cur
            and isinstance(cur[0], _Symbol)
            and not cur[0].quoted
            and cur[0].name == "!"
        ):
            ann_args = cur[1:]
            if len(ann_args) < 3 or len(ann_args) % 2 == 0:
                msg = "Attribute term '(! <term> :kw <val> ...)' is malformed"
                raise ValueError(msg)
            for idx in range(1, len(ann_args), 2):
                kw = ann_args[idx]
                if not isinstance(kw, _Keyword):
                    msg = f"Expected attribute keyword in '!', got {kw!r}"
                    raise ValueError(msg)
                if kw.name == "named":
                    if named_sym is not None:
                        msg = "Multiple :named attributes on a single assertion"
                        raise ValueError(msg)
                    name_atom = self._expect_symbol(
                        ann_args[idx + 1], ":named attribute"
                    )
                    named_sym = name_atom.name
            cur = ann_args[0]
        return cur, named_sym

    def _run_check(self, assumptions: tuple[Expr, ...]) -> str:
        active_named = [pair for scope in self._named_stack for pair in scope]
        all_assumps = [*(ind for ind, _ in active_named), *assumptions]
        verdict = self.solver.check(*all_assumps)
        self._last_check_result = verdict
        self._last_named_map = (
            {ind: name for ind, name in active_named}
            if verdict is SolveResult.UNSAT
            else {}
        )
        return self._format_verdict(verdict)

    def _coerce_domain_args(
        self, parsed: list[Expr], domain: tuple[Sort, ...]
    ) -> list[Expr]:
        if len(parsed) != len(domain):
            return parsed
        return [
            self.ctx.mk_to_real(arg)
            if isinstance(arg, Const) and arg.is_int and exp.is_real
            else arg
            for arg, exp in zip(parsed, domain, strict=True)
        ]

    def _expand_def(
        self,
        name: str,
        fdef: _FuncDef,
        parsed: list[Expr],
        line: int,
        col: int,
    ) -> Expr:
        if len(parsed) != len(fdef.params):
            msg = (
                f"Line {line}, col {col}: defined function {name!r} expects "
                f"{len(fdef.params)} arguments, got {len(parsed)}"
            )
            raise ValueError(msg)
        coerced = self._coerce_domain_args(parsed, fdef.param_sorts)
        for arg, exp in zip(coerced, fdef.param_sorts, strict=True):
            if arg.sort is not exp:
                msg = (
                    f"Argument sort '{arg.sort}' does not match parameter sort "
                    f"'{exp}' in {name!r}"
                )
                raise TypeError(msg)
        if not fdef.params:
            return fdef.body
        return substitute(fdef.body, dict(zip(fdef.params, coerced, strict=True)))

    def _coerce_int_literals_for_real(self, exprs: list[Expr]) -> list[Expr]:
        if not any(item.is_real for item in exprs):
            return exprs
        return [
            self.ctx.mk_to_real(item)
            if isinstance(item, Const) and item.is_int
            else item
            for item in exprs
        ]

    def _parse_term(self, sexpr: SExpr, local_env: dict[str, Expr]) -> Expr:
        if isinstance(sexpr, _BVLiteral):
            return self.ctx.mk_bv_val(sexpr.value, sexpr.width)

        if isinstance(sexpr, _Symbol):
            if not sexpr.quoted:
                if sexpr.name == "true":
                    return self.ctx.mk_true()
                if sexpr.name == "false":
                    return self.ctx.mk_false()
                if sexpr.name.isdigit():
                    if self._logic in (
                        "QF_LRA",
                        "QF_UFLRA",
                        "QF_ALRA",
                        "QF_AUFLRA",
                        "LRA",
                        "UFLRA",
                        "ALRA",
                        "AUFLRA",
                    ):
                        return self.ctx.mk_real_val(sexpr.name)
                    return self.ctx.mk_int_val(int(sexpr.name))
                if _is_decimal_token(sexpr.name):
                    return self.ctx.mk_real_val(sexpr.name)
            if sexpr.name in local_env:
                return local_env[sexpr.name]
            target = self._lookup_callable(sexpr.name)
            if isinstance(target, _FuncDef):
                if target.params:
                    msg = (
                        f"Line {sexpr.line}, col {sexpr.col}: defined function "
                        f"{sexpr.name!r} of arity {len(target.params)} requires "
                        "arguments"
                    )
                    raise ValueError(msg)
                return target.body
            if target is not None:
                if target.arity != 0:
                    msg = (
                        f"Line {sexpr.line}, col {sexpr.col}: function {sexpr.name!r} "
                        f"of arity {target.arity} requires arguments"
                    )
                    raise ValueError(msg)
                return target()
            msg = (
                f"Line {sexpr.line}, col {sexpr.col}: "
                f"undeclared identifier {sexpr.name!r}"
            )
            raise ValueError(msg)

        if not isinstance(sexpr, tuple) or not sexpr:
            msg = f"Invalid SMT-LIB2 term: {sexpr!r}"
            raise ValueError(msg)

        if isinstance(sexpr[0], tuple):
            return self._parse_compound_head_term(sexpr[0], sexpr[1:], local_env)

        head = self._expect_symbol(sexpr[0], "term operator")
        args = sexpr[1:]

        if head.quoted:
            target = self._lookup_callable(head.name)
            if isinstance(target, _FuncDef):
                parsed = [self._parse_term(arg, local_env) for arg in args]
                return self._expand_def(head.name, target, parsed, head.line, head.col)
            if target is not None:
                parsed = [self._parse_term(arg, local_env) for arg in args]
                return target(*self._coerce_domain_args(parsed, target.domain))
            msg = (
                f"Line {head.line}, col {head.col}: "
                f"unknown function application {head.name!r}"
            )
            raise ValueError(msg)

        op = head.name
        if op == "_":
            if len(args) == 2:
                bv_sym = self._expect_symbol(args[0], "indexed bitvector")
                if (
                    not bv_sym.quoted
                    and bv_sym.name.startswith("bv")
                    and bv_sym.name[2:].isdigit()
                ):
                    bv_val = int(bv_sym.name[2:])
                    bv_width = self._parse_nonneg_int(args[1], "(_ bv...)")
                    return self.ctx.mk_bv_val(bv_val, bv_width)
            msg = f"Unsupported indexed identifier: {sexpr!r}"
            raise ValueError(msg)
        if op == "!":
            if len(args) < 3 or len(args) % 2 == 0:
                msg = "Attribute term '(! <term> :kw <val> ...)' is malformed"
                raise ValueError(msg)
            for idx in range(1, len(args), 2):
                if not isinstance(args[idx], _Keyword):
                    msg = f"Expected attribute keyword in '!', got {args[idx]!r}"
                    raise ValueError(msg)
            return self._parse_term(args[0], local_env)

        if op == "let":
            if len(args) != 2 or not isinstance(args[0], tuple):
                msg = "let expects ((<var> <term>)*) <term>"
                raise ValueError(msg)
            bound: dict[str, Expr] = {}
            for binding in args[0]:
                if not isinstance(binding, tuple) or len(binding) != 2:
                    msg = f"Malformed let binding {binding!r}"
                    raise ValueError(msg)
                var_sym = self._expect_symbol(binding[0], "let binding variable")
                if var_sym.name in bound:
                    msg = f"Duplicate variable {var_sym.name!r} in let"
                    raise ValueError(msg)
                bound[var_sym.name] = self._parse_term(binding[1], local_env)
            merged_env = {**local_env, **bound}
            return self._parse_term(args[1], merged_env)

        if op in ("forall", "exists"):
            if len(args) != 2 or not isinstance(args[0], tuple) or not args[0]:
                msg = f"{op} expects ((<var> <sort>)+) <term>"
                raise ValueError(msg)
            q_bound: dict[str, Expr] = {}
            var_names: list[str] = []
            var_sorts: list[Sort] = []
            placeholders: list[App] = []
            for binding in args[0]:
                if not isinstance(binding, tuple) or len(binding) != 2:
                    msg = f"Malformed {op} binder {binding!r}"
                    raise ValueError(msg)
                var_sym = self._expect_symbol(binding[0], f"{op} binder variable")
                if var_sym.name in q_bound:
                    msg = f"Duplicate bound variable {var_sym.name!r} in {op}"
                    raise ValueError(msg)
                sort = self._resolve_sort(binding[1], f"{op} binder sort")
                placeholder = self._alloc_placeholder("__smt2_qvar", sort)
                q_bound[var_sym.name] = placeholder
                var_names.append(var_sym.name)
                var_sorts.append(sort)
                placeholders.append(placeholder)

            body_sexpr: SExpr = args[1]
            raw_patterns: list[tuple[SExpr, ...]] = []
            while (
                isinstance(body_sexpr, tuple)
                and body_sexpr
                and isinstance(body_sexpr[0], _Symbol)
                and not body_sexpr[0].quoted
                and body_sexpr[0].name == "!"
            ):
                ann_args = body_sexpr[1:]
                if len(ann_args) < 3 or len(ann_args) % 2 == 0:
                    msg = "Attribute term '(! <term> :kw <val> ...)' is malformed"
                    raise ValueError(msg)
                for idx in range(1, len(ann_args), 2):
                    kw = ann_args[idx]
                    if not isinstance(kw, _Keyword):
                        msg = f"Expected attribute keyword in '!', got {kw!r}"
                        raise ValueError(msg)
                    if kw.name == "pattern":
                        pat_val = ann_args[idx + 1]
                        if not isinstance(pat_val, tuple) or not pat_val:
                            msg = "Expected non-empty term list after :pattern"
                            raise ValueError(msg)
                        raw_patterns.append(pat_val)
                body_sexpr = ann_args[0]

            merged_env = {**local_env, **q_bound}
            raw_body = self._parse_term(body_sexpr, merged_env)
            abs_body = abstract_vars(raw_body, placeholders)
            abs_patterns = tuple(
                tuple(
                    abstract_vars(self._parse_term(t, merged_env), placeholders)
                    for t in pat
                )
                for pat in raw_patterns
            )
            return self.ctx.mk_quantifier(
                op == "forall",
                var_names,
                var_sorts,
                abs_body,
                patterns=abs_patterns,
            )

        parsed = [self._parse_term(arg, local_env) for arg in args]
        match op:
            case "not":
                if len(parsed) != 1:
                    msg = "'not' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_not(parsed[0])
            case "and":
                if not parsed:
                    msg = "'and' expects at least 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_and(*parsed)
            case "or":
                if not parsed:
                    msg = "'or' expects at least 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_or(*parsed)
            case "=>":
                if len(parsed) < 2:
                    msg = "'=>' expects at least 2 arguments"
                    raise ValueError(msg)
                acc = parsed[-1]
                for item in reversed(parsed[:-1]):
                    acc = self.ctx.mk_implies(item, acc)
                return acc
            case "xor":
                if len(parsed) < 2:
                    msg = "'xor' expects at least 2 arguments"
                    raise ValueError(msg)
                acc = parsed[0]
                for item in parsed[1:]:
                    acc = self.ctx.mk_xor(acc, item)
                return acc
            case "=":
                if len(parsed) < 2:
                    msg = "'=' expects at least 2 arguments"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                if len(coerced) == 2:
                    return self.ctx.mk_eq(coerced[0], coerced[1])
                return self.ctx.mk_and(
                    *(
                        self.ctx.mk_eq(coerced[i], coerced[i + 1])
                        for i in range(len(coerced) - 1)
                    )
                )
            case "distinct":
                if len(parsed) < 2:
                    msg = "'distinct' expects at least 2 arguments"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                return self.ctx.mk_distinct(*coerced)
            case "ite":
                if len(parsed) != 3:
                    msg = "'ite' expects 3 arguments"
                    raise ValueError(msg)
                branches = self._coerce_int_literals_for_real([parsed[1], parsed[2]])
                return self.ctx.mk_ite(parsed[0], branches[0], branches[1])
            case "+":
                if not parsed:
                    msg = "'+' expects at least 1 argument"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                return coerced[0] if len(coerced) == 1 else self.ctx.mk_add(*coerced)
            case "-":
                if not parsed:
                    msg = "'-' expects at least 1 argument"
                    raise ValueError(msg)
                if len(parsed) == 1:
                    return self.ctx.mk_neg(parsed[0])
                coerced = self._coerce_int_literals_for_real(parsed)
                acc = coerced[0]
                for item in coerced[1:]:
                    acc = self.ctx.mk_sub(acc, item)
                return acc
            case "*":
                if not parsed:
                    msg = "'*' expects at least 1 argument"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                return coerced[0] if len(coerced) == 1 else self.ctx.mk_mul(*coerced)
            case "/":
                if len(parsed) < 2:
                    msg = "'/' expects at least 2 arguments"
                    raise ValueError(msg)
                real_args = [
                    self.ctx.mk_to_real(item)
                    if isinstance(item, Const) and item.is_int
                    else item
                    for item in parsed
                ]
                acc = real_args[0]
                for item in real_args[1:]:
                    acc = self.ctx.mk_div(acc, item)
                return acc
            case "<" | "<=" | ">" | ">=":
                if len(parsed) < 2:
                    msg = f"'{op}' expects at least 2 arguments"
                    raise ValueError(msg)
                coerced = self._coerce_int_literals_for_real(parsed)
                mk_cmp = (
                    self.ctx.mk_lt
                    if op == "<"
                    else self.ctx.mk_le
                    if op == "<="
                    else self.ctx.mk_gt
                    if op == ">"
                    else self.ctx.mk_ge
                )
                if len(coerced) == 2:
                    return mk_cmp(coerced[0], coerced[1])
                return self.ctx.mk_and(
                    *(
                        mk_cmp(coerced[i], coerced[i + 1])
                        for i in range(len(coerced) - 1)
                    )
                )
            case "to_real":
                if len(parsed) != 1:
                    msg = "'to_real' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_to_real(parsed[0])
            case "to_int":
                if len(parsed) != 1:
                    msg = "'to_int' expects 1 argument"
                    raise ValueError(msg)
                arg = (
                    self.ctx.mk_to_real(parsed[0])
                    if isinstance(parsed[0], Const) and parsed[0].is_int
                    else parsed[0]
                )
                return self.ctx.mk_to_int(arg)
            case "is_int":
                if len(parsed) != 1:
                    msg = "'is_int' expects 1 argument"
                    raise ValueError(msg)
                arg = (
                    self.ctx.mk_to_real(parsed[0])
                    if isinstance(parsed[0], Const) and parsed[0].is_int
                    else parsed[0]
                )
                return self.ctx.mk_is_int(arg)
            case "abs":
                if len(parsed) != 1:
                    msg = "'abs' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_abs(parsed[0])
            case "div":
                if len(parsed) < 2:
                    msg = "'div' expects at least 2 arguments"
                    raise ValueError(msg)
                acc = parsed[0]
                for item in parsed[1:]:
                    acc = self.ctx.mk_idiv(acc, item)
                return acc
            case "mod":
                if len(parsed) != 2:
                    msg = "'mod' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_mod(parsed[0], parsed[1])
            case "bvnot":
                if len(parsed) != 1:
                    msg = "'bvnot' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(parsed[0])
            case "bvneg":
                if len(parsed) != 1:
                    msg = "'bvneg' expects 1 argument"
                    raise ValueError(msg)
                return self.ctx.mk_bv_neg(parsed[0])
            case "bvand":
                if len(parsed) < 2:
                    msg = "'bvand' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_and(*parsed)
            case "bvor":
                if len(parsed) < 2:
                    msg = "'bvor' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_or(*parsed)
            case "bvxor":
                if len(parsed) < 2:
                    msg = "'bvxor' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_xor(*parsed)
            case "bvnand":
                if len(parsed) != 2:
                    msg = "'bvnand' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(self.ctx.mk_bv_and(parsed[0], parsed[1]))
            case "bvnor":
                if len(parsed) != 2:
                    msg = "'bvnor' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(self.ctx.mk_bv_or(parsed[0], parsed[1]))
            case "bvxnor":
                if len(parsed) != 2:
                    msg = "'bvxnor' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_not(self.ctx.mk_bv_xor(parsed[0], parsed[1]))
            case "bvcomp":
                if len(parsed) != 2:
                    msg = "'bvcomp' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_ite(
                    self.ctx.mk_eq(parsed[0], parsed[1]),
                    self.ctx.mk_bv_val(1, 1),
                    self.ctx.mk_bv_val(0, 1),
                )
            case "bvadd":
                if len(parsed) < 2:
                    msg = "'bvadd' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_add(*parsed)
            case "bvsub":
                if len(parsed) != 2:
                    msg = "'bvsub' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sub(parsed[0], parsed[1])
            case "bvmul":
                if len(parsed) < 2:
                    msg = "'bvmul' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_mul(*parsed)
            case "bvudiv":
                if len(parsed) != 2:
                    msg = "'bvudiv' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_udiv(parsed[0], parsed[1])
            case "bvurem":
                if len(parsed) != 2:
                    msg = "'bvurem' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_urem(parsed[0], parsed[1])
            case "bvsdiv":
                if len(parsed) != 2:
                    msg = "'bvsdiv' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sdiv(parsed[0], parsed[1])
            case "bvsrem":
                if len(parsed) != 2:
                    msg = "'bvsrem' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_srem(parsed[0], parsed[1])
            case "bvsmod":
                if len(parsed) != 2:
                    msg = "'bvsmod' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_smod(parsed[0], parsed[1])
            case "bvshl":
                if len(parsed) != 2:
                    msg = "'bvshl' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_shl(parsed[0], parsed[1])
            case "bvlshr":
                if len(parsed) != 2:
                    msg = "'bvlshr' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_lshr(parsed[0], parsed[1])
            case "bvashr":
                if len(parsed) != 2:
                    msg = "'bvashr' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ashr(parsed[0], parsed[1])
            case "bvult":
                if len(parsed) != 2:
                    msg = "'bvult' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ult(parsed[0], parsed[1])
            case "bvule":
                if len(parsed) != 2:
                    msg = "'bvule' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ule(parsed[0], parsed[1])
            case "bvugt":
                if len(parsed) != 2:
                    msg = "'bvugt' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_ugt(parsed[0], parsed[1])
            case "bvuge":
                if len(parsed) != 2:
                    msg = "'bvuge' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_uge(parsed[0], parsed[1])
            case "bvslt":
                if len(parsed) != 2:
                    msg = "'bvslt' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_slt(parsed[0], parsed[1])
            case "bvsle":
                if len(parsed) != 2:
                    msg = "'bvsle' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sle(parsed[0], parsed[1])
            case "bvsgt":
                if len(parsed) != 2:
                    msg = "'bvsgt' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sgt(parsed[0], parsed[1])
            case "bvsge":
                if len(parsed) != 2:
                    msg = "'bvsge' expects 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_bv_sge(parsed[0], parsed[1])
            case "concat":
                if len(parsed) < 2:
                    msg = "'concat' expects at least 2 arguments"
                    raise ValueError(msg)
                return self.ctx.mk_concat(*parsed)
            case "select":
                if len(parsed) != 2:
                    msg = "'select' expects 2 arguments"
                    raise ValueError(msg)
                arr, idx = parsed
                if (
                    arr.is_array
                    and arr.sort.index_sort.is_real
                    and isinstance(idx, Const)
                    and idx.is_int
                ):
                    idx = self.ctx.mk_to_real(idx)
                return self.ctx.mk_select(arr, idx)
            case "store":
                if len(parsed) != 3:
                    msg = "'store' expects 3 arguments"
                    raise ValueError(msg)
                arr, idx, val = parsed
                if arr.is_array:
                    if (
                        arr.sort.index_sort.is_real
                        and isinstance(idx, Const)
                        and idx.is_int
                    ):
                        idx = self.ctx.mk_to_real(idx)
                    if (
                        arr.sort.element_sort.is_real
                        and isinstance(val, Const)
                        and val.is_int
                    ):
                        val = self.ctx.mk_to_real(val)
                return self.ctx.mk_store(arr, idx, val)
            case _:
                target = self._lookup_callable(op)
                if isinstance(target, _FuncDef):
                    return self._expand_def(op, target, parsed, head.line, head.col)
                if target is not None:
                    return target(*self._coerce_domain_args(parsed, target.domain))
                msg = (
                    f"Line {head.line}, col {head.col}: "
                    f"unsupported operator or undeclared function {op!r}"
                )
                raise ValueError(msg)

    def _parse_compound_head_term(
        self,
        head_tuple: tuple[SExpr, ...],
        args: tuple[SExpr, ...],
        local_env: dict[str, Expr],
    ) -> Expr:
        if not head_tuple:
            msg = f"Invalid empty operator head in {head_tuple!r}"
            raise ValueError(msg)
        tag = self._expect_symbol(head_tuple[0], "compound operator")
        if not tag.quoted and tag.name == "as":
            if len(head_tuple) != 3 or len(args) != 1:
                msg = f"Malformed constant array application: ({head_tuple!r} ...)"
                raise ValueError(msg)
            const_sym = self._expect_symbol(head_tuple[1], "as const")
            if const_sym.quoted or const_sym.name != "const":
                msg = f"Unsupported qualified identifier '(as {const_sym.name} ...)'"
                raise ValueError(msg)
            sort = self._resolve_sort(head_tuple[2], "(as const <Sort>)")
            if not sort.is_array:
                msg = f"Expected Array sort in '(as const ...)', got '{sort}'"
                raise TypeError(msg)
            val = self._parse_term(args[0], local_env)
            if sort.element_sort.is_real and isinstance(val, Const) and val.is_int:
                val = self.ctx.mk_to_real(val)
            return self.ctx.mk_const_array(sort.index_sort, val)

        if not tag.quoted and tag.name == "_":
            if len(head_tuple) < 3 or len(args) != 1:
                msg = f"Unsupported indexed operator application: {head_tuple!r}"
                raise ValueError(msg)
            op_sym = self._expect_symbol(head_tuple[1], "indexed BV operator")
            if op_sym.quoted:
                msg = f"Unsupported quoted indexed operator {op_sym.name!r}"
                raise ValueError(msg)
            arg = self._parse_term(args[0], local_env)
            op_name = op_sym.name
            if op_name == "extract":
                if len(head_tuple) != 4:
                    msg = "'(_ extract hi lo)' expects 2 indices"
                    raise ValueError(msg)
                hi = self._parse_nonneg_int(head_tuple[2], "extract high")
                lo = self._parse_nonneg_int(head_tuple[3], "extract low")
                return self.ctx.mk_extract(hi, lo, arg)
            if len(head_tuple) != 3:
                msg = f"'(_ {op_name} n)' expects 1 index"
                raise ValueError(msg)
            param = self._parse_nonneg_int(head_tuple[2], op_name)
            match op_name:
                case "divisible":
                    return self.ctx.mk_divisible(param, arg)
                case "zero_extend":
                    return self.ctx.mk_zero_ext(param, arg)
                case "sign_extend":
                    return self.ctx.mk_sign_ext(param, arg)
                case "rotate_left":
                    return self.ctx.mk_rotate_left(param, arg)
                case "rotate_right":
                    return self.ctx.mk_rotate_right(param, arg)
                case "repeat":
                    return self.ctx.mk_repeat(param, arg)
                case _:
                    msg = f"Unsupported indexed operator '(_ {op_name} ...)'"
                    raise ValueError(msg)

        msg = f"Unsupported compound operator head: {head_tuple!r}"
        raise ValueError(msg)


def execute_smt2(
    text: str,
    *,
    timeout: float | None = None,
    max_conflicts: int | None = None,
    max_quantifier_rounds: int | None = None,
    max_quantifier_matches: int | None = None,
) -> tuple[list[str], dict[str, int]]:
    """Execute SMT-LIB2 script text and return outputs paired with solver stats."""
    runner = SMT2Runner(
        timeout=timeout,
        max_conflicts=max_conflicts,
        max_quantifier_rounds=max_quantifier_rounds,
        max_quantifier_matches=max_quantifier_matches,
    )
    outputs = runner.execute(text)
    return outputs, runner.statistics()


def execute_smt2_file(
    path: str | Path,
    *,
    timeout: float | None = None,
    max_conflicts: int | None = None,
    max_quantifier_rounds: int | None = None,
    max_quantifier_matches: int | None = None,
) -> tuple[list[str], dict[str, int]]:
    """Read and execute a UTF-8 SMT-LIB2 file, returning outputs and stats."""
    text = Path(path).read_text(encoding="utf-8-sig")
    return execute_smt2(
        text,
        timeout=timeout,
        max_conflicts=max_conflicts,
        max_quantifier_rounds=max_quantifier_rounds,
        max_quantifier_matches=max_quantifier_matches,
    )


def run_smt2(
    text: str,
    *,
    timeout: float | None = None,
    max_conflicts: int | None = None,
    max_quantifier_rounds: int | None = None,
    max_quantifier_matches: int | None = None,
) -> list[str]:
    """Execute SMT-LIB2 script text and return emitted response strings."""
    outputs, _ = execute_smt2(
        text,
        timeout=timeout,
        max_conflicts=max_conflicts,
        max_quantifier_rounds=max_quantifier_rounds,
        max_quantifier_matches=max_quantifier_matches,
    )
    return outputs


def run_smt2_file(
    path: str | Path,
    *,
    timeout: float | None = None,
    max_conflicts: int | None = None,
    max_quantifier_rounds: int | None = None,
    max_quantifier_matches: int | None = None,
) -> list[str]:
    """Read and execute a UTF-8 SMT-LIB2 file and return emitted response strings."""
    outputs, _ = execute_smt2_file(
        path,
        timeout=timeout,
        max_conflicts=max_conflicts,
        max_quantifier_rounds=max_quantifier_rounds,
        max_quantifier_matches=max_quantifier_matches,
    )
    return outputs
