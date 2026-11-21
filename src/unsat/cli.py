"""Command-line interface for the ``unsat`` executable.

Depends on: ``parser``, ``smt``, ``sat``.
"""

import argparse
import sys
from collections.abc import Sequence
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path

from unsat.parser import (
    execute_smt2,
    format_dimacs_result,
    parse_dimacs,
    solve_dimacs,
)


def _package_version() -> str:
    try:
        return version("unsat")
    except PackageNotFoundError:
        return "0.0.0"


def _detect_format(input_arg: str, text: str, explicit: str) -> str:
    if explicit != "auto":
        return explicit

    if input_arg != "-":
        suffix = Path(input_arg).suffix.lower()
        if suffix in (".smt2", ".smt"):
            return "smt2"
        if suffix in (".cnf", ".dimacs"):
            return "dimacs"

    stripped_bom = text.removeprefix("\ufeff")
    for raw_line in stripped_bom.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith(("(", ";")):
            return "smt2"
        return "dimacs"
    return "dimacs"


def build_parser() -> argparse.ArgumentParser:
    """Construct the CLI argument parser."""
    parser = argparse.ArgumentParser(
        prog="unsat",
        description="unsat: A Z3-inspired SMT solver in Python.",
    )
    parser.add_argument(
        "input",
        nargs="?",
        help="Path to an SMT-LIB2 or DIMACS CNF file, or '-' for standard input.",
    )
    parser.add_argument(
        "--format",
        choices=("auto", "dimacs", "smt2"),
        default="auto",
        help="Input format (default: auto-detect by extension or content).",
    )
    parser.add_argument(
        "--stats",
        action="store_true",
        help="Print solver search statistics as comment lines.",
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"unsat {_package_version()}",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    """Entry point for the ``unsat`` CLI."""
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.input is None:
        parser.print_help()
        return 0

    try:
        text = (
            sys.stdin.read()
            if args.input == "-"
            else Path(args.input).read_text(encoding="utf-8-sig")
        )
        fmt = _detect_format(args.input, text, args.format)
        if fmt == "smt2":
            outputs, stats = execute_smt2(text)
            if args.stats:
                for key, val in stats.items():
                    print(f"; {key}: {val}")
            for line in outputs:
                print(line)
            return 0

        cnf = parse_dimacs(text)
        result, model, stats = solve_dimacs(cnf)
        if args.stats:
            for key, val in stats.items():
                print(f"c {key}: {val}")
        print(format_dimacs_result(result, model, cnf.num_vars))
        return 0
    except (OSError, TypeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
