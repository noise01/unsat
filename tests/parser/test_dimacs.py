import pytest

from unsat.parser import (
    DimacsCNF,
    format_dimacs_result,
    parse_dimacs,
    parse_dimacs_file,
    solve_dimacs,
)
from unsat.sat import SolveResult, neg_lit, pos_lit


def test_parse_dimacs_valid_features(tmp_path) -> None:
    text = """
    c Header comment
    c Another comment
    p cnf 4 3

    1 -2
    3 0 4 -1 0
    c Inline comment before empty clause
    0
    %
    this trailing text after percent must be ignored 999 abc
    """
    cnf = parse_dimacs(text)
    assert cnf == DimacsCNF(
        num_vars=4,
        declared_clauses=3,
        clauses=(
            (pos_lit(0), neg_lit(1), pos_lit(2)),
            (pos_lit(3), neg_lit(0)),
            (),
        ),
    )

    path = tmp_path / "sample.cnf"
    path.write_text("p cnf 0 0\n", encoding="utf-8")
    empty_cnf = parse_dimacs_file(path)
    assert empty_cnf == DimacsCNF(num_vars=0, declared_clauses=0, clauses=())

    bom_cnf = parse_dimacs("\ufeffp cnf 1 1\n1 0\n")
    assert bom_cnf == DimacsCNF(
        num_vars=1, declared_clauses=1, clauses=((pos_lit(0),),)
    )


@pytest.mark.parametrize(
    "bad_text",
    [
        "",
        "c only comments\n",
        "1 2 0\np cnf 2 1\n",
        "p cnf 2 1\np cnf 2 1\n",
        "p sat 2 1\n",
        "p cnf 2\n",
        "p cnf -1 1\n",
        "p cnf two one\n",
        "p cnf 2 1\n1 two 0\n",
        "p cnf 2 1\n3 0\n",
        "p cnf 2 1\n-3 0\n",
        "p cnf 2 1\n1 2\n",
    ],
)
def test_parse_dimacs_invalid_inputs(bad_text: str) -> None:
    with pytest.raises(ValueError, match=r".+"):
        parse_dimacs(bad_text)


def test_format_dimacs_result() -> None:
    assert format_dimacs_result(SolveResult.UNSAT) == "s UNSATISFIABLE"
    assert format_dimacs_result(SolveResult.UNKNOWN) == "s UNKNOWN"
    assert format_dimacs_result(SolveResult.SAT) == "s SATISFIABLE\nv 0"
    assert (
        format_dimacs_result(SolveResult.SAT, {0: True, 1: False, 2: True}, num_vars=3)
        == "s SATISFIABLE\nv 1 -2 3 0"
    )
    with pytest.raises(ValueError, match="model"):
        format_dimacs_result(SolveResult.SAT, None, num_vars=2)


def test_solve_dimacs_sat_and_unsat_benchmarks() -> None:
    # 3-coloring a triangle (SAT).
    triangle_3col = """
    c Triangle 3-coloring with 9 variables (3 vertices x 3 colors)
    p cnf 9 12
    1 2 3 0
    4 5 6 0
    7 8 9 0
    -1 -4 0
    -2 -5 0
    -3 -6 0
    -1 -7 0
    -2 -8 0
    -3 -9 0
    -4 -7 0
    -5 -8 0
    -6 -9 0
    """
    cnf_sat = parse_dimacs(triangle_3col)
    res_sat, model_sat, _ = solve_dimacs(cnf_sat)
    assert res_sat is SolveResult.SAT
    assert model_sat is not None
    assert len(model_sat) == 9
    for clause in cnf_sat.clauses:
        assert any(
            (not model_sat[lit >> 1] if (lit & 1) else model_sat[lit >> 1])
            for lit in clause
        )

    # PHP(4, 3) encoded in DIMACS (UNSAT).
    php_4_3 = """
    p cnf 12 22
    1 2 3 0
    4 5 6 0
    7 8 9 0
    10 11 12 0
    -1 -4 0
    -1 -7 0
    -1 -10 0
    -4 -7 0
    -4 -10 0
    -7 -10 0
    -2 -5 0
    -2 -8 0
    -2 -11 0
    -5 -8 0
    -5 -11 0
    -8 -11 0
    -3 -6 0
    -3 -9 0
    -3 -12 0
    -6 -9 0
    -6 -12 0
    -9 -12 0
    """
    cnf_unsat = parse_dimacs(php_4_3)
    res_unsat, model_unsat, stats = solve_dimacs(cnf_unsat)
    assert res_unsat is SolveResult.UNSAT
    assert model_unsat is None
    assert stats["conflicts"] > 0
