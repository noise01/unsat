from typing import Literal

import pytest
from hypothesis import given
from hypothesis import strategies as st

from unsat.sat.heap import VarMaxHeap

type HeapOp = (
    tuple[Literal["insert", "pop", "rescale"], int] | tuple[Literal["bump"], int, float]
)


def _assert_heap_invariants(heap: VarMaxHeap, expected: dict[int, float]) -> None:
    assert len(heap) == len(expected)
    assert heap.empty() == (not expected)
    for var in range(len(heap._pos)):
        pos = heap._pos[var]
        if var in expected:
            assert 0 <= pos < len(heap._heap)
            assert heap._heap[pos] == var
        else:
            assert pos == -1

    for idx, var in enumerate(heap._heap):
        assert heap._pos[var] == idx
        if idx > 0:
            parent = heap._heap[(idx - 1) >> 1]
            assert not heap._higher(var, parent)


def test_heap_basic_operations_and_tie_breaking() -> None:
    activities = [1.0, 3.0, 3.0, 2.0]
    heap = VarMaxHeap(activities)
    heap.ensure_size(4)

    for var in (0, 1, 2, 3):
        heap.insert(var)
    # Idempotent duplicate insert.
    heap.insert(2)

    assert len(heap) == 4
    assert 2 in heap
    assert 4 not in heap

    # Tie between var 1 and var 2 (both 3.0): smaller var index wins first.
    assert heap.pop_max() == 1
    assert 1 not in heap

    # Bump var 0 above var 2.
    activities[0] = 5.0
    heap.increase(0)
    assert heap.pop_max() == 0
    assert heap.pop_max() == 2
    assert heap.pop_max() == 3
    assert heap.empty()

    with pytest.raises(IndexError, match="empty"):
        heap.pop_max()


@given(
    num_vars=st.integers(min_value=1, max_value=20),
    ops=st.lists(
        st.one_of(
            st.tuples(st.just("insert"), st.integers(min_value=0, max_value=19)),
            st.tuples(
                st.just("bump"),
                st.integers(min_value=0, max_value=19),
                st.floats(
                    min_value=0.01,
                    max_value=10.0,
                    allow_nan=False,
                    allow_infinity=False,
                ),
            ),
            st.tuples(st.just("pop"), st.just(0)),
            st.tuples(st.just("rescale"), st.just(0)),
        ),
        min_size=1,
        max_size=80,
    ),
)
def test_heap_matches_reference_model(
    num_vars: int,
    ops: list[HeapOp],
) -> None:
    activities = [0.0] * num_vars
    heap = VarMaxHeap(activities)
    heap.ensure_size(num_vars)
    present: dict[int, float] = {}

    for op in ops:
        if op[0] == "insert":
            var = op[1] % num_vars
            heap.insert(var)
            present.setdefault(var, activities[var])
        elif op[0] == "bump":
            _, raw_var, delta = op
            var = raw_var % num_vars
            activities[var] += delta
            heap.increase(var)
            if var in present:
                present[var] = activities[var]
        elif op[0] == "pop":
            if present:
                expected_var = min(present, key=lambda v: (-present[v], v))
                assert heap.pop_max() == expected_var
                del present[expected_var]
            else:
                assert heap.empty()
        else:
            for v in range(num_vars):
                activities[v] *= 0.5
                if v in present:
                    present[v] = activities[v]
            heap.rebuild()

        _assert_heap_invariants(heap, present)
