"""Indexed binary max-heap for EVSIDS variable selection."""

from unsat.sat.types import Var


class VarMaxHeap:
    """Max-heap of variables ordered by mutable ``activities`` values."""

    def __init__(self, activities: list[float]) -> None:
        self._activities = activities
        self._heap: list[Var] = []
        self._pos: list[int] = []

    def ensure_size(self, num_vars: int) -> None:
        """Ensure internal position tracking accommodates ``num_vars`` variables."""
        if num_vars > len(self._pos):
            self._pos.extend([-1] * (num_vars - len(self._pos)))

    def __contains__(self, var: Var) -> bool:
        return 0 <= var < len(self._pos) and self._pos[var] != -1

    def __len__(self) -> int:
        return len(self._heap)

    def empty(self) -> bool:
        """Return ``True`` when the heap has no variables."""
        return not self._heap

    def insert(self, var: Var) -> None:
        """Insert ``var`` into the heap if not already present."""
        if var >= len(self._pos):
            self.ensure_size(var + 1)
        if self._pos[var] != -1:
            return
        idx = len(self._heap)
        self._heap.append(var)
        self._pos[var] = idx
        self._sift_up(idx)

    def increase(self, var: Var) -> None:
        """Restore heap order after ``activities[var]`` increases."""
        if var >= len(self._pos):
            return
        idx = self._pos[var]
        if idx != -1:
            self._sift_up(idx)

    def rebuild(self) -> None:
        """Restore heap order across all present variables after bulk rescaling."""
        for idx in range(len(self._heap) // 2 - 1, -1, -1):
            self._sift_down(idx)

    def pop_max(self) -> Var:
        """Remove and return the highest-priority variable."""
        if not self._heap:
            msg = "Cannot pop from an empty VarMaxHeap"
            raise IndexError(msg)
        top = self._heap[0]
        last = self._heap.pop()
        self._pos[top] = -1
        if self._heap:
            self._heap[0] = last
            self._pos[last] = 0
            self._sift_down(0)
        return top

    def _higher(self, a: Var, b: Var) -> bool:
        act_a = self._activities[a]
        act_b = self._activities[b]
        return act_a > act_b or (act_a == act_b and a < b)

    def _sift_up(self, idx: int) -> None:
        var = self._heap[idx]
        while idx > 0:
            parent_idx = (idx - 1) >> 1
            parent_var = self._heap[parent_idx]
            if not self._higher(var, parent_var):
                break
            self._heap[idx] = parent_var
            self._pos[parent_var] = idx
            idx = parent_idx
        self._heap[idx] = var
        self._pos[var] = idx

    def _sift_down(self, idx: int) -> None:
        size = len(self._heap)
        var = self._heap[idx]
        while True:
            left_idx = (idx << 1) + 1
            if left_idx >= size:
                break
            best_idx = left_idx
            best_var = self._heap[left_idx]
            right_idx = left_idx + 1
            if right_idx < size:
                right_var = self._heap[right_idx]
                if self._higher(right_var, best_var):
                    best_idx = right_idx
                    best_var = right_var
            if not self._higher(best_var, var):
                break
            self._heap[idx] = best_var
            self._pos[best_var] = idx
            idx = best_idx
        self._heap[idx] = var
        self._pos[var] = idx
