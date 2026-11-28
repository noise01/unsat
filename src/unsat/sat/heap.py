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
        heap = self._heap
        pos = self._pos
        act = self._activities
        var = heap[idx]
        act_var = act[var]
        while idx > 0:
            parent_idx = (idx - 1) >> 1
            parent_var = heap[parent_idx]
            act_parent = act[parent_var]
            if act_var < act_parent or (act_var == act_parent and var >= parent_var):
                break
            heap[idx] = parent_var
            pos[parent_var] = idx
            idx = parent_idx
        heap[idx] = var
        pos[var] = idx

    def _sift_down(self, idx: int) -> None:
        heap = self._heap
        pos = self._pos
        act = self._activities
        size = len(heap)
        var = heap[idx]
        act_var = act[var]
        while True:
            left_idx = (idx << 1) + 1
            if left_idx >= size:
                break
            best_idx = left_idx
            best_var = heap[left_idx]
            best_act = act[best_var]
            right_idx = left_idx + 1
            if right_idx < size:
                right_var = heap[right_idx]
                right_act = act[right_var]
                if right_act > best_act or (right_act == best_act and right_var < best_var):
                    best_idx = right_idx
                    best_var = right_var
                    best_act = right_act
            if best_act < act_var or (best_act == act_var and best_var >= var):
                break
            heap[idx] = best_var
            pos[best_var] = idx
            idx = best_idx
        heap[idx] = var
        pos[var] = idx
