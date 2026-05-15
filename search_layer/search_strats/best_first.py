from __future__ import annotations

import heapq
import itertools
from typing import List, Tuple

from lean_dojo import TacticState

from llm_layer.data_structures.base import TacticCandidate

from .base import SearchStrategy


class BestFirst(SearchStrategy):
    def __init__(self):
        self._heap: List[Tuple[float , int , int , TacticState , List[TacticCandidate] , int]] = []
        self._counter = itertools.count()

    def add_state(self , state: TacticState , path: List[TacticCandidate] , depth: int , score: float = 0.0) -> None:
        # Negate score because heapq is a min-heap.
        idx = next(self._counter)
        heapq.heappush(self._heap , (-score , depth , idx , state , path , depth))

    def get_next_state(self) -> Tuple[TacticState , List[TacticCandidate] , int]:
        _neg_score , _d_key , _idx , state , path , depth = heapq.heappop(self._heap)
        return state , path , depth

    def has_next(self) -> bool:
        return bool(self._heap)
