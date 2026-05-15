from collections import deque
from typing import Deque, List, Tuple

from lean_dojo import TacticState

from llm_layer.data_structures.base import TacticCandidate

from .base import SearchStrategy


class BFS(SearchStrategy):
    def __init__(self):
        self.queue: Deque[Tuple[TacticState , List[TacticCandidate] , int]] = deque()

    def add_state(self , state: TacticState , path: List[TacticCandidate] , depth: int , score: float = 0.0) -> None:
        self.queue.append((state , path , depth))

    def get_next_state(self) -> Tuple[TacticState , List[TacticCandidate] , int]:
        return self.queue.popleft()

    def has_next(self) -> bool:
        return bool(self.queue)
