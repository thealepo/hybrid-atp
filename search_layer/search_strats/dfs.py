from typing import List , Tuple
from .base import SearchStrategy
from lean_dojo import TacticState
from llm_layer.data_structures.base import TacticCandidate

class DFS(SearchStrategy):
    def __init__(self):
        super().__init__()
        self.stack: List[Tuple[TacticState, List[TacticCandidate], int]] = []

    def add_state(self , state: TacticState , path: List[TacticCandidate] , depth: int):
        self.stack.append((state , path , depth))

    def get_next_state(self) -> Tuple[TacticState, List[TacticCandidate], int]:
        return self.stack.pop()

    def has_next(self) -> bool:
        return bool(self.stack)