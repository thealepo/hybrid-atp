from typing import List , Tuple
from .base import SearchStrategy
from llm_layer.data_structures.base import LeanGoalState

class DFS(SearchStrategy):
    def __init__(self):
        super().__init__()
        self.stack = []

    def add_state(self , state , path , depth):
        self.stack.append((state , path , depth))

    def get_next_state(self):
        return self.stack.pop()

    def has_next(self):
        return bool(self.stack)