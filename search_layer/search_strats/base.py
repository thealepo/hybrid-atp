from abc import ABC , abstractmethod
from typing import Tuple , List
from llm_layer.data_structures.base import LeanGoalState

class SearchStrategy(ABC):
    @abstractmethod
    def add_state(self , state: LeanGoalState , path: List[str] , depth: int):
        ...

    @abstractmethod
    def get_next_state(self):
        ...

    @abstractmethod
    def has_next(self) -> bool:
        ...