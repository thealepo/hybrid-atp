from abc import ABC , abstractmethod
from typing import Tuple , List
from lean_dojo import TacticState
from llm_layer.data_structures.base import TacticCandidate

class SearchStrategy(ABC):
    @abstractmethod
    def add_state(self , state: TacticState , path: List[TacticCandidate] , depth: int):
        ...

    @abstractmethod
    def get_next_state(self) -> Tuple[TacticState, List[TacticCandidate], int]:
        ...

    @abstractmethod
    def has_next(self) -> bool:
        ...