from abc import ABC, abstractmethod
from typing import List, Tuple

from lean_dojo import TacticState

from llm_layer.data_structures.base import TacticCandidate


class SearchStrategy(ABC):

    @abstractmethod
    def add_state(self , state: TacticState , path: List[TacticCandidate] , depth: int , score: float = 0.0) -> None:
        ...

    @abstractmethod
    def get_next_state(self) -> Tuple[TacticState , List[TacticCandidate] , int]:
        ...

    @abstractmethod
    def has_next(self) -> bool:
        ...
