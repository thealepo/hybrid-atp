from .base import SearchStrategy
from .best_first import BestFirst
from .bfs import BFS
from .dfs import DFS
from .mcts import MCTS

__all__ = ["SearchStrategy" , "DFS" , "BFS" , "BestFirst" , "MCTS"]


def make_strategy(name: str) -> SearchStrategy:
    name = name.lower()
    if name == "dfs":
        return DFS()
    if name == "bfs":
        return BFS()
    if name in ("best" , "best_first" , "bestfirst"):
        return BestFirst()
    if name == "mcts":
        return MCTS()
    raise ValueError(f"unknown search strategy: {name}")
