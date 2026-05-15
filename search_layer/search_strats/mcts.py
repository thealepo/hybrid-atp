"""MCTS-style frontier compatible with the SearchStrategy interface.

This is a simplified UCT-flavored frontier: nodes are scored by an
upper-confidence bound that mixes their prior priority (from the LLM)
with how often the parent has been visited. The real backpropagation
happens in `Search` via `update_score(path, reward)`.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from lean_dojo import TacticState

from llm_layer.data_structures.base import TacticCandidate

from .base import SearchStrategy


def _state_key(state: TacticState) -> str:
    return state.pp


@dataclass
class _Node:
    state_key: str
    parent_key: Optional[str]
    path: List[TacticCandidate]
    depth: int
    prior: float = 0.0
    visits: int = 0
    value: float = 0.0
    state: Optional[TacticState] = None
    children: List[str] = field(default_factory=list)
    expanded: bool = False


class MCTS(SearchStrategy):
    def __init__(self, exploration_c: float = 1.4):
        self.c = exploration_c
        self.nodes: Dict[str, _Node] = {}
        self.root_key: Optional[str] = None

    def add_state(self, state: TacticState, path: List[TacticCandidate], depth: int, score: float = 0.0) -> None:
        key = _state_key(state)
        if key in self.nodes:
            existing = self.nodes[key]
            existing.prior = max(existing.prior, score)
            return

        parent_key: Optional[str] = None
        if path:
            # parent is the state-key the search loop already added; we can't easily
            # recover it here, so we attach to the current root for UCT scoring.
            parent_key = self.root_key

        node = _Node(
            state_key=key,
            parent_key=parent_key,
            path=path,
            depth=depth,
            prior=score,
            state=state,
        )
        self.nodes[key] = node
        if self.root_key is None:
            self.root_key = key
        elif parent_key and parent_key in self.nodes:
            self.nodes[parent_key].children.append(key)

    def _uct(self, node: _Node) -> float:
        parent_visits = self.nodes[node.parent_key].visits if node.parent_key and node.parent_key in self.nodes else 1
        exploitation = node.value / node.visits if node.visits else node.prior
        exploration = self.c * math.sqrt(math.log(max(1, parent_visits)) / max(1, node.visits))
        # Depth penalty discourages running away to unfounded branches.
        return exploitation + exploration - 0.01 * node.depth

    def has_next(self) -> bool:
        return any(not n.expanded for n in self.nodes.values())

    def get_next_state(self) -> Tuple[TacticState, List[TacticCandidate], int]:
        unexpanded = [n for n in self.nodes.values() if not n.expanded]
        if not unexpanded:
            raise StopIteration("MCTS frontier empty")
        best = max(unexpanded, key=self._uct)
        best.expanded = True
        best.visits += 1
        assert best.state is not None
        return best.state, best.path, best.depth

    def update_score(self, state: TacticState, reward: float) -> None:
        """Backpropagate a reward up the tree from `state`."""
        key = _state_key(state)
        node = self.nodes.get(key)
        while node is not None:
            node.visits += 1
            node.value += reward
            node = self.nodes.get(node.parent_key) if node.parent_key else None
