# search_layer/search_strats/mcts.py
import math
import random
from typing import Optional, List, Callable, Tuple
from .base import SearchStrategy
from llm_layer.data_structures.base import LeanGoalState

class MCTSNode:
    def __init__(self, state: LeanGoalState, parent: Optional['MCTSNode'] = None, action: Optional[str] = None):
        self.state = state
        self.parent = parent
        self.action = action

        self.children: List['MCTSNode'] = []
        self.visits = 0
        self.value = 0.0
        self.untried_actions: List[Tuple[LeanGoalState, str, float]] = []

    def is_fully_expanded(self) -> bool:
        return len(self.untried_actions) == 0

    def best_child(self, c: float = 1.4) -> 'MCTSNode':
        def uct_value(child: 'MCTSNode') -> float:
            if child.visits == 0:
                return float('inf')
            exploitation = child.value / child.visits
            exploration = c * math.sqrt(math.log(max(1, self.visits)) / child.visits)
            return exploitation + exploration

        return max(self.children, key=uct_value)

    def backpropagate(self, result: float):
        self.visits += 1
        self.value += result
        if self.parent:
            self.parent.backpropagate(result)

class MCTS(SearchStrategy):
    def __init__(self, iterations: int = 200, rollout_depth: int = 8):
        super().__init__()
        self.iterations = iterations
        self.rollout_depth = rollout_depth

    def search(self, root_state: LeanGoalState, generate_next_states: Callable[[LeanGoalState], List[Tuple[LeanGoalState, str, float]]]):
        root = MCTSNode(root_state)
        root.untried_actions = generate_next_states(root.state)

        for _ in range(self.iterations):
            node = root

            # SELECTION
            while node.is_fully_expanded() and node.children:
                node = node.best_child()

            # EXPANSION
            if not node.is_fully_expanded():
                idx = random.randrange(len(node.untried_actions))
                next_state, tactic, estimation = node.untried_actions.pop(idx)
                child = MCTSNode(next_state, parent=node, action=tactic)
                child.untried_actions = generate_next_states(child.state)
                node.children.append(child)
                node = child

            # SIMULATION
            result = self.simulate(node.state, generate_next_states)

            # BACKPROPAGATION
            node.backpropagate(result)

        if not root.children:
            return None, None

        best = max(root.children, key=lambda child: child.visits)
        return best.action, best.state

    def simulate(self, state: LeanGoalState, generate_next_states: Callable[[LeanGoalState], List[Tuple[LeanGoalState, str, float]]]):
        current = state

        for _ in range(self.rollout_depth):
            actions = generate_next_states(current)
            if not actions:
                break
            next_state , _ , est = random.choice(actions)
            current = next_state

            if est >= 0.99:
                return 1.0

        return est if 'est' in locals() else 0.0