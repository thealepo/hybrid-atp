# this is the class for the Monte-Carlo Search Tree

'''
algo designed for problems with large decision spaces so its good for this

It is a 4-Phase Algo:
    - Selection: starting from root node, traverse down tree using a selection policy, most common being UCB applied to trees (UCT)
    - Expansion: when selection phase reaches a nonterminal leaf, algo expands the tree by adding one or mode child nodes
    - Simulation: from the newly added node, a random playout is performed until reaching a terminal state, in which moves are randomly chosen
    - Backpropogation: result of the simulation is propogated back up the tree, updating statistics for all visited nodes

SKELETON:
class MCTSNode:
    def __init__(self, state, parent=None, action=None):
        self.state = state                    # Current board
        self.parent = parent                  # Parent node
        self.action = action                  # Move leading to this node
        self.children = []                    # List of children
        self.visits = 0                       # Visit count
        self.wins = 0                         # Win count
        self.untried_actions = self.get_actions()  # Available moves

    def get_actions(self):
        """Return all empty cells."""
        return [(i, j) for i in range(3) for j in range(3) if self.state[i][j] == 0]

    def is_terminal(self):
        """Check if the game has ended."""
        return self.check_winner() is not None or not self.get_actions()

    def is_fully_expanded(self):
        return len(self.untried_actions) == 0

    def check_winner(self):
        """Find winner (1 or 2) or None."""
        for i in range(3):
            if self.state[i][0] == self.state[i][1] == self.state[i][2] != 0:
                return self.state[i][0]
            if self.state[0][i] == self.state[1][i] == self.state[2][i] != 0:
                return self.state[0][i]
        if self.state[0][0] == self.state[1][1] == self.state[2][2] != 0:
            return self.state[0][0]
        if self.state[0][2] == self.state[1][1] == self.state[2][0] != 0:
            return self.state[0][2]
        return None

    def expand(self):
        """Add one of the remaining actions as a child."""
        action = self.untried_actions.pop()
        new_state = [row[:] for row in self.state]
        player = self.get_current_player()
        new_state[action[0]][action[1]] = player
        child = MCTSNode(new_state, parent=self, action=action)
        self.children.append(child)
        return child

    def get_current_player(self):
        """Find whose turn it is."""
        x_count = sum(row.count(1) for row in self.state)
        o_count = sum(row.count(2) for row in self.state)
        return 1 if x_count == o_count else 2

    def best_child(self, c=1.4):
        """Select child with best UCB1 score."""
        return max(self.children, key=lambda child:
                   (child.wins / child.visits) +
                   c * math.sqrt(math.log(self.visits) / child.visits))

    def rollout(self):
        """Play random moves until the game ends."""
        state = [row[:] for row in self.state]
        player = self.get_current_player()

        while True:
            winner = self.check_winner_for_state(state)
            if winner: return 1 if winner == 1 else 0

            actions = [(i, j) for i in range(3) for j in range(3) if state[i][j] == 0]
            if not actions: return 0.5  # Draw

            move = random.choice(actions)
            state[move[0]][move[1]] = player
            player = 1 if player == 2 else 2

    def check_winner_for_state(self, state):
        """Same winner check for rollout."""
        return MCTSNode(state).check_winner()

    def backpropagate(self, result):
        """Update stats up the tree."""
        self.visits += 1
        self.wins += result
        if self.parent:
            self.parent.backpropagate(result)

IMPLEMENTATION:
def mcts_search(root_state, iterations=500):
    root = MCTSNode(root_state)

    for _ in range(iterations):
        node = root

        # Selection
        while not node.is_terminal() and node.is_fully_expanded():
            node = node.best_child()

        # Expansion
        if not node.is_terminal():
            node = node.expand()

        # Simulation
        result = node.rollout()

        # Backpropagation
        node.backpropagate(result)

    return root.best_child(c=0).action  # Return best move

TIC-TAC-TOE EXAMPLE:
def play_game():
    board = [[0]*3 for _ in range(3)]
    current_player = 1

    print("MCTS Tic-Tac-Toe Demo")
    print("0 = empty, 1 = X, 2 = O\n")

    for turn in range(9):
        for row in board: print(row)
        print()

        if current_player == 1:
            move = mcts_search(board, iterations=500)
            print(f"MCTS plays: {move}")
        else:
            empty = [(i, j) for i in range(3) for j in range(3) if board[i][j] == 0]
            move = random.choice(empty)
            print(f"Random plays: {move}")

        board[move[0]][move[1]] = current_player

        if MCTSNode(board).check_winner():
            for row in board: print(row)
            print(f"Player {current_player} wins!")
            return

        current_player = 1 if current_player == 2 else 2

    print("Draw!")
'''
import math
import random
from typing import Optional , List
from .base import SearchStrategy
from llm_layer.data_structures.base import LeanGoalState

class MCTSNode:
    def __init__(self , state: LeanGoalState , parent: Optional['MCTSNode'] = None , action: Optional[str] = None):
        self.state = state
        self.parent = parent
        self.action = action

        self.children = List['MCTSNode'] = []
        self.visits = 0
        self.value = 0.0
        self.untried_actions = []

    def is_fully_expanded(self) -> bool:
        return len(self.untried_actions) == 0

    def best_child(self , c: float = 1.4) -> 'MCTSNode':
        # UCT formula
        def uct_value(child: 'MCTSNode') -> float:
            if child.visits == 0:
                return float('inf')

            exploitation = child.value / child.visits
            exploration = c * math.sqrt(
                math.log(self.visits) / child.visits
            )

            return exploitation + exploration

        return max(self.children , key=uct_value)

    def backpropagate(self , result: float):
        self.visits += 1
        self.value += result

        if self.parent:
            self.parent.backpropagate(result)

class MCTS(SearchStrategy):
    def __init__(self , iterations: int = 200):
        super().__init__()
        self.iterations = iterations

    def search(self , root_state: LeanGoalState , generate_next_states):
        root = MCTSNode(root_state)
        root.untried_actions = generate_next_states(root.state)

        for _ in range(self.iterations):
            node = root
                
            # SELECTION: descend using UCB until a leaf
            while node.is_fully_expanded() and node.children:
                node = node.best_child

            # EXPANSION: expand if possible
            if not node.is_fully_expanded():
                next_state , tactic , estimation = node.untried_actions.pop(
                    random.randrange(len(node.untried_actions))
                )

                child = MCTSNode(
                    next_state , parent=node , action=tactic
                )
                child.untried_actions = generate_next_states(child.state)

                node.children.append(child)
                node = child
                
            # SIMULATION
            result = self.simulate(
                node.state , generate_next_states
            )

            # BACKPROPOGATION
            node.backpropagate(result)

        if not root.children:
            return None , None

        best = max(root.children , key=lambda child: child.visits)
        return best.action , best.state

    def simulate(self , state: LeanGoalState , generate_next_states):
        ...
            