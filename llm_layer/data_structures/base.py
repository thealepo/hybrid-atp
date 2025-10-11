from dataclasses import dataclass , field
from typing import List , Optional , Dict , Tuple

@dataclass
class LeanGoalState:
    goal: str
    hypothesis: Dict[str,str]
    local_context: List[str] = field(default_factory=list)
    proof_depth: int = 0

    def to_prompt_format(self) -> str:
        hypothesis_format = '\n'.join([f"{name}:{typ}" for name,typ in self.hypothesis.items()])
        context_format = '\n'.join(self.local_context) if self.local_context else "Standard Context"
        return f"""
        GOAL: {self.goal}

        HYPOTHESIS:
        {hypothesis_format}

        CONTEXT:
        {context_format}

        PROOF DEPTH: {self.proof_depth}
        """

@dataclass
class FailedTactic:
    '''failed tactic attempts'''
    tactic: str
    error_message: str
    goal_state: str

@dataclass
# search constraints built on theoretical weights. fuzzy cognitive map implementation unknown until now.
class SearchConstraints:
    primary_tactic_types: List[str]
    relevant_lemmas: List[str]
    avoid_tactics: List[str]
    expected_depth: int
    confidence: float
    tactic_weights: Dict[str,float]
    reasoning: str
    alternative_strategies: List[str] = field(default_factory=list)

    def get_weighted_tactics(self) -> List[Tuple[str,float]]:
        # should this be where the fuzzy cognitive map is implemented? we need weights for the tactics. here is a placeholder.
        return sorted(
            self.tactic_weights.items(),
            key=lambda x:x[1],
            reverse=True
        )
    def should_explore_alternatives(self) -> bool:
        return self.confidence < 0.8

@dataclass
class TacticCandidate:
    tactic_code: str
    tactic_type: str
    justification: str
    priority: float
    expected_subgoals: List[str]