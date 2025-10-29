import re
from typing import Dict
from lean_dojo import TacticState
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState

def translation(tactic_state: TacticState , proof_depth: int = 0) -> LeanGoalState:
    # goal is to translate the symbolic TacticState from lean_dojo to the LeanGoalState dataclass

    state_string = tactic_state.pretty()

    return LeanGoalState(
        goal=...,
        hypothesis=...,
        local_context=state_string,
        proof_depth=proof_depth
    )

    # i have to explore the state_string object.