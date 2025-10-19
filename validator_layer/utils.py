import re
from typing import Dict
from lean_dojo import TacticState
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState

def translation(tactic_state: TacticState , proof_depth: int = 0) -> LeanGoalState:
    ...
    # goal is to translate the symbolic TacticState from lean_dojo to the LeanGoalState dataclass