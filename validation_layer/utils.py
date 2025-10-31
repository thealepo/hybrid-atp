import tempfile
import os
from llm_layer.data_structures.base import LeanGoalState

def goal_to_file(goal_state: LeanGoalState) -> str:
    # convert LeanGoalState to a temporary .lean file and return file path
    ...
