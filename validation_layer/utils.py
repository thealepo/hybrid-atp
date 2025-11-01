import tempfile
import os
from llm_layer.data_structures.base import LeanGoalState

def goal_to_file(goal_state: LeanGoalState) -> str:
    # convert LeanGoalState to a temporary .lean file and return file path
    if goal_state is None or not getattr(goal_state, "goal", None):
        raise ValueError("goal_state is missing or invalid")
    
    temp_dir = tempfile.gettempdir()
    file_path = os.path.join(temp_dir , 'temp_goal.lean')

    # convert goal_state to a .lean file
    goal_text = f'''
    import Mathlib

    theorem temp_goal : {goal_state.goal} := by
    '''

    with open(file_path , 'w' , encoding='utf-8') as f:
        f.write(goal_text)
    
    return file_path
