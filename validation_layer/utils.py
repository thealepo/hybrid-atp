import os
from llm_layer.data_structures.base import LeanGoalState

def goal_to_file(goal_state: LeanGoalState) -> str:
    # convert LeanGoalState to a temporary .lean file and return file path
    project_root = os.path.join(
        os.path.dirname(__file__),
        '..',
        'lean_core'
    )
    temp_dir = os.path.join(project_root , 'temp_goals')
    os.makedirs(temp_dir , exist_ok=True)

    file_path = os.path.join(temp_dir , 'temp_goal.lean')

    # claude-suggested cleanup goal text (for Lean syntax)
    goal = goal_state.goal.replace('⊢' , '').strip()
    print(f'4: {goal}')

    # convert goal_state to a .lean file
    goal_text = f'''import Mathlib
import HybridAtp.Basic

theorem temp_goal : {goal} := by
'''

    with open(file_path , 'w' , encoding='utf-8') as f:
        f.write(goal_text)
    
    return file_path
