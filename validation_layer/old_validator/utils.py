import os
import uuid
from llm_layer.data_structures.base import LeanGoalState

def goal_to_file(goal_state: LeanGoalState) -> str:
    
    project_root = os.path.join(os.path.dirname(__file__), '..', 'lean_core')
    temp_dir = os.path.join(project_root, 'HybridAtp')
    os.makedirs(temp_dir, exist_ok=True)

    unique_name = f"temp_goal_{uuid.uuid4().hex[:8]}.lean"
    file_path = os.path.join(temp_dir, unique_name)

    # Cleanup goal for Lean syntax
    goal = goal_state.goal.replace('⊢', '').strip()

    goal_text = f"""import Mathlib

theorem temp_goal : {goal} := by
"""

    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(goal_text)

    return file_path
