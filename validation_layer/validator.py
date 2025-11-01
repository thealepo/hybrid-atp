import os
import tempfile
import shutil
from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional
from validation_layer.lean_proof_environment import ProofEnvironment
from validation_layer.utils import goal_to_file
from llm_layer.data_structures.base import LeanGoalState

class ValidationResult(Enum):
    VALID = auto()
    INVALID = auto()
    PROOF_FINISHED = auto()

@dataclass
class ValidationResponse:
    result_type: ValidationResult
    error: Optional[str] = None
    file_path: Optional[str] = None

class LeanValidator:
    def __init__(self):
        project_root = os.path.join(os.path.dirname(__file__), "..", "lean_core")
        self.environment = ProofEnvironment(project_root)
    
    def validate(self, goal_state: LeanGoalState, tactic_code: str) -> ValidationResponse:
        file_path = goal_to_file(goal_state)

        # Append the tactic to the temp goal
        with open(file_path, "a", encoding="utf-8") as f:
            f.write(f"  {tactic_code}\n")
        
        print(f'2: {tactic_code}')
        
        # appending tactic to temp_goal.lean
        success , error = self.environment.proof_check(file_path)

        if success:
            result = ValidationResult.PROOF_FINISHED
            print(f'3: result: {result}')
        else:
            result = ValidationResult.INVALID
            print(f'3: result: {result}')

        return ValidationResponse(
            result_type=result,
            error=error,
            file_path=file_path
        )

    def _is_goal_finished(self , file_path: str) -> bool:
        print('7.')
        return True

        # truth is, in the future we would have to parse whether Lean reports "'goals':[]" at the end of the file.