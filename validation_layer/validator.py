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
        self.environment = ProofEnvironment()
    
    def validate(self , goal_state: LeanGoalState , tactic_code: str) -> ValidationResponse:
        base_path = goal_to_file(goal_state=goal_state)

        # temporary temp copy every attempt
        temp_dir = tempfile.gettempdir()
        temp_path = os.path.join(temp_dir , f'temp_{os.getpid()}_{os.urandom(4).hex()}.lean')

        shutil.copy(base_path , temp_path)

        # Append the new tactic
        with open(temp_path, "a", encoding="utf-8") as f:
            f.write(f"\n  {tactic_code}\n")

        # Run Lean on the temp file
        success, error = self.environment.proof_check(temp_path)

        if success:
            # checking if finishes proof
            if self._is_goal_finished(temp_path):
                result = ValidationResult.PROOF_FINISHED
            else:
                result = ValidationResult.VALID
        else:
            result = ValidationResult.INVALID
        
        return ValidationResponse(
            result_type=result,
            error=error if not success else None,
            file_path=temp_path
        )

    def _is_goal_finished(self , file_path: str) -> bool:
        with open(file_path , 'r' , encoding='utf-8') as f:
            contents = f.read()
        return any(kw in contents for kw in ["qed", "done", "exact", "rfl"])

        # truth is, in the future we would have to parse whether Lean reports "'goals':[]" at the end of the file.