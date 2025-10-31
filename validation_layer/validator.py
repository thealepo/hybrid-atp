from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional
from lean_proof_environment import ProofEnvironment
from utils import goal_to_file
from llm_layer.data_structures.base import LeanGoalState

class ValidationResult(Enum):
    VALID = auto()
    INVALID = auto()
    PROOF_FINISHED = auto()

@dataclass
class ValidationResponse:
    result_type: ValidationResult
    error: Optional[str] = None

class LeanValidator:
    def __init__(self):
        self.environment = ProofEnvironment()
    
    def validate(self , goal_state: LeanGoalState , tactic_code: str) -> ValidationResponse:
        file_path = goal_to_file(goal_state=goal_state)

        with open(file_path , 'a') as f:
            f.write(f'\n{tactic_code}\n')
        
        success , error = self.environment.proof_check(file_path)

        if success:
            return ValidationResponse(
                result_type=ValidationResult.PROOF_FINISHED
            )
        else:
            return ValidationResponse(
                result_type=ValidationResult.INVALID
            )