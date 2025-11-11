import os
from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional
from validation_layer.lean_proof_environment import ProofEnvironment
from validation_layer.utils import goal_to_file
from llm_layer.data_structures.base import LeanGoalState

import threading

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
        self.project_root = os.path.join(
            os.path.dirname(__file__) , '..' , 'lean_core'
        )

        self._cache = {}
        self._lock = threading.Lock()

    def _cache_key(self, goal_state: LeanGoalState, tactic_code: str):
        return (hash(str(goal_state)), tactic_code)
    
    def validate(self, goal_state: LeanGoalState, tactic_code: str) -> ValidationResponse:
        key = self._cache_key(goal_state , tactic_code)
        with self._lock:
            if key in self._cache:
                return self._cache[key]

        file_path = goal_to_file(goal_state)
        with open(file_path, "a", encoding="utf-8") as f:
            f.write(f"  {tactic_code}\n")

        success, error = self.environment.proof_check(file_path, self.project_root)

        # check if proof finished by searching for sorry or leftover goals
        if success and self._is_goal_finished(file_path):
            result = ValidationResult.PROOF_FINISHED
        elif success:
            result = ValidationResult.VALID
        else:
            result = ValidationResult.INVALID

        response = ValidationResponse(result_type=result, error=error, file_path=file_path)

        with self._lock:
            self._cache[key] = response

        return response

    def _is_goal_finished(self, file_path: str) -> bool:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        return 'sorry' not in content