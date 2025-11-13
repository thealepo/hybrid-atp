import os
import json
import hashlib
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
        key_str = json.dumps({
            "goal": goal_state.goal,
            "hypothesis": goal_state.hypothesis,
            "context": goal_state.local_context,
            "tactic": tactic_code
        }, sort_keys=True)
        return hashlib.sha256(key_str.encode('utf-8')).hexdigest()

    def validate(self, goal_state: LeanGoalState, tactic_code: str) -> ValidationResponse:
        key = self._cache_key(goal_state , tactic_code)
        with self._lock:
            if key in self._cache:
                return self._cache[key]

        file_path = goal_to_file(goal_state)
        with open(file_path, "a", encoding="utf-8") as f:
            f.write(f"  {tactic_code}\n")

        success, error = self.environment.proof_check(file_path, self.project_root)

        if success and self._is_goal_finished(error):
            result = ValidationResult.PROOF_FINISHED
        elif success:
            result = ValidationResult.VALID
        else:
            result = ValidationResult.INVALID

        response = ValidationResponse(result_type=result, error=error, file_path=file_path)

        with self._lock:
            self._cache[key] = response

        if result == ValidationResult.INVALID:
            try:
                os.remove(file_path)
            except Exception:
                pass

        return response

    def _is_goal_finished(self, error_output: str) -> bool:

        if "unsolved goals" in error_output:
            return False
        if "error:" in error_output:
            return False

        if "no goals to be solved" in error_output:
            return True
            
        return False