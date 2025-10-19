import re
from enum import Enum
from dataclasses import dataclass
from typing import Optional , Dict
# notebook imports
from lean_dojo import (
    LeanGitRepo , Theorem , Dojo , TacticState , ProofFinished , LeanError
)
import sys
import os

from numpy import result_type

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState


class ValidationResult:
    VALID = ...
    INVALID = ...
    PROOF_FINISHED = ...

@dataclass
class ValidationResponse:
    result_type = ValidationResult
    new_state = Optional[TacticState] = None
    error_msg = Optional[str]

class LeanValidator:
    def __init__(self , repo , file_path , theorem_name):
        self.theorem = Theorem(repo , file_path , theorem_name)
        self.dojo = Dojo(self.theorem)
        self.initial_state = self.dojo.get_initial_state()  # for some reason this method is not working anymore, must check docs
    
    def validate_tactic(self , current_state , tactic_code):
        ''' def search(state: TacticState , depth: int) -> Optional(Proof) '''
        result = self.dojo.run_tac(current_state , tactic_code)

        if isinstance(result , ProofFinished):
            return ValidationResponse(result_type=ValidationResult.PROOF_FINISHED)
        elif isinstance(result , TacticState):
            return ValidationResponse(result_type=ValidationResult.VALID)