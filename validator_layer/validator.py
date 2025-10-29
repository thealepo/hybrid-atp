import re
from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional , Dict
# notebook imports
from lean_dojo import (
    LeanGitRepo , Theorem , Dojo , TacticState , ProofFinished , LeanError , TracedRepo
)


class ValidationResult(Enum):
    VALID = auto()
    INVALID = auto()
    PROOF_FINISHED = auto()

@dataclass
class ValidationResponse:
    result_type = ValidationResult
    new_state = Optional[TacticState] = None
    error_msg = Optional[str] = None

class LeanValidator:
    def __init__(self , repo: LeanGitRepo , file_path , theorem_name):
        self.traced_repo = TracedRepo(self.repo)
        self.theorem = Theorem(self.repo, file_path, theorem_name)
        self.traced_theorem = self.traced_repo.get_traced_theorem(self.theorem)
        self.dojo = Dojo(self.theorem)
        self.initial_state = self.traced_theorem.tactic_states[0]
    # we have to find a new way to initialize a tactic state. probably should look into old docs and see how the old get_initial_state() worked, and replicate.
    
    def validate_tactic(self , current_state , tactic_code):
        ''' def search(state: TacticState , depth: int) -> Optional(Proof) '''
        result = self.dojo.run_tac(current_state , tactic_code)

        if isinstance(result , ProofFinished):
            return ValidationResponse(result_type=ValidationResult.PROOF_FINISHED , new_state=None , error_msg=None)
        elif isinstance(result , TacticState):
            return ValidationResponse(result_type=ValidationResult.VALID , new_state=result , error_msg=None)
        else:
            return ValidationResponse(result_type=ValidationResult.INVALID , new_state=None , error_msg='INVALID')