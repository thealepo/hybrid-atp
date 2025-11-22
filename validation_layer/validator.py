from lean_dojo import *
from dataclasses import dataclass
from enum import Enum , auto
from typing import Optional

class ValidationResult(Enum):
    VALID = auto()
    INVALID = auto()
    PROOF_FINISHED = auto()

@dataclass
class ValidationResponse:
    result_type: ValidationResult
    next_state: Optional[TacticState] = None
    error: Optional[str] = None

class LeanDojoValidator:
    def __init__(self ,  file_path: str , theorem_name: str , repo_url: str = "https://github.com/leanprover-community/mathlib4" , repo_hash: str = 'b5eba595428809e96f3ed113bc7ba776c5f801ac'):
        self.repo = LeanGitRepo(repo_url , repo_hash)

        self.theorem = Theorem(self.repo , file_path , theorem_name)

        self.dojo = None
        self.initial_state = None

    def initialize(self):
        self.dojo , self.initial_state = Dojo(
            self.theorem
        ).__enter__()
        return self.initial_state

    def get_initial_state(self) -> TacticState:
        if self.initial_state is None:
            return self.initialize()
        return self.initial_state

    def validate(self , state: TacticState , tactic_code: str) -> ValidationResponse:
        next_state = self.dojo.run_tac(state , tactic_code)

        if isinstance(next_state , ProofFinished):
            return ValidationResponse(ValidationResult.PROOF_FINISHED , next_state=None)
        
        if isinstance(next_state , LeanError):
            return ValidationResponse(ValidationResult.INVALID , next_state=None , error=str(next_state))

        return ValidationResponse(ValidationResult.VALID , next_state=next_state)

    def close(self):
        if self.dojo:
            self.dojo.__exit__(None , None , None)