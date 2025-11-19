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
    def __init__(self , repo_url: str , file_path: str , theorem_name: str):
        self.repo = LeanGitRepo(repo_url , 'be5e7c616339bf31dbc732277a12edd5ef8bdb92')  # hash of repo, put on environment variable?

        self.theorem = Theorem(self.repo , file_path , theorem_name)

        self.dojo , self.initial_state = Dojo(
            self.theorem
        ).__enter__()

    def get_initial_state(self) -> TacticState:
        return self.initial_state

    def validate(self , state: TacticState , tactic_code: str) -> ValidationResponse:
        next_state = self.dojo.run_tac(state , tactic_code)

        if isinstance(next_state , ProofFinished):
            return ValidationResponse(ValidationResult.PROOF_FINISHED , next_state=None)
        
        if isinstance(next_state , LeanError):
            return ValidationResponse(ValidationResult.INVALID , next_state=None , error=str(next_state))

        return ValidationResponse(ValidationResult.VALID , next_state=next_state)

    def close(self):
        self.dojo.__exit__(None , None , None)