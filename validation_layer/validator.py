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
        self.repo = LeanGitRepo(repo_url , '48b7eb4c1789b21a9804ba876d458c2e95b45fd7')  # hash of repo, put on environment variable?

        traced_repo = trace(self.repo)
        theorems = traced_repo.get_traced_theorems()

        state_tactic_pairs = []
        for theorem in theorems:
            for t in theorem.get_traced_tactics():
                state_tactic_pairs.append((t.state_before() , t.tactic()))

        self.state_tactic_pairs = state_tactic_pairs

    def get_initial_state(self) -> TacticState:
        ...

    def validate(self , state: TacticState , tactic_code: str) -> ValidationResponse:
        next_state = self.dojo.run_tac(state , tactic_code)

        if isinstance(next_state , ProofFinished):
            return ValidationResponse(ValidationResult.PROOF_FINISHED , next_state=None)
        
        if isinstance(next_state , LeanError):
            return ValidationResponse(ValidationResult.INVALID , next_state=None , error=str(next_state))

        return ValidationResponse(ValidationResult.VALID , next_state=next_state)