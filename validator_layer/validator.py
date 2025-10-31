import os
from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional
# notebook imports
from lean_dojo import (
    LeanGitRepo , Theorem , Dojo , TacticState , ProofFinished, TracedRepo
)


class ValidationResult(Enum):
    VALID = auto()
    INVALID = auto()
    PROOF_FINISHED = auto()

@dataclass
class ValidationResponse:
    result_type: ValidationResult
    new_state: Optional[TacticState] = None
    error_msg: Optional[str] = None

class LeanWrapper:
    def __init__(self , repo_url: str = 'https://github.com/leanprover-community/mathlib4' , commit: str = '68abb997e5168875b210d31c6c31588b0998db03'):
        self.repo = LeanGitRepo(
            url=repo_url,
            commit=commit
        )

    def get_theorem(self , file_path: str , theorem_name: str) -> Theorem:
        return Theorem(
            repo=self.repo,
            file_path=file_path,
            full_name=theorem_name
        )

    def get_dojo(self , theorem) -> Dojo:
        return Dojo(theorem)

class LeanValidator:
    def __init__(self , repo_url: str , file_path: str , theorem_name: str):
        self.lean_wrapper = LeanWrapper(repo_url=repo_url)
        self.theorem = self.lean_wrapper.get_theorem(file_path=file_path , theorem_name=theorem_name)

        # traced repo
        self.traced_repo = TracedRepo(self.wrapper.repo)
        self.traced_theorem = self.traced_repo.get_traced_theorem(self.theorem)

        # load dojo
        self.dojo = self.lean_wrapper.get_dojo(self.theorem)

        traced_tactics = getattr(self.traced_theorem , 'traced_tactics' , [])
        self.initial_state = traced_tactics[0].tactic_state if traced_tactics else None

    def validate_tactic(self , current_state: TacticState , tactic_code) -> ValidationResponse:
        ''' def search(state: TacticState , depth: int) -> Optional(Proof) '''
        result = self.dojo.run_tac(current_state , tactic_code)

        if isinstance(result , ProofFinished):
            return ValidationResponse(result_type=ValidationResult.PROOF_FINISHED , new_state=None , error_msg=None)
        elif isinstance(result , TacticState):
            return ValidationResponse(result_type=ValidationResult.VALID , new_state=result , error_msg=None)
        else:
            return ValidationResponse(result_type=ValidationResult.INVALID , new_state=None , error_msg='INVALID')