import re
import sys , os
from dotenv import load_dotenv
from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional , Dict
# notebook imports
from lean_dojo import (
    LeanGitRepo , Theorem , Dojo , TacticState , ProofFinished , LeanError , TracedRepo
)

load_dotenv()
COMMIT_HASH = os.getenv('LEANGITREPO_COMMIT_HASH')

os.environ["GITHUB_TOKEN"] = os.getenv("GITHUB_TOKEN")

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
    def __init__(self , repo_path: str = 'https://github.com/leanprover-community/mathlib4' , commit: str = '68abb997e5168875b210d31c6c31588b0998db03'):
        self.repo_path = repo_path
        self.commit = commit

        self.repo = LeanGitRepo(
            url=self.repo_path,
            commit=self.commit
        )

    def get_theorem(self , file_path: str , theorem_name: str):
        return Theorem(
            repo=self.repo,
            file_path=file_path,
            theorem_name=theorem_name
        )

    def get_dojo(self , theorem):
        return Dojo(theorem)

class LeanValidator:
    def __init__(self , repo_path: str , file_path: str , theorem_name: str):
        self.lean_wrapper = LeanWrapper(repo_path=repo_path)
        self.theorem = self.lean_wrapper.get_theorem(file_path=file_path , theorem_name=theorem_name)
    
        # load dojo
        self.dojo = self.lean_wrapper.get_dojo(self.theorem)

    def validate_tactic(self , current_state: TacticState , tactic_code) -> ValidationResponse:
        ''' def search(state: TacticState , depth: int) -> Optional(Proof) '''
        result = self.dojo.run_tac(current_state , tactic_code)

        if isinstance(result , ProofFinished):
            return ValidationResponse(result_type=ValidationResult.PROOF_FINISHED , new_state=None , error_msg=None)
        elif isinstance(result , TacticState):
            return ValidationResponse(result_type=ValidationResult.VALID , new_state=result , error_msg=None)
        else:
            return ValidationResponse(result_type=ValidationResult.INVALID , new_state=None , error_msg='INVALID')