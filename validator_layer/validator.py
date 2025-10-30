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
COMMIT_HASH = os.getenv('LEANGITREPO_COMMIT_HASH')  # set to dbf90e0db68eba55c03d45fab71c1d42f2d6ec85 normally

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

class LeanValidator:
    def __init__(self , repo_path: str , file_path , theorem_name):
        
        # load repo
        self.repo = LeanGitRepo(repo_path , commit='68abb997e5168875b210d31c6c31588b0998db03')
        self.theorem = Theorem(self.repo , file_path , theorem_name)

        # load traced theorem
        self.traced_repo = TracedRepo(self.repo)
        self.traced_theorem = self.traced_repo.get_traced_theorem(self.theorem)

        # LeanDojo
        self.dojo = Dojo(self.theorem)

        traced_tactics = getattr(self.traced_theorem , 'traced_tactics' , [])
        self.initial_state = traced_tactics[0].tactic_state if traced_tactics else None
        print(traced_tactics[0].__dict__.keys())

    
    def validate_tactic(self , current_state: TacticState , tactic_code) -> ValidationResponse:
        ''' def search(state: TacticState , depth: int) -> Optional(Proof) '''
        result = self.dojo.run_tac(current_state , tactic_code)

        if isinstance(result , ProofFinished):
            return ValidationResponse(result_type=ValidationResult.PROOF_FINISHED , new_state=None , error_msg=None)
        elif isinstance(result , TacticState):
            return ValidationResponse(result_type=ValidationResult.VALID , new_state=result , error_msg=None)
        else:
            return ValidationResponse(result_type=ValidationResult.INVALID , new_state=None , error_msg='INVALID')