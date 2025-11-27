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

def validate_tactic(dojo: Dojo , state: TacticState , tactic: str) -> ValidationResponse:
    result = dojo.run_tac(state , tactic)

    if isinstance(result , ProofFinished):
        return ValidationResponse(ValidationResult.PROOF_FINISHED)
    elif isinstance(result , LeanError):
        return ValidationResponse(ValidationResult.INVALID , error=result.error)
    elif isinstance(result , TacticState):
        return ValidationResponse(ValidationResult.VALID , next_state=result)
    