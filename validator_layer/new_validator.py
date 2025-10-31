# new validator... we might need different modules
# this is beyond complicated

import os
from enum import Enum , auto
from dataclasses import dataclass
from typing import Optional
# notebook imports
from lean_dojo import (
    LeanGitRepo , Theorem , Dojo , TacticState , ProofFinished
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

class SandboxValidator:
    ...