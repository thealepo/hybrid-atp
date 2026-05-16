from __future__ import annotations

import threading
from dataclasses import dataclass
from enum import Enum, auto
from typing import Optional

from lean_dojo import (
    Dojo,
    DojoCrashError,
    DojoInitError,
    DojoTacticTimeoutError,
    LeanError,
    ProofFinished,
    ProofGivenUp,
    TacticState,
)


class ValidationResult(Enum):
    VALID = auto()
    INVALID = auto()
    PROOF_FINISHED = auto()
    GIVEN_UP = auto()
    CRASHED = auto()


@dataclass
class ValidationResponse:
    result_type: ValidationResult
    next_state: Optional[TacticState] = None
    error: Optional[str] = None


def _classify(result) -> ValidationResponse:
    if isinstance(result , ProofFinished):
        return ValidationResponse(ValidationResult.PROOF_FINISHED)
    if isinstance(result , ProofGivenUp):
        return ValidationResponse(ValidationResult.GIVEN_UP , error="proof given up")
    if isinstance(result , LeanError):
        return ValidationResponse(ValidationResult.INVALID , error=getattr(result, "error", str(result)))
    if isinstance(result , TacticState):
        return ValidationResponse(ValidationResult.VALID , next_state=result)
    return ValidationResponse(ValidationResult.INVALID , error=f"unknown result type: {type(result).__name__}")


def validate_tactic(dojo: Dojo , state: TacticState , tactic: str) -> ValidationResponse:
    try:
        result = dojo.run_tac(state , tactic)
    except DojoTacticTimeoutError as e:
        return ValidationResponse(ValidationResult.INVALID , error=f"timeout: {e}")
    except (DojoCrashError , DojoInitError) as e:
        return ValidationResponse(ValidationResult.CRASHED , error=str(e))
    except Exception as e:
        return ValidationResponse(ValidationResult.INVALID , error=str(e))
    return _classify(result)


class DojoValidator:
    """Thread-safe wrapper around a single Dojo instance."""

    def __init__(self, dojo: Dojo):
        self.dojo = dojo
        self._lock = threading.Lock()

    def validate(self, state: TacticState, tactic: str) -> ValidationResponse:
        with self._lock:
            return validate_tactic(self.dojo, state, tactic)
