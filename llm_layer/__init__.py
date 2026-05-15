"""Top-level package. Models are imported lazily so light-weight callers
(tests, scripts that only touch data structures) don't have to pay for
torch/transformers at import time."""
from .data_structures import (
    FailedTactic,
    LeanGoalState,
    SearchConstraints,
    TacticCandidate,
)

__all__ = [
    "FailedTactic",
    "LeanGoalState",
    "SearchConstraints",
    "TacticCandidate",
    "MathReasoner",
    "LeanGenerator",
]


def __getattr__(name):
    if name == "MathReasoner":
        from .models.reasoning_model import MathReasoner

        return MathReasoner
    if name == "LeanGenerator":
        from .models.lean_generator_model import LeanGenerator

        return LeanGenerator
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
