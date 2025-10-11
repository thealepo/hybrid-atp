import os
import sys
from pathlib import Path
from dotenv import load_dotenv

from llm_layer.models.reasoning_model import MathReasoner
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.data_structures.base import LeanGoalState

parent_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0 , str(parent_dir))

load_dotenv()
HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')


def test():
    reasoner = MathReasoner(api_token=HF_TOKEN)
    lean_generator = LeanGenerator(api_token=HF_TOKEN)

    goal = LeanGoalState(
        goal="⊢ FiniteDimensional.finrank K V = FiniteDimensional.finrank K (LinearMap.ker T) + FiniteDimensional.finrank K (LinearMap.range T)",
        hypothesis={
            "K": "Type u_1",
            "V": "Type u_2",
            "W": "Type u_3",
            "T": "V →ₗ[K] W",
            "inst_1": "Field K",
            "inst_2": "AddCommGroup V",
            "inst_3": "Module K V",
            "inst_4": "AddCommGroup W",
            "inst_5": "Module K W",
            "h": "FiniteDimensional K V"
        },
        local_context=["import Mathlib.LinearAlgebra.FiniteDimensional"],
        proof_depth=0
    )

    # step 1: generate search constrsients
    constraints = reasoner.generate_search_constraints(
        goal_state=goal,
        context="Prove the rank-nullity theorem for finite-dimensional spaces"
    )
    print(constraints)

    # step 2: generate candidate tactics
    candidates = lean_generator.generate_candidates(
        goal_state=goal,
        constraints=constraints,
        num_candidates=3
    )
    print(candidates)


if __name__ == "__main__":
    test()