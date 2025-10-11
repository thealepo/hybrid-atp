import os
import sys
from pathlib import Path
from dotenv import load_dotenv

parent_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0 , str(parent_dir))

load_dotenv()
HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')

from reasoner_model import LeanGoalState, LeanTacticGenerator, MathReasoner


def test_reasoner():
    reasoner = MathReasoner(api_token=HF_TOKEN)
    tactic_generator = LeanTacticGenerator(api_token=HF_TOKEN)

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

    # Step 1: Generate search constraints
    print("=== Generating Search Constraints ===")
    constraints = reasoner.generate_search_constraints(
        goal_state=goal,
        context="Prove the rank-nullity theorem for finite-dimensional spaces"
    )
    
    print(f"Primary tactics: {constraints.primary_tactic_types}")
    print(f"Relevant lemmas: {constraints.relevant_lemmas}")
    print(f"Confidence: {constraints.confidence}")
    print(f"Reasoning: {constraints.reasoning}")
    
    # Step 2: Generate concrete tactics
    print("\n=== Generating Tactic Candidates ===")
    candidates = tactic_generator.generate_candidates(goal, constraints, num_candidates=3)
    
    for i, cand in enumerate(candidates, 1):
        print(f"\nCandidate {i} (priority: {cand.priority}):")
        print(f"  Code: {cand.tactic_code}")
        print(f"  Type: {cand.tactic_type}")
        print(f"  Why: {cand.justification}")

if __name__ == "__main__":
    test_reasoner()