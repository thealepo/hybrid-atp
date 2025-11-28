"""
Simple CLI demo of the strategy generator (no validation).
For web interface, run app.py instead.
"""
import os
import json
from dotenv import load_dotenv

from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from strategy_generator import StrategyGenerator


def main():
    load_dotenv()
    HF_TOKEN = os.getenv("HUGGINGFACE_TOKEN")

    # Initialize models
    reasoner = MathReasoner(api_token=HF_TOKEN)
    generator = LeanGenerator(
        api_token=HF_TOKEN,
        model_id="kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small"
    )

    # Create strategy generator
    strategy_gen = StrategyGenerator(
        reasoner=reasoner,
        generator=generator
    )

    # Example theorem
    theorem = "⊢ ∀ (xs ys : List α), reverse (xs ++ ys) = reverse ys ++ reverse xs"

    print("\n=== GENERATING PROOF STRATEGY ===")
    print(f"Theorem: {theorem}\n")

    # Generate strategy
    result = strategy_gen.generate_strategy(
        theorem_statement=theorem,
        context="Property about list reversal and concatenation",
        num_tactics=3
    )

    # Pretty print results
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
