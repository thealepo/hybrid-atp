'''
.py version of the test script
'''
import os
from dotenv import load_dotenv
from llm_layer.data_structures.base import LeanGoalState
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from validation_layer.validator import LeanValidator
from search_layer.search import Search

def main():

    # load environmental vars
    load_dotenv()
    HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')

    # initializing models
    reasoner = MathReasoner(api_token=HF_TOKEN)
    generator = LeanGenerator(api_token=HF_TOKEN)
    validator = LeanValidator()

    # defining a test goal state
    test_goal = LeanGoalState(
        goal="⊢ ∀ (n : ℕ), n + 0 = n",
        hypothesis={},  # no hypotheses
        local_context=[],
        proof_depth=0
    )

    search = Search(
        reasoner=reasoner,
        generator=generator,
        validator=validator
    )

    path = search.search(
        state=test_goal,
        max_depth=2,
        max_iterations=30
    )

    print(path)

if __name__ == "__main__":
    main()
