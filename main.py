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
from search_layer.search_strats.dfs import DFS

def main():

    # load environmental vars
    load_dotenv()
    HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')

    # initializing models
    reasoner = MathReasoner(api_token=HF_TOKEN)
    generator = LeanGenerator(api_token=HF_TOKEN , model_id='kaiyuy/leandojo-lean3-tacgen-byt5-small')
    validator = LeanValidator()

    # choosing a strategy (DFS IS ALL WE HAVE FOR NOW)
    strategy = DFS()

    # defining a test goal state
    test_goal = LeanGoalState(
        goal="Prove that the sum of any two decreasing functions is decreasing",
        hypothesis={},
        local_context=[],
        proof_depth=0
    )

    search = Search(
        reasoner=reasoner,
        generator=generator,
        validator=validator,
        strategy=strategy
    )

    path = search.search(
        state=test_goal,
        max_depth=4,
        max_iterations=200,
        parallel=3
    )

    print(path)

if __name__ == "__main__":
    main()
