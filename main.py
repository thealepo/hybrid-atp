import os
import sys
from dotenv import load_dotenv

sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from lean_dojo import Dojo, DojoCrashError
from search_layer.search import Search
from search_layer.search_strats.dfs import DFS

def main():
    load_dotenv()
    HF_TOKEN = os.getenv("HUGGINGFACE_TOKEN")

    reasoner = MathReasoner(api_token=HF_TOKEN)
    generator = LeanGenerator(
        api_token=HF_TOKEN,
        model_id="kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small"
    )

    target_file = "Mathlib/LinearAlgebra/Dimension.lean" 
    target_theorem = "rank_range_add_rank_ker"




    strategy = DFS()

    search = Search(
        reasoner=reasoner,
        generator=generator,
        strategy=strategy
    )


    path = search.search(
        init_state=initial_state,
        max_depth=5,
        max_iterations=200,
        parallel=3
    )

    print(path)

if __name__ == "__main__":
    main()