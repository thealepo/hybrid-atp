import os
from dotenv import load_dotenv

from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from validation_layer.lean_dojo_validator import LeanDojoValidator
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

    validator = LeanDojoValidator(
        repo_url="https://github.com/yangky11/lean4-example",
        file_path="Lean4Example.lean",
        theorem_name="add_abc"
    )

    initial_state = validator.dojo.get_initial_state()

    strategy = DFS()

    search = Search(
        reasoner=reasoner,
        generator=generator,
        validator=validator,
        strategy=strategy
    )

    path = search.search(
        state=initial_state,
        max_depth=5,
        max_iterations=200,
        parallel=3
    )

    print("\n=== FINAL PROOF PATH ===")
    print(path)


if __name__ == "__main__":
    main()
