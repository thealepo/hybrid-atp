import os
import sys
from pathlib import Path
from dotenv import load_dotenv

parent_dir = Path(__file__).parent.parent.parent
sys.path.insert(0 , str(parent_dir))

load_dotenv()
HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')

from llm_layer.reasoner_model import MathReasoner


def test_reasoner():
    reasoner = MathReasoner(HF_TOKEN)

    # linear transformation
    proof = "dim(V) = rank(T) + nullity(T), where T: V → W is a linear transformation from finite-dimensional vector space V to vector space W"

    result = reasoner.analyze_proof_TEST(proof_text=proof)

    print(result.problem_understanding)
    print(result.key_concepts)
    print(result.suggested_tactic)

if __name__ == "__main__":
    test_reasoner()