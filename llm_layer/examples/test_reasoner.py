import os
import sys
from builtins import Exception
from pathlib import Path
from dotenv import load_dotenv

parent_dir = Path(__file__).parent.parent.parent
sys.path.insert(0 , str(parent_dir))
load_dotenv()

from llm_layer import MathReasoner


def test_reasoner():
    reasoner = MathReasoner()

    # linear transformation
    proof = "dim(V) = rank(T) + nullity(T), where T: V → W is a linear transformation from finite-dimensional vector space V to vector space W"

    result = reasoner.analyze_proof_TEST(proof_text=proof)

    print(result.problem_understanding)
    print(result.key_concepts)
    print(result.suggested_tactic)

if __name__ == "__main__":
    test_reasoner()