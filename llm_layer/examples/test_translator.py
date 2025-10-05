import os
import sys
from builtins import Exception
from pathlib import Path

parent_dir = Path(__file__).parent.parent.parent
sys.path.insert(0 , str(parent_dir))

from llm_layer import LeanTranslator


def test_translator():
    translator = LeanTranslator()

    # proof on Linear Transformations
    proof_step = ""
    context = ""

    translator._create_lean_translation_prompt(proof_step=proof_step , context=context)
    result = translator.lean_translation_TEST(proof_step=proof_step , context=context)

    print(result.raw_lean_code)


if __name__ == "__main__":
    test_translator()