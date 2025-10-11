import os
import sys
from pathlib import Path
from dotenv import load_dotenv

parent_dir = Path(__file__).parent.parent.parent
sys.path.insert(0 , str(parent_dir))

load_dotenv()
HF_TOKEN = os.getenv('HUGGINGFACE_TOKEN')

from llm_layer.translator_model import LeanTranslator


def test_translator():
    translator = LeanTranslator(api_token=HF_TOKEN)  # add a new model (must research)

    # proof on Linear Transformations
    proof_step = ""
    context = ""

    translator._create_lean_translation_prompt(proof_step=proof_step , context=context)
    result = translator.lean_translation_TEST(proof_step=proof_step , context=context)

    print(result.raw_lean_code)


if __name__ == "__main__":
    test_translator()