from typing import Optional, List
from dataclasses import dataclass

from google import genai


@dataclass
class LeanProofStep:
    '''single Lean step'''
    statement: str
    tactic: str
    justification: str
    dependencies: List[str] = None

class GeminiLeanTranslator:

    def __init__(self, api_key: Optional[str] = None, model_name: str = 'gemini-1.5-pro'):
        """translator init"""
        client = genai.Client(api_key=api_key)
        self.model = client.models.get(model_name)

    def _create_lean_translation_prompt(self, proof_step: str, context: str = "", 
                                      domain: str = "linear_algebra") -> str:
        """translating proof steps in Lean prompt"""
        
        return f"""
        You are an expert Lean 4 theorem prover. Convert the following mathematical proof step into valid Lean 4 code.

        CONTEXT:
        {context}

        PROOF STEP TO TRANSLATE:
        {proof_step}

        REQUIREMENTS:
        1. Generate syntactically correct Lean 4 code
        2. Use appropriate tactics (rw, simp, exact, apply, etc.)
        3. Include necessary imports
        4. Define any required variables or hypotheses
        5. Provide clear justification for each tactic
        6. Ensure the proof is verifiable in Lean 4

        OUTPUT FORMAT (JSON):
        {{
            "theorem_statement": "theorem name : statement := by",
            "proof_steps": [
                {{
                    "statement": "What this step accomplishes",
                    "tactic": "exact h1",
                    "justification": "Why this tactic works",
                    "dependencies": ["h1", "h2"]
                }}
            ],
            "imports": ["import Mathlib.LinearAlgebra.Basic"],
            "variables": ["variable {{α : Type*}} [Field α]"],
            "raw_lean_code": "Complete Lean code block"
        }}

        Ensure the JSON is valid and the Lean code is syntactically correct.
        """