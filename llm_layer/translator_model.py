import json
from typing import Optional, List
from dataclasses import dataclass

from google import genai

from llm_layer.reasoner_model import ProofStep


@dataclass
class LeanProofStep:
    '''single Lean step'''
    statement: str
    tactic: str
    justification: str
    dependencies: List[str] = None

@dataclass
class LeanTranslation:
    '''complete Lean translation'''
    theorem_statement: str
    proof_steps: List[LeanProofStep]
    imports: List[str]
    variables: List[str]
    raw_lean_code: str

class GeminiLeanTranslator:

    def __init__(self, api_key: Optional[str] = None, model_name: str = 'gemini-1.5-pro'):
        """translator init"""
        self.client = genai.Client(api_key=api_key)
        self.model = self.client.models.get(model_name)

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

    def _parse_response(self , response_text: str) -> LeanProofStep:
        # TODO: parse response and return a LeanProofStep object

        json_text = response_text.strip()
        if "```json" in json_text:
            json_text = json_text.split("```json")[1].split("```")[0]
        elif "```" in json_text:
            json_text = json_text.split("```")[1].split("```")[0]
        json_text = json_text.strip()

        data = json.loads(json_text)

        # extract data
        theorem_statement = data.get("theorem_statement" , "")
        proof_steps = []
        for step in data.get("proof_steps" , []):
            proof_steps.append(LeanProofStep(
                statement=step.get('statement' , ''),
                tactic=step.get('tactic' , ''),
                justification=step.get('justification' , ''),
                dependencies=step.get('dependencies' , ''),
            ))
        imports = data.get("imports" , [])
        variables = data.get("variables" , [])
        raw_lean_code = data.get("raw_lean_code" , "")

        return LeanTranslation(
            theorem_statement=theorem_statement,
            proof_step=proof_steps,
            imports=imports,
            variables=variables,
            raw_lean_code=raw_lean_code
        )

    def lean_translation_TEST(self , proof_step: str , context: str = '') -> LeanTranslation:
        prompt = self._create_lean_translation_prompt(context,proof_step)
        response = self.client.models.generate_content(prompt)

        return self._parse_response(response.text)
        