import json
from typing import Optional, List
from dataclasses import dataclass
import requests


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

class LeanTranslator:

    def __init__(self, api_key: Optional[str] = None, model_name: str = 'qwen2.5:7b-instruct', host: str = "http://localhost:11434"):
        self.model_name = model_name
        self.host = host
        self.default_config = {'temperature': 0.2, 'max_output_tokens': 2048}

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

    def _parse_response(self , response_text: str) -> LeanTranslation:
        # parse response and return a LeanTranslation object
        json_text = response_text.strip()
        if "```json" in json_text:
            json_text = json_text.split("```json")[1].split("```")[0]
        elif "```" in json_text:
            json_text = json_text.split("```")[1].split("```")[0]
        json_text = json_text.strip()

        data = json.loads(json_text)

        # extract data
        theorem_statement = data.get("theorem_statement" , "")
        proof_steps: List[LeanProofStep] = []
        for step in data.get("proof_steps" , []):
            proof_steps.append(LeanProofStep(
                statement=step.get('statement' , ''),
                tactic=step.get('tactic' , ''),
                justification=step.get('justification' , ''),
                dependencies=step.get('dependencies' , []),
            ))
        imports = data.get("imports" , [])
        variables = data.get("variables" , [])
        raw_lean_code = data.get("raw_lean_code" , "")

        return LeanTranslation(
            theorem_statement=theorem_statement,
            proof_steps=proof_steps,
            imports=imports,
            variables=variables,
            raw_lean_code=raw_lean_code
        )

    def _generate(self, prompt: str) -> str:
        options = {
            'temperature': self.default_config['temperature'],
            'num_predict': self.default_config['max_output_tokens']
        }
        payload = {
            "model": self.model_name,
            "prompt": prompt,
            "stream": False,
            "options": options
        }
        resp = requests.post(f"{self.host}/api/generate", json=payload, timeout=300)
        resp.raise_for_status()
        return resp.json().get("response", "")

    def lean_translation_TEST(self , proof_step: str , context: str = '') -> LeanTranslation:
        prompt = self._create_lean_translation_prompt(proof_step=proof_step, context=context)
        response = self._generate(prompt)
        return self._parse_response(response)
        