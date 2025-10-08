import json
import os
from dotenv import load_dotenv
from typing import List , Optional , Dict , Any
from dataclasses import dataclass , asdict
import requests
from huggingface_hub import InferenceClient
import logging


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

class Model:
    def __init__(self , model_id , api_token , use_inference_endpoint: bool = False , endpoint_url: Optional[str] = None , generation_config: Optional[Dict] = None):
        self.model_id = model_id
        self.api_token = api_token
        self.use_inference_endpoint = use_inference_endpoint
        self.endpoint_url = endpoint_url
        self.generation_config = generation_config or {
            'temperature': 0.2,
            'max_new_tokens': 2048,
            'top_p': 0.9,
            'do_sample': True
        }

        if use_inference_endpoint and endpoint_url:
            self.client = None
        else:
            self.client = InferenceClient(token=api_token)

    def generate_content(self , prompt , config: Optional[Dict] = None) -> str:
        final_config = {**self.generation_config , **(config or{})}

        if self.use_inference_endpoint and self.endpoint_url:
            response = self._call_inference_endpoint(prompt , final_config)
        else:
            response = self.client.text_generation(
                prompt=prompt,
                model=self.model_id,
                **final_config
            )

        return response if isinstance(response , str) else response.get('generated_text','')

    def _call_inference_endpoint(self , prompt , config: Dict) -> str:
        headers = {
            'Authorization': f'Bearer {self.api_token}',
            'Content-Type': 'application/json'
        }
        payload = {
            'inputs': prompt,
            'parameters': config
        }

        response = requests.post(
            self.endpoint_url,
            headers=headers,
            json=payload,
            timeout=300
        )
        response.raise_for_status()

        data = response.json()

        return str(data)

class LeanTranslator:
    def __init__(self , api_token , model_id: str = '.(lean translator model)' , use_inference_endpoint: bool = False , endpoint_url: Optional[str] = None):
        self.model = Model(
            model_id=model_id,
            api_token=api_token,
            use_inference_endpoint=use_inference_endpoint,
            endpoint_url=endpoint_url,
            generation_config={
                'temperature': 0.0, # change this according to model
                'max_new_tokens': 2048,
                'top_p': 0.9,
                'do_sample': True,
                'return_full_text': False # change this according to model
            }
        )
        self.model_id = model_id

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

    def lean_translation_TEST(self , proof_step: str , context: str) -> LeanTranslation:
        prompt = self._create_lean_translation_prompt(
            proof_step=proof_step,
            context=context
            # domain=linear_algebra
        )
        response = self.model.generate_content(prompt)

        return self._parse_response(getattr(response , 'text' , '') or '')