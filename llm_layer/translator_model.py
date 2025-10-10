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
        self.use_inference_endpoints = use_inference_endpoint
        self.endpoint_url = endpoint_url
        self.generation_config = generation_config or {
            'temperature': 0.2,
            'top_p': 0.9,
        }

        if use_inference_endpoint and endpoint_url:
            self.client = None
        else:
            self.client = InferenceClient(token=api_token)
    
    def chat_completion(self , messages: List[Dict[str,str]] , config: Optional[Dict] = None) -> str:
        final_config = {**self.generation_config , **(config or{})}
        return self.client.chat_completion(model=self.model_id , messages=messages , **final_config)

class LeanTranslator:
    def __init__(self , api_token , model_id: str = '<RESEARCH A BETTER MODEL FOR LEAN TRANSLATION>' , use_inference_endpoint: bool = False , endpoint_url: Optional[str] = None):
        self.model = Model(
            model_id=model_id,
            api_token=api_token,
            use_inference_endpoint=use_inference_endpoint,
            endpoint_url=endpoint_url,
            generation_config={
                'temperature': 0.2,
                'top_p': 0.9,
            }
        )
        self.model_id = model_id

    def _create_lean_translation_prompt(self, proof_step: str, context: str = "") -> str:
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

    def _system_message(self) -> str:
        ...

    def translate_to_lean(self , proof_step , context) -> LeanTranslation:
        ...