import json
from typing import List , Optional , Dict , Any
from dataclasses import dataclass , asdict
from huggingface_hub import InferenceClient
import logging
import re

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class ProofStep:
    '''single step in mathematical proof'''
    statement: str
    reasoning: str
    tactic_suggestion: Optional[str] = None

@dataclass
class CoTAnalysis:
    problem_understanding: str
    key_concepts: List[str]
    proof_strategy: str
    next_steps: List[ProofStep]
    suggested_tactic: str
    reasoning_chain: List[str]

    def to_dict(self) -> Dict[str , Any]:
        return asdict(self)

class Model:
    def __init__(self , model_id , api_token , use_inference_endpoint: bool = False , endpoint_url: Optional[str] = None , generation_config: Optional[Dict] = None):
        self.model_id = model_id
        self.api_token = api_token
        self.use_inference_endpoint = use_inference_endpoint
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

class MathReasoner:
    def __init__(self , api_token , model_id: str = 'meta-llama/Meta-Llama-3-8B-Instruct' , use_inference_endpoint: bool = False , endpoint_url: Optional[str] = None):
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
        
    def _create_linear_algebra_prompt(self, proof_text: str) -> str:
        """Enhanced prompt for rigorous linear algebra proof analysis."""
        
        return f"""
        You are an expert mathematician specializing in Linear Algebra and formal theorem proving. 
        Analyze the following proof with rigorous mathematical precision.

        PROOF TEXT:
        {proof_text}

        Provide a comprehensive analysis following this structure:

        1. CONTEXT & SETUP
        - State the theorem/proposition being proven
        - List all hypotheses and given conditions explicitly
        - Identify the goal (what must be shown)
        - Note the proof framework (direct, contradiction, contrapositive, induction, etc.)

        2. MATHEMATICAL OBJECTS INVENTORY
        - Enumerate all objects: vectors, matrices, subspaces, transformations, etc.
        - Specify their properties (dimensions, domains, codomains, bases, etc.)
        - Identify relationships between objects (e.g., "T is a linear map from V to W")

        3. CONCEPTUAL FOUNDATIONS
        - List relevant definitions being used
        - Identify applicable theorems and lemmas (name them specifically)
        - Note key properties (linearity, orthogonality, rank-nullity, etc.)
        - Flag which concepts are central vs. peripheral

        4. PROOF STATE ANALYSIS
        - What has been established so far? (completed steps)
        - What assumptions are in play at this point?
        - What remains to be proven? (the gap between current state and goal)
        - Are there any implicit steps that should be made explicit?

        5. LOGICAL STRUCTURE MAPPING
        - Trace the flow of implications (A → B → C → goal)
        - Identify proof techniques used (construction, computation, algebraic manipulation, etc.)
        - Check for logical soundness: are there any gaps or unjustified leaps?
        - Assess completeness: what's missing?

        6. NEXT STEP RECOMMENDATION
        Based on your analysis, recommend the single most effective next step:
        a) STATE THE TACTIC: Name the specific mathematical move
            (e.g., "Apply rank-nullity theorem", "Choose an explicit basis", 
            "Use Gram-Schmidt orthogonalization", "Compute the kernel")
        b) JUSTIFY THE CHOICE: Explain why this tactic bridges the gap
            - What does it accomplish?
            - Why is it better than alternatives?
            - What new information will it provide?
        c) PREVIEW THE OUTCOME: Describe what the proof state will look like after
            applying this tactic and what would follow next

        7. VERIFICATION CHECKLIST
        Before finalizing your recommendation, verify:
        - Does the next step logically follow from what's established?
        - Are all necessary conditions satisfied to apply the suggested theorem/technique?
        - Will this genuinely move toward the goal, or is it a distraction?

        IMPORTANT: Return your response in the following JSON format:
        {{
            "problem_understanding": "Complete text from Section 1 (CONTEXT & SETUP)",
            "key_concepts": [
                "First key concept from Section 2",
                "Second key concept from Section 2",
                "Third key concept from Section 2"
            ],
            "proof_strategy": "Complete text from Section 3 (CONCEPTUAL FOUNDATIONS)",
            "next_steps": [
                {{
                    "statement": "Description of what needs to be done",
                    "reasoning": "Why this step is necessary",
                    "tactic_suggestion": "Specific tactic to use"
                }}
            ],
            "suggested_tactic": "Complete text from Section 5 (LOGICAL STRUCTURE MAPPING)",
            "reasoning_chain": [
                "First reasoning point from Section 6",
                "Second reasoning point from Section 6",
                "Third reasoning point from Section 6"
            ]
        }}

        Ensure the JSON is valid and properly escaped. Do not include any text outside the JSON object.
        """

    def _system_message(self) -> str:
        return (
            "You are a precise mathematical reasoning assistant. "
            "You MUST respond with valid JSON only, matching exactly the requested JSON structure. "
            "Do NOT include any explanation, commentary, or markdown. "
            "If you cannot produce the JSON because of missing info, return the keys with empty values."
        )
    def _assistant_example(self) -> Dict[str,str]:
        example = {
            "problem_understanding": "We must show dim(V) = rank(T) + nullity(T) for T: V->W, V finite-dim.",
            "key_concepts": ["linear map", "kernel", "image", "rank-nullity theorem"],
            "proof_strategy": "Apply rank-nullity theorem by constructing kernel and image dimensions; show dim V = dim ker T + dim im T.",
            "next_steps": [
                {
                    "statement": "Compute kernel dimension",
                    "reasoning": "Knowing dim ker T plus dim im T yields dim V by rank-nullity",
                    "tactic_suggestion": "Compute basis for ker(T) and extend to basis of V"
                }
            ],
            "suggested_tactic": "Apply rank-nullity theorem directly",
            "reasoning_chain": [
                "Identify kernel and image subspaces",
                "Compute their dimensions",
                "Sum dimensions to obtain dim(V)"
            ]
        }
        return {"role": "assistant", "content": json.dumps(example)}
    def _extract_json(self , raw: str) -> Optional[str]:
        s = raw.strip()

        if "```json" in s:
            s = s.split("```json", 1)[1].rsplit("```", 1)[0].strip()
        elif "```" in s:
            s = s.split("```", 1)[1].rsplit("```", 1)[0].strip()

        first = s.find("{")
        last = s.rfind("}")
        if first != -1 and last != -1 and last > first:
            return s[first:last + 1]

        return None
    
    def _parse_response_to_cot(self, json_text: str) -> CoTAnalysis:
        # claude suggested cleanup
        def clean_json_string(s) -> str:
            s = s.strip()
            s = re.sub(r'^[^{]*', '', s)
            s = re.sub(r'[^}]*$', '', s)
            if s.count('"') < s.count("'"):
                s = s.replace("'" , '"')
            s = re.sub(r',\s*([}\]])', r'\1', s)
            return s

        # making JSON exception and seeing if the cleanup works
        try:
            data = json.loads(json_text)
        except json.JSONDecodeError:
            cleaned_text = clean_json_string(json_text)
            try:
                data = json.loads(cleaned_text)
            except json.JSONDecodeError:
                raise ValueError('Error.')

        problem_understanding = data.get("problem_understanding", "")
        key_concepts = data.get("key_concepts", [])
        proof_strategy = data.get("proof_strategy", "")
        suggested_tactic = data.get("suggested_tactic", "")
        reasoning_chain = data.get("reasoning_chain", [])

        next_steps_raw = data.get("next_steps", [])
        next_steps = []
        for step in next_steps_raw:
            if isinstance(step, dict):
                next_steps.append(ProofStep(
                    statement=step.get("statement", ""),
                    reasoning=step.get("reasoning", ""),
                    tactic_suggestion=step.get("tactic_suggestion")
                ))

        return CoTAnalysis(
            problem_understanding=problem_understanding,
            key_concepts=key_concepts,
            proof_strategy=proof_strategy,
            next_steps=next_steps,
            suggested_tactic=suggested_tactic,
            reasoning_chain=reasoning_chain
        )

    def analyze_proof(self , proof_text: str) -> CoTAnalysis:
        messages = [
            { 'role':'system' , 'content': self._system_message()},
            {'role':'user' , 'content': self._create_linear_algebra_prompt(proof_text=proof_text)},
            self._assistant_example()
        ]

        response_obj = self.model.chat_completion(messages=messages)
        raw_content = response_obj.choices[0].message.content

        json_text = self._extract_json(raw_content)
        if not json_text:
            raise ValueError("NO VALID JSON")

        return self._parse_response_to_cot(json_text=json_text)