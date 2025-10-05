import json
from typing import List, Optional
from dataclasses import dataclass
import requests


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

# creating model class, Gemini API was updated AGAIN and i cant find the model object
# changed to Ollama
class Model:
    '''local Ollama model wrapper'''
    def __init__(self , model_name: str , default_config: dict = None , host: str = "http://localhost:11434"):
        self.model_name = model_name
        self.default_config = default_config or {}
        self.host = host

    def generate_content(self , contents: str , config: dict = None):
        config = config or {}
        final_config = {**self.default_config , **config}

        print("1")
        options = {}
        if 'temperature' in final_config:
            options['temperature'] = final_config['temperature']
        if 'top_p' in final_config:
            options['top_p'] = final_config['top_p']
        if 'max_output_tokens' in final_config:
            options['num_predict'] = final_config['max_output_tokens']

        payload = {
            "model": self.model_name,
            "prompt": contents,
            "stream": False,
            "options": options
        }
        resp = requests.post(f"{self.host}/api/generate", json=payload, timeout=300)
        resp.raise_for_status()
        data = resp.json()

        class _Resp:
            def __init__(self, text: str):
                self.text = text

        return _Resp(data.get('response', ''))


class MathReasoner:
    
    def __init__(self, api_key: Optional[str] = None, model_name: str = "qwen2.5:7b-instruct"):
        self.model = Model(
            model_name,
            default_config={'temperature':0.2 , 'max_output_tokens':2048}
        )

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
    
    def _parse_response(self, response_text: str) -> CoTAnalysis:
        #TODO: parse the response and return as a CoTAnalysis object
        
        print("2")
        if not response_text or not isinstance(response_text, str):
            raise ValueError("Empty or invalid response text from the model.")
        json_text = response_text.strip()
        if "```json" in json_text:
            json_text = json_text.split("```json")[1].split("```")[0]
        elif "```" in json_text:
            json_text = json_text.split("```")[1].split("```")[0]
        json_text = json_text.strip()

        data = json.loads(json_text)

        # extracting data
        problem_understanding = data.get('problem_understanding', '')
        key_concepts = data.get('key_concepts', [])
        proof_strategy = data.get('proof_strategy', '')
        suggested_tactic = data.get('suggested_tactic', '')
        reasoning_chain = data.get('reasoning_chain', [])

        next_steps = []
        for step in data.get('next_steps' , []):
            next_steps.append(ProofStep(
                statement=step.get('statement' , ''),
                reasoning=step.get('reasoning' , ''),
                tactic_suggestion=step.get('tactic_suggestion')
            ))

        return CoTAnalysis(
            problem_understanding=problem_understanding,
            key_concepts=key_concepts,
            proof_strategy=proof_strategy,
            next_steps=next_steps,
            suggested_tactic=suggested_tactic,
            reasoning_chain=reasoning_chain
        )

    def analyze_proof_TEST(self , proof_text: str) -> CoTAnalysis:
        prompt = self._create_linear_algebra_prompt(proof_text)
        response = self.model.generate_content(prompt)

        return self._parse_response(getattr(response, 'text', '') or '')
