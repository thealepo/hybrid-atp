import json
from typing import List
import re

from .wrapper import Model
from ..data_structures.base import LeanGoalState , SearchConstraints , TacticCandidate
from ..utils.json_parser import extract_json

class LeanGenerator:
    def __init__(self , api_token: str , model_id: str = 'meta-llama/Meta-Llama-3-8B-Instruct'):
        self.model = Model(
            model_id=model_id,
            api_token=api_token,
            generation_config={
                'temperature': 0.1,
                'top_p': 0.95
            }
        )
        self.model_id=model_id

    def _create_tactic_generation_prompt(self , goal_state: LeanGoalState , constraints: SearchConstraints , num_candidates: int) -> str:
        weighted_tactics = constraints.get_weighted_tactics()
        priority_list = ', '.join([f"{t} (weight: {w})" for t,w in weighted_tactics[:5]])

        return f"""
        Generate {num_candidates} concrete Lean 4 tactics for this proof state.

        {goal_state.to_prompt_format()}

        SEARCH CONSTRAINTS (follow these priorities):
        - Primary tactics: {constraints.primary_tactic_types}
        - Relevant lemmas: {constraints.relevant_lemmas}
        - Avoid: {constraints.avoid_tactics}
        - Strategy: {constraints.reasoning}
        - Priorities: {priority_list}

        Generate {num_candidates} DIFFERENT, CONCRETE Lean 4 tactics.
        Each must be:
        1. Valid Lean 4 syntax
        2. Executable on the current goal
        3. Different from the others
        4. Aligned with the constraints

        Return JSON array:
        [
            {{
                "tactic_code": "apply FiniteDimensional.finrank_add_finrank_ker",
                "tactic_type": "apply",
                "justification": "Directly applies rank-nullity theorem to the goal",
                "priority": 2.5,
                "expected_subgoals": ["prove T is linear", "prove V is finite-dimensional"]
            }},
            ...
        ]

        Return ONLY the JSON array, no other text.
        """

    def _tactic_system_message(self) -> str:
        return """You are a Lean 4 code generator. Generate syntactically correct Lean 4 tactics.
        You MUST return valid JSON only. Each tactic must be executable Lean 4 code.
        """

    def _parse_candidates(self , json_text: str) -> List[TacticCandidate]:
        print('\n\n\n')

        # fixing json problem as before
        fixed_json_text = re.sub(r'\}\s*\{', '}, {', json_text.strip())
        if not fixed_json_text.startswith('['):
            fixed_json_text = f'[{fixed_json_text}]'

        try:
            data = json.loads(fixed_json_text)
        except json.JSONDecodeError as e:
            raise ValueError(f"INVALID JSON: {e}")

        if not isinstance(data , list):
            data = [data]

        candidates = []
        for item in data:
            if not isinstance(item , dict):
                continue

            candidate = TacticCandidate(
                tactic_code=item.get("tactic_code", ""),
                tactic_type=item.get("tactic_type", "unknown"),
                justification=item.get("justification", ""),
                priority=item.get("priority", 1.0),
                expected_subgoals=item.get("expected_subgoals", [])
            )

            if candidate.tactic_code:
                candidates.append(candidate)
            
        candidates.sort(key=lambda c: c.priority , reverse=True)
        return candidates

    def generate_candidates(self , goal_state: LeanGoalState , constraints: SearchConstraints , num_candidates: int = 5) -> List[TacticCandidate]:

        prompt = self._create_tactic_generation_prompt(
            goal_state,
            constraints,
            num_candidates
        )

        messages = [
            { 'role':'system' , 'content':self._tactic_system_message() },
            { 'role':'user' , 'content':prompt }     
        ]

        try:
            if "byt5" in self.model_id.lower() or "t5" in self.model_id.lower():
                # For seq2seq models like ByT5
                response = self.model.text_generation(prompt)
            else:
                # For chat-based models (Llama, Qwen, etc.)
                response = self.model.chat_completion(messages)

            json_text = extract_json(response)
            return self._parse_candidates(json_text)
            
        except Exception as e:
            raise ValueError(f"Error: {e}")