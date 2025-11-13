import json
import re
from typing import List
from .wrapper import Model
from ..data_structures.base import LeanGoalState , SearchConstraints , TacticCandidate
from ..utils.json_parser import extract_json

class LeanGenerator:
    def __init__(self , api_token: str , model_id: str):
        self.model = Model(
            model_id=model_id,
            api_token=api_token,
            generation_config={
                'temperature': 0.1,
                'top_p': 0.95
            }
        )
        self.model_id = model_id

    def _create_tactic_generation_prompt(self , goal_state: LeanGoalState , constraints: SearchConstraints) -> str:
        weighted_tactics = constraints.get_weighted_tactics()
        priority_list = ', '.join([f'{t} (weight: {w})' for t,w in weighted_tactics[:5]])

        return f"""
        Given the following Lean 4 proof state:

        {goal_state.to_prompt_format()}

        Follow these search constraints:
        - Primary tactics: {constraints.primary_tactic_types}
        - Relevant lemmas: {constraints.relevant_lemmas}
        - Avoid: {constraints.avoid_tactics}
        - Strategy: {constraints.reasoning}
        - Priorities: {priority_list}

        Generate the single best, concrete, and executable Lean 4 tactic for this state.

        EXAMPLE:
        apply FiniteDimensional.finrank_add_finrank_ker

        Return ONLY the Lean 4 tactic code, and nothing else.
        """

    def _tactic_system_message(self) -> str:
        return """You are a Lean 4 code generator. 
        You output only valid, executable Lean 4 tactic code.
        Do not add any explanations, markdown, or JSON.
        """

    def generate_candidates(self , goal_state: LeanGoalState , constraints: SearchConstraints):
        system_message = self._tactic_system_message()
        user_prompt = self._create_tactic_generation_prompt(
            goal_state,
            constraints
        )

        try:
            full_prompt = f'{system_message}\n\n{user_prompt}'
            response_text = self.model.text_generation(full_prompt)

            s = response_text.strip()
            if "```" in s:
                s = s.split("```")[-2] if s.count("```") >= 2 else s.replace("```", "")
            s = s.strip().strip('`').strip()

            tactic_line = s.splitlines()[0].strip()

            if not tactic_line:
                raise ValueError("Model returned empty tactic")

            candidate = TacticCandidate(
                tactic_code=tactic_line,
                tactic_type="raw_generated",
                justification="Raw tactic from model",
                priority=1.0,
                expected_subgoals=[]
            )

            return [candidate]

        except Exception as e:
            raise ValueError(f'{e}')