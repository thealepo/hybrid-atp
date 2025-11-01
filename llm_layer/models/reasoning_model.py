import json
from typing import List , Optional

from .wrapper import Model
from ..data_structures.base import LeanGoalState , FailedTactic , SearchConstraints
from ..utils.json_parser import extract_json

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
        
    def _create_constraint_generation_prompt(self , goal_state: LeanGoalState , failed_attempts: Optional[List[FailedTactic]] , context: Optional[str]) -> str:

        failed_section = ''
        if failed_attempts:
            failed_list = '\n'.join([
                f"- {t.tactic}: {t.error_message}"
                for t in failed_attempts[-5:]
            ])
            failed_section = f"""
            PREVIOUS FAILED ATTEMPTS:
            {failed_list}

            Learn from these failures and suggest different approaches.
            """

        context_section = f'\nTHEOREM CONTEXT:\n{context}\n' if context else ''

        # gemini-generated prompt
        return f"""
        You are guiding an automated theorem proving search algorithm for Lean 4.
        Your job is to constrain the search space so it explores the most promising tactics first.

        {goal_state.to_prompt_format()}
        {context_section}
        {failed_section}

        TASK: Analyze this proof state and provide ACTIONABLE search constraints.

        Think step-by-step:
        1. What is the structure of the goal? (equality, implication, forall, etc.)
        2. What hypotheses are available? Which are most relevant?
        3. What proof technique fits this structure? (induction, cases, direct proof, etc.)
        4. What specific Lean tactics accomplish this? (apply, rw, have, intro, etc.)
        5. What lemmas from Mathlib are likely helpful?
        6. What tactics should be avoided? (won't help with this goal type)
        7. How confident are you in this strategy? (affects exploration vs exploitation)

        Return a JSON object with these EXACT fields:
        {{
            "primary_tactic_types": ["apply", "rw"],
            "relevant_lemmas": ["FiniteDimensional.finrank_add_finrank_ker"],
            "avoid_tactics": ["ring", "omega"],
            "expected_depth": 5,
            "confidence": 0.85,
            "tactic_weights": {{
                "apply": 2.5,
                "rw": 1.8,
                "have": 1.2,
                "simp": 0.8
            }},
            "reasoning": "The goal is an equality of dimensions. Primary strategy: apply the rank-nullity theorem directly, then simplify. High confidence because all hypotheses align.",
            "alternative_strategies": [
                "If apply fails, try rewriting with dimension lemmas first",
                "Could also prove by showing both sides equal to same value"
            ]
        }}

        CRITICAL RULES:
        1. primary_tactic_types: Must be valid Lean 4 tactic names
        2. relevant_lemmas: Must be actual Mathlib lemma names (or generic descriptors)
        3. confidence: 0.0 to 1.0 (be honest about uncertainty)
        4. expected_depth: Realistic estimate of remaining proof steps
        5. tactic_weights: Higher numbers = higher priority (1.0 = baseline)
        6. reasoning: Concise explanation of your strategy
        7. Return ONLY valid JSON, no other text

        Be specific and actionable. The search algorithm will use these constraints directly.
        """

    def _system_message(self) -> str:
        return """You are a Lean 4 proof strategy expert. You analyze proof states and recommend search constraints for automated theorem provers.

        You MUST respond with valid JSON only. No explanations outside the JSON.
        Your recommendations directly control search behavior, so be precise and actionable.
        """
    def _example_goal(self) -> str:
        example_state = LeanGoalState(
            goal="⊢ ∀ (n : ℕ), n + 0 = n",
            hypothesis={},
            proof_depth=0
        )
        return f"""
        {example_state.to_prompt_format()}

        THEOREM CONTEXT:
        Basic arithmetic property about addition with zero.
        """
    def _example_constraints(self) -> str:
        example = {
            "primary_tactic_types": ["intro", "simp", "rfl"],
            "relevant_lemmas": ["add_zero"],
            "avoid_tactics": ["induction", "cases", "ring"],
            "expected_depth": 2,
            "confidence": 0.95,
            "tactic_weights": {
                "intro": 2.0,
                "simp": 1.8,
                "rfl": 1.5,
                "rw": 1.0
            },
            "reasoning": "Universal quantifier requires intro first. Then add_zero simplifies directly, or simp will solve it. Very straightforward, high confidence.",
            "alternative_strategies": [
                "Could use rw [add_zero] explicitly instead of simp"
            ]
        }
        return json.dumps(example, indent=2)    
    
    def _parse_constraints(self , json_text: str) -> SearchConstraints:
        try:
            data = json.loads(json_text)
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON: {e}")

        return SearchConstraints(
            primary_tactic_types=data.get("primary_tactic_types", []),
            relevant_lemmas=data.get("relevant_lemmas", []),
            avoid_tactics=data.get("avoid_tactics", []),
            expected_depth=data.get("expected_depth", 5),
            confidence=max(0.0, min(1.0, data.get("confidence", 0.5))),
            tactic_weights=data.get("tactic_weights", {}),
            reasoning=data.get("reasoning", ""),
            alternative_strategies=data.get("alternative_strategies", [])
        )

    def generate_search_constraints(self , goal_state: LeanGoalState , failed_attempts: Optional[List[FailedTactic]] = None , context: Optional[str] = None) -> SearchConstraints:
        prompt = self._create_constraint_generation_prompt(
            goal_state=goal_state,
            failed_attempts=failed_attempts,
            context=context
        )

        messages = [
            { 'role':'system' , 'content':self._system_message() },
            { 'role':'user' , 'content':self._example_goal() },
            { 'role':'assistant' , 'content':self._example_constraints() },
            { 'role':'user' , 'content':prompt }
        ]

        try:
            response = self.model.chat_completion(messages)
            json_text = extract_json(response)
            return self._parse_constraints(json_text)
        except Exception as e:
            raise ValueError(e)