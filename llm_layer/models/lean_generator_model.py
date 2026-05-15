from __future__ import annotations

import json
import re
from typing import List, Optional

from ..data_structures.base import LeanGoalState, SearchConstraints, TacticCandidate
from ..utils.json_parser import extract_json
from .wrapper import Model


class LeanGenerator:
    def __init__(
        self,
        api_token: str,
        model_id: str,
        num_candidates: int = 8,
        num_beams: Optional[int] = None,
    ):
        self.model = Model(
            model_id=model_id,
            api_token=api_token,
            generation_config={
                "temperature": 0.7,
                "top_p": 0.95,
                "max_new_tokens": 256,
            },
        )
        self.model_id = model_id
        self.num_candidates = num_candidates
        self.num_beams = num_beams or num_candidates

    @property
    def is_seq2seq(self) -> bool:
        return "t5" in self.model_id.lower()

    def _seq2seq_prompt(self , goal_state: LeanGoalState) -> str:
        # ReProver / LeanDojo retriever-tacgen models take the raw tactic state.
        return goal_state.goal if goal_state.goal else goal_state.to_prompt_format()

    def _chat_prompt(self, goal_state: LeanGoalState, constraints: SearchConstraints) -> str:
        weighted = constraints.get_weighted_tactics()
        priorities = ", ".join(f"{t} (w={w})" for t, w in weighted[:6])

        return f"""Generate {self.num_candidates} candidate Lean 4 tactics for the proof state below.

{goal_state.to_prompt_format()}

CONSTRAINTS:
- Primary tactic types: {constraints.primary_tactic_types}
- Relevant lemmas: {constraints.relevant_lemmas}
- Avoid: {constraints.avoid_tactics}
- Strategy: {constraints.reasoning}
- Priority tactics: {priorities}

Return a JSON array of at most {self.num_candidates} candidates. Each candidate is an object:
{{"tactic_code": "...", "tactic_type": "apply|rw|simp|...", "justification": "...", "priority": 1.0}}

Rules:
- Each tactic_code must be a single valid Lean 4 tactic.
- No backticks, no markdown, no explanations outside the JSON.
"""

    def _system_message(self) -> str:
        return (
            "You are a Lean 4 tactic generator. Output ONLY valid JSON: an array of "
            "tactic candidate objects. Each tactic must be syntactically valid Lean 4."
        )

    @staticmethod
    def _clean_tactic(text: str) -> str:
        s = text.strip()
        if "```" in s:
            parts = [p for p in s.split("```") if p.strip()]
            if parts:
                s = parts[0] if "{" not in parts[0] else parts[-1]
        s = s.strip().strip("`")
        first_line = s.splitlines()[0].strip() if s else ""
        return first_line

    def _parse_candidates(self , json_text: str) -> List[TacticCandidate]:
        if not json_text:
            return []
        fixed = re.sub(r"\}\s*\{", "}, {", json_text.strip())
        if not fixed.startswith("["):
            fixed = f"[{fixed}]"
        try:
            data = json.loads(fixed)
        except json.JSONDecodeError:
            return []
        if isinstance(data, dict):
            data = [data]

        candidates: List[TacticCandidate] = []
        for item in data:
            if not isinstance(item, dict):
                continue
            code = (item.get("tactic_code") or "").strip()
            if not code:
                continue
            candidates.append(
                TacticCandidate(
                    tactic_code=code,
                    tactic_type=item.get("tactic_type", "unknown"),
                    justification=item.get("justification", ""),
                    priority=float(item.get("priority", 1.0)),
                    expected_subgoals=item.get("expected_subgoals", []),
                )
            )
        return candidates

    def generate_candidates(
        self, goal_state: LeanGoalState, constraints: SearchConstraints
    ) -> List[TacticCandidate]:
        if self.is_seq2seq:
            prompt = self._seq2seq_prompt(goal_state)
            try:
                samples = self.model.sample_local(
                    prompt,
                    num_return_sequences=self.num_candidates,
                    num_beams=self.num_beams,
                    do_sample=False,
                    max_new_tokens=128,
                )
            except Exception:
                samples = [self.model.text_generation(prompt)]

            seen = set()
            candidates: List[TacticCandidate] = []
            for i, raw in enumerate(samples):
                tac = self._clean_tactic(raw)
                if not tac or tac in seen:
                    continue
                seen.add(tac)
                tactic_type = tac.split()[0] if tac.split() else "unknown"
                weight = constraints.tactic_weights.get(tactic_type, 1.0)
                candidates.append(
                    TacticCandidate(
                        tactic_code=tac,
                        tactic_type=tactic_type,
                        justification="seq2seq sample",
                        priority=weight - (i * 0.01),
                        expected_subgoals=[],
                    )
                )
            candidates.sort(key=lambda c: c.priority, reverse=True)
            return candidates

        messages = [
            {"role": "system", "content": self._system_message()},
            {"role": "user", "content": self._chat_prompt(goal_state, constraints)},
        ]
        try:
            response = self.model.chat_completion(messages)
        except Exception as e:
            raise ValueError(f"Generator chat_completion failed: {e}") from e

        json_text = extract_json(response) or ""
        candidates = self._parse_candidates(json_text)
        candidates.sort(key=lambda c: c.priority, reverse=True)
        return candidates
