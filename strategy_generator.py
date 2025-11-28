"""
Simplified strategy generator without validation layer.
Given a theorem statement, generates a proof strategy using LLM reasoning.
"""
import logging
from typing import Optional, Dict, Any

from llm_layer.models.reasoning_model import MathReasoner
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.data_structures.base import LeanGoalState, SearchConstraints, TacticCandidate

logger = logging.getLogger("strategy_generator")
logger.setLevel(logging.INFO)


class StrategyGenerator:
    """Generates proof strategies for theorems without validation."""

    def __init__(self, reasoner: MathReasoner, generator: LeanGenerator):
        self.reasoner = reasoner
        self.generator = generator

    def generate_strategy(
        self,
        theorem_statement: str,
        hypothesis: Optional[Dict[str, str]] = None,
        context: Optional[str] = None,
        num_tactics: int = 5
    ) -> Dict[str, Any]:
        """
        Generate a proof strategy for the given theorem.

        Args:
            theorem_statement: The theorem to prove (e.g., "⊢ ∀ (n : ℕ), n + 0 = n")
            hypothesis: Optional dictionary of hypothesis names to types
            context: Optional context about the theorem
            num_tactics: Number of tactic candidates to generate

        Returns:
            Dictionary containing the strategy analysis and suggested tactics
        """
        # Create goal state from theorem
        goal_state = LeanGoalState(
            goal=theorem_statement,
            hypothesis=hypothesis or {},
            proof_depth=0
        )

        logger.info(f"Analyzing theorem: {theorem_statement}")

        # Generate search constraints using the reasoner
        try:
            constraints = self.reasoner.generate_search_constraints(
                goal_state=goal_state,
                failed_attempts=None,
                context=context
            )

            logger.info(f"Strategy generated with confidence: {constraints.confidence}")

        except Exception as e:
            logger.error(f"Error generating constraints: {e}")
            raise

        # Generate tactic candidates
        # Note: The generator returns the same tactic when called multiple times
        # because it uses low temperature. We'll just call it once and use
        # the weighted tactics from constraints to generate variety.
        tactic_candidates = []

        try:
            # Get one primary candidate from the generator
            candidates = self.generator.generate_candidates(
                goal_state=goal_state,
                constraints=constraints
            )
            if candidates:
                tactic_candidates.extend(candidates)
        except Exception as e:
            logger.warning(f"Error generating primary tactic: {e}")

        # Add additional candidates based on the weighted tactics from constraints
        weighted_tactics = constraints.get_weighted_tactics()[:num_tactics-1]

        for tactic_name, weight in weighted_tactics:
            # Create simple tactic candidates from the strategy
            if tactic_name.lower() in ['intro', 'simp', 'rfl']:
                tactic_candidates.append(
                    TacticCandidate(
                        tactic_code=tactic_name,
                        tactic_type="strategy_suggested",
                        justification=f"Suggested by strategy analysis (weight: {weight:.2f})",
                        priority=weight,
                        expected_subgoals=[]
                    )
                )
            # For rewrite, need a lemma
            elif tactic_name.lower() == 'rw' and constraints.relevant_lemmas:
                lemma = constraints.relevant_lemmas[0]
                tactic_candidates.append(
                    TacticCandidate(
                        tactic_code=f"rw [{lemma}]",
                        tactic_type="rewrite_with_lemma",
                        justification=f"Rewrite using suggested lemma (weight: {weight:.2f})",
                        priority=weight,
                        expected_subgoals=[]
                    )
                )
            # For lemma-based tactics
            elif constraints.relevant_lemmas and tactic_name in ['apply', 'exact', 'have']:
                lemma = constraints.relevant_lemmas[0]
                tactic_candidates.append(
                    TacticCandidate(
                        tactic_code=f"{tactic_name} {lemma}",
                        tactic_type="lemma_application",
                        justification=f"Apply relevant lemma (weight: {weight:.2f})",
                        priority=weight,
                        expected_subgoals=[]
                    )
                )

        # Build response
        return {
            "theorem": theorem_statement,
            "analysis": {
                "goal_type": constraints.goal_type,
                "confidence": constraints.confidence,
                "reasoning": constraints.reasoning,
                "expected_depth": constraints.expected_depth
            },
            "strategy": {
                "primary_tactics": constraints.primary_tactic_types,
                "relevant_lemmas": constraints.relevant_lemmas,
                "avoid_tactics": constraints.avoid_tactics,
                "tactic_weights": constraints.tactic_weights,
                "alternative_strategies": constraints.alternative_strategies
            },
            "suggested_tactics": [
                {
                    "tactic": tc.tactic_code,
                    "type": tc.tactic_type,
                    "justification": tc.justification,
                    "priority": tc.priority
                }
                for tc in tactic_candidates
            ]
        }
