import os
import re
from typing import Dict, List, Optional, Tuple, Union
from dataclasses import dataclass
from enum import Enum

from google import genai


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


class GeminiMathReasoner:
    
    def __init__(self, api_key: Optional[str] = None, model_name: str = "gemini-1.5-pro"):
        client = genai.Client(api_key=api_key)
        self.model = client.models.get(model_name)
    
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

        Format your response with clear markdown headers. Be mathematically precise and explicit.
        """
    
    def _parse_gemini_response(self, response_text: str) -> CoTAnalysis:
        pass #TODO: parse the response and return as a CoTAnalysis object
