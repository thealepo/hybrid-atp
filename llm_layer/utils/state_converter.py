"""
Utility to convert between lean_dojo TacticState and LeanGoalState.
"""
import re
from typing import Dict
from lean_dojo import TacticState
from ..data_structures.base import LeanGoalState


def tactic_state_to_goal_state(state: TacticState, proof_depth: int = 0) -> LeanGoalState:
    pp_text = state.pp
    
    # Extract goal (usually starts with ⊢)
    goal_match = re.search(r'⊢\s*(.+?)(?:\n|$)', pp_text, re.MULTILINE | re.DOTALL)
    if goal_match:
        goal = f"⊢ {goal_match.group(1).strip()}"
    else:
        goal = "⊢ " + pp_text.split('⊢')[-1].split('\n')[0].strip() if '⊢' in pp_text else pp_text.strip()
    
    # Extract hypotheses (usually in format "name : type" before the goal)
    hypothesis: Dict[str, str] = {}
    
    # Try to parse hypotheses from the pp text
    # Hypotheses are typically listed before the goal, one per line
    lines = pp_text.split('\n')
    for line in lines:
        line = line.strip()
        if not line or line.startswith('⊢'):
            break
        # Match pattern like "name : type" or "name: type"
        hyp_match = re.match(r'^([a-zA-Z_][a-zA-Z0-9_\']*)\s*:\s*(.+)$', line)
        if hyp_match:
            name = hyp_match.group(1)
            typ = hyp_match.group(2).strip()
            hypothesis[name] = typ
    
    # If no hypotheses found, try alternative parsing
    if not hypothesis:
        # Look for patterns in the entire text
        hyp_pattern = r'([a-zA-Z_][a-zA-Z0-9_\']*)\s*:\s*([^\n⊢]+)'
        matches = re.findall(hyp_pattern, pp_text)
        for name, typ in matches:
            if name not in ['Type', 'Field', 'AddCommGroup', 'Module']:
                hypothesis[name] = typ.strip()
    
    return LeanGoalState(
        goal=goal,
        hypothesis=hypothesis,
        local_context=[],
        proof_depth=proof_depth
    )

