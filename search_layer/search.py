''' this class will contain the whole logic and workflow step by step  '''
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState , SearchConstraints , TacticCandidate , FailedTactic
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from validator_layer.validator import LeanValidator

class Search:
    def __init__(self , reasoner: MathReasoner , generator: LeanGenerator):
        self.reasoner = reasoner
        self.generator = generator
        self.validator = LeanValidator
    
    def search(self , state: LeanGoalState , depth: int):
        # dfs for now>
        # candidates -> goal
        failures = []  # placeholder

        
        # STEP 1: call MathReasoner to generate SearchConstraints
        constraints = self.reasoner.generate_search_constraints(
            goal_state=state,
            failed_attempts=failures,
        )
        # STEP 2: check with FCM
        ...
        # STEP 3: call LeanGenerator
        candidates = self.generator.generate_candidates(
            goal_state=state,
            constraints=constraints
        )
        # STEP 4: take TacticCandidate(s) and validate
        for candidate in candidates:
            next_state = self.validator(...)
        # STEP 5: learning loop
            # VALID: new LeanGoalState, strengthen weights on FCM, repeat 1
            # INVALID: weaken weights on FCM, try next candidate from 3 and repeat 4. 
                        # if all has been exhausted, repeat from 1 and add to FailedTactics
            # PROOF_FINISHED: yay!

        pass