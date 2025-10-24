''' this class will contain the whole logic and workflow step by step  '''
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState , SearchConstraints , TacticCandidate
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner

class Search:
    def __init__(self , reasoner: MathReasoner , generator: LeanGenerator):
        self.reasoner = reasoner
        self.generator = generator
    
    def search():
        # dfs for now>
        # candidates -> goal
        
        # STEP 1: call MathReasoner to generate SearchConstraints

        # STEP 2: check with FCM

        # STEP 3: call LeanGenerator

        # STEP 4: take TacticCandidate(s) and validate

        # STEP 5: learning loop
            # VALID: new LeanGoalState, strengthen weights on FCM, repeat 1
            # INVALID: weaken weights on FCM, try next candidate from 3 and repeat 4. 
                        # if all has been exhausted, repeat from 1 and add to FailedTactics
            # PROOF_FINISHED: yay!

        pass