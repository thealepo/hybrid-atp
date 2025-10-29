''' this class will contain the whole logic and workflow step by step  '''
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState , SearchConstraints , TacticCandidate , FailedTactic
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from validator_layer.validator import LeanValidator, ValidationResult

class Search:
    def __init__(self , reasoner: MathReasoner , generator: LeanGenerator , validator: LeanValidator):
        self.reasoner = reasoner
        self.generator = generator
        self.validator = validator
        # self.fcm = None
    
    def search(self , state: LeanGoalState , max_depth: int = 10 , max_iterations: int = 500):
        # dfs for now>
        # MCTS (Monte-Carlo Tree Search) can be ideal.
        # BENCHMARKING IDEA: between different search algos
        # candidates -> goal
        iterations = 0
        failures = list[FailedTactic] = []
        stack = []

        while stack and iterations < max_iterations:
            iterations += 1
            tactic_state , lean_goal_state , depth , path = stack.pop()

            # STEP 1: call MathReasoner to generate SearchConstraints
            constraints = self.reasoner.generate_search_constraints(
                goal_state=state,
                failed_attempts=failures
            )
            # STEP 2: check with FCM
            ...
            # STEP 3: call LeanGenerator
            candidates = self.generator.generate_candidates(
                goal_state=state,
                constraints=constraints
            )
            # validate candidates
            for candidate in candidates:
                response = self.validator.validate_tactic(
                    current_state='''untranslated''',
                    tactic_code=candidate.tactic_code
                )

                if response.result_type == ValidationResult.PROOF_FINISHED:
                    final_path = path + [candidate.tactic_code]
                    return final_path
                elif response.result_type == ValidationResult.VALID:
                    new_tactic_state = response.new_state
                
                    new_path = path + [candidate.tactic_code]
                elif response.result_type == ValidationResult.INVALID:
                    failures.append(
                        FailedTactic(
                            tactic=candidate.tactic_code,
                            error_message=...,
                            goal_state=...
                        )
                    )