''' this class will contain the whole logic and workflow step by step  '''
import sys
import os
from copy import deepcopy

sys.path.append(os.path.join(os.path.dirname(__file__) , '..'))
from llm_layer.data_structures.base import LeanGoalState , FailedTactic
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from validation_layer.validator import LeanValidator , ValidationResult

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

        stack = [(state , [] , 0)]
        failures: list[FailedTactic] = []
        iterations = 0

        while stack and iterations < max_iterations:
            iterations += 1
            current_state , path , depth = stack.pop()

            if depth >= max_depth:
                continue

            # generate search constraints
            constraints = self.reasoner.generate_search_constraints(
                goal_state=current_state,
                failed_attempts=failures
            )

            # generate candidates
            candidates = self.generator.generate_candidates(
                goal_state=current_state,
                constraints=constraints
            )

            # validate each candidate
            for candidate in candidates:
                response = self.validator.validate(
                    goal_state=current_state,
                    tactic_code=candidate.tactic_code
                )

                # PROOF_FINISHED
                if response.result_type == ValidationResult.PROOF_FINISHED:
                    return path + [candidate.tactic_code]
                elif response.result_type == ValidationResult.VALID:
                    # create new LeanGoalSatte
                    new_state = deepcopy(current_state)
                    new_state.proof_depth += 1

                    stack.append(
                        (new_state , path+[candidate.tactic_code] , depth+1)
                    )
                elif response.result_type == ValidationResult.INVALID:
                    failures.append(
                        FailedTactic(
                            tactic=candidate.tactic_code,
                            error_message=response.error,
                            goal_state=str(current_state)
                        )
                    )

        return None