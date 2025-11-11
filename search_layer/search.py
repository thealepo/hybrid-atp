''' controller class'''

import logging
from copy import deepcopy
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List
from llm_layer.data_structures.base import LeanGoalState, FailedTactic
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from search_layer.search_strats.base import SearchStrategy
from validation_layer.validator import LeanValidator, ValidationResult, ValidationResponse

logger = logging.getLogger("hybrid_atp.search")
logger.setLevel(logging.INFO)

class SearchMetrics:
    def __init__(self):
        self.iterations = 0
        self.states_visited = 0
        self.candidates_evaluated = 0
        self.successful_validations = 0
        self.failed_validations = 0
        self.proofs_found = 0

class Search:
    def __init__(self , reasoner: MathReasoner , generator: LeanGenerator , validator: LeanValidator , strategy: SearchStrategy):
        self.reasoner = reasoner
        self.generator = generator
        self.validator = validator
        self.strategy = strategy

        self.failures: List[FailedTactic] = []
        self.visited = set()
        self.metrics = SearchMetrics()

    def search(self, state: LeanGoalState, max_depth: int = 10, max_iterations: int = 500, parallel: int = 3):
        self.strategy.add_state(state, [], 0)

        with ThreadPoolExecutor(max_workers=parallel) as pool:
            while self.strategy.has_next() and self.metrics.iterations < max_iterations:
                self.metrics.iterations += 1

                current_state, path, depth = self.strategy.get_next_state()
                self.metrics.states_visited += 1

                state_hash = hash(str(current_state))
                if state_hash in self.visited:
                    continue
                self.visited.add(state_hash)

                if depth >= max_depth:
                    continue

                constraints = self.reasoner.generate_search_constraints(
                    goal_state=state,
                    failed_attempts=self.failures
                )
                candidates = self.generator.generate_candidates(
                    goal_state=state,
                    constraints=constraints,
                    num_candidates=5
                )

                if not candidates:
                    continue

                # parallel validation of candidates to speed up I/O
                futures = {pool.submit(self.validator.validate, current_state, c.tactic_code): c for c in candidates}
                for fut in as_completed(futures):
                    candidate = futures[fut]
                    try:
                        response: ValidationResponse = fut.result()
                    except Exception as e:
                        logger.warning(f"Validation raised: {e}")
                        self.failures.append(FailedTactic(candidate.tactic_code, str(e), str(current_state)))
                        self.metrics.failed_validations += 1
                        continue

                    self.metrics.candidates_evaluated += 1

                    if response.result_type == ValidationResult.PROOF_FINISHED:
                        self.metrics.proofs_found += 1
                        logger.info(f"Proof finished in {self.metrics.iterations} iterations")
                        return path + [candidate.tactic_code]
                    elif response.result_type == ValidationResult.VALID:
                        self.metrics.successful_validations += 1
                        new_state = deepcopy(current_state)
                        new_state.proof_depth += 1
                        self.strategy.add_state(new_state, path + [candidate.tactic_code], depth + 1)
                    else:
                        self.metrics.failed_validations += 1
                        self.failures.append(FailedTactic(candidate.tactic_code, response.error, str(current_state)))

            logger.info("Search ended without proof")
            logger.info(f"Metrics: iterations={self.metrics.iterations}, visited={self.metrics.states_visited}, candidates={self.metrics.candidates_evaluated}, successes={self.metrics.successful_validations}, fails={self.metrics.failed_validations}, proofs={self.metrics.proofs_found}")
            return None
