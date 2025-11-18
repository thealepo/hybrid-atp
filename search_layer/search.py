import logging
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Set, List, Optional

from llm_layer.models.reasoning_model import MathReasoner
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.data_structures.base import FailedTactic, TacticCandidate
from llm_layer.utils.state_converter import tactic_state_to_goal_state
from search_layer.search_strats.base import SearchStrategy
from validation_layer.validator import LeanDojoValidator, ValidationResult, ValidationResponse

from lean_dojo import TacticState

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
    def __init__(self, reasoner: MathReasoner, generator: LeanGenerator, validator: LeanDojoValidator, strategy: SearchStrategy):
        self.reasoner = reasoner
        self.generator = generator
        self.validator = validator
        self.strategy = strategy

        self.metrics = SearchMetrics()
        self.failures: List[FailedTactic] = []
        self.visited: Set[str] = set()

    def _hash_state(self, state: TacticState) -> str:
        return state.pp

    def search(self, init_state: TacticState, max_depth: int = 10, max_iterations: int = 500, parallel: int = 3) -> Optional[List[TacticCandidate]]:
        self.strategy.add_state(init_state, [], 0)

        with ThreadPoolExecutor(max_workers=parallel) as pool:
            while self.strategy.has_next() and self.metrics.iterations < max_iterations:
                self.metrics.iterations += 1
                current_state, path, depth = self.strategy.get_next_state()
                self.metrics.states_visited += 1

                state_hash = self._hash_state(current_state)
                if state_hash in self.visited:
                    continue
                self.visited.add(state_hash)

                if depth >= max_depth:
                    continue

                # Convert TacticState to LeanGoalState for LLM models
                goal_state = tactic_state_to_goal_state(current_state, proof_depth=depth)
                
                constraints = self.reasoner.generate_search_constraints(
                    goal_state=goal_state,
                    failed_attempts=self.failures if self.failures else None
                )
                candidates = self.generator.generate_candidates(
                    goal_state=goal_state,
                    constraints=constraints,
                )

                if not candidates:
                    continue

                futures = {pool.submit(self.validator.validate, current_state, c.tactic_code): c for c in candidates}

                for fut in as_completed(futures):
                    candidate = futures[fut]

                    try:
                        response: ValidationResponse = fut.result()
                    except Exception as e:
                        self.metrics.failed_validations += 1
                        self.failures.append(FailedTactic(
                            tactic=candidate.tactic_code,
                            error_message=str(e),
                            goal_state=current_state.pp
                        ))
                        continue

                    self.metrics.candidates_evaluated += 1

                    if response.result_type == ValidationResult.PROOF_FINISHED:
                        self.metrics.proofs_found += 1
                        logger.info(f"Proof finished after {self.metrics.iterations} iterations.")
                        return path + [candidate]

                    elif response.result_type == ValidationResult.VALID:
                        self.metrics.successful_validations += 1
                        next_state = response.next_state

                        self.strategy.add_state(
                            next_state,
                            path + [candidate],
                            depth + 1
                        )

                    else:
                        self.metrics.failed_validations += 1
                        self.failures.append(FailedTactic(
                            tactic=candidate.tactic_code,
                            error_message=response.error or "Unknown error",
                            goal_state=current_state.pp
                        ))

        logger.info("Search ended with no proof.")
        logger.info(
            f"Metrics: iterations={self.metrics.iterations}, "
            f"visited={self.metrics.states_visited}, "
            f"candidates={self.metrics.candidates_evaluated}, "
            f"successes={self.metrics.successful_validations}, "
            f"fails={self.metrics.failed_validations}, "
            f"proofs={self.metrics.proofs_found}"
        )
        return None
