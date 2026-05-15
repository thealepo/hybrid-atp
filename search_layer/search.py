from __future__ import annotations

import json
import logging
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import List, Optional, Set

from lean_dojo import Dojo, TacticState

from llm_layer.data_structures.base import FailedTactic, TacticCandidate
from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from llm_layer.utils.state_converter import tactic_state_to_goal_state
from search_layer.search_strats.base import SearchStrategy
from search_layer.search_strats.mcts import MCTS
from validation_layer.validator import (
    ValidationResponse,
    ValidationResult,
    validate_tactic,
)

logger = logging.getLogger("hybrid_atp.search")


@dataclass
class SearchMetrics:
    iterations: int = 0
    states_visited: int = 0
    candidates_evaluated: int = 0
    successful_validations: int = 0
    failed_validations: int = 0
    crashes: int = 0
    proofs_found: int = 0
    wall_seconds: float = 0.0


@dataclass
class SearchResult:
    success: bool
    path: List[TacticCandidate] = field(default_factory=list)
    metrics: SearchMetrics = field(default_factory=SearchMetrics)

    def proof_script(self) -> str:
        return "\n".join(c.tactic_code for c in self.path)

    def to_dict(self) -> dict:
        return {
            "success": self.success,
            "proof": [c.tactic_code for c in self.path],
            "metrics": asdict(self.metrics),
        }


class Search:
    def __init__(
        self,
        reasoner: MathReasoner,
        generator: LeanGenerator,
        dojo: Dojo,
        strategy: SearchStrategy,
        *,
        reasoner_every: int = 1,
    ):
        self.reasoner = reasoner
        self.generator = generator
        self.dojo = dojo
        self.strategy = strategy
        self.reasoner_every = max(1 , reasoner_every)

        self.metrics = SearchMetrics()
        self.failures: List[FailedTactic] = []
        self.visited: Set[str] = set()
        self._dojo_lock = threading.Lock()
        self._constraints_cache = None

    def _hash_state(self , state: TacticState) -> str:
        return state.pp

    def _validate(self , state: TacticState , tactic: str) -> ValidationResponse:
        with self._dojo_lock:
            return validate_tactic(self.dojo, state, tactic)

    def search(
        self,
        init_state: TacticState,
        max_depth: int = 10,
        max_iterations: int = 500,
        parallel: int = 1,
        timeout_seconds: Optional[float] = None,
    ) -> SearchResult:
        self.strategy.add_state(init_state , [] , 0 , score=1.0)
        start = time.time()

        with ThreadPoolExecutor(max_workers=max(1,parallel)) as pool:
            while self.strategy.has_next() and self.metrics.iterations < max_iterations:
                if timeout_seconds is not None and (time.time() - start) > timeout_seconds:
                    logger.info("Search timed out after %.1fs" , time.time() - start)
                    break

                self.metrics.iterations += 1
                current_state, path, depth = self.strategy.get_next_state()
                self.metrics.states_visited += 1

                state_hash = self._hash_state(current_state)
                if state_hash in self.visited:
                    continue
                self.visited.add(state_hash)

                if depth >= max_depth:
                    continue

                goal_state = tactic_state_to_goal_state(current_state , proof_depth=depth)

                if self._constraints_cache is None or self.metrics.iterations % self.reasoner_every == 0:
                    try:
                        self._constraints_cache = self.reasoner.generate_search_constraints(
                            goal_state=goal_state,
                            failed_attempts=self.failures or None,
                        )
                    except Exception as e:
                        logger.warning("Reasoner failed: %s — using cached/default constraints", e)
                        if self._constraints_cache is None:
                            continue
                constraints = self._constraints_cache

                try:
                    candidates = self.generator.generate_candidates(
                        goal_state=goal_state , constraints=constraints
                    )
                except Exception as e:
                    logger.warning("Generator failed: %s", e)
                    continue

                if not candidates:
                    continue

                logger.debug("iter=%d depth=%d candidates=%d" , self.metrics.iterations , depth , len(candidates))

                futures = {
                    pool.submit(self._validate , current_state , c.tactic_code): c
                    for c in candidates
                }

                proof_found: Optional[List[TacticCandidate]] = None
                for fut in as_completed(futures):
                    candidate = futures[fut]
                    self.metrics.candidates_evaluated += 1
                    try:
                        response: ValidationResponse = fut.result()
                    except Exception as e:
                        self.metrics.failed_validations += 1
                        self.failures.append(
                            FailedTactic(
                                tactic=candidate.tactic_code,
                                error_message=str(e),
                                goal_state=current_state.pp,
                            )
                        )
                        continue

                    if response.result_type == ValidationResult.PROOF_FINISHED:
                        self.metrics.proofs_found += 1
                        proof_found = path + [candidate]
                        if isinstance(self.strategy , MCTS):
                            self.strategy.update_score(current_state , 1.0)
                        logger.info(
                            "Proof finished in %d iterations (depth=%d)" , self.metrics.iterations , depth + 1
                        )
                        break

                    if response.result_type == ValidationResult.VALID and response.next_state is not None:
                        self.metrics.successful_validations += 1
                        next_state = response.next_state
                        new_score = candidate.priority - 0.05 * (depth + 1)
                        self.strategy.add_state(
                            next_state, path + [candidate], depth + 1, score=new_score
                        )
                        if isinstance(self.strategy, MCTS):
                            self.strategy.update_score(current_state, 0.1)
                    elif response.result_type == ValidationResult.CRASHED:
                        self.metrics.crashes += 1
                        logger.error("Dojo crashed on tactic %r: %s" , candidate.tactic_code , response.error)
                    else:
                        self.metrics.failed_validations += 1
                        self.failures.append(
                            FailedTactic(
                                tactic=candidate.tactic_code,
                                error_message=response.error or "unknown",
                                goal_state=current_state.pp,
                            )
                        )

                if proof_found is not None:
                    self.metrics.wall_seconds = time.time() - start
                    return SearchResult(success=True , path=proof_found , metrics=self.metrics)

        self.metrics.wall_seconds = time.time() - start
        logger.info("Search ended without proof: %s" , asdict(self.metrics))
        return SearchResult(success=False , path=[] , metrics=self.metrics)

    def dump_metrics(self , path: Path) -> None:
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(asdict(self.metrics) , indent=2))
