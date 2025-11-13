import json
import hashlib
import threading
import traceback
from dataclasses import dataclass
from typing import Optional, Any


from validation_layer.validator import ValidationResult, ValidationResponse
from llm_layer.data_structures.base import LeanGoalState


try:
    import lean_dojo as dojo  # type: ignore
except Exception as e:
    dojo = None
    _dojo_import_error = e 


class LeanDojoValidator:
    def __init__(self, dojo_module: Optional[Any] = None):
        self.dojo = dojo_module or dojo
        self._cache = {}
        self._lock = threading.Lock()

        if self.dojo is None:
            raise ImportError(
                f"Import error was: {_dojo_import_error}"
            )

    def _cache_key(self, goal_state: LeanGoalState, tactic_code: str) -> str:
        key_str = json.dumps({
            "goal": getattr(goal_state, "goal", repr(goal_state)),
            "hypothesis": getattr(goal_state, "hypothesis", None),
            "context": getattr(goal_state, "local_context", None),
            "tactic": tactic_code
        }, sort_keys=True, default=str)
        return hashlib.sha256(key_str.encode("utf-8")).hexdigest()

    def validate(self, goal_state: Any, tactic_code: str) -> ValidationResponse:
        key = self._cache_key(goal_state, tactic_code)
        with self._lock:
            if key in self._cache:
                return self._cache[key]

        try:
            tactic_state = self._ensure_dojo_state(goal_state)
        except Exception as e:
            err = f"Failed to convert goal_state to LeanDojo TacticState: {e}\n{traceback.format_exc()}"
            resp = ValidationResponse(result_type=ValidationResult.INVALID, error=err, file_path=None)
            with self._lock:
                self._cache[key] = resp
            return resp

        try:
            result = self.dojo.run_tac(tactic_state, tactic_code)
        except Exception as e:
            err = f"dojo.run_tac raised an exception:\n{e}\n{traceback.format_exc()}"
            resp = ValidationResponse(result_type=ValidationResult.INVALID, error=err, file_path=None)
            with self._lock:
                self._cache[key] = resp
            return resp

        rname = result.__class__.__name__ if result is not None else "None"
        raw_info = repr(result)

        if rname.lower().startswith("prooffinished") or getattr(result, "is_proof_finished", False):
            resp = ValidationResponse(result_type=ValidationResult.PROOF_FINISHED, error=str(raw_info), file_path=None)
        elif rname.lower().startswith("leanerror") or getattr(result, "is_error", False) or hasattr(result, "error"):
            msg = getattr(result, "message", None) or getattr(result, "error", None) or str(raw_info)
            resp = ValidationResponse(result_type=ValidationResult.INVALID, error=str(msg), file_path=None)
        else:
            resp = ValidationResponse(result_type=ValidationResult.VALID, error=str(raw_info), file_path=None)

        with self._lock:
            self._cache[key] = resp

        return resp

    def _ensure_dojo_state(self, goal_state: Any):
        if hasattr(goal_state, "pp") or hasattr(goal_state, "goals") or hasattr(goal_state, "hypotheses"):
            return goal_state

        if isinstance(goal_state, LeanGoalState) or hasattr(goal_state, "goal"):
            pp = goal_state.goal
            helpers = [
                ("parse_state", lambda f: getattr(self.dojo, "parse_state")(f)),
                ("state_from_pp", lambda f: getattr(self.dojo, "state_from_pp")(f)),
                ("TacticState.from_pp", lambda f: getattr(self.dojo, "TacticState").from_pp(f)),
                ("TacticState", lambda f: getattr(self.dojo, "TacticState")(f)),
                ("mk_state", lambda f: getattr(self.dojo, "mk_state")(f)),
            ]
            tried = []
            for name, fn in helpers:
                try:
                    if hasattr(self.dojo, name.split(".")[0]) or ("TacticState" in name and hasattr(self.dojo, "TacticState")):
                        st = fn(pp)
                        if st is not None and (hasattr(st, "pp") or hasattr(st, "goals")):
                            return st
                except Exception as e:
                    tried.append((name, str(e)))
                    continue

            details = "\n".join([f"{n}: {err}" for n, err in tried])
            raise RuntimeError(
                "Could not convert LeanGoalState string to a LeanDojo TacticState automatically.\n"
                "LeanDojo helper functions attempted but not available or failed. "
                "You should either:\n"
                "  1) pass a LeanDojo TacticState object into LeanDojoValidator.validate(...), or\n"
                "  2) implement a conversion using your local dojo API (e.g., dojo.parse_state or dojo.TacticState.from_pp).\n\n"
                f"Attempts:\n{details}"
            )

        # Unknown type
        raise TypeError("goal_state must be either a LeanDojo TacticState or your LeanGoalState dataclass with a 'goal' string.")

