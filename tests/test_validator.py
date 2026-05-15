from validation_layer.validator import (
    ValidationResult,
    _classify,
    validate_tactic,
)


class _Dojo:
    def __init__(self , result):
        self._result = result
        self.calls = 0

    def run_tac(self , state , tactic):
        self.calls += 1
        if isinstance(self._result, Exception):
            raise self._result
        return self._result


def test_classify_proof_finished(fake_proof_finished):
    resp = _classify(fake_proof_finished)
    assert resp.result_type == ValidationResult.PROOF_FINISHED


def test_classify_lean_error(fake_lean_error):
    resp = _classify(fake_lean_error)
    assert resp.result_type == ValidationResult.INVALID
    assert resp.error == "bad tactic"


def test_classify_tactic_state_is_valid(fake_state):
    resp = _classify(fake_state("⊢ new goal"))
    assert resp.result_type == ValidationResult.VALID
    assert resp.next_state is not None


def test_validate_tactic_handles_exception(fake_state):
    dojo = _Dojo(RuntimeError("boom"))
    resp = validate_tactic(dojo, fake_state(), "intro")
    assert resp.result_type == ValidationResult.INVALID
    assert "boom" in resp.error
