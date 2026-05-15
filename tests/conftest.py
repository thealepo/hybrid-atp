from __future__ import annotations

import sys
import types
from dataclasses import dataclass

import pytest


class _FakeTacticState:
    def __init__(self, pp: str, idx: int = 0):
        self.pp = pp
        self.id = idx


class _FakeProofFinished: ...
class _FakeProofGivenUp: ...


@dataclass
class _FakeLeanError:
    error: str


def _install_fake_lean_dojo() -> None:
    if "lean_dojo" in sys.modules:
        return
    mod = types.ModuleType("lean_dojo")
    mod.TacticState = _FakeTacticState
    mod.ProofFinished = _FakeProofFinished
    mod.ProofGivenUp = _FakeProofGivenUp
    mod.LeanError = _FakeLeanError
    mod.Dojo = object
    mod.LeanGitRepo = object
    mod.Theorem = object

    class _Err(Exception):
        ...

    mod.DojoCrashError = _Err
    mod.DojoInitError = _Err
    mod.DojoHardTimeoutError = _Err
    sys.modules["lean_dojo"] = mod


_install_fake_lean_dojo()


@pytest.fixture
def fake_state():
    def _make(pp: str = "⊢ True"):
        return _FakeTacticState(pp)

    return _make


@pytest.fixture
def fake_proof_finished():
    return _FakeProofFinished()


@pytest.fixture
def fake_lean_error():
    return _FakeLeanError(error="bad tactic")
