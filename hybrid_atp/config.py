from __future__ import annotations

import json
import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Optional

try:
    import tomllib  # type: ignore[attr-defined]
except ModuleNotFoundError:  # py < 3.11
    import tomli as tomllib  # type: ignore[no-redef]


@dataclass
class ReasonerConfig:
    model_id: str = "meta-llama/Meta-Llama-3-8B-Instruct"
    use_inference_endpoint: bool = False
    endpoint_url: Optional[str] = None


@dataclass
class GeneratorConfig:
    model_id: str = "kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small"
    num_candidates: int = 8
    num_beams: Optional[int] = None


@dataclass
class SearchConfig:
    strategy: str = "best_first"
    max_depth: int = 8
    max_iterations: int = 200
    parallel: int = 1
    timeout_seconds: Optional[float] = 600.0
    reasoner_every: int = 3


@dataclass
class TheoremConfig:
    repo_url: str = "https://github.com/leanprover-community/mathlib4"
    repo_commit: str = "4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84"
    file_path: str = "Mathlib/Data/Nat/Basic.lean"
    theorem_name: str = "Nat.add_comm"


@dataclass
class Config:
    hf_token: Optional[str] = None
    log_level: str = "INFO"
    metrics_path: Optional[str] = "outputs/metrics.json"
    proof_path: Optional[str] = "outputs/proof.lean"
    reasoner: ReasonerConfig = field(default_factory=ReasonerConfig)
    generator: GeneratorConfig = field(default_factory=GeneratorConfig)
    search: SearchConfig = field(default_factory=SearchConfig)
    theorem: TheoremConfig = field(default_factory=TheoremConfig)

    @classmethod
    def from_file(cls, path: Path) -> "Config":
        path = Path(path)
        raw: Dict[str, Any]
        if path.suffix.lower() in (".toml",):
            with path.open("rb") as f:
                raw = tomllib.load(f)
        elif path.suffix.lower() in (".json",):
            raw = json.loads(path.read_text())
        else:
            raise ValueError(f"unsupported config format: {path.suffix}")
        return cls.from_dict(raw)

    @classmethod
    def from_dict(cls, raw: Dict[str, Any]) -> "Config":
        cfg = cls()
        cfg.hf_token = raw.get("hf_token", cfg.hf_token)
        cfg.log_level = raw.get("log_level", cfg.log_level)
        cfg.metrics_path = raw.get("metrics_path", cfg.metrics_path)
        cfg.proof_path = raw.get("proof_path", cfg.proof_path)
        for section, dc in (
            ("reasoner", ReasonerConfig),
            ("generator", GeneratorConfig),
            ("search", SearchConfig),
            ("theorem", TheoremConfig),
        ):
            if section in raw and isinstance(raw[section], dict):
                merged = {**dc().__dict__, **raw[section]}
                setattr(cfg, section, dc(**merged))
        return cfg

    def resolve_token(self) -> str:
        token = self.hf_token or os.getenv("HUGGINGFACE_TOKEN") or os.getenv("HF_TOKEN")
        if not token:
            raise RuntimeError(
                "HuggingFace token is required. Set HUGGINGFACE_TOKEN in the environment "
                "or add `hf_token = \"...\"` to your config file."
            )
        return token
