from __future__ import annotations

import argparse
import logging
import sys
from pathlib import Path
from typing import Optional

from dotenv import load_dotenv

from hybrid_atp.config import Config


def _setup_logging(level: str) -> None:
    logging.basicConfig(
        level=getattr(logging, level.upper(), logging.INFO),
        format="%(asctime)s %(levelname)-7s %(name)s :: %(message)s",
    )


def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="hybrid-atp", description="Hybrid neuro-symbolic theorem prover")
    p.add_argument("--config", "-c", type=Path, help="Path to TOML or JSON config file")
    p.add_argument("--repo", help="Lean repo URL (overrides config)")
    p.add_argument("--commit", help="Lean repo commit hash (overrides config)")
    p.add_argument("--file", help="Lean file path inside the repo")
    p.add_argument("--theorem", help="Theorem name")
    p.add_argument("--strategy", choices=["dfs", "bfs", "best_first", "mcts"], help="Search strategy")
    p.add_argument("--max-depth", type=int)
    p.add_argument("--max-iterations", type=int)
    p.add_argument("--parallel", type=int)
    p.add_argument("--timeout", type=float, help="Wall-clock timeout in seconds")
    p.add_argument("--log-level", choices=["DEBUG", "INFO", "WARNING", "ERROR"])
    return p


def _apply_overrides(cfg: Config, args: argparse.Namespace) -> Config:
    if args.repo:
        cfg.theorem.repo_url = args.repo
    if args.commit:
        cfg.theorem.repo_commit = args.commit
    if args.file:
        cfg.theorem.file_path = args.file
    if args.theorem:
        cfg.theorem.theorem_name = args.theorem
    if args.strategy:
        cfg.search.strategy = args.strategy
    if args.max_depth is not None:
        cfg.search.max_depth = args.max_depth
    if args.max_iterations is not None:
        cfg.search.max_iterations = args.max_iterations
    if args.parallel is not None:
        cfg.search.parallel = args.parallel
    if args.timeout is not None:
        cfg.search.timeout_seconds = args.timeout
    if args.log_level:
        cfg.log_level = args.log_level
    return cfg


def run(cfg: Config) -> int:
    # Heavy imports deferred so `--help` and tests don't pull torch/lean_dojo.
    from lean_dojo import Dojo, LeanGitRepo, Theorem

    from llm_layer.models.lean_generator_model import LeanGenerator
    from llm_layer.models.reasoning_model import MathReasoner
    from search_layer.search import Search
    from search_layer.search_strats import make_strategy

    _setup_logging(cfg.log_level)
    log = logging.getLogger("hybrid_atp.cli")

    token = cfg.resolve_token()

    log.info("Constructing reasoner: %s", cfg.reasoner.model_id)
    reasoner = MathReasoner(
        api_token=token,
        model_id=cfg.reasoner.model_id,
        use_inference_endpoint=cfg.reasoner.use_inference_endpoint,
        endpoint_url=cfg.reasoner.endpoint_url,
    )

    log.info("Constructing generator: %s", cfg.generator.model_id)
    generator = LeanGenerator(
        api_token=token,
        model_id=cfg.generator.model_id,
        num_candidates=cfg.generator.num_candidates,
        num_beams=cfg.generator.num_beams,
    )

    log.info(
        "Tracing theorem %s in %s @ %s",
        cfg.theorem.theorem_name,
        cfg.theorem.file_path,
        cfg.theorem.repo_commit[:8],
    )
    repo = LeanGitRepo(cfg.theorem.repo_url, cfg.theorem.repo_commit)
    theorem = Theorem(repo, cfg.theorem.file_path, cfg.theorem.theorem_name)

    strategy = make_strategy(cfg.search.strategy)

    with Dojo(theorem) as (dojo, init_state):
        log.info("Initial state:\n%s", init_state.pp)
        search = Search(
            reasoner=reasoner,
            generator=generator,
            dojo=dojo,
            strategy=strategy,
            reasoner_every=cfg.search.reasoner_every,
        )
        result = search.search(
            init_state=init_state,
            max_depth=cfg.search.max_depth,
            max_iterations=cfg.search.max_iterations,
            parallel=cfg.search.parallel,
            timeout_seconds=cfg.search.timeout_seconds,
        )

    if cfg.metrics_path:
        search.dump_metrics(Path(cfg.metrics_path))
        log.info("Wrote metrics to %s", cfg.metrics_path)

    if result.success:
        proof_script = result.proof_script()
        log.info("✔ PROOF FOUND in %d iter / %.1fs", result.metrics.iterations, result.metrics.wall_seconds)
        log.info("Proof:\n%s", proof_script)
        if cfg.proof_path:
            Path(cfg.proof_path).parent.mkdir(parents=True, exist_ok=True)
            Path(cfg.proof_path).write_text(proof_script + "\n")
            log.info("Wrote proof to %s", cfg.proof_path)
        return 0

    log.warning("✘ No proof found")
    return 1


def main(argv: Optional[list[str]] = None) -> int:
    load_dotenv()
    args = _build_argparser().parse_args(argv)

    cfg = Config.from_file(args.config) if args.config else Config()
    cfg = _apply_overrides(cfg, args)
    return run(cfg)


if __name__ == "__main__":
    sys.exit(main())
