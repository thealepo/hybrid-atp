# Hybrid Neuro-Symbolic Theorem Prover

![Status](https://img.shields.io/badge/status-research%20prototype-orange)
![Python](https://img.shields.io/badge/python-3.10%2B-blue)
![Lean](https://img.shields.io/badge/lean-4-green)
![License](https://img.shields.io/badge/license-MIT-lightgrey)

A research prototype that proves Lean 4 theorems by pairing an LLM "strategist"
with an LLM "tactician" and verifying every step in a real Lean kernel via
[LeanDojo](https://github.com/lean-dojo/LeanDojo).

```
   ┌──────────────┐    constraints     ┌──────────────┐    tactic   ┌──────────────┐
   │ MathReasoner │  ───────────────▶  │ LeanGenerator │  ────────▶ │  LeanDojo /  │
   │     (LLM)    │                    │     (LLM)     │            │   Lean 4     │
   └──────▲───────┘                    └───────────────┘            └──────┬───────┘
          │                                                                │
          │      failure / next state ◀────── ValidationResponse ──────────┘
          │
   ┌──────┴───────┐
   │   Search     │   DFS / BFS / Best-first / MCTS frontier
   │  Controller  │
   └──────────────┘
```

## Pipeline at a glance

1. **Trace** a Lean theorem with LeanDojo to get an initial `TacticState`.
2. **Reason**: `MathReasoner` reads the proof state and emits `SearchConstraints`
   — recommended tactic types, relevant Mathlib lemmas, tactics to avoid, and
   per-tactic weights. JSON-structured for safety.
3. **Generate**: `LeanGenerator` (a ByT5 retriever-tacgen for `t5*` models,
   or a chat LLM via HF Inference) proposes a ranked list of `TacticCandidate`s.
4. **Validate**: each candidate is sent through `validate_tactic`, which calls
   `Dojo.run_tac` and classifies the response into
   `VALID | PROOF_FINISHED | INVALID | GIVEN_UP | CRASHED`.
5. **Update the frontier**: VALID children are added to the chosen `SearchStrategy`
   (DFS, BFS, best-first, or MCTS). Failures feed back into the next reasoner
   call to discourage repeated mistakes.
6. **Persist**: on success, the proof script is written to disk and a JSON
   metrics file records iteration count, validation outcomes, and wall time.

## Layout

```
hybrid_atp/                # CLI + config (top-level orchestration)
  cli.py
  config.py
llm_layer/
  data_structures/         # LeanGoalState, SearchConstraints, TacticCandidate, FailedTactic
  models/
    reasoning_model.py     # MathReasoner — constraint generation
    lean_generator_model.py# LeanGenerator — tactic candidates
    wrapper.py             # local seq2seq + HF Inference unified interface
  utils/                   # state_converter, json_parser
search_layer/
  search.py                # Search controller (parallel-safe Dojo, metrics)
  search_strats/
    dfs.py, bfs.py, best_first.py, mcts.py
validation_layer/
  validator.py             # LeanDojo classification + thread-safe DojoValidator
tests/                     # pytest unit tests (no LeanDojo / HF needed)
configs/example.toml       # starter config
```

## Install

```bash
git clone https://github.com/thealepo/hybrid-atp.git
cd hybrid-atp
conda create -n hybrid-atp python=3.11 -y
conda activate hybrid-atp
pip install -e ".[dev]"
cp .env.example .env       # add your HUGGINGFACE_TOKEN
```

LeanDojo additionally needs a working Lean 4 toolchain (`elan` / `lean`) and a
Mathlib trace. See the LeanDojo docs for cache setup.

## Run

```bash
# Use defaults (Nat.add_comm against Mathlib4):
hybrid-atp

# Pick a strategy, point at a theorem:
hybrid-atp --strategy mcts --theorem Nat.add_comm \
           --file Mathlib/Data/Nat/Basic.lean \
           --max-iterations 100 --timeout 300

# Or use a config file:
hybrid-atp --config configs/example.toml
```

Outputs land in `outputs/proof.lean` and `outputs/metrics.json`.

## Tests

```bash
pytest                    # unit tests, no LeanDojo / HF required
```

The test suite stubs `lean_dojo` and exercises parsers, data structures, all
four search strategies, validator classification, and config loading.

## What works, what doesn't yet

| Component                 | Status         | Notes                                                                 |
| ------------------------- | -------------- | --------------------------------------------------------------------- |
| LeanDojo validation       | ✅ working      | thread-safe via `DojoValidator`, classifies all 5 result types         |
| DFS / BFS / Best-first    | ✅ working      | pluggable via `--strategy`                                            |
| MCTS                      | ⚠ simplified   | UCT frontier with reward backprop; no learned value/policy network    |
| MathReasoner (Llama 3 8B) | ✅ working      | JSON-structured constraints with example-shot prompt                  |
| LeanGenerator (ByT5)      | ✅ working      | multi-candidate via beam search; local model                          |
| LeanGenerator (chat)      | ✅ working      | JSON array of candidates from HF Inference                            |
| FCM weight adaptation     | ❌ not built    | placeholder slot in `SearchConstraints.tactic_weights`                 |
| Premise selection         | ❌ not built    | reasoner suggests lemmas but no retrieval index                       |
| End-to-end benchmarks     | ❌ not built    | see [BENCHMARKS.md](BENCHMARKS.md) for proposed experiments            |

## License

MIT — see [LICENSE](LICENSE).
