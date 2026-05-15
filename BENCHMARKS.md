# Benchmark ideas

Concrete experiments that would turn this prototype into a meaningful
research artifact.

## Baselines to compare against

- **LLM-only**: same generator model, no validation loop. Measures how much
  the search/validator buys us.
- **Validator-only**: random or `simp_all` tactics with no LLM guidance.
  Measures how much the LLM buys us.
- **Existing ATPs**: LeanDojo's [ReProver](https://github.com/lean-dojo/ReProver),
  [LeanCoPilot](https://github.com/lean-dojo/LeanCopilot), or
  [DeepSeek-Prover](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5).

## Ablations within the system

- Strategy comparison: DFS vs BFS vs best-first vs MCTS, holding everything
  else constant.
- Reasoner on vs off: does `MathReasoner`'s constraint generation improve
  success rate, or is the generator already strong enough alone?
- Failure-memory window size (`failures[-5:]` today): 0 / 3 / 5 / 10.
- Number of candidates per expansion: 1 / 4 / 8 / 16.

## Datasets

- **MiniF2F-Lean4** for olympiad-style problems.
- A subset of **Mathlib4** theorems by file (basic arithmetic, group theory,
  topology) to study domain-specific behavior.

## Metrics

- Pass rate within `max_iterations`.
- Wall-clock time to proof.
- Mean proof depth on success.
- Dojo crashes per 1000 tactics.
- LLM cost per successful proof (HF Inference billing or local FLOPs).
