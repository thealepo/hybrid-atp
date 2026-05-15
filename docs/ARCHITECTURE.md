# Architecture

## Layers

### 1. LLM Layer (`llm_layer/`)

Two agents share a thin model wrapper (`models/wrapper.py`) that hides the
local-vs-remote distinction:

- **Local seq2seq path**: any model with `"t5"` in its id is loaded via
  `transformers.AutoModelForSeq2SeqLM`. Used for LeanDojo's
  `kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small`. `sample_local`
  exposes beam search and multi-return sampling so the generator can
  produce a diverse candidate set.
- **HF Inference path**: chat-capable models (Llama, Mixtral, etc.) are called
  via `huggingface_hub.InferenceClient.chat_completion` or `text_generation`.

The two agents:

- **`MathReasoner`** emits `SearchConstraints` as JSON. The prompt includes a
  one-shot example to anchor the schema. The class also encodes simple
  syntactic priors (the `_detect_goal_type` heuristic and a per-type tactic
  hint table) so the reasoner gets a usable answer even when JSON parsing
  fails. Failures from previous attempts are folded into the prompt to
  encourage diversification.
- **`LeanGenerator`** produces ranked `TacticCandidate`s. For seq2seq models
  it samples N completions and dedupes; for chat models it asks for a JSON
  array and parses with `extract_json` + a regex fixup for malformed object
  separators.

### 2. Search Layer (`search_layer/`)

`Search` drives the generator/validator loop. Key invariants:

- A single `threading.Lock` serializes access to `Dojo.run_tac`. LeanDojo is
  NOT thread-safe; the `parallel` knob enables a thread pool that lets us
  validate multiple candidates from the same parent *while* the LLM has
  already returned them, but they still execute serially in the Dojo. (To
  get real parallelism you'd shard across multiple `Dojo` instances — a
  reasonable next step.)
- The reasoner is rate-limited via `reasoner_every` because constraint
  generation dominates wall time when calling a remote 8B model.
- All four `SearchStrategy` implementations share the same interface:
  `add_state(state, path, depth, score)` / `get_next_state()` / `has_next()`.
  This lets `Search` swap strategies without behavioral changes.
- After each successful validation `Search.add_state` passes
  `score = candidate.priority − 0.05 * (depth + 1)`. For `BestFirst` this is
  literal priority; for `MCTS` it becomes the node's prior in UCT scoring.
- `SearchResult` is a dataclass with the proof path and metrics, dumped to
  `outputs/metrics.json` for analysis.

### 3. Validation Layer (`validation_layer/`)

`validate_tactic` calls `dojo.run_tac` and classifies the response into one
of five `ValidationResult`s. Crashes and timeouts are first-class signals
rather than uncaught exceptions, so the search loop can distinguish "this
tactic is wrong" from "the underlying Lean process died".

`DojoValidator` wraps the function with an internal lock; `Search` uses
`validate_tactic` directly under its own lock, but `DojoValidator` is the
recommended path for code that doesn't already own one.

## Data flow

```
TacticState  ──tactic_state_to_goal_state──▶  LeanGoalState
LeanGoalState + failures  ──MathReasoner──▶   SearchConstraints
LeanGoalState + constraints  ──LeanGenerator──▶  [TacticCandidate]
TacticCandidate + Dojo  ──validate_tactic──▶  ValidationResponse
ValidationResponse  ──{VALID, PROOF_FINISHED, ...}──▶  frontier update
```

## What's intentionally NOT here

- No retraining or fine-tuning loop. The reasoner and generator are queried
  in inference mode.
- No learned premise retriever — the constraint's `relevant_lemmas` field is
  the LLM's guess, not a top-k from a retrieval index.
- No theorem natural-language frontend. Theorems must already exist in a Lean
  file that LeanDojo can trace.

These are good places to extend the prototype.
