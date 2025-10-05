# Hybrid Neuro-Symbolic Theorem Prover

Our proposed project aims to design and implement a hybrid system, combining the interpretive capabilities of large language models (LLMs) with the established rigor of symbolic proof assistants (Lean, Coq), to solve mathematical theorems. This system will interpret problems, identify proof strategies, and decompose them into subgoals using chain-of-thought reasoning. Each candidate proof step will be validated symbolically. We are interested in how adaptive reasoning techniques can guide proof search and strategy selection. 

## Running locally with Ollama (Qwen2.5)
1. install Ollama and start it
2. pull a model:
   - `ollama pull qwen2.5:7b-instruct`
3. create venv and install deps:
   - `python -m venv venv`
   - `./venv/Scripts/Activate.ps1`
   - `pip install -r requirements.txt`
4. run examples:
   - `python -m llm_layer.examples.test_reasoner`
   - `python -m llm_layer.examples.test_translator`
- ensure Ollama is running at `http://localhost:11434`.
