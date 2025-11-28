# Hybrid ATP - Proof Strategy Generator

This simplified version generates proof strategies for mathematical theorems using LLMs, **without validation**. It provides both a CLI and a web interface.

## What Changed

- **Removed**: Validation layer (no Lean execution or proof checking)
- **Added**: Simple strategy generator that analyzes theorems and suggests proof approaches
- **Added**: Flask web interface for easy interaction
- **Simplified**: Focus is purely on strategy generation, not proof validation

## Setup

1. Install dependencies:
```bash
pip install -r requirements.txt
```

2. Configure your environment:
   - Copy `.env.example` to `.env`
   - Add your HuggingFace token to `.env`:
     ```
     HUGGINGFACE_TOKEN=your_token_here
     ```

## Usage

### Option 1: Web Interface (Recommended)

Run the Flask web app:
```bash
python app.py
```

Then open your browser to: http://127.0.0.1:5000

The web interface allows you to:
- Enter any theorem statement
- Provide optional context
- Get AI-generated proof strategies
- See suggested tactics, lemmas, and reasoning

### Option 2: Command Line

Run the CLI demo:
```bash
python main.py
```

This runs a hardcoded example and prints the strategy as JSON.

## What You Get

For each theorem, the system generates:

1. **Analysis**:
   - Goal type classification (equality, implication, etc.)
   - Confidence score
   - Strategic reasoning
   - Expected proof depth

2. **Strategy**:
   - Primary tactics to try
   - Relevant Mathlib lemmas
   - Tactics to avoid
   - Weighted tactic priorities
   - Alternative approaches

3. **Suggested Tactics**:
   - Concrete Lean 4 tactic code
   - Justification for each tactic
   - Priority ranking

## Example

**Input Theorem:**
```lean
⊢ ∀ (n : ℕ), n + 0 = n
```

**Output Includes:**
- Goal Type: "universal equality"
- Primary Tactics: ["intro", "simp", "rfl"]
- Relevant Lemmas: ["add_zero"]
- Reasoning: "Universal quantifier requires intro first. Then add_zero simplifies directly..."
- Generated Tactics: `intro n`, `simp [add_zero]`, etc.

## Notes

- This version does **NOT** validate tactics in Lean
- Strategies are purely LLM-generated suggestions
- No proof search or validation occurs
- Perfect for strategy exploration and learning
