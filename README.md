# Hybrid Neuro-Symbolic Theorem Prover

A hybrid system combining the interpretive capabilities of large language models (LLMs) with the established rigor of symbolic proof assistants to solve mathematical theorems, specifically optimized for **Linear Algebra**.

## 🎯 Project Overview

This system uses **Google's Gemini API** with **Chain-of-Thought (CoT) reasoning** to:

- **Interpret** Linear Algebra mathematical proofs and problems
- **Extract** mathematical questions and structure from natural language
- **Reason** step-by-step through complex proofs
- **Suggest** the next best tactics for proof search
- **Guide** theorem proving strategy selection

## 🚀 Key Features

### 🧠 Gemini-Powered CoT Reasoning
- Advanced mathematical understanding using Gemini 1.5 Pro
- Step-by-step Chain-of-Thought analysis
- Problem decomposition and strategy identification

### 📖 Linear Algebra Specialization
- Specialized for vector spaces, linear transformations, matrices
- Recognizes eigenvalues, span, basis, dimension concepts
- Understands proof patterns common in Linear Algebra

### 🎯 Intelligent Tactic Suggestion
- Suggests next proof steps based on current context
- Lean theorem prover syntax generation
- Confidence scoring for each suggestion

### 🔍 Mathematical Proof Parsing
- Extracts mathematical objects and concepts
- Identifies proof structure and type
- Analyzes proof completeness

## 📦 Installation

### Prerequisites
- Python 3.11+
- Google AI API key (Gemini)

### Quick Setup

1. **Clone the repository:**
```bash
git clone <repository-url>
cd hybrid-atp
```

2. **Run the automated setup:**
```bash
python setup_and_test.py
```

This will:
- Install all dependencies
- Set up environment configuration
- Test basic functionality
- Test API connection (if key is provided)

### Manual Setup

1. **Install dependencies:**
```bash
pip install -r requirements.txt
```

2. **Set up environment:**
```bash
# Copy the example environment file
cp .env.example .env

# Edit .env and add your Gemini API key
GEMINI_API_KEY=your_actual_api_key_here
```

3. **Get a Gemini API key:**
   - Visit [Google AI Studio](https://makersuite.google.com/app/apikey)
   - Create a new API key
   - Add it to your `.env` file

## 🎮 Usage

### Quick Example

```python
from llm_layer import GeminiMathReasoner, LinearAlgebraProofParser, LinearAlgebraTacticEngine
from llm_layer.model import MathDomain

# Initialize the system
reasoner = GeminiMathReasoner()
parser = LinearAlgebraProofParser()
tactic_engine = LinearAlgebraTacticEngine(reasoner)

# Analyze a Linear Algebra proof
proof_text = """
Theorem: Let V be a vector space and let S = {v₁, v₂, ..., vₙ} be a linearly independent set.
Then S can be extended to a basis of V.
"""

# Get Chain-of-Thought analysis
analysis = reasoner.analyze_proof(proof_text, MathDomain.LINEAR_ALGEBRA)
print(f"Problem Understanding: {analysis.problem_understanding}")
print(f"Suggested Strategy: {analysis.proof_strategy}")

# Get tactic suggestions
current_goal = "Show that S ∪ {w} is linearly independent"
suggestions = tactic_engine.suggest_tactics(proof_text, current_goal)

for suggestion in suggestions:
    print(f"Tactic: {suggestion.tactic_name}")
    print(f"Confidence: {suggestion.confidence:.2f}")
    print(f"Reasoning: {suggestion.reasoning}")
```

### Interactive Demo

Run the interactive example:
```bash
python example_usage.py
```

This demonstrates:
- ✅ Proof analysis and CoT reasoning
- ✅ Mathematical question extraction
- ✅ Proof structure parsing
- ✅ Tactic suggestion system
- ✅ Interactive proof exploration

## 🏗️ System Architecture

```
Input: Linear Algebra Proof Text
              ↓
    ┌─────────────────────────┐
    │   Proof Parser          │ ← Extracts mathematical structure
    │   - Mathematical objects│
    │   - Concepts & keywords │
    │   - Proof type & steps  │
    └─────────────────────────┘
              ↓
    ┌─────────────────────────┐
    │   Gemini CoT Reasoner   │ ← Chain-of-Thought analysis
    │   - Problem understanding│
    │   - Strategy identification│
    │   - Step-by-step reasoning│
    └─────────────────────────┘
              ↓
    ┌─────────────────────────┐
    │   Tactic Engine         │ ← Suggests next proof steps
    │   - Pattern matching    │
    │   - LLM-based suggestions│
    │   - Theorem applications │
    └─────────────────────────┘
              ↓
    Output: Tactic Suggestions + Reasoning
```

## 📚 Core Components

### `GeminiMathReasoner`
- Main interface to Gemini API
- Specialized prompts for Linear Algebra
- Chain-of-Thought analysis pipeline

### `LinearAlgebraProofParser`
- Extracts mathematical entities and concepts
- Identifies proof structure and completeness
- Specialized for Linear Algebra terminology

### `LinearAlgebraTacticEngine`  
- Suggests proof tactics with confidence scores
- Pattern-based and LLM-based suggestions
- Generates Lean theorem prover syntax

## 🔧 Configuration

### Environment Variables

```bash
# Required
GEMINI_API_KEY=your_gemini_api_key

# Optional
GEMINI_MODEL=gemini-1.5-pro  # Default model
```

### Supported Mathematical Domains

Currently optimized for:
- ✅ **Linear Algebra** (vector spaces, linear transformations, matrices)
- 🔄 Abstract Algebra (planned)
- 🔄 Real Analysis (planned)
- 🔄 Topology (planned)

## 🎯 Example Use Cases

### 1. Proof Analysis
Analyze complex Linear Algebra proofs and understand their structure:
```python
analysis = reasoner.analyze_proof(proof_text, MathDomain.LINEAR_ALGEBRA)
```

### 2. Question Extraction
Extract the main mathematical question from natural language:
```python
main_question, sub_questions = reasoner.extract_mathematical_question(problem_text)
```

### 3. Tactic Suggestion
Get intelligent suggestions for the next proof step:
```python
suggestions = tactic_engine.suggest_tactics(proof_context, current_goal)
```

### 4. Proof Planning
Generate a high-level proof strategy:
```python
proof_plan = tactic_engine.generate_proof_plan(problem_statement)
```

## 🤝 Contributing

We welcome contributions! Areas of particular interest:

- 🔧 Additional mathematical domain support
- 🎯 Improved tactic suggestion algorithms  
- 🔗 Integration with formal proof assistants (Lean, Coq)
- 📊 Evaluation metrics and benchmarks

## 📄 License

[Add your license information here]

## 🙏 Acknowledgments

- Google AI for the Gemini API
- The Lean theorem prover community
- Linear Algebra educational resources
