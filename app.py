"""
Flask web application for generating proof strategies.
Run with: python app.py
"""
import os
import logging
from flask import Flask, render_template, request, jsonify
from dotenv import load_dotenv

from llm_layer.models.lean_generator_model import LeanGenerator
from llm_layer.models.reasoning_model import MathReasoner
from strategy_generator import StrategyGenerator

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Load environment
load_dotenv()
HF_TOKEN = os.getenv("HUGGINGFACE_TOKEN")

# Initialize Flask app
app = Flask(__name__)

# Initialize models (do this once at startup)
logger.info("Initializing models...")
try:
    reasoner = MathReasoner(api_token=HF_TOKEN)
    generator = LeanGenerator(
        api_token=HF_TOKEN,
        model_id="kaiyuy/leandojo-lean4-retriever-tacgen-byt5-small"
    )
    strategy_gen = StrategyGenerator(reasoner=reasoner, generator=generator)
    logger.info("Models initialized successfully")
except Exception as e:
    logger.error(f"Failed to initialize models: {e}")
    strategy_gen = None


@app.route('/')
def index():
    """Render the main page."""
    return render_template('index.html')


@app.route('/generate', methods=['POST'])
def generate_strategy():
    """API endpoint to generate proof strategy."""
    if strategy_gen is None:
        return jsonify({
            'error': 'Models not initialized. Check your HUGGINGFACE_TOKEN in .env'
        }), 500

    try:
        data = request.get_json()
        theorem = data.get('theorem', '')
        context = data.get('context', '')
        num_tactics = int(data.get('num_tactics', 3))
        validate = data.get('validate', False)
        lean_file = data.get('lean_file', '')
        theorem_name = data.get('theorem_name', '')

        if not theorem:
            return jsonify({'error': 'Theorem statement is required'}), 400

        logger.info(f"Generating strategy for: {theorem}")

        # Generate strategy
        result = strategy_gen.generate_strategy(
            theorem_statement=theorem,
            context=context if context else None,
            num_tactics=num_tactics
        )

        # Optionally validate tactics
        if validate and lean_file and theorem_name:
            logger.info("Validating tactics in Lean...")
            from tactic_validator import validate_tactics_for_theorem

            tactics_to_validate = [
                {'tactic': t['tactic'], 'justification': t['justification']}
                for t in result['suggested_tactics']
            ]

            try:
                validated = validate_tactics_for_theorem(
                    tactics=tactics_to_validate,
                    file_path=lean_file,
                    theorem_name=theorem_name
                )

                # Merge validation results back
                for i, tactic in enumerate(result['suggested_tactics']):
                    if i < len(validated):
                        tactic.update(validated[i])

                result['validation_enabled'] = True

            except Exception as e:
                logger.error(f"Validation error: {e}")
                result['validation_error'] = str(e)

        return jsonify(result)

    except Exception as e:
        logger.error(f"Error generating strategy: {e}")
        return jsonify({'error': str(e)}), 500


@app.route('/health')
def health():
    """Health check endpoint."""
    return jsonify({
        'status': 'ok',
        'models_loaded': strategy_gen is not None
    })


# For Vercel serverless deployment
# The app instance is automatically picked up by Vercel

if __name__ == '__main__':
    # This is only for local development
    app.run(debug=True, host='127.0.0.1', port=5000)
