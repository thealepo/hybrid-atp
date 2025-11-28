"""
Validates generated tactics by running them in Lean.
"""
import logging
from typing import List, Dict, Any, Optional
from validation_layer.validator import LeanDojoValidator, ValidationResult

logger = logging.getLogger("tactic_validator")
logger.setLevel(logging.INFO)


class TacticValidator:
    """Validates tactics by executing them in Lean."""

    def __init__(self, file_path: str, theorem_name: str):
        """
        Initialize the validator for a specific theorem.

        Args:
            file_path: Path to the Lean file (e.g., "Mathlib/Data/List/Basic.lean")
            theorem_name: Name of the theorem (e.g., "List.reverse_append")
        """
        self.validator = LeanDojoValidator(
            file_path=file_path,
            theorem_name=theorem_name
        )
        self.initial_state = None

    def initialize(self):
        """Initialize the Lean environment and get the initial proof state."""
        try:
            logger.info("Starting Lean environment initialization...")
            logger.info("This may take 2-5 minutes on first run (downloading Mathlib4)")
            logger.info("Subsequent runs will be much faster (uses cache)")

            self.initial_state = self.validator.get_initial_state()

            logger.info(f"Validator initialized successfully!")
            logger.info(f"Initial state: {self.initial_state.pp}")
            return True
        except Exception as e:
            logger.error(f"Failed to initialize validator: {e}")
            return False

    def validate_tactics(self, tactics: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        Validate a list of tactics by running them in Lean.

        Args:
            tactics: List of tactic dictionaries with 'tactic' and 'justification' fields

        Returns:
            List of tactics with validation results added
        """
        if not self.initial_state:
            if not self.initialize():
                return [{
                    **tactic,
                    'validated': False,
                    'validation_error': 'Failed to initialize Lean environment'
                } for tactic in tactics]

        validated_tactics = []
        current_state = self.initial_state

        for tactic in tactics:
            tactic_code = tactic.get('tactic', '')

            try:
                response = self.validator.validate(current_state, tactic_code)

                if response.result_type == ValidationResult.PROOF_FINISHED:
                    validated_tactics.append({
                        **tactic,
                        'validated': True,
                        'validation_status': 'proof_complete',
                        'validation_message': 'Proof finished!',
                        'next_state': None
                    })
                    break  # Proof is done

                elif response.result_type == ValidationResult.VALID:
                    validated_tactics.append({
                        **tactic,
                        'validated': True,
                        'validation_status': 'valid',
                        'validation_message': 'Tactic succeeded',
                        'next_state': response.next_state.pp if response.next_state else None
                    })
                    current_state = response.next_state  # Update state for next tactic

                else:  # INVALID
                    validated_tactics.append({
                        **tactic,
                        'validated': False,
                        'validation_status': 'invalid',
                        'validation_error': response.error or 'Tactic failed',
                        'next_state': None
                    })

            except Exception as e:
                validated_tactics.append({
                    **tactic,
                    'validated': False,
                    'validation_status': 'error',
                    'validation_error': str(e),
                    'next_state': None
                })

        return validated_tactics

    def close(self):
        """Clean up the Lean environment."""
        try:
            self.validator.close()
        except Exception as e:
            logger.warning(f"Error closing validator: {e}")


def validate_tactics_for_theorem(
    tactics: List[Dict[str, Any]],
    file_path: str,
    theorem_name: str
) -> List[Dict[str, Any]]:
    """
    Convenience function to validate tactics for a specific theorem.

    Args:
        tactics: List of tactic dictionaries
        file_path: Path to Lean file
        theorem_name: Name of theorem

    Returns:
        List of tactics with validation results
    """
    validator = TacticValidator(file_path, theorem_name)

    try:
        return validator.validate_tactics(tactics)
    finally:
        validator.close()
