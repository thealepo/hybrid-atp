__all__ = ["MathReasoner" , "LeanGenerator"]


def __getattr__(name):
    if name == "MathReasoner":
        from .reasoning_model import MathReasoner

        return MathReasoner
    if name == "LeanGenerator":
        from .lean_generator_model import LeanGenerator

        return LeanGenerator
    raise AttributeError(f"module 'llm_layer.models' has no attribute {name!r}")
