"""Search layer. `Search` is imported lazily because it pulls in the LLM stack."""

__all__ = ["Search", "SearchMetrics", "SearchResult"]


def __getattr__(name):
    if name in __all__:
        from .search import Search, SearchMetrics, SearchResult

        return {"Search": Search, "SearchMetrics": SearchMetrics, "SearchResult": SearchResult}[name]
    raise AttributeError(f"module 'search_layer' has no attribute {name!r}")
