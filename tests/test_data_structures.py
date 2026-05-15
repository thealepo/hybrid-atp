from llm_layer.data_structures.base import LeanGoalState, SearchConstraints


def test_goal_state_prompt_includes_goal_and_hypotheses():
    gs = LeanGoalState(goal="⊢ n + 0 = n" , hypothesis={"n": "ℕ"})
    formatted = gs.to_prompt_format()
    assert "⊢ n + 0 = n" in formatted
    assert "n:ℕ" in formatted


def test_weighted_tactics_sorted_descending():
    sc = SearchConstraints(
        primary_tactic_types=["apply"],
        relevant_lemmas=[],
        avoid_tactics=[],
        expected_depth=3,
        confidence=0.9,
        tactic_weights={"apply": 2.5 , "rw": 1.0 , "simp": 1.8},
        reasoning="",
    )
    weights = sc.get_weighted_tactics()
    assert [t for t, _ in weights] == ["apply" , "simp" , "rw"]


def test_should_explore_alternatives_threshold():
    base = dict(
        primary_tactic_types=[],
        relevant_lemmas=[],
        avoid_tactics=[],
        expected_depth=1,
        tactic_weights={},
        reasoning="",
    )
    assert SearchConstraints(confidence=0.5 , **base).should_explore_alternatives() is True
    assert SearchConstraints(confidence=0.95 , **base).should_explore_alternatives() is False
