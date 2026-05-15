from llm_layer.data_structures.base import TacticCandidate
from search_layer.search_strats import BFS, DFS, BestFirst, make_strategy


def _cand(code: str) -> TacticCandidate:
    return TacticCandidate(
        tactic_code=code,
        tactic_type=code.split()[0] if code else "x",
        justification="",
        priority=1.0,
        expected_subgoals=[],
    )


def test_dfs_is_lifo(fake_state):
    s = DFS()
    a , b , c = fake_state("a") , fake_state("b") , fake_state("c")
    s.add_state(a,[],0)
    s.add_state(b,[],1)
    s.add_state(c,[],2)
    assert s.get_next_state()[0].pp == "c"
    assert s.get_next_state()[0].pp == "b"
    assert s.get_next_state()[0].pp == "a"
    assert not s.has_next()


def test_bfs_is_fifo(fake_state):
    s = BFS()
    for pp in ("a","b","c"):
        s.add_state(fake_state(pp),[],0)
    order = [s.get_next_state()[0].pp for _ in range(3)]
    assert order == ["a", "b", "c"]


def test_best_first_pops_highest_score(fake_state):
    s = BestFirst()
    s.add_state(fake_state("low") , [] , 0 , score=0.1)
    s.add_state(fake_state("high") , [] , 0 , score=5.0)
    s.add_state(fake_state("mid") , [] , 0 , score=1.0)
    assert s.get_next_state()[0].pp == "high"
    assert s.get_next_state()[0].pp == "mid"
    assert s.get_next_state()[0].pp == "low"


def test_make_strategy_unknown_raises():
    import pytest

    with pytest.raises(ValueError):
        make_strategy("nope")
