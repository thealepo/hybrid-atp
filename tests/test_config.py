import json

from hybrid_atp.config import Config


def test_default_config_has_sensible_defaults():
    cfg = Config()
    assert cfg.search.strategy == "best_first"
    assert cfg.theorem.theorem_name == "Nat.add_comm"
    assert cfg.generator.num_candidates > 0


def test_from_dict_partial_overrides():
    raw = {
        "log_level": "DEBUG",
        "search": {"strategy": "dfs" , "max_depth": 99},
        "theorem": {"theorem_name": "my_thm"},
    }
    cfg = Config.from_dict(raw)
    assert cfg.log_level == "DEBUG"
    assert cfg.search.strategy == "dfs"
    assert cfg.search.max_depth == 99
    # other search fields keep their defaults
    assert cfg.search.parallel == 1
    assert cfg.theorem.theorem_name == "my_thm"


def test_from_file_json(tmp_path):
    p = tmp_path / "c.json"
    p.write_text(json.dumps({"search": {"max_iterations": 7}}))
    cfg = Config.from_file(p)
    assert cfg.search.max_iterations == 7
