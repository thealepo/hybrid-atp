from llm_layer.utils.json_parser import extract_json


def test_extract_plain_json():
    raw = '{"a": 1, "b": 2}'
    assert extract_json(raw) == '{"a": 1, "b": 2}'


def test_extract_fenced_json():
    raw = "```json\n{\"a\": 1}\n```"
    assert extract_json(raw) == '{"a": 1}'


def test_extract_with_leading_prose():
    raw = "Sure, here is the result:\n{\"a\": [1,2]}\nThanks."
    assert extract_json(raw) == '{"a": [1,2]}'


def test_extract_none_when_no_json():
    assert extract_json("nothing here") is None
