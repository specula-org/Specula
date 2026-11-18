"""Tests for full_traces.py. Run with `python3 -m pytest test_full_traces.py`."""

from __future__ import annotations

import json
from pathlib import Path

from full_traces import domain_args, inputs_only, used_values


def atom(value: object) -> dict:
    return {"tag": "atom", "value": value}


def test_inputs_only_keeps_init_and_drops_later_post_states(tmp_path: Path) -> None:
    source = tmp_path / "run.ndjson"
    events = [
        {"event": "Init", "post": {"tag": "record", "value": {}}, "tag": "trace"},
        {"event": "Ready", "params": atom(1), "post": {"tag": "record", "value": {"x": atom(2)}}, "tag": "trace"},
    ]
    source.write_text("\n".join(json.dumps(e) for e in events) + "\n")
    inputs_only(source, tmp_path / "out.ndjson")
    lines = [json.loads(line) for line in (tmp_path / "out.ndjson").read_text().splitlines()]
    assert lines[0]["post"] == {"tag": "record", "value": {}}
    assert lines[1]["post"] == atom(0)


def test_used_values_include_nested_entries_and_the_limits(tmp_path: Path) -> None:
    entry = {"tag": "record", "value": {"id": atom(0), "weight": atom(0), "encoded": atom(10)}}
    message = {"tag": "record", "value": {"entries": {"tag": "seq", "value": [entry]}}}
    events = [
        {"event": "InvokeV2", "params": {"tag": "record", "value": {"id": atom(7), "weight": atom(24)}}},
        {"event": "Receive", "params": {"tag": "record", "value": {"message": message}}},
    ]
    trace = tmp_path / "run.ndjson"
    trace.write_text("\n".join(json.dumps(e) for e in events) + "\n")
    values = used_values(trace)
    assert values == {"RequestId": {1, 2, 3, 7}, "PayloadWeights": {0, 1, 24}, "EncodedWeights": {1, 2, 10}}
    assert domain_args({"RequestId": {3, 1}}) == ["--domain", "RequestId={1, 3}"]
