"""Tests for full_traces.py. Run with `python3 -m pytest test_full_traces.py`."""

from __future__ import annotations

import json
from pathlib import Path

from full_traces import domain_args, inputs_only, label, triage_one, used_values


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


def run(alarm: str | None, checks: list[str], recording: list[str] | None = None) -> dict:
    search = {"violated": f"PB_{alarm}"} if alarm else {"violated": None}
    return {"search": search, "build": {"checks": checks}, "recording_violations": recording or []}


def test_triage_sorts_alarms() -> None:
    assert triage_one("V01", "r", run("X", ["X"], ["X"]), None) == "already broken by the recording"
    assert triage_one("V01", "r", run("X", ["X"]), None) == "no previous version to compare"
    assert triage_one("V02", "r", run("X", ["X"]), run("X", ["X"])) == "also found on the previous version"
    assert triage_one("V02", "r", run("X", ["X"]), run(None, ["X"])) == "new in this version"
    assert triage_one("V03", "r", run("RevisedX", ["RevisedX"]), run(None, ["X"])) == (
        "property not in the previous version"
    )


def test_labels_follow_qians_verdicts() -> None:
    remove = 'requests[5].changes: [] -> [{"kind": "Remove", "target": 1}]\nrequests[5].transition: "Legacy" -> "Auto"'
    empty = 'requests[5].transition: "Legacy" -> "Auto"'
    assert label("V01", "node-lifecycle", "NoUnexpectedFatal", remove) == "noise"
    assert label("V01", "node-lifecycle", "NoUnexpectedFatal", empty) == "real, not from the update"
    assert (
        label("V03", "node-lifecycle", "NoUnexpectedFatal", 'requests[2].transition: "Legacy" -> "JointImplicit"')
        == "not reviewed"
    )
    assert (
        label("V02", "outgoing-snapshot-restore", "RevisedCampaignDecisionEligibility") == "real, not from the update"
    )
    assert label("V02", "ready-intervening-output", "NoUnexpectedFatal", empty) == "real, not from the update"
    assert label("V03", "ready-intervening-output", "NoUnexpectedFatal", empty) == "noise"
    assert label("V01", "joint-explicit", "CampaignDecisionEligibility") == "real, from the update"
    assert label("V02", "joint-explicit", "CampaignDecisionEligibility") == "real, not from the update"
    assert label("V02", "learner-vote", "SomethingElse") == "not reviewed"
