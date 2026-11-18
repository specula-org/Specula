"""Tests for choose.py. Run with `python3 -m pytest test_choose.py`."""

from __future__ import annotations

from pathlib import Path

from choose import base_actions, rank


def test_wrapped_actions_map_to_the_base_action_they_call(tmp_path: Path) -> None:
    (tmp_path / "MC.tla").write_text(
        "MCCampaign(n) == /\\ Budget(1) /\\ Original!Campaign(n) /\\ Spend(1)\n"
        "MCTransfer(n, p) == Original!TransferLeader(n, p)\n"
    )
    probes = [{"index": 1, "label": "MCCampaign"}, {"index": 2, "label": "MCTransfer"}, {"index": 3, "label": "Ready"}]
    assert base_actions(tmp_path, probes) == {1: "Campaign", 2: "TransferLeader"}


def step(open_: set[int]) -> dict:
    return {"event": "Ready", "enabled": set(open_), "taken": set(), "open": set(open_)}


def test_rank_prefers_points_whose_untried_alternatives_are_rare() -> None:
    common = {"steps": {p: step({1}) for p in range(10)}}
    rare = {"steps": {0: step({1}), 5: step({1, 2}), 6: step({1})}}
    rank([common, rare], top=1)
    assert rare["points"] == [5]
    assert common["points"] == [0]
    assert rare["score"] > common["score"]
