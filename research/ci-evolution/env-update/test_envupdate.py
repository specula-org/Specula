"""Tests for envupdate.py. Run with `python3 -m pytest test_envupdate.py`."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from envupdate import ROOT, actions, named_parts, normal, shapes, view_fields, view_text, wrappers

DEFINITIONS = {
    "Reactive": "\n    \\/ \\E n \\in S: A(n) \\/ B(n)\n    \\/ \\E m \\in M, t \\in T: C(m, t)",
    "Next": "\n    \\/ /\\ Reactive /\\ UNCHANGED f\n    \\/ \\E n \\in S: MCX(n) \\/ (\\E k \\in 1..2: MCY(n, k))",
    "OneLine": " \\E n \\in S: Framed(A(n)) \\/ Framed(B(n))",
}


def test_actions_split_quantifiers_and_definitions() -> None:
    assert actions(DEFINITIONS["Next"], DEFINITIONS) == [
        "\\E n \\in S: A(n) /\\ UNCHANGED f",
        "\\E n \\in S: B(n) /\\ UNCHANGED f",
        "\\E m \\in M, t \\in T: C(m, t) /\\ UNCHANGED f",
        "\\E n \\in S: MCX(n)",
        "\\E n \\in S: \\E k \\in 1..2: MCY(n, k)",
    ]
    assert actions("\n    \\/ OneLine", DEFINITIONS) == ["\\E n \\in S: Framed(A(n))", "\\E n \\in S: Framed(B(n))"]


def test_actions_distribute_a_guard_over_a_bulleted_disjunction() -> None:
    body = "\n    /\\ Len(q) <= 3\n    /\\ \\/ \\E i \\in S : A(i)\n       \\/ \\E m \\in q : B(m)\n"
    assert actions(body, {}) == [
        "(Len(q) <= 3) /\\ (\\E i \\in S: A(i))",
        "(Len(q) <= 3) /\\ (\\E m \\in q: B(m))",
    ]


def test_wrappers_make_framed_actions_equal() -> None:
    macros = wrappers("Framed(a) == a /\\ UNCHANGED f\nOther == 1\n")
    assert macros == {"Framed": ("a", "a /\\ UNCHANGED f")}
    assert normal("\\E n \\in S: Framed(Original!A(n))", macros) == normal("\\E n\\in S:A(n) /\\ UNCHANGED f", macros)


def test_named_parts_decide_focus() -> None:
    parts = ["\\E n \\in S: A(n) /\\ UNCHANGED f", "\\E n \\in S: B(n) /\\ UNCHANGED f", "\\E n \\in S: MCX(n)"]
    focused = ["\\E n \\in S: Framed(A(n))", "\\E n \\in S: n = 1 /\\ Framed(B(n))"]
    lines = named_parts(parts, focused, {"Framed": ("a", "a /\\ UNCHANGED f")})
    assert "EnvPart1 ==\n    (\\E n \\in S: A(n) /\\ UNCHANGED f) /\\ envAct' = 1" in lines
    assert "EnvFocus1 ==\n    TRUE" in lines
    assert "EnvFocus2 ==\n    (\\E n \\in S: n = 1 /\\ Framed(B(n)))" in lines
    assert "EnvFocus3 ==\n    FALSE" in lines


def test_shapes_and_view_fields() -> None:
    state = {
        "raft": {"s1": {"term": 1, "log": []}, "s2": {"term": 1, "log": []}},
        "history": {"acks": [], "campaigns": []},
        "quality": {"votes": [], "campaigns": []},
        "wire": [],
    }
    shape, servers = shapes(state)
    assert servers == ["s1", "s2"]
    assert shape == {
        "raft": ("node", ["log", "term"]),
        "history": ("record", ["acks", "campaigns"]),
        "quality": ("record", ["campaigns", "votes"]),
        "wire": ("whole", []),
    }
    definitions = {"P": "\\A n \\in S: raft[n].term >= 0 /\\ Q(history) /\\ quality.votes = <<>>", "Q(h)": ""}
    definitions["Q"] = "h.campaigns = {}"
    text = view_text(definitions, ["P"])
    assert view_fields(text, shape) == ["history.campaigns", "quality.votes", "raft.term"]


SPEC = {
    "base.tla": """---- MODULE base ----
EXTENDS Naturals
VARIABLES x, y, z
vars == <<x, y, z>>
Init == x = 0 /\\ y = 0 /\\ z = 0
Inc == x < 3 /\\ x' = x + 1 /\\ UNCHANGED <<y, z>>
Copy == y' = x /\\ UNCHANGED <<x, z>>
Noise == z' = 1 - z /\\ UNCHANGED <<x, y>>
Bump == y < 5 /\\ y' = y + 1 /\\ UNCHANGED <<x, z>>
====
""",
    "MC.tla": """---- MODULE MC ----
EXTENDS base
MCNext ==
    \\/ Inc
    \\/ Copy
    \\/ Noise
    \\/ Bump
====
""",
    "Update.tla": """---- MODULE Update ----
EXTENDS MC
ConcreteUpdateNext ==
    \\/ Inc
    \\/ Copy
FullUpdateNext == MCNext
FullUpdateSpec == Init /\\ [][FullUpdateNext]_vars
ConcreteUpdateSpec == Init /\\ [][ConcreteUpdateNext]_vars
UpdateCopyBound == y <= x
====
""",
    "Update_full.cfg": "SPECIFICATION FullUpdateSpec\nCHECK_DEADLOCK FALSE\n",
    "Update_focused.cfg": "SPECIFICATION ConcreteUpdateSpec\nINVARIANT UpdateCopyBound\n",
}


@pytest.mark.skipif(shutil.which("java") is None or not (ROOT / "lib/tla2tools.jar").exists(), reason="needs TLC")
def test_end_to_end(tmp_path: Path) -> None:
    spec = tmp_path / "spec"
    spec.mkdir()
    for name, text in SPEC.items():
        (spec / name).write_text(text)
    out = tmp_path / "out"
    tool = Path(__file__).resolve().parent / "envupdate.py"
    command = [sys.executable, str(tool), str(spec), "--out", str(out), "--depth", "20"]
    subprocess.run(command + ["--seconds", "10", "--check-seconds", "10", "--heap", "1g"], check=True)
    result = json.loads((out / "result.json").read_text())
    rows = {row["label"]: row for row in result["parts"]}
    assert result["view"] == ["x", "y"]
    assert not rows["Inc"]["outside_focused"] and rows["Inc"]["in_focused_model"]
    assert rows["Noise"]["outside_focused"] and rows["Noise"]["changes_view"] == []
    assert rows["Bump"]["changes_view"] == ["y"]
    assert result["env_update_keeps"] == ["x"]
    assert result["discharge_check"]["violated"] is None
    assert "x' = x" in (out / "EnvUpdate.tla").read_text()
