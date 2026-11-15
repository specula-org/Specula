"""Tests for the text handling in check.py. Run with `python3 -m pytest research/ci-evolution/update-coverage`."""

from __future__ import annotations

from pathlib import Path

import check

UPDATE = r"""---- MODULE Update ----
EXTENDS MC

Framed(a) == a /\ UNCHANGED faultVars

\* comment between definitions
GroupA ==
    \/ \E n\in Server,id\in RequestId:
          MCInvokeV2(n,id)
    \/ \E n\in Server,t\in Timeouts:MCCampaign(n,t) \/ MCTick(n,t)

GroupB ==
    \E n\in Server:Framed(Original!Ready(n)) \/ Framed(Original!Advance(n))

GroupC ==
    \/ \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type="MsgSnap"
         /\ Framed(Original!Receive(m,t))

AffectedActions ==
    \/ GroupA
    \/ GroupB
    \/ GroupC
====
"""


def test_affected_actions_expand_named_groups_and_split_quantified_disjunctions(tmp_path: Path) -> None:
    update = tmp_path / "Update.tla"
    update.write_text(UPDATE)
    probes = check.affected_probes(update)
    assert [(p.index, p.group, p.label) for p in probes] == [
        (1, "GroupA", "MCInvokeV2"),
        (2, "GroupA", "MCCampaign"),
        (3, "GroupA", "MCTick"),
        (4, "GroupB", "Ready"),
        (5, "GroupB", "Advance"),
        (6, "GroupC", "Receive (some message types)"),
    ]
    assert probes[1].formula == r"\E n\in Server,t\in Timeouts:MCCampaign(n,t)"
    assert probes[5].formula.splitlines()[1].strip() == '/\\ m.type="MsgSnap"'


def test_split_quantified_keeps_conjunctions_and_brackets_whole() -> None:
    assert check.split_quantified(r"\E n\in S:A(n) /\ B(n) \/ C(n)") == [r"\E n\in S:A(n) /\ B(n) \/ C(n)"]
    assert check.split_quantified(r"\E n\in S:F(A(n) \/ B(n))") == [r"\E n\in S:F(A(n) \/ B(n))"]
    assert check.split_quantified(r"\E n\in S:x<=n \/ C(n)") == [r"\E n\in S:x<=n", r"\E n\in S:C(n)"]


def test_missing_affected_actions_is_an_error(tmp_path: Path) -> None:
    update = tmp_path / "Update.tla"
    update.write_text("---- MODULE Update ----\nOther == TRUE\n====\n")
    try:
        check.affected_probes(update)
    except SystemExit as error:
        assert "AffectedActions" in str(error)
    else:
        raise AssertionError("expected SystemExit")


def test_split_config_drops_checks_comments_and_deadlock_but_keeps_constraints() -> None:
    checks, body = check.split_config(
        "SPECIFICATION Spec\n"
        'CONSTANTS\n    WorkloadKinds = {"V2"}\n'
        "INVARIANTS\n    Safety\n\\* INVARIANT Commented\n    Other\n"
        "(* PROPERTY Hidden *)\n"
        "PROPERTY Progress\n"
        "CONSTRAINT StateConstraint\n"
        "CHECK_DEADLOCK TRUE\n"
    )
    assert checks == {"Safety": "invariant", "Other": "invariant", "Progress": "property"}
    assert body.split() == [
        "SPECIFICATION",
        "Spec",
        "CONSTANTS",
        "WorkloadKinds",
        "=",
        '{"V2"}',
        "CONSTRAINT",
        "StateConstraint",
    ]


def test_analyse_reports_checks_never_run_with_a_reached_action() -> None:
    probes = [check.Probe(1, "G", "New", "A"), check.Probe(2, "G", "Old", "B"), check.Probe(3, "G", "Never", "C")]
    configs = [
        check.Config("MC.cfg", "MC", {"Inv": "invariant", "Safety": "invariant"}, taken=[2], status="budget used"),
        check.Config("Update_full.cfg", "Update", {"Safety": "invariant"}, taken=[1, 2], status="budget used"),
        check.Config("Broken.cfg", "MC", {"Inv": "invariant"}, taken=[1, 2], status="error: parse"),
    ]
    result = check.analyse(probes, configs)
    assert result == {
        "unreached": [3],
        "never_enabled": [3],
        "gaps": [{"check": "Inv", "kind": "invariant", "configs": ["MC.cfg"], "missing": [1], "possible": []}],
        "properties": [],
        "errors": [{"config": "Broken.cfg", "status": "error: parse"}],
        "ignored": [],
    }
    ignored = check.analyse(probes, configs, ignore=r"^Inv$")
    assert (ignored["gaps"], ignored["ignored"]) == ([], ["Inv"])


def test_enabled_but_untaken_actions_are_possible_and_groups_share_missing_actions() -> None:
    probes = [check.Probe(1, "G", "New", "A"), check.Probe(2, "G", "Old", "B")]
    configs = [
        check.Config("MC.cfg", "MC", {"I1": "invariant", "I2": "invariant"}, taken=[2], enabled=[1, 2]),
        check.Config("MC_hunt.cfg", "MC", {"I3": "invariant"}, taken=[2], enabled=[2]),
        check.Config("Update_full.cfg", "Update", {}, taken=[1, 2], enabled=[1, 2]),
    ]
    result = check.analyse(probes, configs)
    assert [(g["check"], g["missing"], g["possible"]) for g in result["gaps"]] == [
        ("I1", [1], [1]),
        ("I2", [1], [1]),
        ("I3", [1], []),
    ]
    assert check.gap_groups(result) == [
        {"missing": [(1, True)], "checks": ["I1", "I2"]},
        {"missing": [(1, False)], "checks": ["I3"]},
    ]
    text = check.report("spec", probes, configs, result)
    assert "| 1 New (possible) | 2 | `I1`, `I2` |" in text
    assert "| 1 New (never possible) | 1 | `I3` |" in text
    assert "| `MC_hunt.cfg` | not run | - | None | . | x |" in text


def test_comments_inside_a_definition_do_not_hide_its_disjuncts() -> None:
    body = "\n    \\* first family\n    \\/ \\E s \\in S : MCA(s)\n    \\* second family\n    \\/ \\E s \\in S : MCB(s)  \\* tail\n"
    assert check.disjuncts(body) == [r"\E s \in S : MCA(s)", r"\E s \in S : MCB(s)"]


def test_labels_ignore_quantifier_bounds() -> None:
    assert check.probe_label(r"\E s, t \in AliveNodes(Server) : MCSendConfig(s, t)") == "MCSendConfig"
    assert check.probe_label("\\E n\\in Server,\n      t\\in Timeouts:Framed(Original!Restart(n,t))") == "Restart"
