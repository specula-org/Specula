"""Tests for the module and config generation in branch.py. Run with `python3 -m pytest test_branch.py`."""

from __future__ import annotations

import argparse
from pathlib import Path

from branch import (
    SPEC_DEF,
    build,
    constants,
    declared_variables,
    domain_candidates,
    extends_chain,
    section_names,
    suite_checks,
)

FILES = {
    "base.tla": """---- MODULE base ----
EXTENDS Naturals
CONSTANTS Server, RequestId
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\\ y = 0
Step(n) == x' = x + 1 /\\ UNCHANGED y
Echo(n) == y' = x /\\ UNCHANGED x
ReactiveActions ==
    \\/ \\E n \\in Server: Step(n)
    \\/ \\E n \\in Server: Echo(n)
Safe == x >= y
====
""",
    "Trace.tla": """---- MODULE Trace ----
EXTENDS base, Json, IOUtils
VARIABLE l
TraceServer == {1, 2}
""",
    "MC.tla": """---- MODULE MC ----
EXTENDS base
VARIABLE faultCount
mcvars == <<vars, faultCount>>
MCInit == Init /\\ faultCount = 0
MCNext == ReactiveActions /\\ UNCHANGED faultCount
""",
    "Update.tla": """---- MODULE Update ----
EXTENDS MC
AffectedActions ==
    \\/ \\E n \\in Server: Step(n) /\\ UNCHANGED faultCount
FullUpdateNext == MCNext
FullUpdateSpec == MCInit /\\ [][FullUpdateNext]_mcvars
NotReached == TRUE
====
""",
    "Trace.cfg": """SPECIFICATION TraceSpec
CONSTANTS
    Server <- TraceServer
    RequestId <- TraceRequestId
INVARIANT Safe
""",
    "Update_full.cfg": """\\* limits
SPECIFICATION FullUpdateSpec
CONSTANTS
    Server = {s1, s2}
    RequestId = {1, 2}
    CrashLimit = 1
INVARIANTS
    Safe
    NotReached
CONSTRAINT Small
""",
}


def suite(tmp_path: Path) -> Path:
    for name, text in FILES.items():
        (tmp_path / name).write_text(text)
    return tmp_path


def options(**overrides: object) -> argparse.Namespace:
    values = {
        "limits": "Update_full.cfg",
        "actions": "AffectedActions",
        "settle": "base.tla:ReactiveActions",
        "replay": "strict",
        "guard": "",
        "settled": "",
        "constraint": True,
        "after": 100,
        "checks": "",
        "ignore": r"NotReached$",
        "steps": 0,
    }
    values.update(overrides)
    return argparse.Namespace(**values)


def test_config_parsing(tmp_path: Path) -> None:
    spec = suite(tmp_path)
    limits = (spec / "Update_full.cfg").read_text()
    assert constants(limits) == {"Server": "= {s1, s2}", "RequestId": "= {1, 2}", "CrashLimit": "= 1"}
    assert section_names(limits, "SPECIFICATION") == ["FullUpdateSpec"]
    assert section_names(limits, "CONSTRAINT") == ["Small"]
    assert suite_checks(spec, r"NotReached$") == ["Safe"]


def test_chain_and_variables(tmp_path: Path) -> None:
    spec = suite(tmp_path)
    assert extends_chain(spec, "Update") == ["Update", "MC", "base"]
    assert declared_variables(spec, "base") == ["x", "y"]
    assert declared_variables(spec, "MC") == ["faultCount"]


def test_build_keeps_trace_constants_except_domains(tmp_path: Path) -> None:
    module, cfg, info = build(options(), suite(tmp_path), 10, {"RequestId"})
    assert "EXTENDS Trace, Update, TLC" in module
    assert "PBInit == TraceInit /\\ MCInit" in module
    assert info["extra_variables"] == ["faultCount"]
    assert info["settle_parts"] == 2
    assert "    Server <- TraceServer" in cfg
    assert "    RequestId = {1, 2}" in cfg
    assert "    CrashLimit = 1" in cfg
    assert "    PBMaxSteps = 110" in cfg
    assert "PB_Safe == ~pbBranched \\/ Safe" in module
    assert "PBConstraint == ~pbBranched \\/ (Small)" in module


def test_build_input_replay_guard_and_random_settle(tmp_path: Path) -> None:
    module, _, info = build(
        options(replay="MatchEvent(logline)", guard="x' > x", settle="next"), suite(tmp_path), 10, set()
    )
    assert "PBInit == MCInit /\\ l = 2" in module
    assert "/\\ MatchEvent(logline)" in module
    assert "UNCHANGED <<l, pbAt, pbSlot>> /\\ (x' > x)" in module
    assert "PBSettle1 ==\n    FullUpdateNext" in module
    assert "UNCHANGED <<l, pbAt, pbBranched, pbAction>>" in module
    assert info["settle_parts"] == 1


def test_checks_outside_the_module_chain_are_skipped(tmp_path: Path) -> None:
    spec = suite(tmp_path)
    (spec / "Witness.cfg").write_text("INVARIANT WitnessOnly\n")
    module, _, info = build(options(), spec, 10, set())
    assert info["checks"] == ["Safe"]
    assert info["skipped_checks"] == ["WitnessOnly"]
    assert "WitnessOnly" not in module


def test_domain_candidates_are_trace_bound_sets_the_limits_config_narrows(tmp_path: Path) -> None:
    assert domain_candidates(suite(tmp_path), "Update_full.cfg") == ["Server", "RequestId"]


def test_settled_condition_is_checked_when_quiet(tmp_path: Path) -> None:
    module, cfg, _ = build(options(settled="x = y"), suite(tmp_path), 10, set())
    assert "PB_Settled == ~PBQuiet \\/ (x = y)" in module
    assert "    PB_Settled" in cfg


def test_explicit_domains_override_the_trace_and_the_limits(tmp_path: Path) -> None:
    _, cfg, info = build(options(domain=["RequestId={1, 2, 9}"]), suite(tmp_path), 10, {"RequestId"})
    assert "    RequestId = {1, 2, 9}" in cfg
    assert info["explicit_domains"] == {"RequestId": "{1, 2, 9}"}


def test_spec_definition_accepts_a_tuple_of_variables() -> None:
    match = SPEC_DEF.match(" MCInit /\\ [][MCNext]_<<allVars, mcVars>>")
    assert match and match.groups() == ("MCInit", "MCNext", "<<allVars, mcVars>>")
