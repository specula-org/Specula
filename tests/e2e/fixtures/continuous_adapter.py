"""Deterministic continuous-orchestration adapter: real dispatch, never an LLM.

Behavior switches are files next to this script:
  repair          the first main pass reports MC-1, which confirmation hands back
  fail-main-N     exit 9 on the Nth main invocation (after the session exists)
  implicit        end main turns without calling request_bug_confirmation
  unconsumed      the repair turn requests confirmation without consuming its RR
  fail-confirm    the CR-1 worker fails once
"""

import json
import os
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "src"))

from specula.context_control import TOKEN_ENV, YIELD_PREFIX, request_confirmation
from specula.resource_summary import _confirmation_finding_statuses

here = Path(__file__).resolve().parent
options = dict(arg[2:].split("=", 1) for arg in sys.argv[1:] if arg.startswith("--") and "=" in arg)
work = Path(os.environ["SPECULA_WORK_DIR"])
log = Path(options["log"])
resume = Path(options["resume-state"])
prompt = Path(options["prompt-file"]).read_text()
phase = os.environ["SPECULA_PHASE"]
target = work.parent.name
adapter = os.environ.get("FIXTURE_ADAPTER", "fake")


def event(kind: str, name: str, **extra: object) -> None:
    with (here / "events.jsonl").open("a") as stream:
        stream.write(json.dumps({"kind": kind, "name": name, "phase": phase, "time": time.time(), **extra}) + "\n")


def respond(text: str) -> None:
    log.write_text(text + "\n")
    log.with_suffix(".last-message.txt").write_text(text + "\n")


def usage(session: str, cost: float) -> None:
    log.with_suffix(".usage.json").write_text(
        json.dumps(
            {
                "agent": "claude-code",
                "session_id": session,
                "total_cost_usd": cost,
                "usage": {"total_tokens": 100, "cached_input_tokens": 50},
            }
        )
    )


def handoff() -> None:
    if (here / "implicit").exists():
        respond("Validation complete; deliverables saved.")
        return
    try:
        request_confirmation()
    except ValueError as exc:
        # The tool refused; end the turn anyway so the controller's own check runs.
        (here / "tool-refusal.txt").write_text(str(exc))
        respond("Repair attempt ended.")
        return
    respond(f"{YIELD_PREFIX} {os.environ[TOKEN_ENV]}")


def first_pass() -> None:
    spec = work / "spec"
    for directory in (spec, work / "harness", work / "traces"):
        directory.mkdir(parents=True, exist_ok=True)
    (work / "modeling-brief.md").write_text("# Fixture brief\n\n## Scenario 1: Candidate one\n")
    (work / "analysis-report.md").write_text("Fixture analysis; no real verification.\n")
    for name in ("base.tla", "base.cfg", "MC.tla", "MC.cfg", "Trace.tla", "Trace.cfg", "instrumentation-spec.md"):
        (spec / name).write_text(f"fixture {name}\n")
    (spec / "brief-coverage.md").write_text("Fixture coverage.\n")
    (work / "harness/run.sh").write_text("#!/bin/sh\n")
    (work / "traces/fixture.ndjson").write_text('{"event":"fixture"}\n')
    (spec / "changelog.md").write_text("Fixture validation; MC was not run.\n")
    (spec / "bug-report.md").write_text("# Fixture report\nNo semantic verification performed.\n")
    findings: list[dict[str, str]] = []
    if (here / "repair").exists():
        (spec / "output").mkdir(exist_ok=True)
        (spec / "output/x.out").write_text("Fixture counterexample.\n")
        (spec / "MC_hunt.cfg").write_text("INVARIANT Inv\n")
        findings.append(
            {
                "id": "MC-1",
                "title": "Model artifact",
                "source": "model-checking",
                "summary": "Fixture mismatch.",
                "invariant": "Inv",
                "config": "MC_hunt.cfg",
                "counterexample": "spec/output/x.out",
            }
        )
    (spec / "findings.json").write_text(json.dumps({"findings": findings}))


def repair_pass() -> None:
    snapshot = json.loads((work / "spec/.repair-phase3-snapshot.json").read_text())
    if not (here / "unconsumed").exists():
        for filename in snapshot["requests"]:
            rr = work / "spec/repair-requests" / filename
            text = rr.read_text().replace("status: OPEN", "status: CONSUMED").replace("round: 0", "round: 1")
            rr.write_text(text + "\n- r1: Fixed model; full trace regression and scoped checks passed.\n")
    (work / "spec/base.tla").write_text("fixture repaired model\n")
    (work / "spec/findings.json").write_text(json.dumps({"findings": []}))


if phase == "main":
    counter = here / f"main-calls-{target}"
    calls = int(counter.read_text()) + 1 if counter.exists() else 1
    counter.write_text(str(calls))
    (here / f"main-prompt-{target}-{calls}.md").write_text(prompt)
    if resume.exists():
        session = json.loads(resume.read_text())["session_id"]
    else:
        sessions = here / f"sessions-{target}"
        number = int(sessions.read_text()) + 1 if sessions.exists() else 1
        sessions.write_text(str(number))
        session = f"main-{target}-{number}"
    resume.write_text(json.dumps({"adapter": adapter, "session_id": session}))
    usage(session, 0.01)
    event("start", "main", target=target, session=session, call=calls, model=options.get("model"))
    if (here / f"fail-main-{calls}").exists():
        respond("Interrupted fixture main session.")
        raise SystemExit(9)
    if "## Repair Round" in prompt:
        repair_pass()
    elif not (work / "spec/bug-report.md").exists():
        first_pass()
    handoff()
elif "Consolidate + dedup" in prompt:
    candidates = [
        {
            "id": "CR-1",
            "title": "Candidate one",
            "source": "code-review",
            "scenario": "Scenario 1",
            "severity": "High",
            "invariant": None,
            "config": None,
            "counterexample": None,
            "affected_code": ["logic.txt:1"],
            "summary": "A fixture code-review candidate.",
        }
    ]
    candidates.extend(json.loads((work / "spec/findings.json").read_text())["findings"])
    (work / "spec/candidates.json").write_text(json.dumps({"generated_by": "consolidate", "findings": candidates}))
    respond("Fixture candidates written.")
elif phase == "bug_classification":
    event("start", "classify", target=target)
    statuses = _confirmation_finding_statuses((work / "confirmed-bugs.md").read_text()) or {}
    (work / "bug-severity.md").write_text("# Severity Classification\n\n## Summary\n\n## Per-entry classification\n")
    bullets = "".join(f"- **{fid} — fixture** — Status: {status}. Fixture only.\n" for fid, status in statuses.items())
    (work / ".summary-findings.md").write_text(
        f"Fixture classification of {len(statuses)} finding(s).\n\n## Findings\n\n"
        + (bullets or "- Other dispositions only.\n")
        + "\n## Validation limits\n\nFixture only; no semantic validation was performed.\n"
    )
    respond("Fixture classification written.")
else:
    name = log.parent.name
    if resume.exists():
        assert json.loads(resume.read_text())["session_id"] == f"{log.stem}-{name}"
    resume.write_text(json.dumps({"adapter": adapter, "session_id": f"{log.stem}-{name}"}))
    event("start", name, target=target)
    repo = re.search(r"Source repo \(build/run here\): (.+)", prompt)
    repo_file = log.parent / "fixture-repo.txt"
    if repo:
        repo_file.write_text(repo[1])
    repo_path = Path(repo_file.read_text())
    (repo_path / "worker.txt").write_text(name)
    if name == "CR-1" and (here / "fail-confirm").exists():
        (here / "fail-confirm").unlink()
        respond("Interrupted fixture confirmation.")
        raise SystemExit(9)
    if name == "MC-1":
        (log.parent / "repair-request.body.md").write_text(
            "---\ntarget: SPEC_REPAIR\ncounterexample: spec/output/x.out\nscope:\n"
            "  actions: [Foo]\n  invariants: [Inv]\n  hunt_cfgs: [MC_hunt.cfg]\n  fault_actions: []\n---\n\n"
            "## Trigger\nA transition the implementation rejects.\n\n"
            "## Evidence\nSource logic.txt:1 rejects it, unlike the model trace.\n"
        )
        respond("VERDICT: PENDING REPAIR\n- **Source**: MC\nThe fixture counterexample requires a model repair.")
    else:
        (work / "repro" / f"test_bug{name}_fixture.py").write_text("print('fixture evidence')\n")
        respond(f"VERDICT: REPRODUCED\n- **Source**: Code Review\n- **Novelty**: NEW\n\nFixture evidence for {name}.")
    event("end", name, target=target)
