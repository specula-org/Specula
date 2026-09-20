"""Deterministic CI/confirmation adapter: exercises real dispatch, never an LLM."""

import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "src"))

from specula import persistent_findings
from specula.context_control import CONFIRMATION_REQUEST, TOKEN_ENV, YIELD_PREFIX, request_confirmation

options = dict(arg[2:].split("=", 1) for arg in sys.argv[1:] if arg.startswith("--") and "=" in arg)
work = Path(os.environ["SPECULA_WORK_DIR"])
run = Path(os.environ["SPECULA_RUN_DIR"])
log = Path(options["log"])
resume = Path(options["resume-state"])
prompt = Path(options["prompt-file"]).read_text()
phase = os.environ["SPECULA_PHASE"]
repair_enabled = (Path(__file__).parent / "repair-confirmation").exists()
name = "main" if phase == "incremental" else log.parent.name
session = "workflow" if name == "main" else log.stem + "-" + name
if resume.exists():
    assert json.loads(resume.read_text())["session_id"] == session
resume.write_text(json.dumps({"adapter": "fake", "session_id": session}))
log.with_suffix(".usage.json").write_text(
    json.dumps(
        {
            "agent": "codex",
            "session_id": session,
            "total_cost_usd": 0.01,
            "usage": {"total_tokens": 100, "cached_input_tokens": 50},
        }
    )
)


def event(kind: str) -> None:
    with (work / "dispatch.jsonl").open("a") as stream:
        stream.write(
            json.dumps(
                {
                    "kind": kind,
                    "name": name,
                    "log": log.name,
                    "model": options.get("model"),
                    "cwd": str(Path.cwd()),
                    "time": time.time(),
                }
            )
            + "\n"
        )


event("start")
if phase == "incremental":
    if (Path(__file__).parent / "policy-confirmation").exists():
        events = [json.loads(line) for line in (work / "dispatch.jsonl").read_text().splitlines()]
        main_calls = sum(e["kind"] == "start" and e["name"] == "main" for e in events)
        if main_calls in (1, 3):
            log.write_text("Fixture policy interruption.\n")
            raise SystemExit(76)
    pending = work / CONFIRMATION_REQUEST
    if not pending.exists():
        (work / "modeling-brief.md").write_text("\n".join(f"## Scenario {n}: Candidate {n}" for n in (1, 2, 3)))
        (work / "spec/bug-report.md").write_text("No MC violations. CR candidates remain to be confirmed.\n")
        (work / "spec/findings.json").write_text('{"findings": []}')
        if repair_enabled:
            (work / "spec/output").mkdir(exist_ok=True)
            (work / "spec/output/x.out").write_text("Fixture counterexample.\n")
            (work / "spec/MC_hunt.cfg").write_text("INVARIANT Inv\n")
            (work / "spec/findings.json").write_text(
                json.dumps(
                    {
                        "findings": [
                            {
                                "id": "MC-1",
                                "title": "Model artifact",
                                "source": "model-checking",
                                "summary": "Fixture mismatch.",
                                "invariant": "Inv",
                                "config": "MC_hunt.cfg",
                                "counterexample": "spec/output/x.out",
                            }
                        ]
                    }
                )
            )
        source, rid, _ = persistent_findings.context(work)
        for fid in persistent_findings.index(work):
            persistent_findings.reuse_issue(work, source, rid, fid, "Same fixture logic and premises.")
        request_confirmation()
        log.write_text(YIELD_PREFIX + " " + os.environ[TOKEN_ENV] + "\n")
    else:
        assert json.loads(pending.read_text())["status"] == "completed"
        assert "Continue this same conversation" in prompt
        assert (work / "spec/confirmation-report.md").is_file()
        rr = work / "spec/repair-requests/RR-001.md"
        if repair_enabled and "status: OPEN" in rr.read_text():
            rr.write_text(
                rr.read_text().replace("status: OPEN", "status: CONSUMED").replace("round: 0", "round: 1")
                + "\n- r1: Fixed model; full trace regression and scoped checks passed.\n"
            )
            (work / "spec/base.tla").write_text("Fixture repaired model.\n")
            (work / "spec/findings.json").write_text('{"findings": []}')
            request_confirmation()
            log.write_text(YIELD_PREFIX + " " + os.environ[TOKEN_ENV] + "\n")
            event("end")
            raise SystemExit(0)
        findings: list[dict[str, Any]] = []
        for fid in ("CR-1", "CR-2", "CR-3"):
            if (work / persistent_findings.RECEIPTS / f"{fid}.json").exists():
                findings.append({"id": fid, "reuse": "Same fixture logic and premises."})
                continue
            verdict = json.loads((work / "confirmation" / fid / "verdict.json").read_text())
            findings.append(
                {
                    "id": fid,
                    "title": fid,
                    "source": "code-review",
                    "status": verdict["status"],
                    "cause": "fixture cause",
                    "trigger": "fixture trigger",
                    "consequence": "fixture consequence",
                    "evidence": ["spec/confirmation-report.md"],
                    "persistence": {
                        "premises": ["fixture premise"],
                        "dependencies": [{"root": "source", "path": "logic.txt"}],
                    },
                }
            )
        if repair_enabled:
            assert "| MC-1 | FALSE POSITIVE |" in (work / "spec/confirmation-report.md").read_text()
            findings.append(
                {
                    "id": "MC-1",
                    "title": "Model artifact",
                    "source": "model-checking",
                    "status": "FALSE POSITIVE",
                    "cause": "Repaired model mismatch",
                    "trigger": "Fixture",
                    "consequence": "No real defect",
                    "evidence": ["spec/confirmation-report.md"],
                }
            )
        (work / "spec/final-result.json").write_text(
            json.dumps(
                {
                    "version": 1,
                    "run_id": run.name,
                    "summary": "Fixture confirmation completed.",
                    "validation_limits": ["No semantic verification."],
                    "findings": findings,
                }
            )
        )
        log.with_suffix(".usage.json").write_text(
            json.dumps(
                {
                    "agent": "codex",
                    "session_id": session,
                    "total_cost_usd": 0.02,
                    "usage": {"total_tokens": 200, "cached_input_tokens": 100},
                }
            )
        )
        log.write_text("SPECULA_INCREMENTAL_COMPLETE " + run.name + "\n")
elif "Consolidate + dedup" in prompt:
    candidates = [
        {
            "id": f"CR-{n}",
            "title": f"Candidate {n}",
            "source": "code-review",
            "scenario": f"Scenario {n}",
            "severity": "High",
            "invariant": None,
            "config": None,
            "counterexample": None,
            "affected_code": ["logic.txt:1"],
            "summary": "A fixture code-review candidate.",
        }
        for n in (1, 2, 3)
    ]
    if repair_enabled:
        candidates.extend(json.loads((work / "spec/findings.json").read_text())["findings"])
    (work / "spec/candidates.json").write_text(json.dumps({"generated_by": "consolidate", "findings": candidates}))
    log.write_text("Fixture candidates written.\n")
else:
    assert name in {"CR-1", "CR-2", "CR-3", "MC-1"}
    repo = re.search(r"Source repo \(build/run here\): (.+)", prompt)
    repo_file = log.parent / "fixture-repo.txt"
    if repo:
        repo_file.write_text(repo[1])
    repo_path = Path(repo_file.read_text())
    assert repo_path.resolve() != (run / "footest/source").resolve()
    (repo_path / "worker.txt").write_text(name)
    if name == "CR-2" and (Path(__file__).parent / "fail-confirmation").exists():
        log.write_text("Interrupted fixture confirmation.\n")
        raise SystemExit(9)
    time.sleep(0.3)
    if name == "MC-1":
        (log.parent / "repair-request.body.md").write_text(
            "---\ntarget: SPEC_REPAIR\ncounterexample: spec/output/x.out\nscope:\n"
            "  actions: [Foo]\n  invariants: [Inv]\n  hunt_cfgs: [MC_hunt.cfg]\n  fault_actions: []\n---\n\n"
            "## Trigger\nA transition the implementation rejects.\n\n"
            "## Evidence\nSource logic.txt:1 rejects it, unlike the model trace.\n"
        )
        log.write_text(
            "VERDICT: PENDING REPAIR\n- **Source**: MC\nThe fixture counterexample requires a model repair.\n"
        )
        event("end")
        raise SystemExit(0)
    status = "DROPPED" if name == "CR-3" else "REPRODUCED"
    if status == "REPRODUCED":
        (work / "repro" / f"test_bug{name}_fixture.py").write_text("print('fixture evidence')\n")
    novelty = "KNOWN (cite: fixture)" if status == "DROPPED" else "NEW"
    log.write_text(
        f"VERDICT: {status}\n- **Source**: Code Review\n"
        f"- **Novelty**: {novelty}\n\nFixture investigation and execution evidence.\n"
    )
event("end")
