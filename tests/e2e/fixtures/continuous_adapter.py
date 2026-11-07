"""Deterministic continuous-orchestration adapter: real dispatch, never an LLM.

Behavior switches are files next to this script:
  repair          the first main pass reports MC-1, which confirmation hands back
  fail-main-N     exit 9 on the Nth main invocation (after the session exists)
  implicit        end main turns without calling request_bug_confirmation
  unconsumed      the repair turn requests confirmation without consuming its RR
  unconsumed-once ... only on the first repair turn
  blocked         the first pass writes spec/BLOCKED.md instead of its deliverables
  fail-confirm    the CR-1 worker fails once
  minimal         the first pass writes only the outputs continuous mode requires
  sany-error      the first pass writes a Trace.tla that the fake SANY rejects
  no-traces       the first pass collects no traces (the harness cannot run)
  fix-on-rejection  when the confirmation tool or a resumed main call reports
                  unaccepted required outputs, rewrite each output it names
                  (after a tool refusal: in the same turn, then request again)
  tool-no-sany    the confirmation tool runs without SANY (java off PATH)

Fault-injection switches (tests/e2e/test_continuous_faults.py):
  block-POINT     at POINT, publish reached-POINT.json (pid, pgid, session) and
                  wait for release-POINT; POINT is main-N (main call N, after
                  its analysis or repair work), worker-ID, consolidate, classify
  background      the first main call starts a registered background job
                  through start_background.sh (release-job ends it); before a
                  handoff the session waits for it, or restarts it if it died
                  unfinished
  background-detached  the job's tool shell escapes the agent's session
  background-lock the job inherits the run lock, as a native CLI tool shell does
  abandon-job     hand off without waiting for a live job
  abandon-job-once ... only at the first handoff
  compact-N       main call N requests native compaction instead of handing off
  rate-limit-N    exit 75 on the Nth main invocation (after the session exists)
  policy-N        exit 76 (provider policy block) on the Nth main invocation
  cr2             consolidation adds a second code-review candidate CR-2
  quota-after-ID  the ID worker turns the fixture quota endpoint over its limit

The first pass is staged: a resumed session skips the stages it completed
(its conversation remembers them); a new session starts over. A main prompt
that reports code analysis as already complete (--skip-analysis) keeps the
existing Phase 1 outputs instead of writing its own.
"""

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "src"))

from specula.context_control import TOKEN_ENV, YIELD_PREFIX, request_compaction, request_confirmation
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
ANALYSIS_COMPLETE = "1. **Code analysis**: already complete."


def event(kind: str, name: str, **extra: object) -> None:
    with (here / "events.jsonl").open("a") as stream:
        stream.write(json.dumps({"kind": kind, "name": name, "phase": phase, "time": time.time(), **extra}) + "\n")


def publish(path: Path, value: object) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value))
    temporary.replace(path)


def block(point: str, **extra: object) -> None:
    """Hold this process at a named fault point until the test releases it."""
    if not (here / f"block-{point}").exists():
        return
    publish(here / f"reached-{point}.json", {"pid": os.getpid(), "pgid": os.getpgrp(), **extra})
    while not (here / f"release-{point}").exists():
        time.sleep(0.02)


def remembered(session: str) -> list[str]:
    path = here / f"memory-{session}.json"
    return list(json.loads(path.read_text())) if path.exists() else []


def remember(session: str, stage: str) -> None:
    publish(here / f"memory-{session}.json", [*remembered(session), stage])
    event("stage", stage, target=target, session=session)


def start_background_job() -> None:
    """Start a long job the way an agent does, through start_background.sh."""
    script = here.parents[1] / "infra/start_background.sh"
    env = {**os.environ, "FIXTURE_JOB_DIR": str(here)}
    lock = os.environ.get("SPECULA_RUN_LOCK_FD")
    started = subprocess.run(
        ["bash", str(script), "-d", str(work), "-o", "job.log", "-s", "MC.tla", "-c", "MC.cfg"],
        env=env,
        capture_output=True,
        text=True,
        # A native CLI's tool shells inherit its descriptors, including the run lock.
        pass_fds=(int(lock),) if lock and (here / "background-lock").exists() else (),
        start_new_session=(here / "background-detached").exists(),
    )
    pid = re.search(r"Process started! PID: (\d+)", started.stdout)
    assert started.returncode == 0 and pid, started.stdout + started.stderr
    event("job", "main", target=target, pid=int(pid[1]))
    publish(here / "job.json", {"pid": int(pid[1]), "log": str(work / "job.log")})


def job_alive(pid: int) -> bool:
    try:
        return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0] != "Z"
    except OSError:
        return False


def harvest_job() -> None:
    """Wait for the background job in the foreground; restart it if it died unfinished."""
    job = json.loads((here / "job.json").read_text())
    running = job_alive(job["pid"])
    if not running and "Finished in" not in Path(job["log"]).read_text():
        start_background_job()
        job = json.loads((here / "job.json").read_text())
    abandon = (here / "abandon-job").exists()
    if abandon and (here / "abandon-job-once").exists():
        for flag in ("abandon-job", "abandon-job-once"):
            (here / flag).unlink()
    if not abandon:
        waiter = here.parents[1] / "infra/wait_for_pid.sh"
        subprocess.run(["bash", str(waiter), "--pid", str(job["pid"]), "--timeout", "120s", "--quiet"], check=False)
    finished = "Finished in" in Path(job["log"]).read_text()
    event("harvest", "main", target=target, alive=running, finished=finished)


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


def request_with_tool() -> None:
    if not (here / "tool-no-sany").exists():
        request_confirmation()
        return
    path = os.environ["PATH"]
    os.environ["PATH"] = "/usr/bin:/bin"  # neither the fake SANY nor a usable TLA+ jar
    try:
        request_confirmation()
    finally:
        os.environ["PATH"] = path


def handoff() -> None:
    if (here / "implicit").exists():
        respond("Validation complete; deliverables saved.")
        return
    for attempt in (1, 2):
        try:
            request_with_tool()
            break
        except ValueError as exc:
            (here / "tool-refusal.txt").write_text(str(exc))
            event("refusal", "tool", target=target, attempt=attempt)
            fixable = "Required outputs are missing or invalid" in str(exc)
            if attempt == 1 and fixable and (here / "fix-on-rejection").exists():
                fix_rejected_outputs(str(exc))  # the tool result named them; fix in this turn
                continue
            # End the turn anyway so the controller's own check runs.
            respond("Repair attempt ended.")
            return
    respond(f"{YIELD_PREFIX} {os.environ[TOKEN_ENV]}")


def compact() -> None:
    handoff = work / "notes/handoff.md"
    handoff.parent.mkdir(exist_ok=True)
    handoff.write_text("Fixture handoff; no semantic state.\n")
    request_compaction(str(handoff))
    respond(f"{YIELD_PREFIX} {os.environ[TOKEN_ENV]}")


def first_pass(session: str, call: int) -> None:
    done = remembered(session)
    if "analysis" not in done:
        opening = here / f"opening-{session}.md"
        if ANALYSIS_COMPLETE in (opening.read_text() if opening.exists() else prompt):
            event("reused", "analysis", target=target, session=session)
        else:
            (work / "modeling-brief.md").write_text("# Fixture brief\n\n## Scenario 1: Candidate one\n")
            if not (here / "minimal").exists():
                (work / "analysis-report.md").write_text("Fixture analysis; no real verification.\n")
        if (here / "background").exists() and not (here / "job.json").exists():
            start_background_job()
        remember(session, "analysis")
    block(f"main-{call}", session=session)
    if (here / "blocked").exists():
        (work / "spec").mkdir(exist_ok=True)
        (work / "spec/BLOCKED.md").write_text("Fixture: the build cannot run here; nothing was validated.\n")
        return
    if "validation" in done:
        return
    validation()
    remember(session, "validation")


def validation() -> None:
    spec = work / "spec"
    for directory in (spec, work / "harness", work / "traces"):
        directory.mkdir(parents=True, exist_ok=True)
    minimal = (here / "minimal").exists()
    for name in ("base.tla", "base.cfg", "MC.tla", "MC.cfg", "Trace.tla", "Trace.cfg", "instrumentation-spec.md"):
        if not (minimal and name in ("base.cfg", "instrumentation-spec.md")):
            (spec / name).write_text(f"fixture {name}\n")
    if (here / "sany-error").exists():
        (spec / "Trace.tla").write_text("fixture Trace.tla\nSANY-ERROR\n")
    if not minimal:
        (spec / "brief-coverage.md").write_text("Fixture coverage.\n")
        (spec / "changelog.md").write_text("Fixture validation; MC was not run.\n")
    (work / "harness/run.sh").write_text("#!/bin/sh\n")
    if not (here / "no-traces").exists():
        (work / "traces/fixture.ndjson").write_text('{"event":"fixture"}\n')
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


def fix_rejected_outputs(reason: str) -> None:
    """Rewrite each output an unaccepted handoff named, as an agent reading the reason would."""
    fixed = []
    for relative in re.findall(r"^- `([^`]+)`", reason, flags=re.MULTILINE):
        path = work / relative.rstrip("/")
        if relative.endswith("/"):
            path.mkdir(parents=True, exist_ok=True)
            (path / "fixture.txt").write_text("fixture\n")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"fixture {relative}\n")
        fixed.append(relative)
    event("fix", "fix", target=target, fixed=fixed)


def repair_pass(session: str, call: int) -> None:
    snapshot = json.loads((work / "spec/.repair-phase3-snapshot.json").read_text())
    stage = f"repair-{snapshot['round']}"
    if stage not in remembered(session):
        consume = not (here / "unconsumed").exists()
        if not consume and (here / "unconsumed-once").exists():
            for name in ("unconsumed", "unconsumed-once"):
                (here / name).unlink()
        if consume:
            for filename in snapshot["requests"]:
                rr = work / "spec/repair-requests" / filename
                text = rr.read_text().replace("status: OPEN", "status: CONSUMED").replace("round: 0", "round: 1")
                rr.write_text(text + "\n- r1: Fixed model; full trace regression and scoped checks passed.\n")
        (work / "spec/base.tla").write_text("fixture repaired model\n")
        (work / "spec/findings.json").write_text(json.dumps({"findings": []}))
        if consume:
            remember(session, stage)
    block(f"main-{call}", session=session)


if phase == "main":
    counter = here / f"main-calls-{target}"
    calls = int(counter.read_text()) + 1 if counter.exists() else 1
    counter.write_text(str(calls))
    (here / f"main-prompt-{target}-{calls}.md").write_text(prompt)
    resumed = resume.exists()
    if resumed:
        session = json.loads(resume.read_text())["session_id"]
    else:
        sessions = here / f"sessions-{target}"
        number = int(sessions.read_text()) + 1 if sessions.exists() else 1
        sessions.write_text(str(number))
        session = f"main-{target}-{number}"
        (here / f"opening-{session}.md").write_text(prompt)  # a resumed conversation still knows its task
    resume.write_text(json.dumps({"adapter": adapter, "session_id": session}))
    usage(session, 0.01)
    event("start", "main", target=target, session=session, call=calls, model=options.get("model"), resumed=resumed)
    if (here / f"fail-main-{calls}").exists():
        respond("Interrupted fixture main session.")
        raise SystemExit(9)
    if (here / f"rate-limit-{calls}").exists():
        respond("API Error: rate limit reached (fixture).")
        raise SystemExit(75)
    if (here / f"policy-{calls}").exists():
        respond("Fixture provider policy block.")
        raise SystemExit(76)
    if (here / "fix-on-rejection").exists() and "Required outputs are missing or invalid" in prompt:
        fix_rejected_outputs(prompt)
    # The conversation knows it is repairing even when resumed with a generic prompt.
    if (work / "spec/.repair-phase3-snapshot.json").exists():
        repair_pass(session, calls)
    else:
        first_pass(session, calls)
    if (here / "job.json").exists():
        harvest_job()  # the stop gate requires harvested jobs before a handoff
    if (here / f"compact-{calls}").exists():
        compact()
    else:
        handoff()
elif "Consolidate + dedup" in prompt:
    event("start", "consolidate", target=target)
    block("consolidate")
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
    if (here / "cr2").exists():
        candidates.append({**candidates[0], "id": "CR-2", "title": "Candidate two", "summary": "A second candidate."})
    candidates.extend(json.loads((work / "spec/findings.json").read_text())["findings"])
    (work / "spec/candidates.json").write_text(json.dumps({"generated_by": "consolidate", "findings": candidates}))
    respond("Fixture candidates written.")
elif phase == "bug_classification":
    # Native CLIs report their session id first; a resumed turn keeps it.
    if not resume.exists():
        resume.write_text(json.dumps({"adapter": adapter, "session_id": f"classify-{target}"}))
    event("start", "classify", target=target)
    block("classify")
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
    resumed = resume.exists()
    if resumed:
        assert json.loads(resume.read_text())["session_id"] == f"{log.stem}-{name}"
    resume.write_text(json.dumps({"adapter": adapter, "session_id": f"{log.stem}-{name}"}))
    event("start", name, target=target, resumed=resumed)
    repo = re.search(r"Source repo \(build/run here\): (.+)", prompt)
    repo_file = log.parent / "fixture-repo.txt"
    if repo:
        repo_file.write_text(repo[1])
    repo_path = Path(repo_file.read_text())
    (repo_path / "worker.txt").write_text(name)
    block(f"worker-{name}")
    if (here / f"quota-after-{name}").exists():
        (here / "quota-over").touch()
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
