#!/usr/bin/env python3
"""Run prepared attempts: one fresh agent per (arm, case, rep), in the bwrap sandbox.

    python3 run.py --arm v0 --arm v1 --arm v2 --case case-002 [--rep 1] [--jobs 2]
    python3 run.py --arm v1 --all-cases --rep 1 --timeout 14400 --budget 100
    python3 run.py --plan ...            # list what would run, in order

Order: rep-major, then case; within a case the arm order is shuffled with a fixed seed,
so time-of-day and provider drift do not line up with arms.

Each run writes, outside the workspace,
  WORK/attempts/<arm>/<case>/r<rep>/log/{activity.jsonl, stderr.log, run-manifest.json, command.json}
and copies small outputs into the repository:
  results/<arm>/<case>/r<rep>/{run.json, final-response.json, invariant-evidence.json}
run.json holds status, wall time, cost/usage, tool counts, TLC/build command counts, skill
files read, the network audit, and invariant-evidence statistics. Grading against Gold is
a separate, later step (grading is not done here).
"""

from __future__ import annotations

import argparse
import json
import random
import shutil
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import threading
import time
from datetime import datetime

from agent import limit_wait_seconds, run_agent
from common import ARMS, CASE_IDS, RESULTS, WORK, blind_helpers, check_arm, check_case, read_json, write_json
from prepare import prepare

H = blind_helpers()

RO = [".agents", "lib", "tools", "old-source", "new-source", "previous", "model-scope.md", "case.json",
      "input-manifest.json", "task.md", "final-schema.json"]
RW = ["current", ".cache"]


def evidence_stats(path: Path) -> dict | None:
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError:
        return {"parse_error": True}
    entries = data.get("entries", []) if isinstance(data, dict) else []
    evidence = data.get("evidence", []) if isinstance(data, dict) else []
    decisions: dict[str, int] = {}
    for e in entries:
        d = str(e.get("decision", "?"))
        decisions[d] = decisions.get(d, 0) + 1
    tlc_agree = sum(1 for e in evidence for side in ("old", "new")
                    if isinstance(e.get(side), dict) and "tlc" in e[side] and e[side].get("claimed") == e[side].get("tlc"))
    tlc_total = sum(1 for e in evidence for side in ("old", "new") if isinstance(e.get(side), dict) and "tlc" in e[side])
    sources: dict[str, int] = {}
    for e in evidence:
        s = str(e.get("state_source", "?"))
        sources[s] = sources.get(s, 0) + 1
    return {
        "entries": len(entries),
        "decisions": decisions,
        "changed_from_initial": sum(1 for e in entries if e.get("changed_from_initial")),
        "evidence_records": len(evidence),
        "state_sources": sources,
        "tlc_values_matching_claim": f"{tlc_agree}/{tlc_total}",
        "bug_candidates": len(data.get("bug_candidates", []) or []) if isinstance(data, dict) else 0,
        "unresolved": len(data.get("unresolved", []) or []) if isinstance(data, dict) else 0,
    }


class StopQueue(RuntimeError):
    """A usage limit without a parseable 5-hour reset (e.g. a weekly limit): stop and let a person decide."""


STOP = threading.Event()


def archive_invalid(arm: str, case_id: str, rep: int, manifest: dict) -> Path:
    """Move a usage-limited attempt (log + workspace) out of the way; it is never a result."""
    logical = WORK / "attempts" / arm / case_id / f"r{rep}"
    attempt = read_json(logical / "attempt.json")
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    dest = WORK / "invalid" / f"{arm}-{case_id}-r{rep}-a{attempt.get('attempt_no', 1)}-{stamp}"
    dest.parent.mkdir(parents=True, exist_ok=True)
    physical = Path(attempt["physical"])
    shutil.move(str(logical), str(dest))
    if physical.exists():
        H.make_tree_owner_writable(physical)
        shutil.move(str(physical), str(dest / "ws-physical"))
    write_json(dest / "invalid.json", {
        "arm": arm, "case_id": case_id, "rep": rep, "attempt_no": attempt.get("attempt_no", 1),
        "status": manifest["status"],
        "reason": (manifest["behavior"].get("error") or {}).get("text"),
        "wall_seconds": manifest["wall_seconds"], "cost_usd": manifest["behavior"].get("cost_usd"),
        "streamed_usage": manifest["behavior"].get("streamed_usage"),
    })
    return dest


def run_one(arm: str, case_id: str, rep: int, args) -> dict:
    """Run one (arm, case, rep); on a usage limit, archive it, wait for the reset, re-prepare, retry."""
    for attempt_no in range(1, args.max_attempts + 1):
        if STOP.is_set():
            return {"arm": arm, "case_id": case_id, "rep": rep, "status": "NOT_RUN_QUEUE_STOPPED"}
        summary, manifest = run_once(arm, case_id, rep, args)
        if manifest["status"] not in ("USAGE_LIMIT", "AUTH_ERROR"):
            return summary
        dest = archive_invalid(arm, case_id, rep, manifest)
        # AUTH_ERROR: infrastructure (expired OAuth in the sandbox); the run is void, retry after a minute.
        wait = 60 if manifest["status"] == "AUTH_ERROR" else limit_wait_seconds(manifest["behavior"], dest / "log/stderr.log")
        print(f"{arm} {case_id} r{rep}: {manifest['status']} (attempt {attempt_no}) archived to {dest}; "
              f"wait {wait}s", flush=True)
        if wait is None:
            STOP.set()
            raise StopQueue(f"usage limit without a 5-hour reset time: {(manifest['behavior'].get('error') or {}).get('text')}")
        time.sleep(wait)
        logical = prepare(arm, case_id, rep)
        attempt = read_json(logical / "attempt.json")
        attempt["attempt_no"] = attempt_no + 1
        write_json(logical / "attempt.json", attempt)
    raise RuntimeError(f"{arm} {case_id} r{rep}: still usage-limited after {args.max_attempts} attempts")


def run_once(arm: str, case_id: str, rep: int, args) -> tuple[dict | None, dict]:
    logical = WORK / "attempts" / arm / case_id / f"r{rep}"
    attempt_path = logical / "attempt.json"
    if not attempt_path.exists():
        raise RuntimeError(f"not prepared: {logical}")
    attempt = read_json(attempt_path)
    if attempt.get("agent_started"):
        raise RuntimeError(f"already started: {logical} (prepare a new rep instead of rerunning)")
    ws = Path(attempt["physical"])
    attempt["agent_started"] = True
    write_json(attempt_path, attempt)
    manifest = run_agent(
        backend=args.backend, workspace=ws, ro=RO, rw=RW,
        prompt=(ws / "task.md").read_text(), log_dir=logical / "log",
        timeout_s=args.timeout, model=args.model, effort=args.effort, budget_usd=args.budget,
        schema="/work/final-schema.json", final_path="/work/current/final-response.json",
        extra_binds=[(str(ws / ".agents/skills"), "/work/.claude/skills")],
        meta={"arm": arm, "case_id": case_id, "rep": rep, "attempt_no": attempt.get("attempt_no", 1),
              "skills_tree_sha256": attempt["skills_tree_sha256"], "prior_tree_sha256": attempt["prior_tree_sha256"]},
    )
    if manifest["status"] in ("USAGE_LIMIT", "AUTH_ERROR"):
        return None, manifest
    out = RESULTS / arm / case_id / f"r{rep}"
    out.mkdir(parents=True, exist_ok=True)
    final = ws / "current/final-response.json"
    final_data = None
    if final.is_file():
        shutil.copy2(final, out / "final-response.json")
        try:
            final_data = json.loads(final.read_text())
        except json.JSONDecodeError:
            final_data = {"parse_error": True}
    evidence = ws / "current/.specula-output/spec/invariant-evidence.json"
    if evidence.is_file():
        shutil.copy2(evidence, out / "invariant-evidence.json")
    summary = {
        "arm": arm, "case_id": case_id, "rep": rep, "attempt_no": attempt.get("attempt_no", 1),
        "status": manifest["status"],
        "completed": bool(final_data) and not final_data.get("parse_error", False),
        "decision": (final_data or {}).get("decision"),
        "workflow_status": (final_data or {}).get("workflow_status"),
        "findings_paths": (final_data or {}).get("findings_paths"),
        "wall_seconds": manifest["wall_seconds"],
        "model": manifest["model"], "effort": manifest["effort"], "backend": manifest["backend"],
        "behavior": manifest["behavior"],
        "invariant_evidence": evidence_stats(evidence),
        "skills_tree_sha256": attempt["skills_tree_sha256"],
        "prior_tree_sha256": attempt["prior_tree_sha256"],
        "graded": None,
    }
    write_json(out / "run.json", summary)
    b = manifest["behavior"]
    print(f"{arm} {case_id} r{rep}: {manifest['status']} decision={summary['decision']} "
          f"workflow={summary['workflow_status']} findings={len(summary['findings_paths'] or [])} "
          f"${b['cost_usd']} {manifest['wall_seconds']:.0f}s contaminated={b['network_audit']['contaminated']}", flush=True)
    return summary, manifest


def plan(args) -> list[tuple[str, str, int]]:
    cases = list(CASE_IDS) if args.all_cases else (args.cases or [])
    rng = random.Random(f"inv-e2e-{args.seed}")
    jobs = []
    for rep in args.reps:
        for case_id in cases:
            arms = list(args.arms)
            rng.shuffle(arms)
            jobs += [(arm, case_id, rep) for arm in arms]
    return jobs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--arm", action="append", dest="arms", required=True)
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--all-cases", action="store_true")
    parser.add_argument("--rep", action="append", dest="reps", type=int)
    parser.add_argument("--jobs", type=int, default=1, help="parallel runs; keep 1 under a 5-hour usage window")
    parser.add_argument("--max-attempts", type=int, default=10, help="usage-limit retries per run")
    parser.add_argument("--backend", default="claude", choices=("claude", "codex"))
    parser.add_argument("--model")
    parser.add_argument("--effort")
    parser.add_argument("--timeout", type=int, default=14400, help="seconds per run (blind protocol: 4 h)")
    parser.add_argument("--budget", type=float, default=100.0, help="USD cap per run (claude backend)")
    parser.add_argument("--seed", default="1")
    parser.add_argument("--plan", action="store_true")
    args = parser.parse_args()
    args.reps = args.reps or [1]
    for arm in args.arms:
        check_arm(arm)
    for case_id in (CASE_IDS if args.all_cases else args.cases or []):
        check_case(case_id)
    jobs = plan(args)
    if not jobs:
        raise SystemExit("nothing to run: give --case or --all-cases")
    if args.plan:
        for job in jobs:
            print(*job)
        return 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_one, arm, case_id, rep, args) for arm, case_id, rep in jobs]
        results = []
        for (arm, case_id, rep), fut in zip(jobs, futures):
            try:
                results.append(fut.result())
            except StopQueue as exc:
                results.append({"arm": arm, "case_id": case_id, "rep": rep, "status": "QUEUE_STOPPED", "error": str(exc)})
                print(f"QUEUE STOPPED: {exc}", flush=True)
            except Exception as exc:  # keep the batch going; record the error
                results.append({"arm": arm, "case_id": case_id, "rep": rep, "status": "RUNNER_ERROR", "error": repr(exc)})
                print(f"{arm} {case_id} r{rep}: RUNNER_ERROR {exc!r}", flush=True)
    return 0 if all(r.get("status") == "EXITED_0" for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
