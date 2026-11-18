#!/usr/bin/env python3
"""Pipelined pilot driver: annotate the next case while the current case runs its last arm.

    python3 pipeline.py --case case-002 --case case-003 --case case-004 [--wait-log FILE]

For each case, in order:
  1. wait until its frozen annotation exists (annotate.py, started earlier in the background);
  2. wait until the previous case's runs have finished;
  3. prepare v0/v1/v2 workspaces (rep 1);
  4. run the arms one at a time in the fixed order v2, v0, v1 (run.py, one arm per call);
     just before the last arm, start annotate.py for the next case in the background.
The first case's annotation starts at once (the previous batch is assumed to be in its last arm).
--wait-log names a run log whose final "EXIT" line marks the end of an earlier batch.

Annotation sessions are fresh agents in the sandbox that see only the base revision of their
own case (annotate.py); nothing from other cases or runs is passed to them.
An annotation that fails its mechanical check is archived and retried once; a second failure
skips the case and is recorded. Every automatic decision is appended to WORK/pipeline-decisions.md.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

from common import HERE, RESULTS, WORK, check_case, read_json

ORDER = ("v2", "v0", "v1")
LOG = WORK / "pipeline.log"
DECISIONS = WORK / "pipeline-decisions.md"


def log(msg: str) -> None:
    line = f"{datetime.now():%Y-%m-%d %H:%M:%S} {msg}"
    print(line, flush=True)
    with LOG.open("a") as f:
        f.write(line + "\n")


def decide(msg: str) -> None:
    log("DECISION " + msg)
    with DECISIONS.open("a") as f:
        f.write(f"- {datetime.now():%Y-%m-%d %H:%M} {msg}\n")


def start_annotation(case_id: str, attempt: int) -> subprocess.Popen:
    out = (WORK / f"annotate-{case_id}.log").open("a")
    log(f"{case_id}: annotation attempt {attempt} started")
    return subprocess.Popen([sys.executable, str(HERE / "annotate.py"), "--case", case_id],
                            cwd=HERE, stdout=out, stderr=subprocess.STDOUT)


def wait_annotation(case_id: str, proc: subprocess.Popen) -> bool:
    for attempt in (1, 2):
        proc.wait()
        if (WORK / "annotated" / case_id / "manifest.json").exists():
            m = read_json(WORK / "annotated" / case_id / "manifest.json")
            log(f"{case_id}: annotation FROZEN {m['check']['status_counts']} warnings={len(m['check'].get('warnings', []))} "
                f"cost={m['sessions']['annotate']['cost_usd']}+{m['sessions']['review']['cost_usd']} "
                f"contaminated={m['sessions']['annotate']['contaminated']}/{m['sessions']['review']['contaminated']}")
            if m["check"].get("warnings"):
                decide(f"{case_id}: annotation has {len(m['check']['warnings'])} model-talk warnings; kept frozen, "
                       "listed for manual reading in the analysis (heuristic, not a failure)")
            return True
        if attempt == 2:
            break
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        src = WORK / "annotate" / case_id
        if src.exists():
            dest = WORK / "invalid" / f"annotate-{case_id}-failed-{stamp}"
            shutil.move(str(src), str(dest))
            decide(f"{case_id}: annotation not frozen (exit {proc.returncode}); archived to {dest}; retrying once")
        proc = start_annotation(case_id, 2)
    decide(f"{case_id}: annotation failed twice; case skipped")
    return False


def wait_log(path: Path) -> None:
    while not (path.exists() and "EXIT " in path.read_text(errors="replace")):
        time.sleep(60)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--case", action="append", dest="cases", required=True)
    parser.add_argument("--wait-log", type=Path)
    args = parser.parse_args()
    for c in args.cases:
        check_case(c)
    log(f"pipeline start: {args.cases}, arm order {ORDER}")
    procs = {args.cases[0]: start_annotation(args.cases[0], 1)}
    if args.wait_log:
        wait_log(args.wait_log)
        log(f"earlier batch finished ({args.wait_log})")
    for i, case_id in enumerate(args.cases):
        nxt = args.cases[i + 1] if i + 1 < len(args.cases) else None
        if not wait_annotation(case_id, procs[case_id]):
            if nxt and nxt not in procs:
                procs[nxt] = start_annotation(nxt, 1)
            continue
        # Resumable: prepare only arms without a workspace, run only arms without a result.
        missing = [a for a in ORDER if not (WORK / "attempts" / a / case_id / "r1" / "attempt.json").exists()]
        prep_args = [x for a in missing for x in ("--arm", a)]
        done = (subprocess.run([sys.executable, "prepare.py", *prep_args, "--case", case_id, "--rep", "1"],
                               cwd=HERE, capture_output=True, text=True) if missing
                else subprocess.CompletedProcess([], 0, "all arms already prepared", ""))
        log(f"{case_id}: prepare exit {done.returncode}: {done.stdout.strip()[-400:]} {done.stderr.strip()[-400:]}")
        if done.returncode != 0:
            decide(f"{case_id}: prepare failed; case skipped")
            if nxt and nxt not in procs:
                procs[nxt] = start_annotation(nxt, 1)
            continue
        for arm in ORDER:
            if arm == ORDER[-1] and nxt and nxt not in procs:
                procs[nxt] = start_annotation(nxt, 1)
            if (RESULTS / arm / case_id / "r1" / "run.json").exists():
                log(f"{case_id} {arm}: result exists, skipped")
                continue
            log(f"{case_id} {arm}: run start")
            r = subprocess.run([sys.executable, "run.py", "--arm", arm, "--case", case_id, "--rep", "1"],
                               cwd=HERE, capture_output=True, text=True)
            log(f"{case_id} {arm}: run exit {r.returncode}: {r.stdout.strip()[-600:]} {r.stderr.strip()[-600:]}")
    log("pipeline done")
    print("EXIT 0", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
