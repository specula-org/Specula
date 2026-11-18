"""Stage 2 of the property-evidence-ledger experiment (#188 section 3.2).

Reruns two arms of ../inv-ablation with the annotated input model in place of old/spec:
  L0 = A0 prompt + prompts/ledger-addendum.md   (judge only, no execution)
  L2 = A2 prompt + prompts/ledger-addendum.md   (judge + executed evidence, sandboxed)
on V01 (input: V00 model) and V03 (input: V02 model).

Everything else is ../inv-ablation/run.py unchanged: same packet rebuild and hash check, model,
effort, tools, budgets, sandbox and audit. The annotated spec files are overlaid on old/spec
after the packet is verified, and their hashes are recorded in each run.json.

Runs are sequential (one at a time). A run whose results/<run>/ exists is skipped, so rerunning
the same command resumes. A usage-limit failure is moved to $LEDGER_WORK/invalid/ and retried
after the reset time; other API failures are left for the next pass of queue.sh.

Usage:
  python3 run_ledger.py plan                 # list the jobs and which are done
  python3 run_ledger.py run [--reps 1]       # run every missing job, in rep-major order
  python3 run_ledger.py summarize
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ABLATION = HERE.parent / "inv-ablation"
LEDGER_WORK = Path(os.environ.get("LEDGER_WORK", "/mydata/bingzhuo/inv-evidence-ledger"))

spec = importlib.util.spec_from_file_location("ablation_run", ABLATION / "run.py")
ab = importlib.util.module_from_spec(spec)
sys.modules["ablation_run"] = ab
spec.loader.exec_module(ab)

# Annotated models: input model of each transition.
ANNOTATED = {
    "V01": HERE / "annotated/V00-model/spec-final",
    "V03": HERE / "annotated/V02-model/spec-final",
}
ADDENDUM = (HERE / "prompts/ledger-addendum.md").read_text()
BASE_PROMPTS = {"L0": "prompts/A0-skill-rules.md", "L2": "prompts/A2-judge-evidence.md"}
TRANSITIONS = ["V01", "V03"]
ARM_ORDER = ["L0", "L2"]


def build_prompts() -> dict[str, str]:
    """Write prompts/L0.md and prompts/L2.md (base prompt + addendum); return arm -> absolute path."""
    out = {}
    for arm, base in BASE_PROMPTS.items():
        text = (ABLATION / base).read_text().rstrip("\n") + "\n" + ADDENDUM
        path = HERE / "prompts" / f"{arm}.md"
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
        out[arm] = str(path)  # absolute: ab.HERE / abs_path == abs_path
    return out


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


_original_prepare = ab.prepare


def prepare_with_ledger(transition: str, dest: Path) -> dict:
    packet = _original_prepare(transition, dest)
    spec_dir = dest / "old" / "spec"
    overlay = {}
    for f in sorted(ANNOTATED[transition].glob("*")):
        target = spec_dir / f.name
        if not target.exists():
            raise SystemExit(f"{transition}: annotated {f.name} has no counterpart in old/spec")
        data = f.read_bytes()
        if data != target.read_bytes():
            target.write_bytes(data)
            overlay[f.name] = sha256(data)
    packet["ledger_overlay"] = {"source": str(ANNOTATED[transition].relative_to(HERE)), "files": overlay}
    return packet


def configure() -> None:
    ab.ARMS = build_prompts()
    ab.EXECUTING = {"L2"}
    ab.RESULTS = HERE / "results"
    ab.WORK = LEDGER_WORK  # runs/ and invalid/ go here; ETCD and godeps stay with inv-ablation
    ab.MAX_ATTEMPTS = 30
    ab.prepare = prepare_with_ledger
    ab.RESULTS.mkdir(exist_ok=True)


def jobs(reps: int) -> list[tuple[str, str, int]]:
    return [(arm, t, rep) for rep in range(1, reps + 1) for t in TRANSITIONS for arm in ARM_ORDER]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["plan", "run", "summarize"])
    parser.add_argument("--reps", type=int, default=1)
    args = parser.parse_args()
    configure()
    if args.command == "summarize":
        ab.summarize()
        return
    todo = jobs(args.reps)
    if args.command == "plan":
        for arm, t, rep in todo:
            done = (ab.RESULTS / f"{arm}-{t}-r{rep}").exists()
            print(f"{arm}-{t}-r{rep}\t{'done' if done else 'todo'}")
        return
    for job in todo:  # strictly one at a time
        outcome = ab.run_one(*job)
        print(json.dumps(outcome), flush=True)
        if outcome.get("status") == "invalid" and "authenticat" in outcome.get("reason", "").lower():
            # Expired login: every remaining job would fail the same way. Stop this pass;
            # queue.sh waits and retries, and a fresh `claude` login lets the next pass proceed.
            print(json.dumps({"status": "auth failure, stopping pass"}), flush=True)
            ab.summarize()
            sys.exit(3)
    ab.summarize()


if __name__ == "__main__":
    main()
