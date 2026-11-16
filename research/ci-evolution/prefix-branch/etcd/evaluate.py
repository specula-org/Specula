"""Run branch.py on etcd V01-V03 from the recorded joint-autoleave run and compare how the run continues.

The trace is the first 153 events of the run Qian's bug A probe used. Its post-states come from another model
revision, so it is replayed by its inputs (`MatchEvent`). The client-request domains come from `Update_full.cfg`
because the trace's own settings make one step have millions of successors.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BRANCH = HERE.parent / "branch.py"
ETCD = HERE.parents[1] / "etcd-v0-v3"
SPECS = ETCD / "agent-runs/inv-evidence/out/revised-spec"
TRACE = ETCD / "agent-runs/progress-probe-V03/out/joint-autoleave-prefix-inputs.ndjson"
VERSIONS = ("V01", "V02", "V03")
RAWNODE_RULE = "\\A n \\in Server : raft'[n] # raft[n] => ~ready[n].active"
VARIANTS = {
    "rotate": [],
    "rotate-rawnode": ["--guard", RAWNODE_RULE],
    "random": ["--settle", "next"],
}
COMMON = ["--replay", "MatchEvent(logline)", "--domains", "RequestId,PayloadWeights,EncodedWeights"]


def run(version: str, variant: str, args: argparse.Namespace) -> tuple[str, str, int]:
    out = args.reports / f"{version}-{variant}"
    command = [sys.executable, str(BRANCH), str(SPECS / version), str(TRACE), "--out", str(out)]
    command += COMMON + VARIANTS[variant] + ["--seconds", str(args.seconds), "--seed", str(args.seed)]
    if args.checks:
        command += ["--checks", args.checks]
    done = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    return version, variant, done.returncode


def table(reports: Path) -> str:
    rows = [
        "| Version | Continuation | Replay | Result | Seconds | Runs | Branch | Action | Steps after |",
        "|---|---|---|---|---:|---:|---|---|---:|",
    ]
    for path in sorted(reports.glob("*/result.json")):
        r = json.loads(path.read_text())
        version, variant = path.parent.name.split("-", 1)
        search = r.get("search") or {}
        cex = search.get("counterexample") or {}
        replay = f"all {r['recorded_events']} steps" if r["replay"]["complete"] else "failed"
        found = search.get("violated") or search.get("error") or ("budget used" if search.get("timed_out") else "none")
        branch = f"step {cex['branch_step']} ({cex['branch_during']})" if cex else ""
        rows.append(
            f"| {version} | {variant} | {replay} | {found.removeprefix('PB_')} | {search.get('seconds', '')} "
            f"| {search.get('traces') or ''} | {branch} | {cex.get('branch_action', '')} "
            f"| {cex.get('steps_after_branch', '')} |"
        )
    return "\n".join(rows) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("versions", nargs="*", default=list(VERSIONS), choices=VERSIONS)
    parser.add_argument("--variants", nargs="*", default=list(VARIANTS), choices=list(VARIANTS))
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--checks", default="")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--reports", type=Path, default=HERE / "reports")
    parser.add_argument("--table", action="store_true", help="only rebuild the summary table")
    args = parser.parse_args()
    if not args.table:
        jobs = [(v, w) for v in args.versions for w in args.variants]
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            for version, variant, code in pool.map(lambda job: run(*job, args), jobs):
                print(f"{version} {variant}: exit {code}", flush=True)
    (args.reports / "summary.md").write_text(table(args.reports))
    print((args.reports / "summary.md").read_text())


if __name__ == "__main__":
    main()
