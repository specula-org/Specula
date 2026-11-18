"""Run envupdate.py on etcd V01-V03, learning from Init and from the recorded joint-autoleave run.

The suites and the recorded run are the ones prefix-branch/etcd/evaluate.py uses.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOL = HERE.parent / "envupdate.py"
ETCD = HERE.parents[1] / "etcd-v0-v3"
SPECS = ETCD / "agent-runs/inv-evidence/out/revised-spec"
TRACE = ETCD / "agent-runs/progress-probe-V03/out/joint-autoleave-prefix-inputs.ndjson"
VERSIONS = ("V01", "V02", "V03")
STARTS = {
    "init": [],
    "prefix": [
        "--trace",
        str(TRACE),
        "--replay",
        "MatchEvent(logline)",
        "--domains",
        "RequestId,PayloadWeights,EncodedWeights",
    ],
}


def run(version: str, start: str, args: argparse.Namespace) -> tuple[str, str, int]:
    out = args.reports / f"{version}-{start}"
    command = [sys.executable, str(TOOL), str(SPECS / version), "--out", str(out), "--heap", args.heap]
    command += STARTS[start] + ["--seconds", str(args.seconds), "--check-seconds", str(args.seconds)]
    done = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if done.returncode:
        (out / "error.txt").parent.mkdir(parents=True, exist_ok=True)
        (out / "error.txt").write_text(done.stderr[-4000:])
    return version, start, done.returncode


def table(reports: Path) -> str:
    rows = [
        "| Version | Start | Runs | Left out of focus | Seen outside focus | Change the view | EnvUpdate keeps | Check |",
        "|---|---|---:|---|---|---|---:|---|",
    ]
    for path in sorted(reports.glob("*/result.json")):
        r = json.loads(path.read_text())
        version, start = path.parent.name.split("-", 1)
        parts = r["parts"]
        left = sorted({p["label"] for p in parts if not p["in_focused_model"]})
        seen = sorted({p["label"] for p in parts if p["outside_focused"]})
        view = sorted({f"{p['label']}: {', '.join(p['changes_view'])}" for p in parts if p["changes_view"]})
        check = r["discharge_check"]
        verdict = "violated" if check["violated"] else (check["error"] or f"held on {check['traces']} runs")
        rows.append(
            f"| {version} | {start} | {r['learn']['traces']} | {len(left)} | {', '.join(seen) or '-'} "
            f"| {'; '.join(view) or '-'} | {len(r['env_update_keeps'])} of {len(r['view'])} | {verdict} |"
        )
    return "\n".join(rows) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--heap", default="3g")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--reports", type=Path, default=HERE / "reports")
    parser.add_argument("--table", action="store_true", help="only rebuild summary.md from existing reports")
    args = parser.parse_args()
    if not args.table:
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            jobs = [pool.submit(run, v, s, args) for v in VERSIONS for s in STARTS]
            for job in concurrent.futures.as_completed(jobs):
                print(*job.result())
    (args.reports / "summary.md").write_text(table(args.reports))
    print(table(args.reports))


if __name__ == "__main__":
    main()
