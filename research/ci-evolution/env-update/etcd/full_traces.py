"""Run envupdate.py on etcd V02 from each of the 11 recorded runs of its incremental CI run.

Replay and domains are set up as in prefix-branch/etcd/full_traces.py. The summary lists, over all runs together,
which actions outside the focused model change fields the update's properties read.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "prefix-branch" / "etcd"))

from full_traces import domain_args, inputs_only, used_values  # noqa: E402

TOOL = HERE.parent / "envupdate.py"
SPEC = HERE.parents[1] / "etcd-v0-v3/agent-runs/inv-evidence/out/revised-spec/V02"
REPORTS = HERE / "reports" / "full-traces"


def run(trace: Path, args: argparse.Namespace) -> tuple[str, int]:
    out = REPORTS / trace.stem
    command = [sys.executable, str(TOOL), str(SPEC), "--out", str(out), "--trace", str(trace)]
    command += ["--replay", "MatchEvent(logline)", "--heap", args.heap, "--seconds", str(args.seconds)]
    command += ["--check-seconds", str(args.seconds)] + domain_args(used_values(trace))
    done = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if done.returncode:
        out.mkdir(parents=True, exist_ok=True)
        (out / "error.txt").write_text(done.stderr[-4000:])
    return trace.stem, done.returncode


def table() -> str:
    rows = [
        "| Run | Runs learned | Out-of-focus steps that change the view | EnvUpdate keeps | Check |",
        "|---|---:|---|---:|---|",
    ]
    union: dict[str, set[str]] = {}
    for path in sorted(REPORTS.glob("*/result.json")):
        r = json.loads(path.read_text())
        view = {p["label"]: p["changes_view"] for p in r["parts"] if p["changes_view"]}
        for label, fields in view.items():
            union.setdefault(label, set()).update(fields)
        check = r["discharge_check"]
        verdict = (
            f"violated by part {check['violated']['part']}"
            if check["violated"]
            else (check["error"] or f"held on {check['traces']} runs")
        )
        changes = "; ".join(f"{label}: {', '.join(fields)}" for label, fields in sorted(view.items())) or "-"
        rows.append(
            f"| {path.parent.name} | {r['learn']['traces']} | {changes} "
            f"| {len(r['env_update_keeps'])} of {len(r['view'])} | {verdict} |"
        )
    rows += ["", "All runs together:", ""]
    rows += [f"- {label}: {', '.join(sorted(fields))}" for label, fields in sorted(union.items())] or ["- none"]
    return "\n".join(rows) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--traces", type=Path, help="folder with the recorded <scenario>.ndjson files")
    parser.add_argument("--work", type=Path, default=Path("/tmp/etcd-full-traces"))
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--heap", default="3g")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--table", action="store_true", help="only rebuild summary.md")
    args = parser.parse_args()
    if not args.table:
        args.work.mkdir(parents=True, exist_ok=True)
        traces = []
        for source in sorted(args.traces.glob("*.ndjson")):
            target = args.work / source.name
            if not target.exists():
                inputs_only(source, target)
            traces.append(target)
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            for job in concurrent.futures.as_completed([pool.submit(run, t, args) for t in traces]):
                print(*job.result())
    REPORTS.mkdir(parents=True, exist_ok=True)
    (REPORTS / "summary.md").write_text(table())
    print(table())


if __name__ == "__main__":
    main()
