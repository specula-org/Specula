"""Branch from all 11 recorded runs of the etcd V02 incremental CI run (run 20260915-173143-1152) on V01-V03.

The runs were recorded on V02, so they are replayed by their inputs (`MatchEvent`), and on another version each is
cut to the longest prefix that version replays. Client-request domains are the values the run uses plus the values
in `Update_full.cfg`; the trace's own settings (request ids 1-32, weights 0-256) make one step have millions of
successors.

Phases:
  all     branch at every step of every run
  choose  rank branch points with choose.py
  chosen  branch only at the chosen points
  table   rebuild reports/full-traces/summary.md

The recordings are not in this branch; pass the folder with `--traces`.
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
CHOOSE = HERE.parent / "choose.py"
SPECS = HERE.parents[1] / "etcd-v0-v3/agent-runs/inv-evidence/out/revised-spec"
VERSIONS = ("V01", "V02", "V03")
LIMITS = {"RequestId": {1, 2, 3}, "PayloadWeights": {0, 1}, "EncodedWeights": {1, 2}}
PARAMS = {"RequestId": ("id", "parent"), "PayloadWeights": ("weight",), "EncodedWeights": ("encoded",)}
REPORTS = HERE / "reports" / "full-traces"


def inputs_only(source: Path, target: Path) -> None:
    """Keep each event's inputs and drop every post-state but Init's, as for the 153-event prefix."""
    lines = []
    for line in source.read_text().splitlines():
        event = json.loads(line)
        if event.get("event") != "Init" and "post" in event:
            event["post"] = {"tag": "atom", "value": 0}
        lines.append(json.dumps(event, separators=(",", ":")))
    target.write_text("\n".join(lines) + "\n")


def used_values(trace: Path) -> dict[str, set[int]]:
    """Values the run uses for each client-request domain, anywhere in its events (entries inside messages too)."""
    found: dict[str, set[int]] = {name: set(values) for name, values in LIMITS.items()}

    def walk(value: object) -> None:
        if isinstance(value, dict):
            for key, inner in value.items():
                atom = inner.get("value") if isinstance(inner, dict) and inner.get("tag") == "atom" else None
                for name, keys in PARAMS.items():
                    if key in keys and isinstance(atom, int) and (atom > 0 or name == "PayloadWeights"):
                        found[name].add(atom)
                walk(inner)
        elif isinstance(value, list):
            for inner in value:
                walk(inner)

    for line in trace.read_text().splitlines():
        walk(json.loads(line).get("params", {}))
    return found


def domain_args(values: dict[str, set[int]]) -> list[str]:
    return [
        arg for name, vals in values.items() for arg in ("--domain", f"{name}={{{', '.join(map(str, sorted(vals)))}}}")
    ]


def common(args: argparse.Namespace) -> list[str]:
    checks = ["--checks", args.checks] if args.checks else []
    return [
        "--replay",
        "MatchEvent(logline)",
        "--domains",
        "",
        "--seconds",
        str(args.seconds),
        "--heap",
        args.heap,
    ] + checks


def branch(version: str, trace: Path, out: Path, args: argparse.Namespace, points: list[int] | None) -> int:
    command = [sys.executable, str(BRANCH), str(SPECS / version), str(trace), "--out", str(out), "--prefix", "auto"]
    command += common(args) + domain_args(used_values(trace))
    if points is not None:
        command += ["--points", ",".join(map(str, points))]
    out.mkdir(parents=True, exist_ok=True)
    done = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if done.returncode:
        (out / "error.txt").write_text(done.stderr[-4000:])
    return done.returncode


def choose(version: str, traces: list[Path], args: argparse.Namespace) -> int:
    union: dict[str, set[int]] = {name: set() for name in LIMITS}
    for trace in traces:
        for name, vals in used_values(trace).items():
            union[name] |= vals
    out = REPORTS / f"{version}-choose"
    command = [sys.executable, str(CHOOSE), str(SPECS / version), *map(str, traces), "--out", str(out)]
    command += ["--replay", "MatchEvent(logline)", "--seconds", "1800", "--heap", args.heap] + domain_args(union)
    return subprocess.run(command, stdout=subprocess.DEVNULL).returncode


def table() -> str:
    rows = [
        "| Version | Run | Events | Replayed | Points | Result | Seconds | Runs | Branch step | Action |",
        "|---|---|---:|---:|---|---|---:|---:|---:|---|",
    ]
    for path in sorted(REPORTS.glob("*/*/result.json")):
        r = json.loads(path.read_text())
        version, variant = path.parent.parent.name, path.parent.name
        search = r.get("search") or {}
        cex = search.get("counterexample") or {}
        replayed = r.get("replayable_prefix") or r["recorded_events"]
        found = search.get("violated") or search.get("error") or ("none" if search else "not run")
        rows.append(
            f"| {version} | {variant} | {r['recorded_events']} | {replayed if r['replay']['complete'] else 'failed'} "
            f"| {r['settings'].get('points') or 'all'} | {found.removeprefix('PB_')} | {search.get('seconds', '')} "
            f"| {search.get('traces') or ''} | {cex.get('branch_step', '')} | {cex.get('branch_action', '')} |"
        )
    return "\n".join(rows) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("phase", choices=["all", "choose", "chosen", "table"])
    parser.add_argument("--traces", type=Path, help="folder with the recorded <scenario>.ndjson files")
    parser.add_argument("--work", type=Path, default=Path("/tmp/etcd-full-traces"))
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--heap", default="3g")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--checks", default="", help="invariants to check (default: every invariant in the suite)")
    parser.add_argument("--label", default="all-checks", help="report subfolder")
    args = parser.parse_args()
    global REPORTS
    REPORTS = REPORTS / args.label
    if args.phase != "table":
        args.work.mkdir(parents=True, exist_ok=True)
        traces = []
        for source in sorted(args.traces.glob("*.ndjson")):
            target = args.work / source.name
            if not target.exists():
                inputs_only(source, target)
            traces.append(target)
    jobs = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        if args.phase == "all":
            for version in VERSIONS:
                for trace in traces:
                    jobs.append(pool.submit(branch, version, trace, REPORTS / version / trace.stem, args, None))
        elif args.phase == "choose":
            jobs = [pool.submit(choose, version, traces, args) for version in VERSIONS]
        elif args.phase == "chosen":
            for version in VERSIONS:
                chosen = json.loads((REPORTS / f"{version}-choose" / "select.json").read_text())
                for row in chosen["traces"]:
                    if row["points"]:
                        trace = args.work / row["trace"]
                        out = REPORTS / version / f"{trace.stem}-chosen"
                        jobs.append(pool.submit(branch, version, trace, out, args, row["points"]))
        for job in concurrent.futures.as_completed(jobs):
            print(job.result())
    (REPORTS / "summary.md").write_text(table())
    print(table())


if __name__ == "__main__":
    main()
