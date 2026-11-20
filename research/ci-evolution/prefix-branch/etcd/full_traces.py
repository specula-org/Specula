"""Branch from all 11 recorded runs of the etcd V02 incremental CI run (run 20260915-173143-1152) on V01-V03.

The runs were recorded on V02, so they are replayed by their inputs (`MatchEvent`), and on another version each is
cut to the longest prefix that version replays. Client-request domains are the values the run uses plus the values
in `Update_full.cfg`; the trace's own settings (request ids 1-32, weights 0-256) make one step have millions of
successors.

Phases:
  all       branch at every step of every run
  choose    rank branch points with choose.py
  chosen    branch only at the chosen points
  triage    sort each alarm: already broken by the recording, also found on the previous version, or new
  verdicts  rerun Qian's reviewed alarms (qian-verdicts.json) and compare with his verdicts
  table     rebuild the summaries

`--guard` keeps injected V2 requests to ones that leave a well-formed configuration, as upstream rejects the rest.
The recordings are not in this branch; pass the folder with `--traces`.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BRANCH = HERE.parent / "branch.py"
CHOOSE = HERE.parent / "choose.py"
SPECS = HERE.parents[1] / "etcd-v0-v3/agent-runs/inv-evidence/out/revised-spec"
VERSIONS = ("V01", "V02", "V03")
PREVIOUS = {"V02": "V01", "V03": "V02"}
LIMITS = {"RequestId": {1, 2, 3}, "PayloadWeights": {0, 1}, "EncodedWeights": {1, 2}}
PARAMS = {"RequestId": ("id", "parent"), "PayloadWeights": ("weight",), "EncodedWeights": ("encoded",)}
ROOT_REPORTS = HERE / "reports" / "full-traces"
REPORTS = ROOT_REPORTS
VERDICTS = json.loads((HERE / "qian-verdicts.json").read_text())["cases"]
IGNORE = r"NotReached$|NotAppended$|SourceAlignment"
INPUT_GUARD = (
    '\\A id \\in RequestId : (requests[id].status = "Unused" /\\ requests\'[id].status = "Invoked" '
    "/\\ requests'[id].kind = \"V2\") => ConfigWellFormed(ConfigCandidate(raft[requests'[id].node].config, "
    "[kind |-> \"V2\", id |-> id, changes |-> requests'[id].changes, transition |-> requests'[id].transition]))"
)


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


def branch(
    version: str, trace: Path, out: Path, args: argparse.Namespace, points: list[int] | None = None, **change: object
) -> int:
    opts = {"checks": args.checks, "guard": args.guard, "without": args.without} | change
    ignore = IGNORE + "".join(f"|^{name}$" for name in filter(None, str(opts["without"]).split(",")))
    command = [sys.executable, str(BRANCH), str(SPECS / version), str(trace), "--out", str(out), "--prefix", "auto"]
    command += ["--replay", "MatchEvent(logline)", "--domains", "", "--ignore", ignore]
    command += ["--seconds", str(args.seconds), "--heap", args.heap] + domain_args(used_values(trace))
    if opts["checks"]:
        command += ["--checks", str(opts["checks"])]
    if opts["guard"]:
        command += ["--guard", INPUT_GUARD]
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


def found(result: dict) -> str | None:
    violated = (result.get("search") or {}).get("violated")
    return violated.removeprefix("PB_") if violated else None


def results(folder: Path) -> dict[tuple[str, str], dict]:
    return {
        (path.parent.parent.name, path.parent.name): json.loads(path.read_text())
        for path in sorted(folder.glob("V0*/*/result.json"))
    }


def triage_one(version: str, recording: str, result: dict, previous: dict | None) -> str:
    alarm = found(result)
    if alarm in result.get("recording_violations", []):
        return "already broken by the recording"
    if version not in PREVIOUS:
        return "no previous version to compare"
    if previous is None:
        return "previous version not run"
    if alarm not in previous["build"]["checks"]:
        return "property not in the previous version"
    return "also found on the previous version" if found(previous) == alarm else "new in this version"


def triage(args: argparse.Namespace, traces: dict[str, Path]) -> None:
    runs = results(REPORTS)
    jobs = {}
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for (version, recording), result in runs.items():
            alarm = found(result)
            if not alarm or version not in PREVIOUS or alarm in result.get("recording_violations", []):
                continue
            out = REPORTS / "previous" / PREVIOUS[version] / f"{recording}-{alarm}"
            if not (out / "result.json").exists():
                jobs[(version, recording)] = pool.submit(
                    branch, PREVIOUS[version], traces[recording], out, args, checks=alarm, without=""
                )
        concurrent.futures.wait(jobs.values())
    rows = {}
    for (version, recording), result in runs.items():
        alarm = found(result)
        if alarm:
            path = REPORTS / "previous" / PREVIOUS.get(version, "-") / f"{recording}-{alarm}" / "result.json"
            previous = json.loads(path.read_text()) if path.exists() else None
            rows[f"{version}/{recording}"] = {
                "alarm": alarm,
                "triage": triage_one(version, recording, result, previous),
            }
    (REPORTS / "triage.json").write_text(json.dumps(rows, indent=1) + "\n")


def verdicts(args: argparse.Namespace, traces: dict[str, Path]) -> None:
    jobs = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for case in VERDICTS:
            for version in case["versions"]:
                for recording in case["recordings"]:
                    base = REPORTS / case["id"] / version / recording
                    checks = case["invariant"]
                    if case["id"] == "replaced":
                        checks += f",Revised{case['invariant']}"
                    jobs.append(pool.submit(branch, version, traces[recording], base, args, checks=checks, guard=True))
                    if case["id"] == "workload":
                        unguarded = REPORTS / case["id"] / version / f"{recording}-no-guard"
                        jobs.append(
                            pool.submit(branch, version, traces[recording], unguarded, args, checks=checks, guard=False)
                        )
        concurrent.futures.wait(jobs)


def verdict_rows() -> list[str]:
    rows = ["| Case | Qian's verdict | Version | Recording | What the tool reports now |", "|---|---|---|---|---|"]
    for case in VERDICTS:
        for version in case["versions"]:
            for recording in case["recordings"]:
                path = REPORTS / case["id"] / version / recording / "result.json"
                if not path.exists():
                    continue
                result = json.loads(path.read_text())
                skipped = result["build"]["skipped_checks"]
                if case["invariant"] in skipped:
                    got = f"skipped: {skipped[case['invariant']]}"
                elif case["invariant"] in result.get("recording_violations", []):
                    got = "broken by the recording itself, not reported as an alarm"
                elif found(result):
                    prev = REPORTS / case["id"] / PREVIOUS.get(version, "-") / recording / "result.json"
                    previous = json.loads(prev.read_text()) if prev.exists() else None
                    got = f"found ({triage_one(version, recording, result, previous)})"
                    other = case_for(recording, found(result), injected(result))
                    if other is not case:
                        got += f", but it is the {other['id']} case" if other else ", but a different counterexample"
                else:
                    got = "not found in the budget"
                if case["id"] == "workload":
                    loose = REPORTS / case["id"] / version / f"{recording}-no-guard" / "result.json"
                    if loose.exists():
                        loose_result = json.loads(loose.read_text())
                        same = case_for(recording, found(loose_result) or "", injected(loose_result)) is case
                        without = "not found" if not found(loose_result) else "found" if same else "a different alarm"
                        got += f"; without the guard: {without}"
                rows.append(f"| {case['id']} | {case['label']} | {version} | {recording} | {got} |")
    return rows


def injected(result: dict) -> str:
    cex = (result.get("search") or {}).get("counterexample") or {}
    return "\n".join(cex.get("branch_step_changes", []))


def case_for(recording: str, alarm: str, text: str = "") -> dict | None:
    for case in VERDICTS:
        if alarm in [case["invariant"], *case.get("also", [])] and recording in case["recordings"]:
            if re.search(case.get("match", ""), text):
                return case
    return None


def label(version: str, recording: str, alarm: str, text: str = "") -> str:
    case = case_for(recording, alarm, text)
    if case is None:
        return "not reviewed"
    if "real_on" in case:
        return "real, not from the update" if version in case["real_on"] else "noise"
    if case.get("update"):
        return "real, from the update" if version == case["update"] else "real, not from the update"
    return case["label"]


def matrix_rows(folder: Path) -> list[str]:
    rows = [
        "| Version | Run | Events | Replayed | Points | Result | Seconds | Runs | Branch step | Action |",
        "|---|---|---:|---:|---|---|---:|---:|---:|---|",
    ]
    for (version, variant), r in results(folder).items():
        search = r.get("search") or {}
        cex = search.get("counterexample") or {}
        replayed = r.get("replayable_prefix") or r["recorded_events"]
        result = found(r) or search.get("error") or ("none" if search else "not run")
        rows.append(
            f"| {version} | {variant} | {r['recorded_events']} | {replayed if r['replay']['complete'] else 'failed'} "
            f"| {r['settings'].get('points') or 'all'} | {result} | {search.get('seconds', '')} "
            f"| {search.get('traces') or ''} | {cex.get('branch_step', '')} | {cex.get('branch_action', '')} |"
        )
    return rows


def update_rows(labels: list[str]) -> list[str]:
    """Per update: time, CPU, cost, findings, and alarms split by Qian's labels."""
    rows = [
        "| Version | Run set | Wall s | TLC CPU s | Model cost | Alarms | Real, from the update "
        "| Real, not from the update | Noise | Not reviewed |",
        "|---|---|---:|---:|---|---:|---:|---:|---:|---:|",
    ]
    for name in labels:
        runs = results(ROOT_REPORTS / name)
        for version in VERSIONS:
            mine = {rec: r for (v, rec), r in runs.items() if v == version and not rec.endswith("-chosen")}
            if not mine:
                continue
            wall = sum(
                r.get("wall_seconds") or r["replay"]["seconds"] + (r.get("search") or {}).get("seconds", 0)
                for r in mine.values()
            )
            cpu = [r.get("tlc_cpu_seconds") for r in mine.values()]
            counts = {"real, from the update": 0, "real, not from the update": 0, "noise": 0, "not reviewed": 0}
            for rec, r in mine.items():
                if found(r):
                    counts[label(version, rec, found(r), injected(r))] += 1
            rows.append(
                f"| {version} | {name} | {wall:.0f} | {sum(cpu):.0f} | $0 | {sum(counts.values())} | "
                + " | ".join(str(n) for n in counts.values())
                + " |"
                if None not in cpu
                else f"| {version} | {name} | {wall:.0f} | not measured | $0 | {sum(counts.values())} | "
                + " | ".join(str(n) for n in counts.values())
                + " |"
            )
    return rows


def summary() -> str:
    lines = ["# Branching from the 11 V02 recordings", ""]
    lines += ["## Matrix", "", *matrix_rows(REPORTS), ""]
    triage_path = REPORTS / "triage.json"
    if triage_path.exists():
        lines += ["## Triage", "", "| Run | Alarm | Triage |", "|---|---|---|"]
        for run, row in json.loads(triage_path.read_text()).items():
            lines.append(f"| {run} | {row['alarm']} | {row['triage']} |")
        lines.append("")
    skipped = {
        f"{v}: {name}": reason
        for (v, _), r in results(REPORTS).items()
        for name, reason in (r["build"]["skipped_checks"] or {}).items()
    }
    if skipped:
        lines += ["## Skipped checks", ""] + [f"- {k}: {reason}" for k, reason in sorted(skipped.items())] + [""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("phase", choices=["all", "choose", "chosen", "triage", "verdicts", "table"])
    parser.add_argument("--traces", type=Path, help="folder with the recorded <scenario>.ndjson files")
    parser.add_argument("--work", type=Path, default=Path("/tmp/etcd-full-traces"))
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--heap", default="3g")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--checks", default="", help="invariants to check (default: every invariant in the suite)")
    parser.add_argument("--without", default="", help="comma-separated invariants to leave out")
    parser.add_argument("--guard", action="store_true", help="only inject V2 requests upstream would accept")
    parser.add_argument("--label", default="fixed", help="report subfolder")
    args = parser.parse_args()
    global REPORTS
    REPORTS = ROOT_REPORTS / args.label
    traces: dict[str, Path] = {}
    if args.phase != "table":
        args.work.mkdir(parents=True, exist_ok=True)
        for source in sorted(args.traces.glob("*.ndjson")):
            target = args.work / source.name
            if not target.exists():
                inputs_only(source, target)
            traces[target.stem] = target
    jobs = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        if args.phase == "all":
            for version in VERSIONS:
                for name, trace in traces.items():
                    jobs.append(pool.submit(branch, version, trace, REPORTS / version / name, args))
        elif args.phase == "choose":
            jobs = [pool.submit(choose, version, list(traces.values()), args) for version in VERSIONS]
        elif args.phase == "chosen":
            for version in VERSIONS:
                chosen = json.loads((REPORTS / f"{version}-choose" / "select.json").read_text())
                for row in chosen["traces"]:
                    if row["points"]:
                        name = Path(row["trace"]).stem
                        out = REPORTS / version / f"{name}-chosen"
                        jobs.append(pool.submit(branch, version, traces[name], out, args, row["points"]))
        concurrent.futures.wait(jobs)
    if args.phase == "triage":
        triage(args, traces)
    elif args.phase == "verdicts":
        verdicts(args, traces)
    if args.label == "verdicts":
        (REPORTS / "summary.md").write_text("\n".join(["# Qian's verdicts, rerun", "", *verdict_rows()]) + "\n")
    else:
        (REPORTS / "summary.md").write_text(summary())
    labels = [p.name for p in sorted(ROOT_REPORTS.iterdir()) if p.is_dir() and p.name != "verdicts"]
    (ROOT_REPORTS / "per-update.md").write_text("\n".join(update_rows(labels)) + "\n")
    print((REPORTS / "summary.md").read_text())


if __name__ == "__main__":
    main()
