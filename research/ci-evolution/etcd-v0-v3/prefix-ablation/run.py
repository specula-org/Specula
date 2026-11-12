"""Equal-budget comparison of the V03 progress probe (bug B) and ordinary model checking.

Every run gets the same TLC settings and time budget. Inputs are checked against the
hashes recorded for the original probe before anything runs.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPERIMENT = HERE.parent
PROBE = EXPERIMENT / "agent-runs/progress-probe-V03"
SPECS = {version: EXPERIMENT / f"agent-runs/inv-evidence/out/revised-spec/{version}" for version in ("V02", "V03")}
DRIVERS = (PROBE / "out/drivers", HERE / "drivers")
TRACE = PROBE / "out/joint-autoleave-prefix-inputs.ndjson"
SPECULA = EXPERIMENT.parents[2]
BUDGET = 600  # the probe's original limit

RUNS = {
    "probe-v03": ("V03", "C03Clocked", "clocked-leadership.cfg", "prefix", "progress properties"),
    "probe-v02": ("V02", "C03Clocked", "clocked-leadership-v02.cfg", "prefix", "progress properties"),
    "probe-safety-v03": ("V03", "C03Clocked", "clocked-leadership-safety.cfg", "prefix", "safety invariants"),
    "free-153-v03": ("V03", "C03Free", "free-from-153.cfg", "prefix", "progress properties"),
    "free-151-v03": ("V03", "C03Free", "free-from-151.cfg", "prefix to event 151", "progress properties"),
    "free-41-v03": ("V03", "C03Free", "free-from-41.cfg", "prefix to event 41", "progress properties"),
    "free-1-v03": ("V03", "C03Free", "free-from-1.cfg", "Init", "progress properties"),
    "free-151-v02": ("V02", "C03Free", "free-from-151-v02.cfg", "prefix to event 151", "progress properties"),
    "ordinary-v03": ("V03", "MC", "MC.cfg", "Init", "safety invariants"),
    "ordinary-v2-v03": ("V03", "MC", "ordinary-v2.cfg", "Init", "safety invariants"),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_inputs() -> None:
    manifest = json.loads((PROBE / "input-manifest.json").read_text())
    for version, directory in SPECS.items():
        prefix = f"versions/{version}/spec/"
        expected = {key[len(prefix) :]: value for key, value in manifest.items() if key.startswith(prefix)}
        mismatched = [name for name, digest in expected.items() if sha256(directory / name) != digest]
        if mismatched:
            raise SystemExit(f"{directory} differs from the probe inputs: {mismatched}")


def outcome(log: str, timed_out: bool) -> str:
    if re.search(r"Temporal propert(?:y|ies) .*violated", log):
        return "liveness violation"
    violated = re.search(r"Invariant (\w+) is violated", log)
    if violated:
        return f"invariant {violated.group(1)} violated"
    if "Model checking completed. No error has been found" in log:
        return "completed, no error"
    if timed_out:
        return "budget exhausted, no error"
    if "out of memory" in log.lower():
        return "out of memory"
    return "error"


def counts(log: str) -> tuple[int | None, int | None]:
    final = re.findall(r"([\d,]+) states generated(?: \([^)]*\))?, ([\d,]+) distinct states found", log)
    if not final:
        return None, None
    generated, distinct = final[-1]
    return int(generated.replace(",", "")), int(distinct.replace(",", ""))


def trimmed(log: str) -> str:
    """Drop TLC's per-state variable dumps; keep statistics and the counterexample's action sequence."""
    return "".join(line for line in log.splitlines(keepends=True) if not line.startswith(("/\\", " ", "\t")))


def depth(log: str) -> int | None:
    complete = re.findall(r"The depth of the complete state graph search is (\d+)", log)
    if complete:
        return int(complete[-1])
    progress = re.findall(r"Progress\((\d+)\)", log)
    return int(progress[-1]) if progress else None


def run(name: str, seconds: int, heap: str, jars: str, results: Path) -> dict[str, object]:
    version, module, config, start, properties = RUNS[name]
    work = Path(tempfile.mkdtemp(prefix=f"prefix-ablation-{name}-"))
    for source in (SPECS[version], *DRIVERS):
        for path in source.iterdir():
            if path.suffix in (".tla", ".cfg"):
                shutil.copy(path, work / path.name)
    command = [
        "java",
        f"-Xmx{heap}",
        "-Dtlc2.TLC.progressInterval=10",
        "-cp",
        jars,
        "tlc2.TLC",
        "-workers",
        "1",
        "-nowarning",
        "-dumpTrace",
        "json",
        "counterexample.json",
        "-config",
        config,
        module,
    ]
    env = {**os.environ, "JSON": str(TRACE)}
    started = time.monotonic()
    with (work / "tlc.log").open("w") as log:
        process = subprocess.Popen(command, cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT)
        try:
            process.wait(timeout=seconds)
            timed_out = False
        except subprocess.TimeoutExpired:
            timed_out = True
            process.send_signal(signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
    elapsed = time.monotonic() - started
    text = (work / "tlc.log").read_text(errors="replace")
    generated, distinct = counts(text)
    record: dict[str, object] = {
        "name": name,
        "version": version,
        "module": module,
        "config": config,
        "start": start,
        "properties": properties,
        "seconds_limit": seconds,
        "elapsed_seconds": round(elapsed, 2),
        "exit_code": process.returncode,
        "outcome": outcome(text, timed_out),
        "generated": generated,
        "distinct": distinct,
        "depth": depth(text),
        "tlc": next((line for line in text.splitlines() if line.startswith("TLC2 Version")), None),
        "java": subprocess.run(["java", "-version"], capture_output=True, text=True).stderr.splitlines()[0],
        "machine": f"{platform.system()} {platform.machine()}",
        "command": [part.replace(str(SPECULA), "$SPECULA") for part in command],
    }
    destination = results / (name if seconds == BUDGET else f"{name}-{seconds}s")
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "tlc.log").write_text(trimmed(text).replace(str(SPECULA), "$SPECULA"))
    (destination / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    shutil.rmtree(work, ignore_errors=True)
    return record


def summarize(results: Path) -> str:
    rows = [
        "| Run | Version | Start | Checks | Budget | Outcome | Distinct states | Depth | Wall time |",
        "|---|---|---|---|---:|---|---:|---:|---:|",
    ]
    saved = [json.loads(path.read_text()) | {"label": path.parent.name} for path in results.glob("*/run.json")]
    saved.sort(key=lambda record: (list(RUNS).index(record["name"]), record["seconds_limit"]))
    for record in saved:
        name = record["name"]
        log = (results / record["label"] / "tlc.log").read_text(errors="replace")
        _, distinct = counts(log)
        reached = depth(log)
        cells = [
            f"`{record['label']}`",
            record["version"],
            RUNS[name][3],
            RUNS[name][4],
            f"{record['seconds_limit']} s",
            outcome(log, record["outcome"].startswith("budget")),
            "-" if distinct is None else str(distinct),
            "-" if reached is None else str(reached),
            f"{record['elapsed_seconds']} s",
        ]
        rows.append("| " + " | ".join(cells) + " |")
    return "\n".join(rows) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("runs", nargs="*", default=list(RUNS), choices=list(RUNS))
    parser.add_argument("--seconds", type=int, default=BUDGET, help="budget for every run")
    parser.add_argument("--heap", default="6g")
    parser.add_argument("--jobs", type=int, default=1, help="runs in parallel; each TLC run uses one worker")
    parser.add_argument("--results", type=Path, default=HERE / "results")
    parser.add_argument("--summarize", action="store_true", help="only rebuild results/summary.md from saved logs")
    args = parser.parse_args()
    if args.summarize:
        (args.results / "summary.md").write_text(summarize(args.results))
        print((args.results / "summary.md").read_text())
        return
    tla2tools = Path(os.environ.get("TLA2TOOLS", SPECULA / "lib/tla2tools.jar"))
    community = Path(os.environ.get("COMMUNITY_MODULES", SPECULA / "lib/CommunityModules-deps.jar"))
    jars = f"{tla2tools}:{community}"
    verify_inputs()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run, name, args.seconds, args.heap, jars, args.results) for name in args.runs]
        for future in concurrent.futures.as_completed(futures):
            record = future.result()
            print(
                f"{record['name']}: {record['outcome']}, {record['distinct']} distinct, {record['elapsed_seconds']} s"
            )


if __name__ == "__main__":
    main()
