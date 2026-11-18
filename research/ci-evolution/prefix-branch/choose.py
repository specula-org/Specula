"""Pick recorded runs and branch points for branch.py.

Each trace is replayed against the suite. At every recorded step the script records which of the update's affected
actions are enabled and which one the recording itself took. An affected action that is enabled but not taken is an
alternative the recording never tried; branching there is what branch.py is for. Points are ranked by how rare their
untried alternatives are across all the given traces, so an alternative that is open at only a few steps outranks
one that is open almost everywhere.

The same data also says which affected actions the whole trace suite never takes, or never even enables.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import tempfile
from collections import Counter
from pathlib import Path

from branch import MODULE, build, replay_config, run_tlc
from check import ROOT, top_level_definitions


def base_actions(spec: Path, probes: list[dict]) -> dict[int, str]:
    """For `MC...` wrappers, the base action they call, so a recorded event can be matched to them."""
    definitions = top_level_definitions((spec / "MC.tla").read_text()) if (spec / "MC.tla").exists() else {}
    found = {}
    for probe in probes:
        name = probe["label"].split(" ")[0]
        call = re.search(r"Original!(\w+)\(", definitions.get(name, ""))
        if call:
            found[probe["index"]] = call.group(1)
    return found


def replay(spec: Path, trace: Path, args: argparse.Namespace, work: Path) -> dict:
    events = sum(1 for line in trace.read_text().splitlines() if '"trace"' in line)
    options = argparse.Namespace(
        limits=args.limits,
        actions=args.actions,
        settle="next",
        replay=args.replay,
        guard="",
        constraint=False,
        settled="",
        after=0,
        checks="",
        ignore=None,
        steps=0,
        domain=args.domain,
    )
    module, cfg, info = build(options, spec, events, set(filter(None, args.domains.split(","))))
    probes = info["probes"]
    wrapped = base_actions(spec, probes)
    direct = [p["index"] for p in probes if p["index"] not in wrapped]
    count = len(probes)
    lines = [
        "SelEnabled == {k \\in 1.."
        + str(count)
        + " : "
        + "CASE "
        + " [] ".join(f"k = {p['index']} -> ENABLED PBProbe{p['index']}" for p in probes)
        + "}",
        "SelTaken == {k \\in {"
        + ", ".join(map(str, direct))
        + "} : "
        + ("CASE " + " [] ".join(f"k = {k} -> PBProbe{k}" for k in direct) if direct else "FALSE")
        + "}",
        "SelRecord == IF l' = l + 1",
        '    THEN PrintT(<<"select", l, logline.event, SelEnabled, SelTaken>>) ELSE TRUE',
    ]
    module = module.rsplit("=" * 77, 1)[0] + "\n".join(lines) + "\n" + "=" * 77 + "\n"
    (work / f"{MODULE}.tla").write_text(module)
    run = argparse.Namespace(heap=args.heap, steps_total=0, seed=1)
    result = run_tlc(
        work, replay_config(cfg, events - 1) + "ACTION_CONSTRAINT SelRecord\n", run, trace, False, args.seconds
    )
    log = (work / "tlc.log").read_text(errors="replace")
    steps: dict[int, dict] = {}
    for line, event, enabled, taken in re.findall(
        r'<< ?"select", (\d+), "(\w+)", \{([^}]*)\}, \{([^}]*)\} ?>>', re.sub(r"\s+", " ", log)
    ):
        step = steps.setdefault(int(line) - 2, {"event": event, "enabled": set(), "taken": set()})
        step["enabled"] |= {int(k) for k in enabled.split(",") if k.strip()}
        step["taken"] |= {int(k) for k in taken.split(",") if k.strip()}
    for step in steps.values():
        step["taken"] |= {k for k, base in wrapped.items() if base == step["event"]}
        step["open"] = step["enabled"] - step["taken"]
    return {
        "trace": trace.name,
        "events": events - 1,
        "replayed": result["violated"] == "PBReplayed",
        "reached": max(steps, default=-1) + 1,
        "error": result["error"],
        "seconds": result["seconds"],
        "probes": probes,
        "steps": steps,
    }


def rank(runs: list[dict], top: int) -> None:
    """Score every point by the rarity of its untried alternatives across all runs, and keep the best `top`."""
    open_at = Counter(k for run in runs for step in run["steps"].values() for k in step["open"])
    for run in runs:
        scored = [
            (sum(1 / open_at[k] for k in step["open"]), point) for point, step in run["steps"].items() if step["open"]
        ]
        scored.sort(key=lambda x: (-x[0], x[1]))
        run["points"] = sorted(point for _, point in scored[:top])
        run["score"] = round(sum(score for score, _ in scored[:top]), 4)


def summary(runs: list[dict]) -> dict:
    labels = {p["index"]: p["label"] for p in runs[0]["probes"]} if runs else {}
    rows = {}
    for k, label in labels.items():
        rows[f"{k} {label}"] = {
            "enabled_steps": sum(k in s["enabled"] for r in runs for s in r["steps"].values()),
            "taken_steps": sum(k in s["taken"] for r in runs for s in r["steps"].values()),
            "open_steps": sum(k in s["open"] for r in runs for s in r["steps"].values()),
            "traces_taking_it": sorted(r["trace"] for r in runs if any(k in s["taken"] for s in r["steps"].values())),
        }
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path)
    parser.add_argument("traces", type=Path, nargs="+")
    parser.add_argument("--limits", default="Update_full.cfg")
    parser.add_argument("--actions", default="AffectedActions")
    parser.add_argument("--replay", default="strict", help="'strict' (TraceNext) or a step formula over logline")
    parser.add_argument("--domains", default="", help="constants to take from --limits instead of the trace")
    parser.add_argument("--domain", action="append", default=[], metavar="NAME=VALUE", help="as in branch.py")
    parser.add_argument("--top", type=int, default=10, help="branch points to keep per trace")
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--heap", default="4g")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    spec = args.spec.resolve()
    work = Path(tempfile.mkdtemp(prefix="prefix-select-"))
    runs = []
    try:
        for path in spec.glob("*.tla"):
            shutil.copy(path, work / path.name)
        for trace in args.traces:
            runs.append(replay(spec, trace.resolve(), args, work))
            print(f"{trace.name}: replayed {runs[-1]['replayed']} ({runs[-1]['reached']}/{runs[-1]['events']})")
    finally:
        shutil.rmtree(work, ignore_errors=True)
    rank(runs, args.top)
    args.out.mkdir(parents=True, exist_ok=True)
    result = {
        "spec": str(spec).replace(str(ROOT), "$SPECULA"),
        "replay": args.replay,
        "actions": summary(runs),
        "traces": [
            {
                "trace": r["trace"],
                "events": r["events"],
                "replayed": r["replayed"],
                "reached": r["reached"],
                "error": r["error"],
                "seconds": r["seconds"],
                "score": r.get("score"),
                "points": r.get("points", []),
                "open": {
                    str(point): sorted(step["open"]) for point, step in sorted(r["steps"].items()) if step["open"]
                },
            }
            for r in runs
        ],
    }
    (args.out / "select.json").write_text(json.dumps(result, indent=1) + "\n")
    for r in sorted(result["traces"], key=lambda r: -(r["score"] or 0)):
        print(f"{r['trace']:<40} score {r['score']} points {r['points']}")


if __name__ == "__main__":
    main()
