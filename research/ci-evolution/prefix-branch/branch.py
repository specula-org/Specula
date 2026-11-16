"""Search for update bugs by branching from a recorded run instead of from Init.

The run is a trace that `Trace.tla` replays. Each simulated behavior replays it up to a random step, takes one of
the update's affected actions there, and then lets the system settle: the parts of the spec's reactive definition
take turns, so pending work such as persisting, sending and delivering keeps moving. The suite's invariants are
checked from the branch onwards. Branch steps past the end of the recorded run are taken while it settles.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "update-coverage"))

from check import ROOT, affected_probes, disjuncts, split_config, strip_comments, top_level_definitions  # noqa: E402

MODULE = "PrefixBranch"
SPEC_DEF = re.compile(r"^\s*(\w+)\s*/\\\s*\[\]\[(\w+)\]_(\w+)", re.S)
CONSTANT_LINE = re.compile(r"^\s*(\w+)\s*(<-|=)\s*(.+?)\s*$")


def extends_chain(spec: Path, module: str, seen: set[str] | None = None) -> list[str]:
    seen = set() if seen is None else seen
    path = spec / f"{module}.tla"
    if module in seen or not path.exists():
        return []
    seen.add(module)
    match = re.search(r"^EXTENDS\s+([^\n]+)", strip_comments(path.read_text()), re.M)
    chain = [module]
    for name in match.group(1).split(",") if match else []:
        chain += extends_chain(spec, name.strip(), seen)
    return chain


def declared_variables(spec: Path, module: str) -> list[str]:
    text = strip_comments((spec / f"{module}.tla").read_text())
    names: list[str] = []
    for match in re.finditer(r"^VARIABLES?\s+(.+?)(?=^\S|\Z)", text, re.M | re.S):
        names += [n.strip() for n in match.group(1).replace("\n", " ").split(",") if n.strip()]
    return names


def constants(cfg_text: str) -> dict[str, str]:
    found: dict[str, str] = {}
    section = None
    for line in strip_comments(cfg_text).splitlines():
        words = line.split()
        if words and re.fullmatch(r"[A-Z_]+", words[0]):
            section, line = words[0], line.split(words[0], 1)[1]
        match = CONSTANT_LINE.match(line) if section in {"CONSTANT", "CONSTANTS"} else None
        if match:
            found[match.group(1)] = f"{match.group(2)} {match.group(3)}"
    return found


def section_names(cfg_text: str, keyword: str) -> list[str]:
    names: list[str] = []
    section = None
    for line in strip_comments(cfg_text).splitlines():
        words = line.split()
        if words and words[0].isupper() and re.fullmatch(r"[A-Z_]+", words[0]):
            section, words = words[0], words[1:]
        if section in {keyword, keyword + "S"}:
            names += words
    return names


def suite_checks(spec: Path, ignore: str | None) -> list[str]:
    names: list[str] = []
    for cfg in sorted(spec.glob("*.cfg")):
        for name, kind in split_config(cfg.read_text())[0].items():
            if kind == "invariant" and name not in names and not (ignore and re.search(ignore, name)):
                names.append(name)
    return names


def build(args: argparse.Namespace, spec: Path, trace_events: int, domains: set[str]) -> tuple[str, str, dict]:
    limits_text = (spec / args.limits).read_text()
    module = "Update" if args.limits.startswith("Update") else "MC"
    definitions: dict[str, str] = {}
    for name in extends_chain(spec, module):
        definitions.update(top_level_definitions((spec / f"{name}.tla").read_text()))
    spec_name = section_names(limits_text, "SPECIFICATION")[0]
    init, next_name, _vars = SPEC_DEF.match(definitions[spec_name]).groups()

    trace_chain = set(extends_chain(spec, "Trace"))
    extra = [
        v for name in extends_chain(spec, module) if name not in trace_chain for v in declared_variables(spec, name)
    ]
    if args.settle == "next":
        settle_parts = [next_name]
    else:
        settle_file, settle_def = args.settle.split(":")
        settle_parts = disjuncts(top_level_definitions((spec / settle_file).read_text())[settle_def])
    probes = affected_probes(spec / "Update.tla", args.actions)
    for name in extends_chain(spec, "Trace"):
        definitions.update(top_level_definitions((spec / f"{name}.tla").read_text()))
    wanted = args.checks.split(",") if args.checks else suite_checks(spec, args.ignore)
    checks = [name for name in wanted if name in definitions]
    skipped = [name for name in wanted if name not in definitions]
    constraints = section_names(limits_text, "CONSTRAINT") if args.constraint else []

    own = ["pbAt", "pbStep", "pbBranched", "pbSlot", "pbAction"]
    keep = ", ".join(extra)
    settle_keep = "" if args.settle == "next" or not keep else keep + ", "
    replay = "TraceNext" if args.replay == "strict" else args.replay
    start = f"TraceInit /\\ {init}" if args.replay == "strict" else f"{init} /\\ l = 2"
    lines = [
        f"{'-' * 30} MODULE {MODULE} {'-' * 30}",
        f"EXTENDS Trace, {module}, TLC",
        "CONSTANTS PBPoints, PBMaxSteps, PBAfter",
        f"VARIABLES {', '.join(own)}",
        f"pbVars == <<vars, l, {keep + ', ' if keep else ''}{', '.join(own)}>>",
        f"PBInit == {start} /\\ pbAt \\in PBPoints /\\ pbStep = 0 /\\ pbBranched = FALSE /\\ pbSlot = 1 /\\ pbAction = 0",
        f"PBReplay == /\\ ~pbBranched /\\ pbStep < pbAt /\\ l <= Len(TraceLog) /\\ {replay}",
        f"    /\\ l' = l + 1 /\\ pbStep' = pbStep + 1 /\\ UNCHANGED <<{keep + ', ' if keep else ''}pbAt, pbBranched, pbSlot, pbAction>>",
    ]
    for i, part in enumerate(settle_parts, 1):
        lines.append(f"PBSettle{i} ==\n    {part}")
    lines += [
        "PBPart(i) == CASE " + "\n    [] ".join(f"i = {i} -> PBSettle{i}" for i in range(1, len(settle_parts) + 1)),
        f"PBParts == {len(settle_parts)}",
        "PBOffsets == {d \\in 0..(PBParts - 1) : ENABLED PBPart(((pbSlot - 1 + d) % PBParts) + 1)}",
        "PBFirst == CHOOSE d \\in PBOffsets : \\A e \\in PBOffsets : d <= e",
        "PBSettle == /\\ IF pbBranched THEN pbStep < pbAt + 1 + PBAfter ELSE l > Len(TraceLog) /\\ pbStep < pbAt",
        "    /\\ PBOffsets # {}",
        "    /\\ LET i == ((pbSlot - 1 + PBFirst) % PBParts) + 1 IN PBPart(i) /\\ pbSlot' = (i % PBParts) + 1",
        f"    /\\ pbStep' = pbStep + 1 /\\ UNCHANGED <<l, {settle_keep}pbAt, pbBranched, pbAction>>",
    ]
    for p in probes:
        lines.append(f"PBProbe{p.index} ==\n    {p.formula}")
    guard = f" /\\ ({args.guard})" if args.guard else ""
    lines += [
        "PBBranch == /\\ ~pbBranched /\\ pbStep = pbAt",
        "    /\\ \\/ " + "\n       \\/ ".join(f"PBProbe{p.index} /\\ pbAction' = {p.index}" for p in probes),
        "    /\\ pbBranched' = TRUE /\\ pbStep' = pbStep + 1 /\\ UNCHANGED <<l, pbAt, pbSlot>>" + guard,
        "PBSpec == PBInit /\\ [][PBReplay \\/ PBSettle \\/ PBBranch]_pbVars",
        "PBReplayed == l <= Len(TraceLog)",
        "PBAllPoints == 0..(PBMaxSteps - 1)",
        "PBConstraint == ~pbBranched \\/ (" + (" /\\ ".join(constraints) or "TRUE") + ")",
    ]
    lines += [f"PB_{name} == ~pbBranched \\/ {name}" for name in checks]
    if args.settled:
        lines.append("PBQuiet == pbBranched /\\ (pbStep = pbAt + 1 + PBAfter \\/ PBOffsets = {})")
        lines.append(f"PB_Settled == ~PBQuiet \\/ ({args.settled})")
    lines.append("=" * 77)

    trace_constants = constants((spec / "Trace.cfg").read_text())
    limit_constants = constants(limits_text)
    cfg = ["SPECIFICATION PBSpec", "CONSTANTS"]
    for name, binding in trace_constants.items():
        cfg.append(f"    {name} {limit_constants[name] if name in domains else binding}")
    for name, binding in limit_constants.items():
        if name not in trace_constants:
            cfg.append(f"    {name} {binding}")
    cfg += [
        "    PBPoints PBPOINTS",
        f"    PBMaxSteps = {args.steps or trace_events + 100}",
        f"    PBAfter = {args.after}",
    ]
    names = checks + (["Settled"] if args.settled else [])
    cfg += ["CONSTRAINT PBConstraint", "CHECK_DEADLOCK FALSE", "INVARIANTS"] + [f"    PB_{c}" for c in names]
    info = {
        "module": module,
        "init": init,
        "extra_variables": extra,
        "settle_parts": len(settle_parts),
        "probes": [{"index": p.index, "label": p.label} for p in probes],
        "checks": checks,
        "skipped_checks": skipped,
        "domains": sorted(domains),
    }
    return "\n".join(lines) + "\n", "\n".join(cfg) + "\n", info


def domain_candidates(spec: Path, limits: str) -> list[str]:
    trace_constants = constants((spec / "Trace.cfg").read_text())
    limit_constants = constants((spec / limits).read_text())
    return [
        name
        for name, binding in trace_constants.items()
        if binding.startswith("<-") and limit_constants.get(name, "").startswith("= {")
    ]


def replay_config(cfg: str, recorded: int) -> str:
    text = cfg.replace("PBPOINTS", f"= {{{recorded + 1}}}")
    text = re.sub(r"PBMaxSteps = \d+", f"PBMaxSteps = {recorded}", text)
    return text.split("INVARIANTS")[0] + "INVARIANT PBReplayed\n"


def replay_end(work: Path, module: str, cfg: str, args: argparse.Namespace, trace: Path, recorded: int):
    (work / f"{MODULE}.tla").write_text(module)
    (work / "cex.json").unlink(missing_ok=True)
    result = run_tlc(work, replay_config(cfg, recorded), args, trace, simulate=False, seconds=600, dump=True)
    if result["violated"] != "PBReplayed" or not (work / "cex.json").exists():
        return result, None
    return result, json.loads((work / "cex.json").read_text())["counterexample"]["state"][-1][1]


def run_tlc(
    work: Path, cfg: str, args: argparse.Namespace, trace: Path, simulate: bool, seconds: int, dump: bool = False
) -> dict:
    (work / "run.cfg").write_text(cfg)
    jars = (
        os.environ.get("TLA2TOOLS", str(ROOT / "lib/tla2tools.jar"))
        + ":"
        + os.environ.get("COMMUNITY_MODULES", str(ROOT / "lib/CommunityModules-deps.jar"))
    )
    command = ["java", f"-Xmx{args.heap}", "-XX:+UseParallelGC", "-Dtlc2.TLC.progressInterval=30", "-cp", jars]
    command += ["tlc2.TLC", "-workers", "1", "-nowarning", "-config", "run.cfg"]
    if dump and not simulate:
        command += ["-dumpTrace", "json", "cex.json"]
    if simulate:
        command += [
            "-simulate",
            "-depth",
            str(args.steps_total),
            "-seed",
            str(args.seed),
            "-dumpTrace",
            "json",
            "cex.json",
        ]
    command += [MODULE]
    env = dict(os.environ, JSON=str(trace))
    started = time.monotonic()
    with (work / "tlc.log").open("w") as log:
        process = subprocess.Popen(command, cwd=work, stdout=log, stderr=subprocess.STDOUT, env=env)
        try:
            process.wait(timeout=seconds)
            timed_out = False
        except subprocess.TimeoutExpired:
            timed_out = True
            process.send_signal(signal.SIGINT)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
    text = (work / "tlc.log").read_text(errors="replace")
    violated = re.search(r"Invariant (\S+) is violated", text)
    errors = [line for line in text.splitlines() if line.startswith("Error:")]
    traces = re.findall(r"([\d,]+) traces generated", text)
    distinct = re.findall(r"([\d,]+) distinct states found", text)
    return {
        "seconds": round(time.monotonic() - started, 1),
        "timed_out": timed_out,
        "violated": violated.group(1) if violated else None,
        "error": None if violated or not errors else " ".join(errors[:2]),
        "traces": int(traces[-1].replace(",", "")) if traces else None,
        "distinct": int(distinct[-1].replace(",", "")) if distinct else None,
    }


def changed(before: object, after: object, path: str = "", out: list[str] | None = None) -> list[str]:
    out = [] if out is None else out
    if isinstance(before, dict) and isinstance(after, dict) and set(before) == set(after):
        for key in before:
            changed(before[key], after[key], f"{path}.{key}" if path else key, out)
    elif isinstance(before, list) and isinstance(after, list) and len(before) == len(after) and len(before) <= 8:
        for i, (b, a) in enumerate(zip(before, after, strict=True), 1):
            changed(b, a, f"{path}[{i}]", out)
    elif before != after:
        out.append(f"{path}: {json.dumps(before)[:120]} -> {json.dumps(after)[:120]}")
    return out


def summarise(work: Path, info: dict, recorded: int) -> dict:
    states = json.loads((work / "cex.json").read_text())["counterexample"]["state"]
    branch = next(i for i, (_, s) in enumerate(states) if s["pbBranched"])
    before, after = states[branch - 1][1], states[branch][1]
    labels = {p["index"]: p["label"] for p in info["probes"]}
    own = {"pbAt", "pbStep", "pbBranched", "pbSlot", "pbAction", "l"}
    return {
        "states": len(states),
        "branch_step": after["pbAt"],
        "recorded_events_replayed": after["l"] - 2,
        "branch_during": "replay" if after["pbAt"] < recorded else "settle",
        "branch_action": labels.get(after["pbAction"], str(after["pbAction"])),
        "steps_after_branch": len(states) - 1 - branch,
        "branch_step_changes": changed(
            {k: v for k, v in before.items() if k not in own}, {k: v for k, v in after.items() if k not in own}
        )[:40],
        "changes_after_branch": changed(
            {k: v for k, v in after.items() if k not in own}, {k: v for k, v in states[-1][1].items() if k not in own}
        )[:60],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path)
    parser.add_argument("trace", type=Path)
    parser.add_argument("--limits", default="Update_full.cfg", help="config that supplies the checking limits")
    parser.add_argument("--actions", default="AffectedActions", help="Update.tla definition to branch with")
    parser.add_argument(
        "--settle",
        default="base.tla:ReactiveActions",
        help="FILE:DEF whose parts take turns, or 'next' for the spec's own next-state relation at random",
    )
    parser.add_argument("--replay", default="strict", help="'strict' (TraceNext) or a step formula over logline")
    parser.add_argument(
        "--domains",
        default="auto",
        help="constants to take from --limits instead of the trace; 'auto' keeps each one that leaves the replay unchanged",
    )
    parser.add_argument("--guard", default="", help="extra condition on the branch step")
    parser.add_argument(
        "--no-constraint", dest="constraint", action="store_false", help="ignore the limits config's state constraint"
    )
    parser.add_argument(
        "--settled", default="", help="condition that must hold once the system has settled after the branch"
    )
    parser.add_argument("--after", type=int, default=100, help="settle steps after the branch")
    parser.add_argument("--checks", default="", help="invariants to check (default: every invariant in the suite)")
    parser.add_argument("--ignore", default=r"NotReached$|NotAppended$")
    parser.add_argument("--steps", type=int, default=0, help="branch points and settle budget (default: run + 100)")
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--heap", default="4g")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    spec, trace = args.spec.resolve(), args.trace.resolve()
    events = sum(1 for line in trace.read_text().splitlines() if '"trace"' in line)
    recorded = events - 1
    args.out.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="prefix-branch-"))
    try:
        for path in spec.glob("*.tla"):
            shutil.copy(path, work / path.name)
        tried: dict[str, bool] = {}
        if args.domains == "auto":
            domains: set[str] = set()
            _, reference = replay_end(work, *build(args, spec, events, domains)[:2], args, trace, recorded)
            for name in domain_candidates(spec, args.limits) if reference else []:
                _, end = replay_end(work, *build(args, spec, events, domains | {name})[:2], args, trace, recorded)
                tried[name] = end == reference
                if tried[name]:
                    domains.add(name)
        else:
            domains = set(filter(None, args.domains.split(",")))
        module, cfg, info = build(args, spec, events, domains)
        info["domains_tried"] = tried
        max_steps = int(re.search(r"PBMaxSteps = (\d+)", cfg).group(1))
        args.steps_total = max_steps + args.after + 5
        (work / f"{MODULE}.tla").write_text(module)
        (args.out / f"{MODULE}.tla").write_text(module)
        (args.out / "run.cfg").write_text(cfg)

        replay = run_tlc(work, replay_config(cfg, recorded), args, trace, simulate=False, seconds=600)
        replay["complete"] = replay["violated"] == "PBReplayed"
        result = {"spec": str(spec).replace(str(ROOT), "$SPECULA"), "trace": trace.name, "recorded_events": recorded}
        result.update(
            {
                "settings": {
                    k: (sorted(v) if isinstance(v, set) else v)
                    for k, v in vars(args).items()
                    if k not in {"spec", "trace", "out"}
                },
                "build": info,
                "replay": replay,
            }
        )
        if replay["complete"]:
            search = run_tlc(work, cfg.replace("PBPOINTS", "<- PBAllPoints"), args, trace, True, args.seconds)
            if search["violated"]:
                search["counterexample"] = summarise(work, info, recorded)
            result["search"] = search
        log = (work / "tlc.log").read_text(errors="replace")
        log = log.replace(str(work), "$WORK").replace(str(ROOT), "$SPECULA").splitlines()
        kept = [line for line in log if not line.startswith((" ", "/\\", "\\", "Parsing file", "Semantic processing"))]
        (args.out / "tlc.log").write_text("\n".join(kept[:400]) + "\n")
        (args.out / "result.json").write_text(json.dumps(result, indent=1, default=str) + "\n")
        print(json.dumps({k: result[k] for k in ("replay", "search") if k in result}, indent=1, default=str))
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
