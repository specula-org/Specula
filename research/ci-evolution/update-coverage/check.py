"""Check whether an update's checking configs exercise its affected actions with the suite's checks enabled.

Specula's incremental workflow writes `Update.tla` with an `AffectedActions` definition that lists the
actions the update changes. This script runs every checking config in a short TLC simulation, records
which affected actions actually occur, and then reports, for every invariant and property the suite
enables somewhere, the affected actions it is never checked against.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PROBE_MODULE = "UpdateCoverage"
CFG_KEYWORDS = {
    "CONSTANT",
    "CONSTANTS",
    "INIT",
    "NEXT",
    "SPECIFICATION",
    "INVARIANT",
    "INVARIANTS",
    "PROPERTY",
    "PROPERTIES",
    "CONSTRAINT",
    "CONSTRAINTS",
    "ACTION_CONSTRAINT",
    "ACTION_CONSTRAINTS",
    "SYMMETRY",
    "VIEW",
    "CHECK_DEADLOCK",
    "ALIAS",
    "POSTCONDITION",
}
CHECK_SECTIONS = {"INVARIANT": "invariant", "INVARIANTS": "invariant", "PROPERTY": "property", "PROPERTIES": "property"}
DEFINITION = re.compile(r"^([A-Za-z_]\w*)(\([^)]*\))?\s*==(.*)$")
ACTION_NAME = re.compile(r"(?:Original!)?\b((?:MC)?[A-Z]\w*)\(")
NOT_ACTIONS = {"Framed", "Last", "SeqSet", "Len", "Cardinality", "UNCHANGED"}


@dataclass
class Probe:
    index: int
    group: str
    label: str
    formula: str


@dataclass
class Config:
    name: str
    module: str
    checks: dict[str, str] = field(default_factory=dict)
    taken: list[int] = field(default_factory=list)
    enabled: list[int] = field(default_factory=list)
    status: str = "not run"
    traces: int | None = None
    seconds: float | None = None
    retried: bool = False


def top_level_definitions(text: str) -> dict[str, str]:
    """Map each top-level definition name to its body; a body ends at the next line starting in column 0."""
    definitions: dict[str, str] = {}
    name = None
    body: list[str] = []
    for line in text.splitlines():
        if line[:1].strip():
            if name:
                definitions[name] = "\n".join(body).strip("\n")
            match = DEFINITION.match(line)
            name = match.group(1) if match else None
            body = [match.group(3)] if match else []
        elif name:
            body.append(line)
    if name:
        definitions[name] = "\n".join(body).strip("\n")
    return definitions


def disjuncts(body: str) -> list[str]:
    lines = [line for line in strip_comments(body).splitlines() if line.strip()]
    if not lines or not lines[0].lstrip().startswith("\\/"):
        return [body.strip()]
    indent = len(lines[0]) - len(lines[0].lstrip())
    parts: list[list[str]] = []
    for line in lines:
        if line.lstrip().startswith("\\/") and len(line) - len(line.lstrip()) == indent:
            parts.append([" " * (indent + 2) + line.lstrip()[2:].lstrip()])
        else:
            parts[-1].append(line)
    return ["\n".join(part).strip() for part in parts]


def split_quantified(part: str) -> list[str]:
    """Split a one-line `\\E bounds: A \\/ B` into `\\E bounds: A` and `\\E bounds: B`; leave anything else whole."""
    match = re.fullmatch(r"(\\E [^:\n]+:)(.+)", part.strip())
    if not match:
        return [part]
    quantifier, body = match.groups()
    pieces, depth, start = [], 0, 0
    for i, char in enumerate(body):
        depth += char in "([{"
        depth -= char in ")]}"
        if depth == 0 and body.startswith("\\/", i):
            pieces.append(body[start:i])
            start = i + 2
    pieces.append(body[start:])
    if len(pieces) == 1 or any("/\\" in piece for piece in pieces):
        return [part]
    return [f"{quantifier}{piece.strip()}" for piece in pieces]


def probe_label(formula: str) -> str:
    body = re.sub(r"^\\E[^:]*:", "", formula.strip(), count=1, flags=re.S)
    names = list(dict.fromkeys(n for n in ACTION_NAME.findall(body) if n not in NOT_ACTIONS))
    label = " / ".join(names) or formula.splitlines()[0][:60]
    return label + (" (some message types)" if "m.type" in formula else "")


def affected_probes(update: Path, root: str = "AffectedActions") -> list[Probe]:
    definitions = top_level_definitions(update.read_text())
    if root not in definitions:
        raise SystemExit(f"{update} has no {root} definition")
    probes: list[Probe] = []

    def expand(name: str, seen: tuple[str, ...]) -> None:
        for part in disjuncts(definitions[name]):
            if part in definitions and part not in seen:
                expand(part, (*seen, part))
                continue
            for piece in split_quantified(part):
                probes.append(Probe(len(probes) + 1, name, probe_label(piece), piece))

    expand(root, (root,))
    return probes


def strip_comments(text: str) -> str:
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    return "\n".join(line.split("\\*", 1)[0] for line in text.splitlines())


def split_config(text: str) -> tuple[dict[str, str], str]:
    checks: dict[str, str] = {}
    kept: list[str] = []
    section = None
    for line in strip_comments(text).splitlines():
        words = line.split()
        if words and words[0] in CFG_KEYWORDS:
            section = words[0]
            words = words[1:]
        if section in CHECK_SECTIONS:
            for word in words:
                checks[word] = CHECK_SECTIONS[section]
        elif section != "CHECK_DEADLOCK":
            kept.append(line)
    return checks, "\n".join(kept).strip() + "\n"


def probe_module(probes: list[Probe], extends: str = "Update") -> str:
    registers = " /\\ ".join(f"TLCSet({100 + p.index}, 0) /\\ TLCSet({300 + p.index}, 0)" for p in probes)
    lines = [
        f"{'-' * 30} MODULE {PROBE_MODULE} {'-' * 30}",
        f"EXTENDS {extends}, TLC",
        "\\* Generated by update-coverage/check.py. Each probe is a disjunct of the affected actions, copied",
        "\\* verbatim. The action constraint never prunes; it records the first step that matches a probe",
        "\\* (register 100+k) and, until then, the first state in which the probe is enabled (300+k).",
        f"ASSUME {registers}",
        "UCTaken(k, A) == IF TLCGet(100 + k) = 0 /\\ A",
        '    THEN TLCSet(100 + k, 1) /\\ PrintT(<<"update-coverage", k>>) ELSE TRUE',
        "UCEnabled(k, A) == IF TLCGet(100 + k) = 0 /\\ TLCGet(300 + k) = 0 /\\ ENABLED A",
        '    THEN TLCSet(300 + k, 1) /\\ PrintT(<<"update-coverage-enabled", k>>) ELSE TRUE',
    ]
    for p in probes:
        lines.append(f"UCProbe{p.index} ==\n    {p.formula}")
    lines.append(
        "UCAll == "
        + " /\\ ".join(
            f"UCEnabled({p.index}, UCProbe{p.index}) /\\ UCTaken({p.index}, UCProbe{p.index})" for p in probes
        )
    )
    lines.append("=" * 77)
    return "\n".join(lines) + "\n"


def discover_configs(spec: Path, extends: str) -> list[tuple[str, str]]:
    found = []
    for path in sorted(spec.glob("*.cfg")):
        if path.name == "MC.cfg" or path.name.startswith("MC_"):
            found.append((path.name, "MC"))
        elif path.name.startswith("Update_") and extends == "Update":
            found.append((path.name, "Update"))
    return found


def run_config(
    spec: Path,
    config: Config,
    probes: list[Probe],
    extends: str,
    seconds: int,
    depth: int,
    seed: int,
    heap: str,
    jars: str,
) -> Config:
    """Run one simulation and merge what it reached into the config, so a retry adds to the first run."""
    config.checks, body = split_config((spec / config.name).read_text())
    work = Path(tempfile.mkdtemp(prefix="update-coverage-"))
    try:
        for path in spec.glob("*.tla"):
            shutil.copy(path, work / path.name)
        (work / f"{PROBE_MODULE}.tla").write_text(probe_module(probes, extends))
        (work / "probe.cfg").write_text(body + "ACTION_CONSTRAINT UCAll\nCHECK_DEADLOCK FALSE\n")
        command = ["java", f"-Xmx{heap}", "-Dtlc2.TLC.progressInterval=10", "-cp", jars, "tlc2.TLC"]
        command += ["-simulate", "-depth", str(depth), "-seed", str(seed), "-workers", "1", "-nowarning"]
        command += ["-config", "probe.cfg", PROBE_MODULE]
        started = time.monotonic()
        with (work / "tlc.log").open("w") as log:
            process = subprocess.Popen(command, cwd=work, stdout=log, stderr=subprocess.STDOUT)
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
        config.seconds = round((config.seconds or 0) + time.monotonic() - started, 1)
        text = (work / "tlc.log").read_text(errors="replace")
        taken = {int(k) for k in re.findall(r'<<"update-coverage", (\d+)>>', text)}
        enabled = {int(k) for k in re.findall(r'<<"update-coverage-enabled", (\d+)>>', text)}
        config.taken = sorted(set(config.taken) | taken)
        config.enabled = sorted(set(config.enabled) | enabled | taken)
        traces = re.findall(r"([\d,]+) traces generated", text)
        if traces:
            config.traces = (config.traces or 0) + int(traces[-1].replace(",", ""))
        lines = text.splitlines()
        errors = [i for i, line in enumerate(lines) if line.startswith("Error:")]
        if errors:
            config.status = "error: " + " ".join(lines[errors[0] : errors[0] + 3])[len("Error:") :].strip()
        else:
            config.status = "budget used" if timed_out else "finished"
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return config


def analyse(probes: list[Probe], configs: list[Config], ignore: str | None = None) -> dict[str, object]:
    ran = [c for c in configs if not c.status.startswith("error")]
    reached = sorted({k for c in ran for k in c.taken})
    checks: dict[str, dict[str, object]] = {}
    for config in ran:
        for name, kind in config.checks.items():
            if ignore and re.search(ignore, name):
                continue
            entry = checks.setdefault(name, {"kind": kind, "configs": [], "covered": set()})
            entry["configs"].append(config.name)
            entry["covered"] |= set(config.taken)
    enabled_in = {c.name: set(c.enabled) | set(c.taken) for c in ran}
    gaps = []
    for name, entry in sorted(checks.items()):
        missing = [k for k in reached if k not in entry["covered"]]
        if missing:
            possible = [k for k in missing if any(k in enabled_in[c] for c in entry["configs"])]
            gaps.append(
                {
                    "check": name,
                    "kind": entry["kind"],
                    "configs": entry["configs"],
                    "missing": missing,
                    "possible": possible,
                }
            )
    gaps.sort(key=lambda gap: (-len(gap["missing"]), gap["check"]))
    ever_enabled = {k for c in ran for k in enabled_in[c.name]}
    return {
        "unreached": [p.index for p in probes if p.index not in reached],
        "never_enabled": [p.index for p in probes if p.index not in ever_enabled],
        "gaps": gaps,
        "properties": sorted(name for name, entry in checks.items() if entry["kind"] == "property"),
        "errors": [{"config": c.name, "status": c.status} for c in configs if c.status.startswith("error")],
        "ignored": sorted({n for c in ran for n in c.checks if ignore and re.search(ignore, n)}),
    }


def gap_groups(result: dict[str, object]) -> list[dict[str, object]]:
    groups: dict[tuple, dict[str, object]] = {}
    for gap in result["gaps"]:
        key = tuple((k, k in gap["possible"]) for k in gap["missing"])
        groups.setdefault(key, {"missing": list(key), "checks": []})["checks"].append(gap["check"])
    return sorted(groups.values(), key=lambda group: (-len(group["checks"]), group["missing"]))


def report(spec_label: str, probes: list[Probe], configs: list[Config], result: dict[str, object]) -> str:
    label = {p.index: f"{p.index} {p.label}" for p in probes}
    lines = [f"# Update coverage: {spec_label}", ""]
    lines += ["## Checks never run while an action happens", ""]
    groups = gap_groups(result)
    if not groups:
        lines.append("None: every enabled check runs in a config that reaches every action some config reaches.")
    else:
        lines += [
            "An action marked *never possible* was never enabled in any state visited by the configs that",
            "enable those checks; *possible* means it was enabled there but not taken within the budget.",
            "",
            "| Never checked while | Checks | Names |",
            "|---|---:|---|",
        ]
        for group in groups:
            missing = "; ".join(f"{label[k]} ({'possible' if ok else 'never possible'})" for k, ok in group["missing"])
            names = ", ".join(f"`{name}`" for name in group["checks"])
            lines.append(f"| {missing} | {len(group['checks'])} | {names} |")
    lines += [""]
    never = set(result["never_enabled"])
    if result["unreached"]:
        parts = [f"{label[k]} ({'never possible' if k in never else 'possible'})" for k in result["unreached"]]
        lines += [f"Actions no config reached: {'; '.join(parts)}.", ""]
    if not result["properties"]:
        lines += ["No config enables a temporal property, so no progress obligation is checked.", ""]
    if result["ignored"]:
        lines += ["Ignored as requested: " + ", ".join(f"`{name}`" for name in result["ignored"]) + ".", ""]
    for error in result["errors"]:
        lines += [f"`{error['config']}` did not run: {error['status']}", ""]
    lines += ["## Actions", "", "| # | Group | Action |", "|---:|---|---|"]
    lines += [f"| {p.index} | {p.group} | {p.label} |" for p in probes]
    lines += ["", "## What each config reached", ""]
    lines += ["`x` taken, `e` enabled but not taken, `.` never enabled. Retried configs ran a second, longer pass.", ""]
    lines += ["| Config | Status | Traces | Seconds | " + " | ".join(str(p.index) for p in probes) + " |"]
    lines += ["|---|---|---:|---:|" + "---|" * len(probes)]
    for c in configs:
        cells = ["x" if p.index in c.taken else "e" if p.index in c.enabled else "." for p in probes]
        traces = "-" if c.traces is None else str(c.traces)
        status = c.status + (", retried" if c.retried else "")
        lines.append(f"| `{c.name}` | {status} | {traces} | {c.seconds} | " + " | ".join(cells) + " |")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path, nargs="?", help="spec directory containing the checking configs")
    parser.add_argument(
        "--actions",
        default="Update.tla:AffectedActions",
        help="FILE.tla:DEFINITION listing the actions to probe; the probe module extends FILE",
    )
    parser.add_argument("--config", action="append", default=[], help="NAME.cfg (default: MC*.cfg, Update_*.cfg)")
    parser.add_argument("--seconds", type=int, default=120, help="first simulation pass per config")
    parser.add_argument("--retry-seconds", type=int, default=240, help="second pass for configs behind a gap")
    parser.add_argument("--depth", type=int, default=100)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--heap", default="4g")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--out", type=Path, help="directory for report.md and report.json")
    parser.add_argument("--ignore", help="regex of check names to leave out, such as reachability canaries")
    parser.add_argument("--rebuild", action="store_true", help="rebuild the report from OUT/report.json without TLC")
    args = parser.parse_args()
    if args.rebuild:
        record = json.loads((args.out / "report.json").read_text())
        probes = [Probe(**{**p, "label": probe_label(p["formula"])}) for p in record["probes"]]
        configs = [Config(**c) for c in record["configs"]]
        write(args, record["spec"], record["settings"], probes, configs)
        return
    spec = args.spec.resolve()
    actions_file, definition = args.actions.split(":", 1)
    extends = Path(actions_file).stem
    probes = affected_probes(spec / actions_file, definition)
    names = args.config or [name for name, _ in discover_configs(spec, extends)]
    configs = [Config(name, extends) for name in names]
    tla2tools = os.environ.get("TLA2TOOLS", str(ROOT / "lib/tla2tools.jar"))
    community = os.environ.get("COMMUNITY_MODULES", str(ROOT / "lib/CommunityModules-deps.jar"))
    jars = f"{tla2tools}:{community}"

    def run_all(batch: list[Config], seconds: int, seed: int) -> None:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [
                pool.submit(run_config, spec, c, probes, extends, seconds, args.depth, seed, args.heap, jars)
                for c in batch
            ]
            for future in concurrent.futures.as_completed(futures):
                done = future.result()
                print(f"{done.name}: {done.status}, reached {len(done.taken)}/{len(probes)}", flush=True)

    run_all(configs, args.seconds, args.seed)
    first = analyse(probes, configs, args.ignore)
    behind = {name for gap in first["gaps"] for name in gap["configs"]}
    retry = [c for c in configs if c.name in behind]
    if retry and args.retry_seconds:
        for config in retry:
            config.retried = True
        run_all(retry, args.retry_seconds, args.seed + 1)
    settings = {
        "actions": args.actions,
        "seconds": args.seconds,
        "retry_seconds": args.retry_seconds,
        "depth": args.depth,
        "seed": args.seed,
        "heap": args.heap,
    }
    write(args, str(spec).replace(str(ROOT), "$SPECULA"), settings, probes, configs)


def write(args: argparse.Namespace, spec: str, settings: dict, probes: list[Probe], configs: list[Config]) -> None:
    result = analyse(probes, configs, args.ignore)
    text = report("/".join(Path(spec).parts[-2:]), probes, configs, result)
    if args.out:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "report.md").write_text(text)
        record = {
            "spec": spec,
            "settings": {**settings, "ignore": args.ignore},
            "probes": [asdict(p) for p in probes],
            "configs": [asdict(c) for c in configs],
            **result,
            "groups": gap_groups(result),
        }
        (args.out / "report.json").write_text(json.dumps(record, indent=2) + "\n")
    print(text)


if __name__ == "__main__":
    main()
