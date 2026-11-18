"""Find what the focused update model leaves out, summarize it as `EnvUpdate`, and check the summary.

`Update.tla` checks the update with a focused next-state relation (`ConcreteUpdateNext`) instead of the full
`MCNext`. Steps of `MCNext` outside the focused relation are the update's environment. This script splits
`MCNext` into single actions, runs the full model in TLC simulation (from Init, or from a recorded run as in
prefix-branch/branch.py) and records, for each action, the steps that fall outside the focused relation and the
state fields they change. Fields read by the update's properties are the update view. The result is an
`EnvUpdate` that keeps every view field no environment step was seen to change, checked on fresh runs, plus a
discharge property (`[][(MCNext /\\ ~ConcreteUpdateNext) => EnvUpdate]_vars`) that later versions can rerun.
Actions whose out-of-focus steps change view fields are reported: they need to be in the focused model or
summarized by hand.
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
sys.path.insert(0, str(HERE.parent / "prefix-branch"))

from branch import MODULE as BRANCH_MODULE  # noqa: E402
from branch import SPEC_DEF, build, extends_chain, section_names  # noqa: E402
from check import (  # noqa: E402
    ACTION_NAME,
    NOT_ACTIONS,
    ROOT,
    probe_label,
    split_config,
    strip_comments,
    top_level_definitions,
)

MODULE = "EnvUpdateCheck"
TOKEN = re.compile(r"[A-Za-z_]\w*")


def top_split(text: str, sep: str) -> list[str]:
    pieces, depth, start, i = [], 0, 0, 0
    while i < len(text):
        depth += text[i] in "([{"
        depth -= text[i] in ")]}"
        if depth == 0 and text.startswith(sep, i):
            pieces.append(text[start:i])
            start = i = i + len(sep)
            continue
        i += 1
    pieces.append(text[start:])
    return [p.strip() for p in pieces if p.strip()]


def unwrap(text: str) -> str:
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for i, char in enumerate(text):
            depth += char in "([{"
            depth -= char in ")]}"
            if depth == 0 and i < len(text) - 1:
                return text
        text = text[1:-1].strip()
    return text


def bulleted(formula: str, op: str) -> list[str] | None:
    """Split a TLA+ bulleted list (`\\/` or `/\\` items aligned in one column), keeping every item's columns."""
    lines = [line for line in strip_comments(formula).splitlines() if line.strip()]
    if not lines or not lines[0].lstrip().startswith(op):
        return None
    column = len(lines[0]) - len(lines[0].lstrip())
    items: list[list[str]] = []
    for line in lines:
        indent = len(line) - len(line.lstrip())
        if indent == column and line.lstrip().startswith(op):
            items.append([line[:indent] + "  " + line[indent + 2 :]])
        elif indent < column or not items:
            return None
        else:
            items[-1].append(line)
    return ["\n".join(item) for item in items]


def flat(formula: str) -> str:
    return unwrap(" ".join(strip_comments(formula).split()))


def pieces(formula: str, definitions: dict[str, str], prefix: str = "") -> list[str]:
    alternatives = bulleted(formula, "\\/")
    if alternatives:
        return [p for alt in alternatives for p in pieces(alt, definitions, prefix)]
    conjuncts = bulleted(formula, "/\\")
    if conjuncts and len(conjuncts) == 1:
        return pieces(conjuncts[0], definitions, prefix)
    if conjuncts:
        split = [pieces(c, definitions) for c in conjuncts]
        branching = [i for i, found in enumerate(split) if len(found) > 1]
        if len(branching) == 1:
            others = " /\\ ".join(f"({flat(c)})" for i, c in enumerate(conjuncts) if i != branching[0])
            return [f"{prefix}{others} /\\ ({p})" for p in split[branching[0]]]
    text = flat(formula)
    if text.startswith("\\E "):
        head = top_split(text, ":")[0]
        body = text[text.index(head) + len(head) :].lstrip()[1:]
        return pieces(body, definitions, f"{prefix}{head}: ")
    alternatives = top_split(text, "\\/")
    if len(alternatives) > 1:
        return [p for alt in alternatives for p in pieces(alt, definitions, prefix)]
    conjuncts = top_split(text.removeprefix("/\\").strip(), "/\\")
    first = conjuncts[0].removeprefix("Original!")
    if re.fullmatch(r"\w+", first) and first in definitions:
        inner = pieces(definitions[first], definitions)
        if len(inner) > 1:
            rest = "".join(f" /\\ {c}" for c in conjuncts[1:])
            return [f"{prefix}{p}{rest}" for p in inner]
    return [f"{prefix}{text}"]


def actions(next_body: str, definitions: dict[str, str]) -> list[str]:
    return pieces(next_body, definitions)


def view_text(definitions: dict[str, str], roots: list[str]) -> str:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        name = stack.pop()
        if name in seen or name not in definitions:
            continue
        seen.add(name)
        stack += [t for t in TOKEN.findall(strip_comments(definitions[name])) if t in definitions]
    return "\n".join(strip_comments(definitions[name]) for name in sorted(seen))


def view_fields(text: str, shape: dict[str, tuple[str, list[str]]]) -> list[str]:
    """Fields the view text reads. A record read only as `var.field` contributes just those fields; per-node
    records and records passed around whole are matched by field name, which may over-approximate."""
    tokens = set(TOKEN.findall(text))
    found = []
    for name, (kind, fields) in shape.items():
        if name not in tokens:
            continue
        if kind == "whole":
            found.append(name)
            continue
        direct = [f for f in fields if re.search(rf"\b{name}\.{f}\b", text)]
        whole = re.search(rf"\b{name}\b(?!\.|\[)", text)
        chosen = direct if kind == "record" and direct and not whole else [f for f in fields if f in tokens]
        found += [f"{name}.{f}" for f in chosen]
    return sorted(found)


def shapes(state: dict) -> tuple[dict[str, tuple[str, list[str]]], list[str]]:
    node_maps = [
        v for v in state.values() if isinstance(v, dict) and len(v) > 1 and all(isinstance(x, dict) for x in v.values())
    ]
    servers = sorted(min(node_maps, key=len)) if node_maps else []
    found: dict[str, tuple[str, list[str]]] = {}
    for name, value in state.items():
        if (
            isinstance(value, dict)
            and servers
            and set(value) == set(servers)
            and all(isinstance(v, dict) for v in value.values())
        ):
            found[name] = ("node", sorted(next(iter(value.values()))))
        elif isinstance(value, dict) and value and not set(value) & set(servers):
            found[name] = ("record", sorted(value))
        else:
            found[name] = ("whole", [])
    return found, servers


def changed_expr(name: str, kind: str, fields: list[str]) -> str:
    if kind == "whole":
        return f'(IF {name}\' # {name} THEN {{"{name}"}} ELSE {{}})'
    names = ", ".join(f'"{f}"' for f in fields)
    differs = (
        f"\\E n \\in DOMAIN {name} : {name}'[n][f] # {name}[n][f]" if kind == "node" else f"{name}'[f] # {name}[f]"
    )
    return f'{{"{name}." \\o f : f \\in {{f \\in {{{names}}} : {differs}}}}}'


def unchanged_expr(atom: str, kind: str) -> str:
    name, _, field = atom.partition(".")
    if kind == "whole":
        return f"{name}' = {name}"
    if kind == "node":
        return f'\\A n \\in DOMAIN {name} : {name}\'[n]["{field}"] = {name}[n]["{field}"]'
    return f'{name}\'["{field}"] = {name}["{field}"]'


def run_tlc(work: Path, module: str, cfg: str, run: dict) -> dict:
    (work / f"{MODULE}.tla").write_text(module)
    (work / "run.cfg").write_text(cfg)
    (work / "cex.json").unlink(missing_ok=True)
    jars = (
        os.environ.get("TLA2TOOLS", str(ROOT / "lib/tla2tools.jar"))
        + ":"
        + os.environ.get("COMMUNITY_MODULES", str(ROOT / "lib/CommunityModules-deps.jar"))
    )
    command = ["java", f"-Xmx{run['heap']}", "-XX:+UseParallelGC", "-cp", jars, "tlc2.TLC", "-workers", "1"]
    command += ["-nowarning", "-config", "run.cfg"]
    if run.get("dump"):
        command += ["-dumpTrace", "json", "cex.json"]
    else:
        command += ["-simulate", "-depth", str(run["depth"]), "-seed", str(run["seed"])]
    command += [MODULE]
    env = dict(os.environ, JSON=str(run["trace"])) if run.get("trace") else None
    started = time.monotonic()
    with (work / "tlc.log").open("w") as log:
        process = subprocess.Popen(command, cwd=work, stdout=log, stderr=subprocess.STDOUT, env=env)
        try:
            process.wait(timeout=run["seconds"])
        except subprocess.TimeoutExpired:
            process.send_signal(signal.SIGINT)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
    text = (work / "tlc.log").read_text(errors="replace")
    traces = re.findall(r"([\d,]+) traces generated", text)
    violated = re.search(r"(?:Invariant|Action property) (\S+) is violated", text)
    errors = [line for line in text.splitlines() if line.startswith("Error:") and "is violated" not in line]
    return {
        "seconds": round(time.monotonic() - started, 1),
        "traces": int(traces[-1].replace(",", "")) if traces else None,
        "violated": violated.group(1) if violated else None,
        "error": " ".join(errors[:2]) or None,
        "log": text,
    }


def flat_log(text: str) -> str:
    """TLC wraps long printed values over several lines; put each back on one."""
    return re.sub(r"\s+", " ", text)


def base_cfg(text: str) -> str:
    _, kept = split_config(text)
    return kept + "CHECK_DEADLOCK FALSE\n"


def action_name(piece: str) -> str:
    body = re.sub(r"^(\\E[^:]*:\s*)+", "", piece)
    called = next((n for n in ACTION_NAME.findall(body) if n not in NOT_ACTIONS), "")
    return called or (re.match(r"\(?(\w+)", body.strip()) or [None, ""])[1]


def wrappers(text: str) -> dict[str, tuple[str, str]]:
    """One-line, one-parameter definitions such as `Framed(a) == a /\\ UNCHANGED faultVars`."""
    found = {}
    for line in strip_comments(text).splitlines():
        match = re.fullmatch(r"(\w+)\((\w+)\)\s*==\s*(.+?)\s*", line)
        if match:
            found[match.group(1)] = (match.group(2), match.group(3))
    return found


def normal(formula: str, macros: dict[str, tuple[str, str]]) -> str:
    text = formula.replace("Original!", "")
    for name, (param, body) in macros.items():
        while (start := text.find(f"{name}(")) >= 0 and (start == 0 or not text[start - 1].isalnum()):
            depth, end = 0, start + len(name)
            for end in range(start + len(name), len(text)):
                depth += text[end] == "("
                depth -= text[end] == ")"
                if depth == 0:
                    break
            arg = text[start + len(name) + 1 : end]
            text = text[:start] + re.sub(rf"\b{param}\b", lambda _, a=arg: a, body) + text[end + 1 :]
    return re.sub(r"\s+", "", text)


def named_parts(parts: list[str], focused: list[str], macros: dict[str, tuple[str, str]]) -> list[str]:
    """One definition per action that records its number in envAct, and the focused actions it could belong to.

    A focused action written exactly like the full model's one is in focus without asking TLC.
    """
    lines = [f"EnvPart{k} ==\n    ({part}) /\\ envAct' = {k}" for k, part in enumerate(parts, 1)]
    lines.append("EnvNext ==\n    " + "\n    \\/ ".join(f"EnvPart{k}" for k in range(1, len(parts) + 1)))
    for k, part in enumerate(parts, 1):
        same = [f for f in focused if action_name(f) == action_name(part)]
        if any(normal(f, macros) == normal(part, macros) for f in same):
            body = "TRUE"
        else:
            body = "\n    \\/ ".join(f"({f})" for f in same) if same else "FALSE"
        lines.append(f"EnvFocus{k} ==\n    {body}")
    return lines


def dispatch(count: int, step: str) -> str:
    cases = "\n    [] ".join(f"envAct' = {k} -> {step.format(k=k)}" for k in range(1, count + 1))
    return f"\n    CASE {cases}\n    [] OTHER -> TRUE"


def recorder(count: int, shape: dict[str, tuple[str, list[str]]]) -> list[str]:
    """Action constraint that never prunes and prints, per action, the fields its out-of-focus steps change."""
    changes = " \\cup ".join(changed_expr(name, kind, fields) for name, (kind, fields) in shape.items())
    return [
        f"ASSUME \\A k \\in 1..{count} : TLCSet(1000 + k, 0) /\\ TLCSet(2000 + k, {{}})",
        f"EnvChanged == {changes}",
        "EnvTaken(k) == IF TLCGet(1000 + k) = 0",
        '    THEN TLCSet(1000 + k, 1) /\\ PrintT(<<"env-taken", k>>) ELSE TRUE',
        "EnvOutside(k) == LET new == EnvChanged \\ TLCGet(2000 + k) IN",
        "    IF TLCGet(1000 + k) < 2 \\/ new # {}",
        "    THEN TLCSet(1000 + k, 2) /\\ TLCSet(2000 + k, TLCGet(2000 + k) \\cup new)",
        '         /\\ PrintT(<<"env-outside", k, new>>)',
        "    ELSE TRUE",
        "EnvRecord == " + dispatch(count, "EnvTaken({k}) /\\ (EnvFocus{k} \\/ EnvOutside({k}))"),
    ]


def frame(keeps: list[str], shape: dict) -> list[str]:
    body = "\n    /\\ ".join(unchanged_expr(a, shape[a.partition(".")[0]][0]) for a in keeps)
    return ["EnvUpdate ==", f"    /\\ {body}" if keeps else "    TRUE"]


def checker(count: int, keeps: list[str], shape: dict) -> list[str]:
    """Action constraint that stops at the first out-of-focus step EnvUpdate does not allow."""
    step = (
        "IF EnvFocus{k} \\/ EnvUpdate THEN TRUE"
        ' ELSE PrintT(<<"env-violation", {k}, EnvChanged>>) /\\ Assert(FALSE, "EnvUpdate violated")'
    )
    changes = " \\cup ".join(changed_expr(name, kind, fields) for name, (kind, fields) in shape.items())
    return [*frame(keeps, shape), f"EnvChanged == {changes}", "EnvDischarge == " + dispatch(count, step)]


def prefix_setup(args: argparse.Namespace, spec: Path, full_next: str, defs: list[str]) -> tuple[str, str, int]:
    """The prefix-branch module with the split full model as the continuation, without its invariants."""
    events = sum(1 for line in args.trace.read_text().splitlines() if '"trace"' in line)
    options = argparse.Namespace(
        limits=args.full,
        actions="AffectedActions",
        settle="next",
        replay=args.replay,
        guard="",
        constraint=True,
        settled="",
        after=args.after,
        checks="",
        ignore=None,
        steps=0,
        domain=args.domain,
    )
    domains = set(filter(None, args.domains.split(",")))
    module, cfg, _ = build(options, spec, events, domains)
    module = module.replace(f"MODULE {BRANCH_MODULE} ", f"MODULE {MODULE} ").rsplit("=" * 77, 1)[0]
    settle = f"PBSettle1 ==\n    {full_next}\n"
    if settle not in module:
        raise SystemExit(f"unexpected prefix-branch module: no {settle!r}")
    module = module.replace(settle, "\n".join(defs) + "\nPBSettle1 ==\n    EnvNext\n")
    edits = [
        (r"^(VARIABLES .*)$", r"\1, envAct"),
        (r"^(pbVars == <<.*)>>$", r"\1, envAct>>"),
        (r"^(PBInit == .*)$", r"\1 /\\ envAct = 0"),
        (r"(pbBranched, pbSlot, pbAction>>)", r"\1 /\\ envAct' = 0"),
        (r"(UNCHANGED <<l, pbAt, pbSlot>>)", r"\1 /\\ envAct' = 0"),
    ]
    for pattern, replacement in edits:
        module, count = re.subn(pattern, replacement, module, count=1, flags=re.M)
        if count != 1:
            raise SystemExit(f"unexpected prefix-branch module: no match for {pattern}")
    cfg = cfg.replace("PBPOINTS", "<- PBAllPoints").split("INVARIANTS")[0]
    depth = int(re.search(r"PBMaxSteps = (\d+)", cfg).group(1)) + args.after + 5
    return module, cfg, depth


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path)
    parser.add_argument("--full", default="Update_full.cfg", help="config of the full model (constants and limits)")
    parser.add_argument("--focused", default="Update_focused.cfg", help="config whose specification is focused")
    parser.add_argument("--view", default="", help="comma-separated properties that define the update view")
    parser.add_argument("--trace", type=Path, help="recorded run to start from, as in prefix-branch/branch.py")
    parser.add_argument("--replay", default="strict", help="'strict' (TraceNext) or a step formula over logline")
    parser.add_argument("--domains", default="", help="constants to take from --full instead of the trace")
    parser.add_argument("--domain", action="append", default=[], metavar="NAME=VALUE", help="as in branch.py")
    parser.add_argument("--after", type=int, default=100, help="steps of the full model after the branch")
    parser.add_argument("--depth", type=int, default=100, help="simulation depth when starting from Init")
    parser.add_argument("--seconds", type=int, default=300, help="simulation time to learn the summary")
    parser.add_argument("--check-seconds", type=int, default=300, help="simulation time to check it afterwards")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--heap", default="4g")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    spec = args.spec.resolve()
    args.trace = args.trace.resolve() if args.trace else None
    definitions: dict[str, str] = {}
    for name in extends_chain(spec, "Update"):
        definitions.update(top_level_definitions((spec / f"{name}.tla").read_text()))
    full_text, focused_text = (spec / args.full).read_text(), (spec / args.focused).read_text()
    full_spec = section_names(full_text, "SPECIFICATION")[0]
    focused_spec = section_names(focused_text, "SPECIFICATION")[0]
    init, full_next, full_vars = SPEC_DEF.match(definitions[full_spec]).groups()
    focused_next = SPEC_DEF.match(definitions[focused_spec]).group(2)
    model_next = full_next
    while model_next in definitions and re.fullmatch(r"\s*\w+\s*", definitions[model_next]):
        model_next = definitions[model_next].strip()
    parts = actions(definitions[model_next], definitions)
    focused = actions(definitions[focused_next], definitions)
    defs = named_parts(parts, focused, wrappers((spec / "Update.tla").read_text()))

    view_roots = args.view.split(",") if args.view else []
    if not view_roots:
        for cfg in sorted(spec.glob("Update_*.cfg")):
            view_roots += [n for n in split_config(cfg.read_text())[0] if n.startswith("Update")]
    view_roots = list(dict.fromkeys(view_roots))
    text = view_text(definitions, view_roots)

    args.out.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="env-update-"))
    try:
        for path in spec.glob("*.tla"):
            shutil.copy(path, work / path.name)
        header = [f"{'-' * 30} MODULE {MODULE} {'-' * 30}", "EXTENDS Update, TLC"]
        footer = ["=" * 77]
        probe = "\n".join([*header, 'EnvStop == TLCGet("level") = 0', *footer]) + "\n"
        first = run_tlc(
            work, probe, base_cfg(full_text) + "INVARIANT EnvStop\n", {"heap": args.heap, "seconds": 600, "dump": True}
        )
        if not (work / "cex.json").exists():
            raise SystemExit(f"could not read an initial state: {first['error']}")
        shape, _ = shapes(json.loads((work / "cex.json").read_text())["counterexample"]["state"][0][1])
        visible = view_fields(text, shape)

        if args.trace:
            base, cfg, depth = prefix_setup(args, spec, full_next, defs)
        else:
            spec_line = f"EnvSpec == {init} /\\ envAct = 0 /\\ [][EnvNext]_<<{full_vars}, envAct>>"
            base = "\n".join([*header, "VARIABLE envAct", *defs, spec_line]) + "\n"
            cfg = base_cfg(full_text).replace(f"SPECIFICATION {full_spec}", "SPECIFICATION EnvSpec")
            depth = args.depth
        run = {"heap": args.heap, "depth": depth, "trace": args.trace}
        learn_module = base + "\n".join([*recorder(len(parts), shape), *footer]) + "\n"
        learn_cfg = cfg + "ACTION_CONSTRAINT EnvRecord\n"
        learn = run_tlc(work, learn_module, learn_cfg, run | {"seconds": args.seconds, "seed": args.seed})
        taken: set[int] = set()
        outside: dict[int, set[str]] = {}
        for kind, k, rest in re.findall(
            r'<< ?"(env-taken|env-outside)", (\d+)(?:, (\{[^}]*\}))? ?>>', flat_log(learn["log"])
        ):
            if kind == "env-taken":
                taken.add(int(k))
            else:
                outside.setdefault(int(k), set()).update(re.findall(r'"([^"]+)"', rest))

        keeps = [a for a in visible if not any(a in fields for fields in outside.values())]
        check_module = base + "\n".join([*checker(len(parts), keeps, shape), *footer]) + "\n"
        check_cfg = cfg + "ACTION_CONSTRAINT EnvDischarge\n"
        check = run_tlc(work, check_module, check_cfg, run | {"seconds": args.check_seconds, "seed": args.seed + 1})
        found = re.search(r'<< ?"env-violation", (\d+), (\{[^}]*\}) ?>>', flat_log(check["log"]))
        check["violated"] = (
            {"part": int(found.group(1)), "changed": re.findall(r'"([^"]+)"', found.group(2))} if found else None
        )
        if not found and '"EnvUpdate violated"' in check["log"]:
            check["violated"] = {"part": None, "changed": []}
        if check["violated"]:
            check["error"] = None

        standalone = [
            f"{'-' * 30} MODULE EnvUpdate {'-' * 30}",
            "EXTENDS Update",
            "\\* Generated by env-update/envupdate.py. Environment steps are the steps of the full model outside",
            "\\* the focused one; EnvUpdate keeps every update-view field none of them was seen to change.",
            *frame(keeps, shape),
            f"EnvStep == {full_next} /\\ ~{focused_next}",
            f"DischargeContext == [][EnvStep => EnvUpdate]_{full_vars}",
            *footer,
        ]
        report = [
            {
                "part": k,
                "label": probe_label(part),
                "in_focused_model": any(action_name(f) == action_name(part) for f in focused),
                "taken": k in taken,
                "outside_focused": k in outside,
                "changes_view": sorted(f for f in outside.get(k, ()) if f in visible),
                "changes_other": sorted(f for f in outside.get(k, ()) if f not in visible),
            }
            for k, part in enumerate(parts, 1)
        ]
        result = {
            "spec": str(spec).replace(str(ROOT), "$SPECULA"),
            "trace": args.trace.name if args.trace else None,
            "full": args.full,
            "focused": args.focused,
            "focused_next": focused_next,
            "view_from": view_roots,
            "view": visible,
            "learn": {k: v for k, v in learn.items() if k != "log"},
            "parts": report,
            "env_update_keeps": keeps,
            "discharge_check": {k: v for k, v in check.items() if k != "log"},
        }
        (args.out / "EnvUpdate.tla").write_text("\n".join(standalone) + "\n")
        (args.out / "result.json").write_text(json.dumps(result, indent=1) + "\n")
        for name, outcome in (("learn", learn), ("check", check)):
            if outcome["error"]:
                lines = outcome["log"].replace(str(work), "$WORK").replace(str(ROOT), "$SPECULA").splitlines()
                kept = [line for line in lines if not line.startswith(("Parsing file", "Semantic processing"))]
                first = next((i for i, line in enumerate(kept) if line.startswith("Error:")), 0)
                (args.out / f"{name}-error.log").write_text("\n".join(kept[first : first + 80]) + "\n")
        print(json.dumps({k: result[k] for k in ("learn", "discharge_check")}, indent=1))
        for row in report:
            if row["outside_focused"]:
                print(f"part {row['part']:>2} {row['label']}: view {row['changes_view'] or '-'}")
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
