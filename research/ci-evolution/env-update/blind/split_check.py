"""Check envupdate.py's action split on suites it was not written against.

For each suite, the next-state relation named by MC.cfg is split into single actions. TLC then simulates the
original model and checks that every step is a step of the split relation, and simulates the split relation and
checks that every step is a step of the original. Both must hold for the split to be safe to use.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from envupdate import (  # noqa: E402  # noqa: E402
    ROOT,
    SPEC_DEF,
    action_name,
    actions,
    base_cfg,
    extends_chain,
    run_tlc,
    section_names,
    top_level_definitions,
)

MODULE = "EnvUpdateCheck"


def next_relation(spec: Path, cfg: str, definitions: dict[str, str]) -> tuple[str, str, str]:
    names = section_names(cfg, "SPECIFICATION")
    if names:
        init, nxt, variables = SPEC_DEF.match(definitions[names[0]]).groups()
        return init, nxt, variables
    init, nxt = section_names(cfg, "INIT")[0], section_names(cfg, "NEXT")[0]
    variables = "vars" if "vars" in definitions else ""
    return init, nxt, variables


def check(case: Path, seconds: int, heap: str) -> dict:
    spec = case / ".specula-output" / "spec"
    cfg = (spec / "MC.cfg").read_text()
    definitions: dict[str, str] = {}
    for name in extends_chain(spec, "MC"):
        definitions.update(top_level_definitions((spec / f"{name}.tla").read_text()))
    init, nxt, variables = next_relation(spec, cfg, definitions)
    if not variables:
        return {"case": case.name, "next": nxt, "error": "no vars tuple"}
    resolved = nxt
    while resolved in definitions and re.fullmatch(r"\s*\w+\s*", definitions[resolved]):
        resolved = definitions[resolved].strip()
    parts = actions(definitions[resolved], definitions)
    split = "SplitNext ==\n    " + "\n    \\/ ".join(f"({p})" for p in parts)
    head = [f"{'-' * 30} MODULE {MODULE} {'-' * 30}", "EXTENDS MC, TLC", split]
    body = base_cfg(cfg)
    body = re.sub(r"^(SPECIFICATION|INIT|NEXT)\b.*\n", "", body, flags=re.M)
    runs = {}
    work = Path(tempfile.mkdtemp(prefix="split-check-"))
    try:
        for path in spec.glob("*.tla"):
            shutil.copy(path, work / path.name)
        dropped = "ControlNext ==\n    " + "\n    \\/ ".join(f"({p})" for p in parts[1:])
        directions = {
            "original_steps_are_split": (f"OrigSpec == {init} /\\ [][{nxt}]_{variables}", "SplitCover"),
            "split_steps_are_original": (f"SplitSpec == {init} /\\ [][SplitNext]_{variables}", "OrigCover"),
            "control_without_first_action": (f"OrigSpec == {init} /\\ [][{nxt}]_{variables}", "ControlCover"),
        }
        for label, (spec_line, prop) in directions.items():
            module = "\n".join(
                [
                    *head,
                    dropped,
                    spec_line,
                    f"SplitCover == [][SplitNext]_{variables}",
                    f"OrigCover == [][{nxt}]_{variables}",
                    f"ControlCover == [][ControlNext]_{variables}",
                    "=" * 77,
                ]
            )
            run_cfg = f"SPECIFICATION {spec_line.split(' ==')[0]}\n{body}PROPERTY {prop}\n"
            result = run_tlc(work, module + "\n", run_cfg, {"heap": heap, "depth": 50, "seed": 1, "seconds": seconds})
            runs[label] = {k: v for k, v in result.items() if k != "log"}
            states = re.findall(r"([\d,]+) states checked", result["log"])
            runs[label]["states"] = int(states[-1].replace(",", "")) if states else None
            if result["error"]:
                runs[label]["log_tail"] = [
                    line for line in result["log"].splitlines() if line.startswith(("Error", "line ", "Unknown"))
                ][:6]
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return {
        "case": case.name,
        "next": nxt,
        "actions": len(parts),
        "dropped_in_control": action_name(parts[0]),
        "unnamed": sum(not action_name(p) for p in parts),
        "checks": runs,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", type=Path, help="folder with case-*/.specula-output")
    parser.add_argument("--seconds", type=int, default=75)
    parser.add_argument("--heap", default="2g")
    parser.add_argument("--out", type=Path, default=HERE / "split-check.json")
    args = parser.parse_args()
    results = [check(case, args.seconds, args.heap) for case in sorted(args.cases.glob("case-*"))]
    args.out.write_text(json.dumps(results, indent=1) + "\n")
    for r in results:
        verdicts = {
            k: v["violated"] or v["error"] or f"held on {v['traces']} runs" for k, v in r.get("checks", {}).items()
        }
        print(r["case"], r.get("next"), r.get("actions"), r.get("error") or verdicts)
    print(f"written to {args.out.relative_to(ROOT) if args.out.is_relative_to(ROOT) else args.out}")


if __name__ == "__main__":
    main()
