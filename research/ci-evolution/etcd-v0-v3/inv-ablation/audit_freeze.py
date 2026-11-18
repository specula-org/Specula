"""Did any A2/A3 run execute evidence before writing its frozen initial decision?

run.py's audit flag counts any Bash call before decision.initial.json. This script separates
read-only commands (cat, sed, grep, ls, diff, find, wc, head, ...) from commands that execute
evidence (java/TLC/SANY, go build/test/run, writing files under evidence/).

Usage: python3 audit_freeze.py   (writes results/freeze-audit.json)
"""

from __future__ import annotations

import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXECUTES = re.compile(r"\b(java|tlc2|tla2sany|go\s+(test|build|run|vet)|python3?\s+-c)\b|>\s*evidence/|mkdir\s+-p\s+evidence")


def audit(run_dir: Path) -> dict:
    record = json.loads((run_dir / "run.json").read_text())
    log = Path(record["log"])
    if not log.exists():
        return {"run": run_dir.name, "status": "log missing"}
    tools = []
    for line in log.read_text().splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("type") == "assistant":
            tools += [b for b in event["message"].get("content", []) if b.get("type") == "tool_use"]
    initial = next((i for i, b in enumerate(tools) if "decision.initial.json" in str(b["input"].get("file_path", ""))
                    or ("decision.initial.json" in str(b["input"].get("command", "")) and ">" in str(b["input"].get("command", "")))), None)
    before = [b["input"].get("command", "") for b in tools[: initial if initial is not None else len(tools)] if b["name"] == "Bash"]
    executing = [c[:200] for c in before if EXECUTES.search(c)]
    return {
        "run": run_dir.name,
        "initial_tool_index": initial,
        "bash_before_initial": len(before),
        "executing_before_initial": executing,
        "freeze_held": initial is not None and not executing,
    }


def main() -> None:
    rows = [audit(p.parent) for p in sorted((HERE / "results").glob("A[23]-*/run.json"))]
    (HERE / "results" / "freeze-audit.json").write_text(json.dumps(rows, indent=2) + "\n")
    for r in rows:
        print(json.dumps(r))


if __name__ == "__main__":
    main()
