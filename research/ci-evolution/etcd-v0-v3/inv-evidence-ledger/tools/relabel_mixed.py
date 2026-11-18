#!/usr/bin/env python3
"""Mechanical status relabel (rule (a), 2026-11-16).

A REQ-EVIDENCE block whose `clause` lines carry a status different from the block's own
status gets block status `mixed`, plus one `relabel:` line recording the old status.
Comment lines only; formulas are untouched. Same rule for every block.

Usage: relabel_mixed.py SRC_SPEC_DIR DEST_SPEC_DIR   (prints a JSON report)
"""
from __future__ import annotations

import json
import re
import shutil
import sys
from pathlib import Path

STATUSES = ("requirement", "impl-abstraction", "unknown", "model-internal")
CLAUSE = re.compile(r"\\\* clause .*?:\s*(" + "|".join(STATUSES) + r")\b")


def relabel(lines: list[str]) -> tuple[list[str], list[dict]]:
    out, changed, i = [], [], 0
    while i < len(lines):
        m = re.match(r"\\\* REQ-EVIDENCE (\S+)", lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        j = i + 1
        while j < len(lines) and lines[j].startswith("\\*"):
            j += 1
        block = lines[i:j]
        status_idx = next((k for k, l in enumerate(block) if l.startswith("\\* status:")), None)
        clauses = {c.group(1) for l in block if (c := CLAUSE.match(l))}
        if status_idx is not None:
            old = block[status_idx].split(":", 1)[1].strip()
            if clauses and clauses - {old}:
                block[status_idx] = "\\* status:   mixed"
                insert_at = next((k for k, l in enumerate(block) if l.startswith("\\* review:")), len(block))
                block.insert(insert_at, f"\\* relabel:  {old} -> mixed (clause statuses: {', '.join(sorted(clauses))}); handle clause by clause")
                changed.append({"property": m.group(1), "old": old, "clauses": sorted(clauses)})
        out.extend(block)
        i = j
    return out, changed


def main() -> None:
    src, dest = Path(sys.argv[1]), Path(sys.argv[2])
    if dest.exists():
        raise SystemExit(f"{dest} exists")
    shutil.copytree(src, dest)
    report = {}
    for f in sorted(dest.glob("*.tla")):
        text = f.read_text()
        new, changed = relabel(text.splitlines())
        if changed:
            f.write_text("\n".join(new) + ("\n" if text.endswith("\n") else ""))
            report[f.name] = changed
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
