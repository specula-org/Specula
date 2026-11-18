"""Layer-1 check: is a decision well formed, and do its citations point at real packet lines?

The agents choose their own JSON field names, so fields are matched loosely:
the entry list is `entries`, the decision is `decision` or `action`, the name is `name` or `property`, the witness is any key containing "witness" or "disagree",
the predicate is any key containing "predicate" or "expression", evidence is any key containing "evidence".

Usage: python3 check_decision.py results/<run> [--packet DIR]   (writes results/<run>/check.json)
       python3 check_decision.py --all
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
EDITS = {"modify", "add", "remove"}
CITATION = re.compile(r"((?:old|new)/(?:source|spec)/[\w./-]+|update\.patch)(?::(\d+)(?:\s*-\s*(\d+))?)?")


def field(entry: dict, *needles: str):
    for key, value in entry.items():
        if any(n in key.lower() for n in needles):
            return value
    return None


def decision_kind(entry: dict) -> str:
    value = str(entry.get("decision", entry.get("action", ""))).lower()
    for kind in ("modify", "add", "remove", "keep", "unresolved"):
        if value.startswith(kind):
            return kind
    return value or "missing"


def truth(value):
    """Normalize a claimed/TLC truth value; None when absent or not a boolean."""
    if isinstance(value, dict):
        value = value.get("value", value.get("result"))
    if isinstance(value, bool):
        return value
    text = str(value).strip().lower()
    if text in ("true", "holds", "pass", "passes", "satisfied", "accept", "accepts"):
        return True
    if text in ("false", "violated", "fail", "fails", "rejects", "reject"):
        return False
    return None


def implementation_citation(rel: str, line: int, packet: Path, end: int | None = None) -> bool:
    """True when rel:line[-end] contains no comment at all in non-test Go code (not valid requirement evidence)."""
    return all(implementation_line(rel, n, packet) for n in range(line, (end or line) + 1))


def implementation_line(rel: str, line: int, packet: Path) -> bool:
    if not rel.endswith(".go") or rel.endswith("_test.go") or "/testdata/" in rel:
        return False
    target = packet / rel
    if not target.exists():
        return False
    lines = target.read_text(errors="replace").splitlines()
    if not 1 <= line <= len(lines):
        return False
    text = lines[line - 1].strip()
    in_block = False
    for prior in lines[:line - 1]:  # inside a /* ... */ block comment (e.g. doc.go)
        if "/*" in prior:
            in_block = True
        if "*/" in prior:
            in_block = False
    if in_block:
        return False
    return bool(text) and "//" not in text  # a line carrying a comment may be cited for that comment


def check_evidence(run_dir: Path, packet: Path) -> dict | None:
    path = run_dir / "evidence.json"
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        return {"status": f"invalid json: {exc}"}
    records = data if isinstance(data, list) else next((v for v in data.values() if isinstance(v, list)), [])
    out = {"status": "ok", "records": len(records), "kinds": {}, "verdicts": {}, "cells": {},
           "tlc_evaluated": 0, "claim_mismatch": [], "code_observed": 0, "implementation_cited_as_requirement": []}
    for r in records:
        if not isinstance(r, dict):
            continue
        rid = str(r.get("id", "?"))
        for key, bucket in (("kind", "kinds"), ("verdict", "verdicts"), ("cell", "cells")):
            v = str(r.get(key, "missing"))[:60]
            out[bucket][v] = out[bucket].get(v, 0) + 1
        for side in ("old_property", "proposed_property"):
            v = r.get(side)
            if isinstance(v, dict):
                claimed, tlc = truth(v.get("claimed")), truth(v.get("tlc"))
                if tlc is not None:
                    out["tlc_evaluated"] += 1
                    if claimed is not None and claimed != tlc:
                        out["claim_mismatch"].append(f"{rid}:{side}")
        obs = json.dumps(r.get("code_observation", "")).lower()
        if obs and "not_representable" not in obs and "unknown" not in obs and ("go test" in obs or "_test.go" in obs):
            out["code_observed"] += 1
        req = r.get("requirement")
        cites = json.dumps(req.get("citations", []) if isinstance(req, dict) else [])
        for m in CITATION.finditer(cites):
            if m.group(2) and implementation_citation(m.group(1), int(m.group(2)), packet, int(m.group(3)) if m.group(3) else None):
                out["implementation_cited_as_requirement"].append(f"{rid}: {m.group(1)}:{m.group(2)}")
    return out


def check(run_dir: Path, packet: Path) -> dict:
    report: dict = {"run": run_dir.name}
    path = run_dir / "decision.json"
    if not path.exists():
        report["status"] = "no decision.json"
        return report
    try:
        decision = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        report["status"] = f"invalid json: {exc}"
        return report
    entries = decision.get("entries")
    if not isinstance(entries, list):
        report["status"] = "no entries list"
        return report

    counts: dict[str, int] = {}
    edits_without_witness, edits_without_predicate, entries_without_evidence = [], [], []
    for entry in entries:
        kind = decision_kind(entry)
        counts[kind] = counts.get(kind, 0) + 1
        name = entry.get("name", entry.get("property", "?"))
        if kind in EDITS and not field(entry, "witness", "disagree"):
            edits_without_witness.append(name)
        if kind in {"modify", "add"} and not field(entry, "predicate", "expression"):
            edits_without_predicate.append(name)
        if not field(entry, "evidence"):
            entries_without_evidence.append(name)

    lines_cache: dict[Path, int] = {}
    cited, bad = 0, []
    for match in CITATION.finditer(json.dumps(decision)):
        rel, start, end = match.group(1).rstrip("."), match.group(2), match.group(3)
        target = packet / rel
        cited += 1
        if not target.exists():
            bad.append(f"{rel}: no such file")
            continue
        if start:
            if target not in lines_cache:
                lines_cache[target] = len(target.read_text(errors="replace").splitlines())
            last = int(end or start)
            if last > lines_cache[target]:
                bad.append(f"{rel}:{start}{'-' + end if end else ''}: file has {lines_cache[target]} lines")

    report.update(
        status="ok",
        entries=len(entries),
        decisions=counts,
        edits_without_witness=edits_without_witness,
        edits_without_predicate=edits_without_predicate,
        entries_without_evidence=entries_without_evidence,
        citations=cited,
        bad_citations=sorted(set(bad)),
        top_level_keys=list(decision),
    )
    evidence = check_evidence(run_dir, packet)
    if evidence is not None:
        report["evidence"] = evidence
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("run", nargs="?")
    parser.add_argument("--packet")
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    runs = sorted(p.parent for p in (HERE / "results").glob("*/run.json")) if args.all else [Path(args.run).resolve()]
    for run_dir in runs:
        if args.packet:
            packet = Path(args.packet)
        else:
            packet = Path(json.loads((run_dir / "run.json").read_text())["log"]).parent / "workspace"
        report = check(run_dir, packet)
        (run_dir / "check.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({k: report.get(k) for k in ("run", "status", "entries", "decisions", "citations")}),
              "bad_citations:", len(report.get("bad_citations", [])),
              "edits_without_witness:", len(report.get("edits_without_witness", [])))


if __name__ == "__main__":
    main()
