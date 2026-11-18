#!/usr/bin/env python3
"""Per-run behavior timeline from activity.jsonl (stream-json has no timestamps; positions are
assistant-turn indices, and `~min` scales the index linearly by the run's wall time).

    python3 analysis/timeline.py ARM CASE [--rep 1] [--pattern REGEX ...]
"""
import argparse, json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import RESULTS, WORK

OVERLAYS = re.compile(r"divergence-evidence\.md|ledger-usage\.md")
VIOL = re.compile(r"(?:Invariant|Property|Temporal properties?)\s+(\w+)?\s*(?:is|was|were)\s+violated", re.I)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("arm"); ap.add_argument("case"); ap.add_argument("--rep", default="1")
    ap.add_argument("--pattern", action="append", default=[])
    a = ap.parse_args()
    act = WORK / "attempts" / a.arm / a.case / f"r{a.rep}" / "log" / "activity.jsonl"
    run = json.loads((RESULTS / a.arm / a.case / f"r{a.rep}" / "run.json").read_text())
    events = [json.loads(l) for l in act.open() if l.strip().startswith("{")]
    turns = sum(1 for e in events if e.get("type") == "assistant")
    wall = run["wall_seconds"] / 60
    out = {"turns": turns, "wall_min": round(wall, 1), "overlay_reads": [], "req_evidence_uses": [],
           "violations": [], "patterns": {p: None for p in a.pattern}, "phases": []}
    t = 0
    for e in events:
        if e.get("type") == "assistant":
            t += 1
            for c in e["message"].get("content", []) or []:
                s = json.dumps(c.get("input")) if c.get("type") == "tool_use" else c.get("text", "") or ""
                where = {"turn": t, "~min": round(wall * t / max(turns, 1))}
                if c.get("type") == "tool_use" and OVERLAYS.search(s):
                    out["overlay_reads"].append(where | {"files": sorted(set(OVERLAYS.findall(s)))})
                if c.get("type") == "tool_use" and re.search(r"REQ-EVIDENCE|ledger_status|watch_touched|status:\s*requirement", s):
                    out["req_evidence_uses"].append(where | {"cmd": s[:160]})
                for p in a.pattern:
                    if out["patterns"][p] is None and re.search(p, s, re.I):
                        out["patterns"][p] = where | {"text": s[:200]}
                if c.get("type") == "text" and re.search(r"\b(Phase|Stage|Part)\s*\d", s):
                    m = re.search(r"\b(?:Phase|Stage|Part)\s*\d[a-z]?[^\n]{0,60}", s)
                    out["phases"].append(where | {"text": m.group(0)})
        elif e.get("type") == "user":
            for c in e["message"].get("content", []) or []:
                if isinstance(c, dict) and c.get("type") == "tool_result":
                    s = json.dumps(c.get("content"))
                    for m in VIOL.finditer(s):
                        out["violations"].append({"turn": t, "~min": round(wall * t / max(turns, 1)), "prop": m.group(1)})
    out["phases"] = out["phases"][:25]
    print(json.dumps(out, indent=1))

main()
