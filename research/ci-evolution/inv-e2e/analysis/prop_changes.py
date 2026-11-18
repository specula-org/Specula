#!/usr/bin/env python3
"""Which prior properties a run changed, deleted or stopped checking (formula text, comments stripped).

    python3 analysis/prop_changes.py ARM CASE [--rep 1]
"""
import argparse, json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import WORK
from check_annotation import properties

def defs(spec: Path) -> dict:
    out = {}
    for f in spec.glob("*.tla"):
        if "TTrace" in f.name: continue
        lines = [l for l in f.read_text(errors="replace").splitlines() if not re.match(r"^\s*\\\*", l)]
        text = "\n".join(re.sub(r"\\\*.*$", "", l).rstrip() for l in lines)
        for m in re.finditer(r"^([A-Za-z_]\w*)\s*(\([^)]*\))?\s*==(.*?)(?=^\S|\Z)", text, re.S | re.M):
            out[f"{m.group(1)}"] = (f.name, re.sub(r"\s+", " ", m.group(3)).strip())
    return out

def checked(spec: Path) -> dict:
    res = {}
    for f in spec.glob("*.cfg"):
        if "TTrace" in f.name: continue
        txt = f.read_text(errors="replace")
        active = "\n".join(l for l in txt.splitlines() if not l.strip().startswith("\\*"))
        for p in properties(active): res.setdefault(p, []).append(f.name)
    return res

ap = argparse.ArgumentParser(); ap.add_argument("arm"); ap.add_argument("case"); ap.add_argument("--rep", default="1")
a = ap.parse_args()
ws = (WORK / "attempts" / a.arm / a.case / f"r{a.rep}" / "ws").resolve()
old, new = ws / "previous/.specula-output/spec", ws / "current/.specula-output/spec"
od, nd, oc, nc = defs(old), defs(new), checked(old), checked(new)
props = sorted(set(oc))
rows = []
for p in props:
    o, n = od.get(p), nd.get(p)
    state = "deleted" if n is None else ("same" if o and o[1] == n[1] else "formula-changed")
    rows.append({"property": p, "definition": state, "checked_before": len(oc.get(p, [])),
                 "checked_after": len(nc.get(p, []))})
added = sorted(set(nc) - set(oc))
print(json.dumps({"prior_properties": rows, "new_checked_properties": added}, indent=1))
