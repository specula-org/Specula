#!/usr/bin/env python3
"""Mechanical check of an annotated spec directory against the original.

    python3 check_annotation.py ORIGINAL_SPEC_DIR ANNOTATED_SPEC_DIR [--json OUT]

Passes only when
  1. every .tla/.cfg file of the original exists in the annotated copy, and no other .tla/.cfg was added;
  2. .cfg files are byte-identical;
  3. in .tla files, the sequence of lines that are not `\\*` comment lines is unchanged
     (so only comment lines were added, edited or removed);
  4. every property named in a cfg (INVARIANT(S)/PROPERT(Y|IES), including commented-out
     entries) has exactly one `\\* REQ-EVIDENCE <name>` block somewhere in the .tla files;
  5. every block has a known status;
  6. SANY parses every changed module (skipped with --no-sany).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

from common import SPECULA

KEYWORDS = {"CONSTANT", "CONSTANTS", "INIT", "NEXT", "SPECIFICATION", "SYMMETRY", "VIEW", "CONSTRAINT",
            "CONSTRAINTS", "CHECK_DEADLOCK", "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES",
            "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS", "ALIAS", "POSTCONDITION"}
STATUSES = {"requirement", "impl-abstraction", "model-internal", "unknown", "mixed", "alias"}
COMMENT = re.compile(r"^\s*\\\*")
# Heuristic for model observations leaking into block text (the rule: notes are about the
# evidence, never about the model). Hits are warnings for a person to read, not failures.
MODEL_TALK = re.compile(r"concerns\.md|\bproxy\b|\bfalse alarm|\bspurious|\bvacuous|\bunmodell?ed|"
                        r"\bby construction\b|\bthe model (?:does|doesn't|does not|reads|uses|allows|lets|never|always)\b|"
                        r"\bweaker than\b|\bstronger than\b|\bbug\b", re.I)
FIELD = re.compile(r"^\s*\\\*\s*(note|clause|review)\b")


def spec_files(root: Path) -> dict[str, Path]:
    return {p.relative_to(root).as_posix(): p for p in root.rglob("*")
            if p.is_file() and p.suffix in (".tla", ".cfg") and "TTrace" not in p.name}


def properties(cfg_text: str) -> set[str]:
    names: set[str] = set()
    # Include commented-out entries (`\* INVARIANT X`, or a bare `\* X` inside such a list),
    # but drop prose comments, whose words are not property names.
    kept = []
    for line in cfg_text.splitlines():
        m = re.match(r"^\s*\\\*\s*(.*)$", line)
        if not m:
            kept.append(line)
        elif re.match(r"(INVARIANTS?|PROPERT(?:Y|IES))\b", m.group(1)) or re.fullmatch(r"[A-Za-z_]\w*\s*", m.group(1)):
            kept.append(m.group(1))
    text = "\n".join(kept)
    for match in re.finditer(r"\b(INVARIANTS?|PROPERT(?:Y|IES))\b((?:\s+[A-Za-z_]\w*)+)", text):
        for word in match.group(2).split():
            if word in KEYWORDS:
                break
            names.add(word)
    return names


def code_lines(text: str) -> list[str]:
    return [line.rstrip() for line in text.splitlines() if not COMMENT.match(line)]


def check(original: Path, annotated: Path, sany: bool = True) -> dict:
    problems: list[str] = []
    orig, ann = spec_files(original), spec_files(annotated)
    missing = sorted(set(orig) - set(ann))
    extra = sorted(set(ann) - set(orig))
    if missing:
        problems.append(f"missing files: {missing}")
    if extra:
        problems.append(f"added files: {extra}")
    changed_modules = []
    for rel in sorted(set(orig) & set(ann)):
        a, b = orig[rel].read_text(errors="replace"), ann[rel].read_text(errors="replace")
        if rel.endswith(".cfg"):
            if a != b:
                problems.append(f"cfg changed: {rel}")
        elif code_lines(a) != code_lines(b):
            problems.append(f"non-comment lines changed: {rel}")
        elif a != b:
            changed_modules.append(rel)

    props: set[str] = set()
    for rel, path in orig.items():
        if rel.endswith(".cfg"):
            props |= properties(path.read_text(errors="replace"))
    blocks: dict[str, int] = {}
    statuses: dict[str, str] = {}
    warnings: list[str] = []
    for rel, path in ann.items():
        if not rel.endswith(".tla"):
            continue
        lines = path.read_text(errors="replace").splitlines()
        for i, line in enumerate(lines):
            m = re.match(r"^\s*\\\*\s*REQ-EVIDENCE\s+(\w+)", line)
            if not m:
                continue
            name = m.group(1)
            blocks[name] = blocks.get(name, 0) + 1
            if re.search(r"->\s*(?:alias of\b|\w+\s*\(alias\b)", line):
                statuses[name] = "alias"
                continue
            for follow in lines[i + 1:i + 6]:
                s = re.match(r"^\s*\\\*\s*status:\s*([\w-]+)", follow)
                if s:
                    statuses[name] = s.group(1)
                    break
            for follow in lines[i + 1:]:
                if not COMMENT.match(follow) or re.match(r"^\s*\\\*\s*REQ-EVIDENCE", follow):
                    break
                if FIELD.match(follow) and (hit := MODEL_TALK.search(follow)):
                    warnings.append(f"{rel}: {name}: model talk ({hit.group(0)!r}): {follow.strip()[:200]}")
    for name in sorted(props):
        if blocks.get(name, 0) != 1:
            problems.append(f"property {name}: {blocks.get(name, 0)} REQ-EVIDENCE blocks")
    for name, status in sorted(statuses.items()):
        if status not in STATUSES:
            problems.append(f"block {name}: unknown status {status!r}")

    sany_results = {}
    if sany:
        classpath = f"{SPECULA}/lib/tla2tools.jar:{SPECULA}/lib/CommunityModules-deps.jar"
        for rel in changed_modules:
            path = ann[rel]
            done = subprocess.run(["java", "-cp", classpath, "tla2sany.SANY", path.name], cwd=path.parent,
                                  capture_output=True, text=True, timeout=300)
            ok = done.returncode == 0 and "Semantic errors" not in done.stdout and "*** Errors" not in done.stdout
            sany_results[rel] = ok
            if not ok:
                problems.append(f"SANY failed: {rel}: {done.stdout[-400:]}")

    counts: dict[str, int] = {}
    for name in props:
        key = statuses.get(name, "missing")
        counts[key] = counts.get(key, 0) + 1
    return {
        "ok": not problems,
        "problems": problems,
        "warnings": warnings,
        "properties": len(props),
        "blocks": sum(blocks.values()),
        "status_counts": counts,
        "changed_modules": changed_modules,
        "sany": sany_results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("original", type=Path)
    parser.add_argument("annotated", type=Path)
    parser.add_argument("--json", type=Path)
    parser.add_argument("--no-sany", action="store_true")
    args = parser.parse_args()
    result = check(args.original, args.annotated, sany=not args.no_sany)
    text = json.dumps(result, indent=2)
    if args.json:
        args.json.write_text(text + "\n")
    print(text)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
