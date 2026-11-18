#!/usr/bin/env python3
"""Assemble the skill tree of each arm.

    python3 build_skills.py [--base-ref REF] [--arm v0 --arm v1 ...] [--show-diff]

Base: the skills listed in common.SKILL_SOURCES, exported with `git archive`
from the Specula repository at --base-ref (default: HEAD), so uncommitted
working-tree edits never leak into an arm. Arms are cumulative (v1 = v0 + v1
overlay, v2 = v1 + v2 overlay); overlay files and hook lines come from
skill-overlays/ (see hooks.json). Every hook anchor must match exactly one
whole line, or the build fails.

Output: WORK/skills/<arm>/<public-skill-name>/... and
WORK/skills/<arm>/manifest.json (base commit, overlay hashes, tree hash).
Existing trees are rebuilt only with --force; a frozen arm must not change.
"""

from __future__ import annotations

import argparse
import difflib
import shutil
import tarfile
import tempfile
from pathlib import Path

from common import ARMS, HERE, SKILL_SOURCES, SPECULA, WORK, read_json, run, sha256, tree_hash, write_json

OVERLAYS = HERE / "skill-overlays"
ARM_LAYERS = {"v0": [], "v1": ["v1"], "v2": ["v1", "v2"]}


def export_base(ref: str, dest: Path) -> str:
    commit = run(["git", "-C", str(SPECULA), "rev-parse", f"{ref}^{{commit}}"]).strip()
    with tempfile.TemporaryDirectory() as tmp:
        tar_path = Path(tmp) / "skills.tar"
        run(["git", "-C", str(SPECULA), "archive", "--format=tar", "-o", str(tar_path), commit,
             *[f"skills/{src}" for src in SKILL_SOURCES.values()]])
        with tarfile.open(tar_path) as tar:
            tar.extractall(tmp, filter="tar")
        for public, src in SKILL_SOURCES.items():
            source = Path(tmp) / "skills" / src
            if not (source / "SKILL.md").is_file():
                raise RuntimeError(f"skills/{src}/SKILL.md missing at {commit}")
            shutil.copytree(source, dest / public)
    return commit


def apply_layer(layer: str, skill_root: Path, spec: dict) -> list[dict]:
    target = skill_root / "incremental-modeling"
    applied = []
    for rel in spec["files"]:
        source = OVERLAYS / rel
        dest = target / Path(rel).relative_to(layer)
        if dest.exists():
            raise RuntimeError(f"overlay {rel} would overwrite an existing base file")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        applied.append({"file": rel, "sha256": sha256(source)})
    for hook in spec["hooks"]:
        path = target / hook["file"]
        text = path.read_text(encoding="utf-8")
        if hook["anchor"] == "end":
            text = text.rstrip("\n") + "\n" + hook["insert"] + "\n"
        else:
            lines = text.split("\n")
            hits = [i for i, line in enumerate(lines) if line == hook["anchor"]]
            if len(hits) != 1:
                raise RuntimeError(f"{layer}: anchor matched {len(hits)} lines in {hook['file']}: {hook['anchor'][:80]}")
            lines[hits[0] + 1:hits[0] + 1] = hook["insert"].split("\n")
            text = "\n".join(lines)
        path.write_text(text, encoding="utf-8")
        applied.append({"hook": hook["file"], "anchor": hook["anchor"][:80]})
    return applied


def build(arm: str, ref: str, force: bool) -> Path:
    out = WORK / "skills" / arm
    if out.exists():
        if not force:
            print(f"{arm}: exists ({out}); use --force to rebuild", flush=True)
            return out
        shutil.rmtree(out)
    hooks = read_json(OVERLAYS / "hooks.json")["arms"]
    stage = Path(tempfile.mkdtemp(prefix=f".{arm}.", dir=WORK / "skills" if (WORK / "skills").exists() else None))
    try:
        tree = stage / "tree"
        tree.mkdir()
        commit = export_base(ref, tree)
        layers = []
        for layer in ARM_LAYERS[arm]:
            layers.append({"layer": layer, "applied": apply_layer(layer, tree, hooks[layer])})
        manifest = {
            "schema_version": 1,
            "arm": arm,
            "base_ref": ref,
            "base_commit": commit,
            "skills": SKILL_SOURCES,
            "layers": layers,
            "hooks_json_sha256": sha256(OVERLAYS / "hooks.json"),
            "tree_sha256": tree_hash(tree),
        }
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(tree), str(out))
        write_json(out / "manifest.json", manifest)
    finally:
        shutil.rmtree(stage, ignore_errors=True)
    print(f"{arm}: built at {out} (base {commit[:10]}, tree {manifest['tree_sha256'][:12]})", flush=True)
    return out


def show_diff(a: Path, b: Path) -> None:
    for path in sorted(b.rglob("*")):
        if not path.is_file() or path.name == "manifest.json":
            continue
        rel = path.relative_to(b)
        old = (a / rel).read_text(encoding="utf-8").splitlines() if (a / rel).exists() else []
        new = path.read_text(encoding="utf-8").splitlines()
        if old != new:
            diff = list(difflib.unified_diff(old, new, f"{a.name}/{rel}", f"{b.name}/{rel}", lineterm="", n=1))
            print("\n".join(diff if len(diff) < 40 else diff[:12] + [f"... ({len(new)} lines, new file)" if not old else "..."]))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base-ref", default="HEAD")
    parser.add_argument("--arm", action="append", dest="arms", choices=ARMS)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--show-diff", action="store_true", help="print the diff of each arm against the previous one")
    args = parser.parse_args()
    arms = args.arms or list(ARMS)
    built = {arm: build(arm, args.base_ref, args.force) for arm in arms}
    if args.show_diff:
        for prev, arm in zip(ARMS, ARMS[1:]):
            if prev in built and arm in built:
                print(f"\n===== {prev} -> {arm} =====")
                show_diff(built[prev], built[arm])
    commits = {read_json(p / "manifest.json")["base_commit"] for p in built.values()}
    if len(commits) > 1:
        raise SystemExit(f"arms were built from different base commits: {commits}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
