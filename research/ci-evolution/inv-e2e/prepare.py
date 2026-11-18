#!/usr/bin/env python3
"""Prepare one blind incremental workspace per (arm, case, rep).

    python3 prepare.py --arm v1 --case case-002 [--rep 1]
    python3 prepare.py --arm v0 --arm v1 --arm v2 --all-cases --rep 1

Layout matches the blind study's prepare_incremental.py, so the task text is unchanged:

  /work/old-source, /work/new-source       changed files at base / update (read-only)
  /work/previous/.specula-output           V0 prior (v2: with annotated spec) (read-only)
  /work/current/.specula-output            writable copy of the same prior
  /work/current/.specula-output/artifact   updated tree, two neutral commits `baseline`, `update`
  /work/model-scope.md, case.json, input-manifest.json, task.md, final-schema.json
  /work/.agents/skills (= /work/.claude/skills)   the arm's skill tree
  /work/lib, /work/tools                   TLA+ jars, infra scripts, trace debugger, network guard

The three arms differ only in .agents/skills and, for v2, the comments in previous/ and
current/ spec files. Nothing inside the workspace names the arm: the physical directory
is WORK/neutral/<random hex>, and the arm, skill-tree hash and prior hash are recorded
outside it, in WORK/attempts/<arm>/<case>/r<rep>/attempt.json (next to a `ws` symlink).
"""

from __future__ import annotations

import argparse
import secrets
import shutil
from datetime import datetime, timezone
from pathlib import Path

from common import (ARMS, BLIND_TOOLS, CASE_IDS, HERE, SPECULA, V0_ROOT, WORK, blind_helpers, check_arm,
                    check_case, read_json, sha256, tree_hash, write_json)

CACHE_DIRS = ("cargo", "cargo-target", "go-build", "go-mod", "gopath", "m2", "rebar3", "tmp")
H = blind_helpers()


def tools_dir(dest: Path) -> None:
    dest.mkdir()
    for name in ("start_background.sh", "wait_for_pid.sh", "clean_states.sh"):
        shutil.copy2(SPECULA / "scripts/infra" / name, dest / name)
    td = SPECULA / "tools/trace_debugger"
    shutil.copytree(td / "src", dest / "trace_debugger/src")
    shutil.copy2(td / "requirements.txt", dest / "trace_debugger/requirements.txt")
    shutil.copytree(BLIND_TOOLS / "network-guard", dest / "network-guard")
    for f in [*dest.glob("*.sh"), *(dest / "network-guard").iterdir()]:
        f.chmod(0o755)


def overlay_annotated(prior: Path, case_id: str) -> dict:
    annotated = WORK / "annotated" / case_id
    manifest = annotated / "manifest.json"
    if not manifest.exists() or not read_json(manifest).get("frozen"):
        raise SystemExit(f"{case_id}: no frozen annotation at {annotated}; run annotate.py first")
    replaced = []
    for path in (annotated / "spec").rglob("*"):
        if path.is_file():
            target = prior / "spec" / path.relative_to(annotated / "spec")
            if not target.exists():
                raise RuntimeError(f"annotated file has no V0 counterpart: {target}")
            shutil.copy2(path, target)
            replaced.append(path.relative_to(annotated / "spec").as_posix())
    return {"annotation_manifest_sha256": sha256(manifest), "replaced_spec_files": sorted(replaced)}


def prepare(arm: str, case_id: str, rep: int) -> Path:
    logical = WORK / "attempts" / arm / case_id / f"r{rep}"
    if logical.exists():
        raise SystemExit(f"refusing to overwrite {logical}")
    subject = WORK / "subjects" / case_id
    skills = WORK / "skills" / arm
    for need in (subject / "subject.json", skills / "manifest.json"):
        if not need.exists():
            raise SystemExit(f"missing {need}: run materialize.py / build_skills.py first")
    subject_data = read_json(subject / "subject.json")
    changed = H.normalize_changed_files(subject_data["changed_files"])
    v0 = V0_ROOT / case_id / ".specula-output"

    physical = WORK / "neutral" / secrets.token_hex(16)
    stage = physical.with_name(f".{physical.name}.tmp")
    stage.mkdir(parents=True)
    try:
        shutil.copytree(subject / "old-source", stage / "old-source", symlinks=True)
        shutil.copytree(subject / "new-source", stage / "new-source", symlinks=True)

        prior = stage / ".prior"
        shutil.copytree(v0, prior, symlinks=True)
        annotation = overlay_annotated(prior, case_id) if arm == "v2" else None
        (stage / "previous").mkdir()
        (stage / "current").mkdir()
        shutil.copytree(prior, stage / "previous/.specula-output", symlinks=True)
        shutil.copytree(prior, stage / "current/.specula-output", symlinks=True)
        prior_hash = tree_hash(prior)
        shutil.rmtree(prior)
        artifact = stage / "current/.specula-output/artifact"
        if artifact.exists() or artifact.is_symlink():
            H.remove_path(artifact)
        H.make_tree_owner_writable(stage / "current")
        synthetic = H.build_synthetic_artifact(subject / "old-tree", subject / "buggy-tree", artifact, changed)

        shutil.copy2(V0_ROOT / case_id / "scope.md", stage / "model-scope.md")
        write_json(stage / "case.json", {
            "schema_version": 1,
            "case_id": case_id,
            "category": subject_data["category"],
            "changed_files": changed,
            "source_history": {"kind": "neutral_synthetic_two_commit_history",
                               "commit_subjects": ["baseline", "update"],
                               "upstream_identifiers_included": False},
        })
        shutil.copytree(skills, stage / ".agents/skills", ignore=shutil.ignore_patterns("manifest.json"))
        (stage / "lib").mkdir()
        for jar in ("tla2tools.jar", "CommunityModules-deps.jar"):
            shutil.copy2(SPECULA / "lib" / jar, stage / "lib" / jar)
        tools_dir(stage / "tools")
        task = (HERE / "prompts/incremental-task.md").read_text().replace("INCREMENTAL_CASE_ID", case_id)
        (stage / "task.md").write_text(task)
        shutil.copy2(HERE / "prompts/final-schema.json", stage / "final-schema.json")
        for name in CACHE_DIRS:
            (stage / ".cache" / name).mkdir(parents=True)
        write_json(stage / "input-manifest.json", {
            "schema_version": 1,
            "case_id": case_id,
            "purpose": "blind_source_derived_incremental_verification",
            "inputs": {
                "old_source": "/work/old-source", "new_source": "/work/new-source",
                "previous": "/work/previous/.specula-output", "current": "/work/current/.specula-output",
                "artifact": "/work/current/.specula-output/artifact", "model_scope": "/work/model-scope.md",
                "case_metadata": "/work/case.json", "skills": "/work/.agents/skills",
                "libraries": "/work/lib", "tools": "/work/tools",
            },
            "forbidden_inputs": [
                "fixed source", "upstream Git objects, refs, tags, remotes, and revision identifiers",
                "issues, pull requests, advisories, papers, release research, and incident history",
                "user memory and paths outside /work", "general internet research",
            ],
            "network_policy": "model API and ordinary build dependencies only; history and research commands are prohibited and audited",
        })
        H.make_tree_read_only(stage / "previous")
        for name in ("old-source", "new-source", ".agents", "lib", "tools"):
            H.make_tree_read_only(stage / name)
        stage.rename(physical)
    except BaseException:
        H.remove_tree(stage)
        raise

    logical.mkdir(parents=True)
    (logical / "ws").symlink_to(physical)
    attempt = {
        "schema_version": 1,
        "arm": arm,
        "case_id": case_id,
        "rep": rep,
        "physical": str(physical),
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "skills_manifest": read_json(skills / "manifest.json"),
        "skills_tree_sha256": tree_hash(physical / ".agents/skills"),
        "prior_tree_sha256": prior_hash,
        "v0_tree_sha256": tree_hash(v0),
        "annotation": annotation,
        "task_sha256": sha256(physical / "task.md"),
        "synthetic_artifact": {k: synthetic[k] for k in ("baseline_commit", "update_commit", "commit_count")},
        "agent_started": False,
    }
    write_json(logical / "attempt.json", attempt)
    print(f"{arm} {case_id} r{rep}: prepared -> {physical.name}", flush=True)
    return logical


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--arm", action="append", dest="arms", required=True)
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--all-cases", action="store_true")
    parser.add_argument("--rep", type=int, default=1)
    args = parser.parse_args()
    cases = list(CASE_IDS) if args.all_cases else (args.cases or [])
    if not cases:
        raise SystemExit("give --case or --all-cases")
    for arm in args.arms:
        check_arm(arm)
    for case_id in cases:
        check_case(case_id)
    for case_id in cases:
        for arm in args.arms:
            prepare(arm, case_id, args.rep)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
