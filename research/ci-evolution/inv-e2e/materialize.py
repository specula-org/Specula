#!/usr/bin/env python3
"""Materialize answer-free subjects for each blind case.

For every case: clone the upstream repository once (WORK/repos), then write
WORK/subjects/<case>/ with

  old-tree/     full source at the base commit (exact-old)
  buggy-tree/   full source at the update commit
  old-source/   changed files only, at the base commit
  new-source/   changed files only, at the update commit
  subject.json  case id, category, changed files (from cohort.json)

and WORK/history/<case>.git, a bare repository holding only the base commit and
its ancestors. It backs tools/hist.sh for the v2 annotation step, so the
annotator can read history up to the base revision and nothing after it.

Only public inputs are used: cases.json and cohort.json. No fixed revision,
issue, or bug description is read.

    python3 materialize.py [--case case-002 ...]
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path

from common import WORK, CASE_IDS, cases_json, cohort_json, check_case, run, write_json, tree_hash


def clone(url: str) -> Path:
    name = url.rstrip("/").split("/")[-1]
    dest = WORK / "repos" / f"{name}.git"
    if not dest.exists():
        dest.parent.mkdir(parents=True, exist_ok=True)
        print(f"cloning {url} -> {dest}", flush=True)
        run(["git", "clone", "--bare", "--quiet", url, str(dest)])
    return dest


def ensure_commit(repo: Path, commit: str) -> None:
    if subprocess.run(["git", "-C", str(repo), "cat-file", "-e", f"{commit}^{{commit}}"]).returncode != 0:
        run(["git", "-C", str(repo), "fetch", "--quiet", "origin", commit])


def archive(repo: Path, commit: str, dest: Path, paths: list[str] | None = None) -> None:
    dest.mkdir(parents=True)
    with tempfile.NamedTemporaryFile(suffix=".tar") as tmp:
        run(["git", "-C", str(repo), "archive", "--format=tar", "-o", tmp.name, commit, *(paths or [])])
        with tarfile.open(tmp.name) as tar:
            tar.extractall(dest, filter="tar")


def name_status(repo: Path, old: str, new: str) -> list[tuple[str, str, str]]:
    out = run(["git", "-C", str(repo), "diff", "--no-renames", "--name-status", old, new])
    rows = []
    for line in out.splitlines():
        status, path = line.split("\t", 1)
        rows.append((status[0], path, path))
    return sorted(rows)


def history_repo(repo: Path, base: str, case_id: str) -> Path:
    dest = WORK / "history" / f"{case_id}.git"
    if dest.exists():
        return dest
    dest.parent.mkdir(parents=True, exist_ok=True)
    run(["git", "init", "--quiet", "--bare", str(dest)])
    run(["git", "-C", str(dest), "fetch", "--quiet", "--no-tags", str(repo), f"{base}:refs/heads/base"])
    run(["git", "-C", str(dest), "symbolic-ref", "HEAD", "refs/heads/base"])
    # Drop anything that is not reachable from base.
    run(["git", "-C", str(dest), "gc", "--quiet", "--prune=now"])
    return dest


def materialize(case_id: str) -> dict:
    case = cases_json()[case_id]
    cohort = cohort_json()[case_id]
    subject = WORK / "subjects" / case_id
    if (subject / "subject.json").exists():
        print(f"{case_id}: already materialized", flush=True)
        return {"case_id": case_id, "status": "exists"}
    repo = clone(case["repository"])
    base, update = case["base_commit"], case["update_commit"]
    for commit in (base, update):
        ensure_commit(repo, commit)

    changed = cohort["changed_files"]
    expected_paths = {c["new_path"] for c in changed} | {c["old_path"] for c in changed}
    actual_paths = {p for _, p, _ in name_status(repo, base, update)}
    if actual_paths != expected_paths:
        raise RuntimeError(f"{case_id}: diff {base}..{update} does not match cohort.json changed_files: "
                           f"only in git {sorted(actual_paths - expected_paths)[:5]}, "
                           f"only in cohort {sorted(expected_paths - actual_paths)[:5]}")

    stage = Path(tempfile.mkdtemp(prefix=f".{case_id}.", dir=subject.parent if subject.parent.exists() else None))
    try:
        archive(repo, base, stage / "old-tree")
        archive(repo, update, stage / "buggy-tree")
        old_paths = [c["old_path"] for c in changed if c["status"][0] != "A"]
        new_paths = [c["new_path"] for c in changed if c["status"][0] != "D"]
        archive(repo, base, stage / "old-source", old_paths)
        archive(repo, update, stage / "new-source", new_paths)
        write_json(stage / "subject.json", {
            "schema_version": 1,
            "case_id": case_id,
            "category": cohort["category"],
            "changed_files": changed,
            "trees": {name: tree_hash(stage / name) for name in ("old-tree", "buggy-tree", "old-source", "new-source")},
        })
        subject.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(stage), str(subject))
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise
    hist = history_repo(repo, base, case_id)
    print(f"{case_id}: materialized ({len(changed)} changed files); history {hist}", flush=True)
    return {"case_id": case_id, "status": "materialized"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--case", action="append", dest="cases")
    args = parser.parse_args()
    for case_id in args.cases or CASE_IDS:
        check_case(case_id)
        materialize(case_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
