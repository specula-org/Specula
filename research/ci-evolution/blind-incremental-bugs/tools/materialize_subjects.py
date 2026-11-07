#!/usr/bin/env python3
"""Materialize answer-free source trees for the blind incremental experiment."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tarfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
GOLD = ROOT / "gold"
SUBJECTS = ROOT / "subjects"

REPOSITORIES = {
    "https://github.com/apache/zookeeper": Path(
        "/home/ubuntu/.cache/specula-incremental-bug-research/zookeeper"
    ),
    "https://github.com/databendlabs/openraft": Path(
        "/home/ubuntu/.cache/specula-incremental-bug-research/openraft"
    ),
    "https://github.com/etcd-io/raft": Path(
        "/home/ubuntu/.cache/specula-incremental-bug-research/etcd-raft"
    ),
    "https://github.com/cometbft/cometbft": Path(
        "/home/ubuntu/.cache/specula-incremental-bug-research/cometbft"
    ),
    "https://github.com/sonic-net/sonic-swss": Path(
        "/home/ubuntu/.cache/specula-incremental-bug-research/sonic-swss"
    ),
}


def run(args: list[str], *, cwd: Path | None = None) -> str:
    completed = subprocess.run(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {args}\n{completed.stderr}"
        )
    return completed.stdout


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tree_manifest(root: Path) -> list[dict[str, Any]]:
    result = []
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            result.append(
                {
                    "path": path.relative_to(root).as_posix(),
                    "type": "symlink",
                    "target": path.readlink().as_posix(),
                }
            )
        elif path.is_file():
            result.append(
                {
                    "path": path.relative_to(root).as_posix(),
                    "type": "file",
                    "bytes": path.stat().st_size,
                    "sha256": sha256(path),
                }
            )
    return result


def archive(repository: Path, revision: str, destination: Path, paths: list[str] | None = None) -> None:
    destination.mkdir(parents=True)
    command = ["git", "-C", str(repository), "archive", "--format=tar", revision]
    if paths:
        command.extend(["--", *paths])
    producer = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert producer.stdout is not None
    try:
        with tarfile.open(fileobj=producer.stdout, mode="r|") as archive_file:
            archive_file.extractall(destination, filter="data")
    finally:
        producer.stdout.close()
    stderr = producer.stderr.read().decode("utf-8", errors="replace") if producer.stderr else ""
    returncode = producer.wait()
    if returncode != 0:
        raise RuntimeError(f"git archive failed ({returncode}): {repository} {revision}\n{stderr}")


def exists_at(repository: Path, revision: str, path: str) -> bool:
    completed = subprocess.run(
        ["git", "-C", str(repository), "cat-file", "-e", f"{revision}:{path}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return completed.returncode == 0


def diff_entries(repository: Path, old: str, buggy: str) -> list[dict[str, str]]:
    output = run(
        [
            "git",
            "-C",
            str(repository),
            "diff",
            "--name-status",
            "-M",
            old,
            buggy,
        ]
    )
    entries: list[dict[str, str]] = []
    for line in output.splitlines():
        fields = line.split("\t")
        status = fields[0]
        if status.startswith(("R", "C")):
            entries.append(
                {"status": status, "old_path": fields[1], "new_path": fields[2]}
            )
        else:
            entries.append(
                {"status": status, "old_path": fields[1], "new_path": fields[1]}
            )
    return entries


def main() -> int:
    candidates = json.loads((GOLD / "candidates.json").read_text(encoding="utf-8"))
    case_map = json.loads((GOLD / "case-map.json").read_text(encoding="utf-8"))
    by_id = {item["id"]: item for item in candidates["cases"]}
    if SUBJECTS.exists() and any(SUBJECTS.iterdir()):
        raise RuntimeError(f"refusing to overwrite nonempty subject root: {SUBJECTS}")
    SUBJECTS.mkdir(parents=True, exist_ok=True)

    public_cases = []
    private_cases = []
    for mapped in case_map["mapping"]:
        case_id = mapped["case_id"]
        candidate = by_id[mapped["candidate_id"]]
        repository = REPOSITORIES[candidate["repository"]]
        if not (repository / ".git").is_dir():
            raise RuntimeError(f"missing repository: {repository}")

        old = candidate["old_revision"]
        buggy = candidate["buggy_revision"]
        fixed = candidate["fixed_revision"]
        for revision in (old, buggy, fixed):
            run(["git", "-C", str(repository), "cat-file", "-e", f"{revision}^{{commit}}"])
        parents = run(["git", "-C", str(repository), "show", "-s", "--format=%P", buggy]).split()
        if parents != [old]:
            raise RuntimeError(f"{case_id}: old is not the sole buggy parent: {parents}")
        subprocess.run(
            ["git", "-C", str(repository), "merge-base", "--is-ancestor", buggy, fixed],
            check=True,
        )

        destination = SUBJECTS / case_id
        old_tree = destination / "old-tree"
        buggy_tree = destination / "buggy-tree"
        fixed_tree = destination / "fixed-tree"
        old_source = destination / "old-source"
        new_source = destination / "new-source"
        entries = diff_entries(repository, old, buggy)

        archive(repository, old, old_tree)
        archive(repository, buggy, buggy_tree)
        archive(repository, fixed, fixed_tree)

        old_paths = sorted(
            {
                item["old_path"]
                for item in entries
                if exists_at(repository, old, item["old_path"])
            }
        )
        new_paths = sorted(
            {
                item["new_path"]
                for item in entries
                if exists_at(repository, buggy, item["new_path"])
            }
        )
        if old_paths:
            archive(repository, old, old_source, old_paths)
        else:
            old_source.mkdir()
        if new_paths:
            archive(repository, buggy, new_source, new_paths)
        else:
            new_source.mkdir()

        public = {
            "schema_version": 1,
            "case_id": case_id,
            "category": candidate["category"],
            "changed_files": entries,
            "old_source_files": old_paths,
            "new_source_files": new_paths,
        }
        (destination / "subject.json").write_text(
            json.dumps(public, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        private = {
            **public,
            "candidate_id": candidate["id"],
            "repository": candidate["repository"],
            "repository_path": str(repository),
            "old_revision": old,
            "buggy_revision": buggy,
            "fixed_revision": fixed,
            "old_tree_manifest": tree_manifest(old_tree),
            "buggy_tree_manifest": tree_manifest(buggy_tree),
            "fixed_tree_manifest": tree_manifest(fixed_tree),
            "old_source_manifest": tree_manifest(old_source),
            "new_source_manifest": tree_manifest(new_source),
        }
        (destination / "provenance.private.json").write_text(
            json.dumps(private, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        public_cases.append(public)
        private_cases.append(private)
        print(
            f"{case_id}: changed={len(entries)} old_files={len(old_paths)} "
            f"new_files={len(new_paths)}"
        )

    (ROOT / "cohort.json").write_text(
        json.dumps(
            {"schema_version": 1, "cases": public_cases}, indent=2, sort_keys=True
        )
        + "\n",
        encoding="utf-8",
    )
    (GOLD / "cohort.private.json").write_text(
        json.dumps(
            {"schema_version": 1, "cases": private_cases}, indent=2, sort_keys=True
        )
        + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
