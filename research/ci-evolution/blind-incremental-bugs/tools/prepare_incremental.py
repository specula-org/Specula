#!/usr/bin/env python3
"""Prepare audit-gated, answer-free workspaces for blind incremental runs.

This script prepares inputs only.  It never starts an Agent or runs the
incremental workflow.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
SPECULA_ROOT = Path("/home/ubuntu/Specula")
CASE_IDS = [f"case-{number:03d}" for number in range(1, 13)]
DEFAULT_BASELINE_ATTEMPT = "attempt-004"
DEFAULT_INCREMENTAL_ATTEMPT = "attempt-001"

# The baseline attempt already contains a frozen copy of the shared skills.
# Only incremental-only skills are added from the same Specula checkout.
ADDITIONAL_SKILLS = {
    "incremental-modeling": "incremental-modeling",
    "bug-confirmation": "bug-confirmation",
}
REQUIRED_SHARED_SKILLS = {
    "code-analysis",
    "spec-generation",
    "harness-generation",
    "tla-trace-workflow",
    "validation-workflow",
    "tla-checking-workflow",
}
CACHE_DIRS = (
    "cargo",
    "cargo-target",
    "go-build",
    "go-mod",
    "gopath",
    "m2",
    "rebar3",
    "tmp",
)


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise RuntimeError(f"missing required JSON: {path}") from error
    except json.JSONDecodeError as error:
        raise RuntimeError(f"invalid JSON in {path}: {error}") from error
    if not isinstance(value, dict):
        raise RuntimeError(f"expected a JSON object: {path}")
    return value


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tree_identity(root: Path, *, exclude_root_names: set[str] | None = None) -> dict[str, Any]:
    """Return mode-sensitive and content-only identities for a filesystem tree."""

    if not root.is_dir():
        raise RuntimeError(f"tree root is not a directory: {root}")
    excluded = exclude_root_names or set()
    full_digest = hashlib.sha256()
    content_digest = hashlib.sha256()
    regular_files = 0
    regular_file_bytes = 0
    symlinks = 0
    directories = 0

    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames.sort()
        filenames.sort()
        base = Path(directory)
        if base == root:
            dirnames[:] = [name for name in dirnames if name not in excluded]
            filenames = [name for name in filenames if name not in excluded]
        entries = [(name, base / name) for name in dirnames + filenames]
        for _name, path in entries:
            relative = path.relative_to(root).as_posix()
            metadata = path.lstat()
            mode = stat.S_IMODE(metadata.st_mode)
            if stat.S_ISLNK(metadata.st_mode):
                kind = "symlink"
                content = os.readlink(path).encode("utf-8", errors="surrogateescape")
                symlinks += 1
            elif stat.S_ISREG(metadata.st_mode):
                kind = "file"
                content = path.read_bytes()
                regular_files += 1
                regular_file_bytes += len(content)
            elif stat.S_ISDIR(metadata.st_mode):
                kind = "dir"
                content = b""
                directories += 1
            else:
                raise RuntimeError(f"unsupported tree entry: {path}")
            content_hash = hashlib.sha256(content).digest()
            for digest, include_mode in ((full_digest, True), (content_digest, False)):
                digest.update(kind.encode())
                digest.update(b"\0")
                if include_mode:
                    digest.update(f"{mode:o}".encode())
                    digest.update(b"\0")
                digest.update(relative.encode())
                digest.update(b"\0")
                digest.update(content_hash)
                digest.update(b"\0")

    return {
        "sha256": full_digest.hexdigest(),
        "content_sha256": content_digest.hexdigest(),
        "regular_files": regular_files,
        "regular_file_bytes": regular_file_bytes,
        "symlinks": symlinks,
        "directories": directories,
    }


def run(
    command: list[str],
    *,
    cwd: Path | None = None,
    environment: dict[str, str] | None = None,
) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {command}\n{completed.stdout}"
        )
    return completed.stdout


def validate_attempt_name(value: str, label: str) -> None:
    if Path(value).name != value or value in {"", ".", ".."}:
        raise SystemExit(f"invalid {label}: {value!r}")


def validate_relative_path(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} must be a nonempty string")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "." in path.parts:
        raise RuntimeError(f"unsafe {label}: {value!r}")
    return value


def normalize_changed_files(value: Any) -> list[dict[str, str]]:
    if not isinstance(value, list):
        raise RuntimeError("subject changed_files must be an array")
    result: list[dict[str, str]] = []
    for index, entry in enumerate(value):
        if not isinstance(entry, dict):
            raise RuntimeError(f"changed_files[{index}] must be an object")
        status_value = entry.get("status")
        if not isinstance(status_value, str) or not status_value:
            raise RuntimeError(f"changed_files[{index}].status is invalid")
        status_prefix = status_value[0]
        if status_prefix not in {"A", "C", "D", "M", "R", "T"}:
            raise RuntimeError(f"changed_files[{index}].status is unsupported: {status_value}")
        old_path = validate_relative_path(entry.get("old_path"), f"changed_files[{index}].old_path")
        new_path = validate_relative_path(entry.get("new_path"), f"changed_files[{index}].new_path")
        result.append({"status": status_value, "old_path": old_path, "new_path": new_path})
    return result


def parse_name_status(output: str) -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for line in output.splitlines():
        if not line:
            continue
        fields = line.split("\t")
        status_value = fields[0]
        if status_value.startswith(("R", "C")):
            if len(fields) != 3:
                raise RuntimeError(f"unexpected rename/copy diff line: {line!r}")
            old_path, new_path = fields[1], fields[2]
        else:
            if len(fields) != 2:
                raise RuntimeError(f"unexpected diff line: {line!r}")
            old_path = new_path = fields[1]
        result.append(
            {"status": status_value, "old_path": old_path, "new_path": new_path}
        )
    return result


def comparable_changed_files(entries: list[dict[str, str]]) -> list[tuple[str, str, str]]:
    return sorted((entry["status"], entry["old_path"], entry["new_path"]) for entry in entries)


def copy_tree_checked(source: Path, destination: Path) -> dict[str, Any]:
    before = tree_identity(source)
    shutil.copytree(source, destination, symlinks=True)
    after = tree_identity(source)
    copied = tree_identity(destination)
    if before != after:
        raise RuntimeError(f"source tree changed while it was copied: {source}")
    if before != copied:
        raise RuntimeError(f"tree copy is not byte/mode identical: {source} -> {destination}")
    return copied


def remove_path(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)
    else:
        raise RuntimeError(f"cannot remove unsupported path: {path}")


def replace_worktree_contents(source: Path, destination: Path) -> dict[str, Any]:
    for child in sorted(destination.iterdir()):
        if child.name == ".git":
            continue
        remove_path(child)
    before = tree_identity(source)
    for child in sorted(source.iterdir()):
        target = destination / child.name
        if child.is_symlink():
            target.symlink_to(os.readlink(child))
            shutil.copystat(child, target, follow_symlinks=False)
        elif child.is_dir():
            shutil.copytree(child, target, symlinks=True)
        elif child.is_file():
            shutil.copy2(child, target)
        else:
            raise RuntimeError(f"unsupported source entry: {child}")
    after = tree_identity(source)
    copied = tree_identity(destination, exclude_root_names={".git"})
    if before != after:
        raise RuntimeError(f"source tree changed while it was copied: {source}")
    if before != copied:
        raise RuntimeError(f"artifact worktree does not match source: {source}")
    return copied


def git_environment(timestamp: str) -> dict[str, str]:
    environment = os.environ.copy()
    environment.update(
        {
            "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_AUTHOR_NAME": "Experiment",
            "GIT_AUTHOR_EMAIL": "experiment@invalid",
            "GIT_COMMITTER_NAME": "Experiment",
            "GIT_COMMITTER_EMAIL": "experiment@invalid",
            "GIT_AUTHOR_DATE": timestamp,
            "GIT_COMMITTER_DATE": timestamp,
        }
    )
    return environment


def commit_all(repository: Path, message: str, timestamp: str) -> str:
    environment = git_environment(timestamp)
    run(["git", "add", "-f", "-A", "."], cwd=repository, environment=environment)
    run(
        ["git", "commit", "-q", "--no-gpg-sign", "-m", message],
        cwd=repository,
        environment=environment,
    )
    if run(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=repository):
        raise RuntimeError(f"synthetic repository is dirty after {message!r} commit")
    return run(["git", "rev-parse", "HEAD"], cwd=repository).strip()


def build_synthetic_artifact(
    old_tree: Path,
    updated_tree: Path,
    destination: Path,
    expected_changes: list[dict[str, str]],
) -> dict[str, Any]:
    old_identity = copy_tree_checked(old_tree, destination)
    run(["git", "init", "-q", "-b", "experiment", "--template="], cwd=destination)
    run(["git", "config", "--local", "user.name", "Experiment"], cwd=destination)
    run(["git", "config", "--local", "user.email", "experiment@invalid"], cwd=destination)
    run(["git", "config", "--local", "commit.gpgsign", "false"], cwd=destination)
    run(["git", "config", "--local", "core.autocrlf", "false"], cwd=destination)
    run(["git", "config", "--local", "core.filemode", "true"], cwd=destination)

    baseline_commit = commit_all(destination, "baseline", "2000-01-01T00:00:00Z")
    updated_identity = replace_worktree_contents(updated_tree, destination)
    update_commit = commit_all(destination, "update", "2000-01-02T00:00:00Z")

    commit_count = int(run(["git", "rev-list", "--all", "--count"], cwd=destination).strip())
    subjects = run(["git", "log", "--reverse", "--format=%s", "--all"], cwd=destination).splitlines()
    remotes = run(["git", "remote"], cwd=destination).splitlines()
    tags = run(["git", "tag", "--list"], cwd=destination).splitlines()
    branches = run(
        ["git", "for-each-ref", "--format=%(refname)", "refs/heads"], cwd=destination
    ).splitlines()
    parent = run(["git", "show", "-s", "--format=%P", update_commit], cwd=destination).split()
    if commit_count != 2:
        raise RuntimeError(f"synthetic repository has {commit_count} commits, expected 2")
    if subjects != ["baseline", "update"]:
        raise RuntimeError(f"unexpected synthetic history: {subjects}")
    if remotes or tags or branches != ["refs/heads/experiment"]:
        raise RuntimeError(
            f"synthetic repository contains unexpected refs: remotes={remotes}, tags={tags}, branches={branches}"
        )
    if parent != [baseline_commit]:
        raise RuntimeError("synthetic update commit does not have only baseline as its parent")

    actual_changes = parse_name_status(
        run(
            ["git", "diff", "--name-status", "-M", baseline_commit, update_commit],
            cwd=destination,
        )
    )
    if comparable_changed_files(actual_changes) != comparable_changed_files(expected_changes):
        raise RuntimeError(
            "synthetic baseline/update diff does not match public subject metadata:\n"
            f"expected={dump_json(expected_changes)}actual={dump_json(actual_changes)}"
        )

    fsck_output = run(
        ["git", "fsck", "--full", "--no-reflogs", "--unreachable"], cwd=destination
    ).strip()
    if fsck_output:
        raise RuntimeError(f"synthetic repository contains unreachable objects:\n{fsck_output}")
    final_identity = tree_identity(destination, exclude_root_names={".git"})
    if final_identity != updated_identity:
        raise RuntimeError("synthetic artifact drifted after its update commit")

    return {
        "branch": "experiment",
        "commit_count": commit_count,
        "commit_subjects": subjects,
        "baseline_commit": baseline_commit,
        "update_commit": update_commit,
        "remotes": remotes,
        "tags": tags,
        "old_worktree_identity": old_identity,
        "updated_worktree_identity": updated_identity,
        "changed_files": actual_changes,
    }


def make_tree_read_only(root: Path) -> None:
    for directory, dirnames, filenames in os.walk(root, topdown=False, followlinks=False):
        base = Path(directory)
        for name in filenames:
            path = base / name
            if path.is_symlink():
                continue
            path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)
        for name in dirnames:
            path = base / name
            if path.is_symlink():
                continue
            path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)
        if not base.is_symlink():
            base.chmod(stat.S_IMODE(base.stat().st_mode) & ~0o222)


def make_tree_owner_writable(root: Path) -> None:
    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        base = Path(directory)
        if not base.is_symlink():
            base.chmod(stat.S_IMODE(base.stat().st_mode) | stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)
        for name in dirnames + filenames:
            path = base / name
            if path.is_symlink():
                continue
            mode = stat.S_IMODE(path.stat().st_mode) | stat.S_IRUSR | stat.S_IWUSR
            if path.is_dir():
                mode |= stat.S_IXUSR
            path.chmod(mode)


def remove_tree(path: Path) -> None:
    def onerror(function: Any, filename: str, _error: Any) -> None:
        target = Path(filename)
        if not target.is_symlink():
            target.chmod(stat.S_IMODE(target.stat().st_mode) | stat.S_IWUSR | stat.S_IXUSR)
        function(filename)

    if path.exists():
        # Prepared inputs deliberately contain read-only directories.  Restore
        # owner write/search bits before removing a failed staging tree.
        make_tree_owner_writable(path)
        shutil.rmtree(path, onerror=onerror)


def require_accepted_audit(baseline: Path, case_id: str, baseline_attempt: str) -> dict[str, Any]:
    audit_path = baseline / "baseline-audit.json"
    if audit_path.is_symlink() or not audit_path.is_file():
        raise RuntimeError(f"missing regular baseline audit: {audit_path}")
    audit = read_json(audit_path)
    verdict = audit.get("verdict")
    if verdict != "ACCEPT":
        raise RuntimeError(
            f"{case_id}: refusing incremental preparation because baseline audit verdict is {verdict!r}, not 'ACCEPT'"
        )
    if "case_id" in audit and audit["case_id"] != case_id:
        raise RuntimeError(f"{case_id}: baseline audit case_id does not match its path")
    for key in ("attempt", "attempt_name", "baseline_attempt"):
        if key in audit and audit[key] != baseline_attempt:
            raise RuntimeError(f"{case_id}: baseline audit {key} does not match {baseline_attempt}")
    return {
        "path": audit_path,
        "sha256": sha256(audit_path),
        "verdict": verdict,
    }


def preflight_case(case_id: str, baseline_attempt: str, incremental_attempt: str) -> dict[str, Any]:
    subject = ROOT / "subjects" / case_id
    baseline = ROOT / "baselines" / case_id / baseline_attempt
    destination = ROOT / "cases" / case_id / incremental_attempt
    if destination.exists():
        raise RuntimeError(f"refusing to overwrite existing incremental attempt: {destination}")

    # Audit acceptance is the first and authoritative gate.  Do not inspect or
    # stage a baseline that has not been explicitly accepted.
    audit = require_accepted_audit(baseline, case_id, baseline_attempt)

    required = [
        subject / "subject.json",
        subject / "old-tree",
        subject / "buggy-tree",
        subject / "old-source",
        subject / "new-source",
        baseline / "prior/.specula-output",
        baseline / "prior/.specula-output/spec/base.tla",
        baseline / "scope.md",
        baseline / ".agents/skills",
        baseline / "lib",
        baseline / "tools",
        SCRIPT_DIR / "incremental-task-template.md",
        SCRIPT_DIR / "incremental-final-schema.json",
        SCRIPT_DIR / "network-guard",
    ]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise RuntimeError(f"{case_id}: missing required inputs: {missing}")

    subject_data = read_json(subject / "subject.json")
    if subject_data.get("case_id") != case_id:
        raise RuntimeError(f"{case_id}: subject metadata case_id mismatch")
    category = subject_data.get("category")
    if category not in {"A_DISTRIBUTED", "B_CONCURRENT"}:
        raise RuntimeError(f"{case_id}: invalid public category: {category!r}")
    changed_files = normalize_changed_files(subject_data.get("changed_files"))
    if not changed_files:
        raise RuntimeError(f"{case_id}: subject has an empty update delta")

    installed = {
        path.name for path in (baseline / ".agents/skills").iterdir() if path.is_dir()
    }
    missing_shared = sorted(REQUIRED_SHARED_SKILLS - installed)
    if missing_shared:
        raise RuntimeError(f"{case_id}: baseline is missing frozen skills: {missing_shared}")
    for public_name, source_name in ADDITIONAL_SKILLS.items():
        source = SPECULA_ROOT / "skills" / source_name
        if public_name not in installed and not (source / "SKILL.md").is_file():
            raise RuntimeError(f"{case_id}: missing incremental skill source: {source}")

    prior_identity = tree_identity(baseline / "prior/.specula-output")
    if prior_identity["regular_files"] == 0:
        raise RuntimeError(f"{case_id}: accepted baseline prior is empty")
    return {
        "case_id": case_id,
        "category": category,
        "subject": subject,
        "baseline": baseline,
        "destination": destination,
        "changed_files": changed_files,
        "audit": audit,
        "prior_identity": prior_identity,
    }


def copy_incremental_inputs(preflight: dict[str, Any], stage: Path) -> dict[str, Any]:
    case_id = preflight["case_id"]
    subject: Path = preflight["subject"]
    baseline: Path = preflight["baseline"]

    old_source_identity = copy_tree_checked(subject / "old-source", stage / "old-source")
    new_source_identity = copy_tree_checked(subject / "new-source", stage / "new-source")

    prior_source = baseline / "prior/.specula-output"
    prior_before = tree_identity(prior_source)
    previous = stage / "previous/.specula-output"
    current = stage / "current/.specula-output"
    shutil.copytree(prior_source, previous, symlinks=True)
    shutil.copytree(prior_source, current, symlinks=True)
    prior_after = tree_identity(prior_source)
    previous_before_read_only = tree_identity(previous)
    current_seed_before_artifact = tree_identity(current)
    if not (prior_before == prior_after == previous_before_read_only == current_seed_before_artifact):
        raise RuntimeError(f"{case_id}: accepted prior changed or copied inconsistently")
    if prior_before != preflight["prior_identity"]:
        raise RuntimeError(f"{case_id}: accepted prior changed after preflight")

    make_tree_owner_writable(current)
    artifact = current / "artifact"
    if artifact.exists() or artifact.is_symlink():
        remove_path(artifact)
    synthetic = build_synthetic_artifact(
        subject / "old-tree",
        subject / "buggy-tree",
        artifact,
        preflight["changed_files"],
    )

    scope_source = baseline / "scope.md"
    scope_sha256 = sha256(scope_source)
    shutil.copy2(scope_source, stage / "model-scope.md")
    if sha256(scope_source) != scope_sha256 or sha256(stage / "model-scope.md") != scope_sha256:
        raise RuntimeError(f"{case_id}: model scope changed or copied inconsistently")
    case_metadata = {
        "schema_version": 1,
        "case_id": case_id,
        "category": preflight["category"],
        "changed_files": preflight["changed_files"],
        "source_history": {
            "kind": "neutral_synthetic_two_commit_history",
            "commit_subjects": ["baseline", "update"],
            "upstream_identifiers_included": False,
        },
    }
    (stage / "case.json").write_text(dump_json(case_metadata), encoding="utf-8")

    copy_tree_checked(baseline / ".agents", stage / ".agents")
    skills_root = stage / ".agents/skills"
    for public_name, source_name in ADDITIONAL_SKILLS.items():
        destination = skills_root / public_name
        if destination.exists():
            continue
        copy_tree_checked(SPECULA_ROOT / "skills" / source_name, destination)
    copy_tree_checked(baseline / "lib", stage / "lib")
    copy_tree_checked(baseline / "tools", stage / "tools")
    network_guard = stage / "tools/network-guard"
    if network_guard.exists() or network_guard.is_symlink():
        remove_path(network_guard)
    copy_tree_checked(SCRIPT_DIR / "network-guard", network_guard)
    for wrapper in network_guard.iterdir():
        if not wrapper.is_file() or wrapper.is_symlink():
            raise RuntimeError(f"unexpected network-guard entry: {wrapper}")
        wrapper.chmod(0o755)

    task = (SCRIPT_DIR / "incremental-task-template.md").read_text(encoding="utf-8")
    task = task.replace("INCREMENTAL_CASE_ID", case_id)
    (stage / "task.md").write_text(task, encoding="utf-8")
    shutil.copy2(SCRIPT_DIR / "incremental-final-schema.json", stage / "final-schema.json")

    for name in CACHE_DIRS:
        (stage / ".cache" / name).mkdir(parents=True, exist_ok=True)

    input_manifest = {
        "schema_version": 1,
        "case_id": case_id,
        "purpose": "blind_source_derived_incremental_verification",
        "baseline_audit": {
            "verdict": "ACCEPT",
            "sha256": preflight["audit"]["sha256"],
        },
        "inputs": {
            "old_source": {
                "path": "/work/old-source",
                "role": "immutable exact-old changed-file snapshot",
                "content_sha256": old_source_identity["content_sha256"],
            },
            "new_source": {
                "path": "/work/new-source",
                "role": "immutable updated changed-file snapshot",
                "content_sha256": new_source_identity["content_sha256"],
            },
            "previous": {
                "path": "/work/previous/.specula-output",
                "role": "immutable accepted exact-old prior",
                "content_sha256": prior_before["content_sha256"],
            },
            "current": {
                "path": "/work/current/.specula-output",
                "role": "writable copy of the accepted prior",
            },
            "artifact": {
                "path": "/work/current/.specula-output/artifact",
                "role": "complete updated source with two neutral synthetic commits",
                "commit_subjects": ["baseline", "update"],
                "commit_count": 2,
                "remotes": [],
                "updated_content_sha256": synthetic["updated_worktree_identity"]["content_sha256"],
            },
            "model_scope": "/work/model-scope.md",
            "case_metadata": "/work/case.json",
            "skills": "/work/.agents/skills",
            "libraries": "/work/lib",
            "tools": "/work/tools",
        },
        "allowed_inputs": [
            "/work/old-source",
            "/work/new-source",
            "/work/previous/.specula-output",
            "/work/current/.specula-output",
            "/work/model-scope.md",
            "/work/case.json",
            "/work/.agents/skills",
            "/work/lib",
            "/work/tools",
        ],
        "forbidden_inputs": [
            "fixed source",
            "upstream Git objects, refs, tags, remotes, and revision identifiers",
            "issues, pull requests, advisories, papers, release research, and incident history",
            "Gold, graders, candidate manifests, private provenance, and another case's outputs",
            "user memory and paths outside /work",
            "general internet research",
        ],
        "network_policy": "model API and ordinary build dependencies only; history and research commands are prohibited and audited",
    }
    (stage / "input-manifest.json").write_text(dump_json(input_manifest), encoding="utf-8")

    make_tree_read_only(previous)
    make_tree_read_only(stage / "old-source")
    make_tree_read_only(stage / "new-source")
    for path in (
        stage / ".agents",
        stage / "lib",
        stage / "tools",
    ):
        make_tree_read_only(path)
    for path in (
        stage / "model-scope.md",
        stage / "case.json",
        stage / "task.md",
        stage / "final-schema.json",
        stage / "input-manifest.json",
    ):
        path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)

    return {
        "old_source_identity": old_source_identity,
        "new_source_identity": new_source_identity,
        "prior_source_identity": prior_before,
        "previous_seed_identity_before_read_only": previous_before_read_only,
        "previous_read_only_identity": tree_identity(previous),
        "current_seed_identity_before_artifact": current_seed_before_artifact,
        "current_identity": tree_identity(current),
        "synthetic_artifact": synthetic,
    }


def prepare_case(preflight: dict[str, Any], baseline_attempt: str, incremental_attempt: str) -> dict[str, Any]:
    case_id = preflight["case_id"]
    destination: Path = preflight["destination"]
    parent = destination.parent
    parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=f".{incremental_attempt}.tmp-", dir=parent))
    try:
        copied = copy_incremental_inputs(preflight, stage)
        if sha256(preflight["audit"]["path"]) != preflight["audit"]["sha256"]:
            raise RuntimeError(f"{case_id}: baseline audit changed during preparation")
        preparation = {
            "schema_version": 1,
            "case_id": case_id,
            "baseline_attempt": baseline_attempt,
            "incremental_attempt": incremental_attempt,
            "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
            "baseline_audit": {
                "verdict": "ACCEPT",
                "sha256": preflight["audit"]["sha256"],
            },
            "source_history_policy": "two neutral synthetic commits named baseline and update; no remotes, tags, or upstream revision identifiers",
            **copied,
            "task_sha256": sha256(stage / "task.md"),
            "final_schema_sha256": sha256(stage / "final-schema.json"),
            "input_manifest_sha256": sha256(stage / "input-manifest.json"),
            "agent_started": False,
        }
        (stage / "initial-manifest.json").write_text(
            dump_json(preparation), encoding="utf-8"
        )
        if destination.exists():
            raise RuntimeError(f"refusing to overwrite existing incremental attempt: {destination}")
        os.replace(stage, destination)
    except BaseException:
        remove_tree(stage)
        raise

    return {
        "case_id": case_id,
        "attempt": str(destination),
        "baseline_attempt": baseline_attempt,
        "baseline_audit_sha256": preflight["audit"]["sha256"],
        "prior_content_sha256": copied["prior_source_identity"]["content_sha256"],
        "updated_artifact_content_sha256": copied["synthetic_artifact"]["updated_worktree_identity"]["content_sha256"],
        "synthetic_commit_count": 2,
        "agent_started": False,
    }


def write_summary(results: list[dict[str, Any]]) -> None:
    manifest = ROOT / "incremental-preparation-manifest.json"
    merged: dict[str, dict[str, Any]] = {}
    if manifest.is_file():
        existing = read_json(manifest)
        for entry in existing.get("cases", []):
            if isinstance(entry, dict) and isinstance(entry.get("case_id"), str):
                merged[entry["case_id"]] = entry
    merged.update({entry["case_id"]: entry for entry in results})
    value = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "case_count": len(merged),
        "cases": [merged[case_id] for case_id in CASE_IDS if case_id in merged],
    }
    temporary = manifest.with_name(f".{manifest.name}.tmp-{os.getpid()}")
    temporary.write_text(dump_json(value), encoding="utf-8")
    os.replace(temporary, manifest)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare audit-accepted baseline/update inputs without starting Agents."
    )
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--baseline-attempt", default=DEFAULT_BASELINE_ATTEMPT)
    parser.add_argument("--attempt", default=DEFAULT_INCREMENTAL_ATTEMPT)
    args = parser.parse_args()

    validate_attempt_name(args.baseline_attempt, "--baseline-attempt")
    validate_attempt_name(args.attempt, "--attempt")
    selected = args.cases or CASE_IDS
    if len(selected) != len(set(selected)):
        raise SystemExit("duplicate --case values are not allowed")
    unknown = sorted(set(selected) - set(CASE_IDS))
    if unknown:
        raise SystemExit(f"unknown cases: {unknown}")

    # Preflight the whole selection before creating any final attempt.  In
    # particular, one absent/non-ACCEPT audit rejects the preparation batch.
    preflights = [
        preflight_case(case_id, args.baseline_attempt, args.attempt)
        for case_id in selected
    ]
    results = [
        prepare_case(preflight, args.baseline_attempt, args.attempt)
        for preflight in preflights
    ]
    write_summary(results)
    output = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "case_count": len(results),
        "cases": results,
        "agent_started": False,
    }
    print(dump_json(output), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
