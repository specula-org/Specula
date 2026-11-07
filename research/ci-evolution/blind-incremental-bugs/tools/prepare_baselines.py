#!/usr/bin/env python3
"""Prepare gold-free exact-old workspaces for V0 prior generation."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
SPECULA_ROOT = Path("/home/ubuntu/Specula")
CASE_IDS = [f"case-{number:03d}" for number in range(1, 13)]
SKILL_SOURCES = {
    "code-analysis": "code_analysis",
    "spec-generation": "spec_generation",
    "harness-generation": "harness-generation",
    "tla-trace-workflow": "tla-trace-workflow",
    "validation-workflow": "validation-workflow",
    "tla-checking-workflow": "tla-checking-workflow",
}


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def run(command: list[str], cwd: Path | None = None) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(f"command failed ({completed.returncode}): {command}\n{completed.stdout}")
    return completed.stdout


def tree_identity(root: Path) -> dict[str, Any]:
    digest = hashlib.sha256()
    count = 0
    total_bytes = 0
    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames.sort()
        filenames.sort()
        base = Path(directory)
        entries = [(name, base / name) for name in dirnames + filenames]
        for name, path in entries:
            relative = path.relative_to(root).as_posix()
            metadata = path.lstat()
            mode = stat.S_IMODE(metadata.st_mode)
            if stat.S_ISLNK(metadata.st_mode):
                kind = "symlink"
                content = os.readlink(path).encode()
            elif stat.S_ISREG(metadata.st_mode):
                kind = "file"
                content = path.read_bytes()
                count += 1
                total_bytes += len(content)
            elif stat.S_ISDIR(metadata.st_mode):
                kind = "dir"
                content = b""
            else:
                raise RuntimeError(f"unsupported source entry: {path}")
            digest.update(kind.encode())
            digest.update(b"\0")
            digest.update(f"{mode:o}".encode())
            digest.update(b"\0")
            digest.update(relative.encode())
            digest.update(b"\0")
            digest.update(hashlib.sha256(content).digest())
            digest.update(b"\0")
    return {"sha256": digest.hexdigest(), "regular_files": count, "regular_file_bytes": total_bytes}


def copy_skills(destination: Path) -> None:
    for public_name, source_name in SKILL_SOURCES.items():
        source = SPECULA_ROOT / "skills" / source_name
        if not (source / "SKILL.md").is_file():
            raise RuntimeError(f"missing skill source: {source}")
        shutil.copytree(source, destination / public_name)


def scope_path(case_id: str) -> Path:
    if case_id in {"case-001", "case-004", "case-007", "case-009", "case-011", "case-012"}:
        return ROOT / "prep/openraft" / case_id / "model-scope.md"
    if case_id in {"case-002", "case-005", "case-010"}:
        return ROOT / "prep/zookeeper/neutral-zab-recovery-v0-scope.md"
    return ROOT / "prep/other" / case_id / "scope.md"


def safe_prep_details(case_id: str) -> dict[str, Any]:
    if case_id in {"case-001", "case-004", "case-007", "case-009", "case-011", "case-012"}:
        value = json.loads((ROOT / "prep/openraft" / case_id / "v0-prior.json").read_text())
        return {
            "track": value.get("track", "primary"),
            "primary_score_eligible": value.get("primary_score_eligible", True),
            "category": value["category"],
            "priority_inputs": value["priority_inputs"],
            "inspection_order": value["inspection_order"],
            "candidate_commands": [
                {
                    **command,
                    "cwd": command["cwd"].replace("/work/old-tree", "/work/source"),
                }
                for command in value["candidate_commands"]
            ],
        }
    if case_id in {"case-002", "case-005", "case-010"}:
        value = json.loads(
            (ROOT / "prep/zookeeper" / case_id / "binding.private.json").read_text()
        )
        return {
            "track": "primary",
            "category": "A_DISTRIBUTED",
            "source_layout": value["source_layout"],
            "build_profile": value["build_profile"],
            "priority_source_paths": value["primary_entry_points"],
        }
    value = json.loads((ROOT / "prep/other" / case_id / "input-manifest.json").read_text())
    return {
        "track": "primary",
        "category": value["category"],
        "priority_source_paths": value["priority_source_paths"],
        "old_only_test_paths": value["old_only_test_paths"],
        "old_only_test_commands": value["old_only_test_commands"],
        "dependencies": value["dependencies"],
    }


def prepare_case(case_id: str, attempt_name: str, retry_reason: str | None) -> dict[str, Any]:
    subject = ROOT / "subjects" / case_id
    source_old = subject / "old-tree"
    if (source_old / ".git").exists():
        raise RuntimeError(f"upstream Git metadata present in exact-old tree: {case_id}")
    attempt = ROOT / "baselines" / case_id / attempt_name
    if attempt.exists():
        raise RuntimeError(f"refusing to overwrite existing attempt: {attempt}")
    attempt.mkdir(parents=True)

    source = attempt / "source"
    shutil.copytree(source_old, source, symlinks=True)
    identity_before = tree_identity(source)

    run(["git", "init", "-q", "-b", "baseline"], cwd=source)
    run(["git", "config", "user.name", "Baseline"], cwd=source)
    run(["git", "config", "user.email", "baseline@invalid"], cwd=source)
    run(["git", "config", "commit.gpgsign", "false"], cwd=source)
    run(["git", "add", "-A"], cwd=source)
    environment = os.environ.copy()
    environment.update(
        {
            "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
            "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
        }
    )
    completed = subprocess.run(
        ["git", "commit", "-q", "--no-gpg-sign", "-m", "baseline"],
        cwd=source,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(f"could not create neutral source commit: {completed.stdout}")
    if run(["git", "remote"], cwd=source).strip():
        raise RuntimeError(f"unexpected remote in synthetic repo: {case_id}")
    if run(["git", "rev-list", "--count", "--all"], cwd=source).strip() != "1":
        raise RuntimeError(f"synthetic repo does not contain exactly one commit: {case_id}")
    if run(["git", "tag", "--list"], cwd=source).strip():
        raise RuntimeError(f"unexpected tag in synthetic repo: {case_id}")
    if run(["git", "status", "--porcelain"], cwd=source).strip():
        raise RuntimeError(f"synthetic repo is dirty before V0 run: {case_id}")
    identity_after = tree_identity(source_old)
    if identity_before != identity_after:
        raise RuntimeError(f"source copy drift: {case_id}")
    shutil.copytree(source, attempt / "work-source", symlinks=True)

    shutil.copy2(scope_path(case_id), attempt / "scope.md")
    task = (SCRIPT_DIR / "baseline-task-template.md").read_text().replace(
        "BASELINE_CASE_ID", case_id
    )
    (attempt / "task.md").write_text(task)
    shutil.copy2(SCRIPT_DIR / "baseline-final-schema.json", attempt / "final-schema.json")
    copy_skills(attempt / ".agents/skills")

    lib = attempt / "lib"
    lib.mkdir()
    for name in ("tla2tools.jar", "CommunityModules-deps.jar"):
        shutil.copy2(SPECULA_ROOT / "lib" / name, lib / name)
    tools = attempt / "tools"
    tools.mkdir()
    for name in ("start_background.sh", "wait_for_pid.sh", "clean_states.sh"):
        shutil.copy2(SPECULA_ROOT / "scripts/infra" / name, tools / name)
    trace_debugger = SPECULA_ROOT / "tools/trace_debugger"
    shutil.copytree(trace_debugger / "src", tools / "trace_debugger/src")
    shutil.copy2(trace_debugger / "requirements.txt", tools / "trace_debugger/requirements.txt")
    shutil.copytree(SCRIPT_DIR / "network-guard", tools / "network-guard")
    for wrapper in (tools / "network-guard").iterdir():
        wrapper.chmod(0o755)

    public_manifest = {
        "schema_version": 1,
        "case_id": case_id,
        "attempt_name": attempt_name,
        "purpose": "neutral_exact_old_v0_prior_generation",
        "source": {
            "pristine_path": "/work/source",
            "writable_work_path": "/work/work-source",
            "role": "exact_old_only",
            "git_history": "one neutral synthetic baseline commit; no remotes, tags, or upstream objects",
            **identity_before,
        },
        "scope_path": "/work/scope.md",
        "output_path": "/work/prior/.specula-output",
        "allowed_inputs": ["/work/source", "/work/work-source", "/work/scope.md", "/work/lib", "/work/tools", "/work/.agents/skills"],
        "forbidden_inputs": [
            "new or fixed source",
            "source diff",
            "upstream history, refs, tags, or remotes",
            "issues, pull requests, advisories, papers, and release notes",
            "Gold, grader, candidate manifest, prior answers, and another case's outputs",
            "general internet research",
        ],
        "network_policy": "model API and ordinary build dependencies only; command activity is audited",
        "prep": safe_prep_details(case_id),
    }
    (attempt / "input-manifest.json").write_text(dump_json(public_manifest))
    (attempt / "prior/.specula-output").mkdir(parents=True)
    for name in ("cargo", "cargo-target", "go-build", "go-mod", "m2", "rebar3"):
        (attempt / ".cache" / name).mkdir(parents=True, exist_ok=True)

    preparation = {
        "schema_version": 1,
        "case_id": case_id,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "attempt": str(attempt),
        "source_identity": identity_before,
        "synthetic_head": run(["git", "rev-parse", "HEAD"], cwd=source).strip(),
        "synthetic_log": run(["git", "log", "--format=%s", "--all"], cwd=source).splitlines(),
        "remotes": run(["git", "remote"], cwd=source).splitlines(),
    }
    (attempt / "preparation-manifest.json").write_text(dump_json(preparation))
    if retry_reason is not None:
        lineage = {
            "schema_version": 1,
            "mode": "INFRASTRUCTURE_RETRY",
            "attempt": attempt_name,
            "reason": retry_reason,
            "prior_attempts": [
                entry.name
                for entry in sorted((ROOT / "baselines" / case_id).glob("attempt-*"))
                if entry.name != attempt_name
            ],
            "semantic_attempt": False,
        }
        (attempt / "retry-lineage.private.json").write_text(dump_json(lineage))
    return preparation


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--attempt", default="attempt-001")
    parser.add_argument("--retry-reason")
    args = parser.parse_args()
    selected = args.cases or CASE_IDS
    unknown = sorted(set(selected) - set(CASE_IDS))
    if unknown:
        raise SystemExit(f"unknown cases: {unknown}")
    if Path(args.attempt).name != args.attempt or args.attempt in {".", ".."}:
        raise SystemExit("invalid --attempt")
    results = [prepare_case(case_id, args.attempt, args.retry_reason) for case_id in selected]
    output = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "cases": results,
    }
    manifest = ROOT / "baseline-preparation-manifest.json"
    if manifest.exists():
        prior = json.loads(manifest.read_text())
        merged = {entry["case_id"]: entry for entry in prior.get("cases", [])}
        merged.update({entry["case_id"]: entry for entry in results})
        output["cases"] = [merged[case_id] for case_id in CASE_IDS if case_id in merged]
    manifest.write_text(dump_json(output))
    print(dump_json(output), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
