"""Shared paths and helpers for the §3.2 end-to-end experiment (inv-e2e).

Design and results: README.md.

Large state (repository clones, attempt workspaces, agent logs) lives under
INV_E2E_WORK (default /mydata/bingzhuo/inv-e2e). Small, reviewable outputs are
written to results/ next to this file.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
SPECULA = HERE.parents[2]
BLIND = SPECULA / "research/ci-evolution/blind-incremental-bugs"
BLIND_TOOLS = BLIND / "tools"
V0_ROOT = BLIND / "blind-incremental-v0"
WORK = Path(os.environ.get("INV_E2E_WORK", "/mydata/bingzhuo/inv-e2e"))
RESULTS = Path(os.environ.get("INV_E2E_RESULTS", HERE / "results"))

ARMS = ("v0", "v1", "v2")
# Cases with an accepted V0 (case-008 and case-009 have none).
CASE_IDS = ("case-001", "case-002", "case-003", "case-004", "case-005",
            "case-006", "case-007", "case-010", "case-011", "case-012")

# Public skill name -> directory under Specula/skills (same mapping as the blind study).
SKILL_SOURCES = {
    "code-analysis": "code_analysis",
    "spec-generation": "spec_generation",
    "harness-generation": "harness-generation",
    "tla-trace-workflow": "tla-trace-workflow",
    "validation-workflow": "validation-workflow",
    "tla-checking-workflow": "tla-checking-workflow",
    "incremental-modeling": "incremental-modeling",
    "bug-confirmation": "bug-confirmation",
}


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    tmp.write_text(dump_json(value), encoding="utf-8")
    os.replace(tmp, path)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tree_hash(root: Path) -> str:
    """Content hash of a directory tree (relative paths + file hashes + symlink targets)."""
    digest = hashlib.sha256()
    for path in sorted(root.rglob("*")):
        rel = path.relative_to(root).as_posix()
        if path.is_symlink():
            digest.update(f"L {rel} {os.readlink(path)}\n".encode())
        elif path.is_file():
            digest.update(f"F {rel} {sha256(path)}\n".encode())
    return digest.hexdigest()


def run(args: list[str], cwd: Path | None = None, check: bool = True) -> str:
    done = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=False)
    if check and done.returncode != 0:
        raise RuntimeError(f"command failed ({done.returncode}): {args}\n{done.stderr}")
    return done.stdout


def cases_json() -> dict[str, dict[str, Any]]:
    """Public case table from the V0 package: repository, module, base and update commits."""
    data = read_json(V0_ROOT / "cases.json")
    return {c["case_id"]: c for c in data["cases"]}


def cohort_json() -> dict[str, dict[str, Any]]:
    data = read_json(BLIND / "cohort.json")
    return {c["case_id"]: c for c in data["cases"]}


def blind_helpers():
    """Import the blind study's preparation helpers without running its CLI.

    Reused: build_synthetic_artifact, tree_identity, copy_tree_checked,
    make_tree_read_only, make_tree_owner_writable, normalize_changed_files, remove_tree.
    """
    spec = importlib.util.spec_from_file_location("blind_prepare", BLIND_TOOLS / "prepare_incremental.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def check_case(case_id: str) -> None:
    if case_id not in CASE_IDS:
        raise SystemExit(f"unknown or V0-less case: {case_id} (choose from {', '.join(CASE_IDS)})")


def check_arm(arm: str) -> None:
    if arm not in ARMS:
        raise SystemExit(f"unknown arm: {arm} (choose from {', '.join(ARMS)})")
