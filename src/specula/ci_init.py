"""Guidance composition and run-scoped baseline registration for CI initialization.

Registration preserves reusable artifacts; it deliberately makes no automatic
semantic-quality verdict. The ordinary pipeline remains the execution owner.
"""

from __future__ import annotations

import contextlib
import hashlib
import json
import os
import shutil
import stat
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from specula.prompts import render

BASELINE_FILENAME = "ci-baseline.json"
INPUTS_DIR = "ci-init/inputs"
SNAPSHOTS_DIR = "ci-init/baselines"
ASSET_DIRS = ("spec", "harness", "traces")
# Generated execution state and source/build trees are not baseline inputs.
_SCRATCH_DIRS = frozenset({".git", ".cache", "__pycache__", "states", "target", "node_modules"})


class CIInitError(RuntimeError):
    """CI initialization metadata cannot safely be recorded."""


def _directory(root: Path, relative: str) -> Path:
    current = root
    for part in ("", *Path(relative).parts):
        current = current / part
        with contextlib.suppress(FileExistsError):
            current.mkdir()
        if not stat.S_ISDIR(current.lstat().st_mode):
            raise CIInitError(f"not a real CI initialization directory: {current}")
    return current


def _write_once(path: Path, content: bytes) -> None:
    try:
        with path.open("xb") as stream:
            stream.write(content)
    except FileExistsError:
        if not stat.S_ISREG(path.lstat().st_mode) or path.read_bytes() != content:
            raise CIInitError(f"CI initialization input changed: {path}") from None


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def prepare_output_directory(run_dir: Path, target: str) -> Path:
    """Keep guidance publication inside the real target output directory."""
    return _directory(run_dir, f"{target}/.specula-output")


def stage_inputs(run_dir: Path, user_text: str) -> tuple[str, Path]:
    """Save original and effective guidance without reinterpreting user text."""
    custom = render("ci-initialization")
    effective = custom + ("\n## User-Provided Guidance\n\n" + user_text if user_text else "")
    digest = hashlib.sha256(effective.encode("utf-8")).hexdigest()
    destination = _directory(run_dir, f"{INPUTS_DIR}/{digest}")
    for name, text in (
        ("user-guidance.md", user_text),
        ("ci-guidance.md", custom),
        ("effective-guidance.md", effective),
    ):
        _write_once(destination / name, text.encode("utf-8"))
    return effective, destination


def fallback_guidance(run_dir: Path, candidate: Path) -> str:
    """Freeze a legacy .prompt-extra input before publishing composed guidance."""
    directory = _directory(run_dir, "ci-init")
    original = directory / "user-guidance.md"
    if original.exists() or original.is_symlink():
        if not stat.S_ISREG(original.lstat().st_mode):
            raise CIInitError(f"unsafe saved user guidance: {original}")
        return original.read_text(encoding="utf-8")
    text = candidate.read_text(errors="replace") if candidate.is_file() else ""
    _write_once(original, text.encode("utf-8"))
    return text


def _regular_file(root: Path, relative: str) -> bool:
    current = root
    try:
        if not stat.S_ISDIR(current.lstat().st_mode):
            return False
        for part in Path(relative).parts:
            current /= part
            mode = current.lstat().st_mode
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                return False
        return stat.S_ISREG(mode)
    except OSError:
        return False


def _copy_assets(work_dir: Path, destination: Path) -> tuple[dict[str, str], list[str]]:
    """Copy verification inputs without following source/cache/secret symlinks."""
    files: dict[str, str] = {}
    omitted: list[str] = []

    def copy(path: Path) -> None:
        relative = path.relative_to(work_dir)
        mode = path.lstat().st_mode
        if stat.S_ISDIR(mode):
            if path.name in _SCRATCH_DIRS:
                omitted.append(relative.as_posix())
                return
            for child in sorted(path.iterdir()):
                copy(child)
        elif stat.S_ISREG(mode):
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
            digest = hashlib.sha256()
            with target.open("rb") as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(block)
            files[relative.as_posix()] = digest.hexdigest()
        else:
            omitted.append(relative.as_posix())

    for path in sorted(work_dir.iterdir()):
        if path.name in ASSET_DIRS or path.suffix == ".md" or path.name == "ci-verdict.json":
            copy(path)
    return files, omitted


def register_baseline(
    run_dir: Path,
    work_dir: Path,
    *,
    target: str,
    invocation: str,
    inputs_dir: Path,
    source: dict[str, Any],
    pipeline_exit_code: int,
) -> Path | None:
    """Register the first available reference, retaining later resume snapshots.

    A failed/incomplete validation does not prevent registration. Absence of a
    readable, nonempty reference does. Existing registration is never replaced.
    """
    try:
        relative_work = work_dir.relative_to(run_dir)
    except ValueError as exc:
        raise CIInitError("CI baseline outputs must be inside the run") from exc
    if ".." in relative_work.parts:
        raise CIInitError("CI baseline outputs must be inside the run")
    if not _regular_file(run_dir, (relative_work / "spec/base.tla").as_posix()):
        return None
    if (work_dir / "spec/base.tla").stat().st_size == 0:
        return None
    if not invocation or not invocation.isalnum():
        raise CIInitError("invalid CI initialization invocation identity")
    parent = _directory(run_dir, SNAPSHOTS_DIR)
    destination = parent / invocation
    destination.mkdir()  # a resume gets its own identity; never overwrite a snapshot
    assets = destination / ".specula-output"
    assets.mkdir()
    files, omitted = _copy_assets(work_dir, assets)
    required = (
        "modeling-brief.md",
        "spec/MC.tla",
        "spec/MC.cfg",
        "spec/Trace.tla",
        "spec/Trace.cfg",
        "spec/instrumentation-spec.md",
        "harness/run.sh",
    )
    record = {
        "version": 1,
        "kind": "ci-initialization",
        "target": target,
        "run_id": run_dir.name,
        "run_root": str(run_dir.absolute()),
        "created_at": datetime.now(timezone.utc).isoformat(),
        "source": source,
        "pipeline_exit_code": pipeline_exit_code,
        "validation_status": "UNVERIFIED",
        "validation_note": "Registration is not a verification verdict; inspect the retained validation evidence.",
        "assets": str(assets.relative_to(run_dir)),
        "guidance": str(inputs_dir.relative_to(run_dir)),
        "run_output": str(work_dir.relative_to(run_dir)),
        "files_sha256": files,
        "missing_artifacts": [name for name in required if name not in files],
        "omitted_paths": omitted,
    }
    payload = _json_bytes(record)
    manifest = destination / BASELINE_FILENAME
    _write_once(manifest, payload)
    # link publishes a complete file atomically, without replacing an earlier
    # registered baseline (including when a later resume has better coverage).
    registered = run_dir / BASELINE_FILENAME
    try:
        os.link(manifest, registered)
    except FileExistsError:
        if not _regular_file(run_dir, BASELINE_FILENAME):
            raise CIInitError(f"unsafe existing baseline registration: {registered}") from None
        try:
            existing = json.loads(registered.read_text(encoding="utf-8"))
            if (
                not isinstance(existing, dict)
                or existing.get("version") != 1
                or existing.get("kind") != "ci-initialization"
                or existing.get("target") != target
                or existing.get("run_id") != run_dir.name
            ):
                raise ValueError("registration does not match this run")
        except (ValueError, UnicodeError) as exc:
            raise CIInitError(f"invalid existing baseline registration: {registered}") from exc
        return manifest
    return registered
