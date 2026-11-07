#!/usr/bin/env python3
"""Prepare an isolated old-only V0 validation-repair attempt."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
SCRIPT_DIR = Path(__file__).resolve().parent


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def copy(source: Path, destination: Path) -> None:
    if source.is_dir():
        shutil.copytree(source, destination, symlinks=True)
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)


def valid_name(value: str) -> bool:
    return Path(value).name == value and value not in {"", ".", ".."}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--from-attempt", default="attempt-004")
    parser.add_argument("--attempt", default="attempt-005")
    args = parser.parse_args()
    if not all(valid_name(value) for value in (args.case, args.from_attempt, args.attempt)):
        raise SystemExit("invalid case or attempt name")
    source_attempt = ROOT / "baselines" / args.case / args.from_attempt
    destination = ROOT / "baselines" / args.case / args.attempt
    if destination.exists():
        raise RuntimeError(f"refusing to overwrite: {destination}")
    audit = source_attempt / "baseline-audit.json"
    replay = ROOT / "logs/baseline-audit" / args.case / args.from_attempt / "tlc-replay"
    required = [
        audit,
        source_attempt / "source/.git",
        source_attempt / "work-source/.git",
        source_attempt / "prior/.specula-output/spec/base.tla",
        source_attempt / ".agents",
        source_attempt / "lib",
        source_attempt / "tools",
        source_attempt / "scope.md",
        source_attempt / "input-manifest.json",
    ]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise RuntimeError(f"missing repair inputs: {missing}")
    audit_value = json.loads(audit.read_text(encoding="utf-8"))
    if audit_value.get("verdict") == "ACCEPT":
        raise RuntimeError("repair is unnecessary for an accepted prior")

    destination.mkdir(parents=True)
    for name in ("source", "work-source", ".agents", "lib", "tools", "scope.md"):
        copy(source_attempt / name, destination / name)
    copy(source_attempt / "prior", destination / "prior")
    old_final = destination / "prior/final-response.json"
    if old_final.exists():
        old_final.unlink()
    cache_source = source_attempt / ".cache"
    if cache_source.is_dir():
        copy(cache_source, destination / ".cache")
    else:
        (destination / ".cache").mkdir()

    audit_dir = destination / "audit"
    copy(audit, audit_dir / "baseline-audit.json")
    if replay.is_dir() and (replay / "replay-manifest.json").is_file():
        copy(replay, audit_dir / "tlc-replay")
    task = (SCRIPT_DIR / "baseline-repair-task-template.md").read_text(encoding="utf-8")
    (destination / "task.md").write_text(task, encoding="utf-8")
    copy(SCRIPT_DIR / "baseline-final-schema.json", destination / "final-schema.json")
    input_value = json.loads(
        (source_attempt / "input-manifest.json").read_text(encoding="utf-8")
    )
    input_value.update(
        {
            "purpose": "exact_old_v0_validation_repair",
            "source_attempt": args.from_attempt,
            "source_audit_sha256": sha256(audit),
            "source_replay_manifest_sha256": (
                sha256(replay / "replay-manifest.json")
                if (replay / "replay-manifest.json").is_file()
                else None
            ),
        }
    )
    (destination / "input-manifest.json").write_text(dump_json(input_value), encoding="utf-8")
    preparation = {
        "schema_version": 1,
        "case_id": args.case,
        "attempt": str(destination),
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_attempt": args.from_attempt,
        "source_identity": json.loads(
            (source_attempt / "preparation-manifest.json").read_text(encoding="utf-8")
        )["source_identity"],
        "repair_input_sha256": sha256(destination / "input-manifest.json"),
    }
    (destination / "preparation-manifest.json").write_text(dump_json(preparation), encoding="utf-8")
    lineage = {
        "schema_version": 1,
        "mode": "OLD_ONLY_VALIDATION_REPAIR",
        "attempt": args.attempt,
        "semantic_source_attempt": args.from_attempt,
        "source_audit_sha256": sha256(audit),
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
    }
    (destination / "retry-lineage.private.json").write_text(dump_json(lineage), encoding="utf-8")
    print(dump_json(preparation), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
