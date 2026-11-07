#!/usr/bin/env python3
"""Move a prepared incremental attempt behind an opaque host path."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import secrets
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
NEUTRAL_ROOT = Path("/home/ubuntu/.cache/sci-20260904")


def dump_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def valid_name(value: str) -> bool:
    return Path(value).name == value and value not in {"", ".", ".."}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--attempt", default="attempt-001")
    args = parser.parse_args()
    if not valid_name(args.case) or not valid_name(args.attempt):
        raise SystemExit("invalid case or attempt")
    logical = ROOT / "cases" / args.case / args.attempt
    if logical.is_symlink():
        raise RuntimeError(f"attempt is already neutralized: {logical}")
    if not logical.is_dir():
        raise RuntimeError(f"prepared attempt is missing: {logical}")
    if (ROOT / "logs/incremental" / args.case / args.attempt / "run-manifest.json").exists():
        raise RuntimeError("refusing to move an attempt after its run started")
    initial = logical / "initial-manifest.json"
    if not initial.is_file():
        raise RuntimeError("initial-manifest.json is missing")

    NEUTRAL_ROOT.mkdir(parents=True, exist_ok=True)
    opaque = secrets.token_hex(16)
    physical = NEUTRAL_ROOT / opaque
    if physical.exists():
        raise RuntimeError(f"opaque destination collision: {physical}")
    os.replace(logical, physical)
    try:
        logical.symlink_to(physical, target_is_directory=True)
    except BaseException:
        os.replace(physical, logical)
        raise
    record = {
        "schema_version": 1,
        "case_id": args.case,
        "attempt": args.attempt,
        "neutralized_at_utc": datetime.now(timezone.utc).isoformat(),
        "logical_path": str(logical),
        "physical_path": str(physical),
        "initial_manifest_sha256": sha256(physical / "initial-manifest.json"),
        "agent_started": False,
    }
    record_path = ROOT / "logs/neutral-paths" / args.case / f"{args.attempt}.json"
    record_path.parent.mkdir(parents=True, exist_ok=True)
    record_path.write_text(dump_json(record), encoding="utf-8")
    print(dump_json(record), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
