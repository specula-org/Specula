#!/usr/bin/env python3
"""Retire an unstarted neutralized attempt without deleting its evidence."""

from __future__ import annotations

import argparse
import json
import os
import secrets
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
NEUTRAL_ROOT = Path("/home/ubuntu/.cache/sci-20260904")


def dump(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def valid(value: str) -> bool:
    return Path(value).name == value and value not in {"", ".", ".."}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--attempt", default="attempt-001")
    parser.add_argument("--reason", required=True)
    args = parser.parse_args()
    if not valid(args.case) or not valid(args.attempt):
        raise SystemExit("invalid case or attempt")
    logical = ROOT / "cases" / args.case / args.attempt
    if not logical.is_symlink():
        raise RuntimeError(f"attempt is not a neutralized symlink: {logical}")
    physical = logical.resolve()
    physical.relative_to(NEUTRAL_ROOT)
    if (ROOT / "logs/incremental" / args.case / args.attempt / "run-manifest.json").exists():
        raise RuntimeError("refusing to retire an attempt after its run started")
    retired = (
        ROOT
        / "logs/retired-incremental-preparations"
        / args.case
        / f"{args.attempt}-{secrets.token_hex(8)}"
    )
    retired.parent.mkdir(parents=True, exist_ok=True)
    os.replace(physical, retired)
    logical.unlink()
    record = {
        "schema_version": 1,
        "case_id": args.case,
        "attempt": args.attempt,
        "reason": args.reason,
        "retired_at_utc": datetime.now(timezone.utc).isoformat(),
        "retired_path": str(retired),
        "original_physical_path": str(physical),
        "agent_started": False,
    }
    record_path = retired.parent / f"{retired.name}.json"
    record_path.write_text(dump(record), encoding="utf-8")
    print(dump(record), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
