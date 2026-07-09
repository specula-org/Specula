#!/usr/bin/env python3
"""Tee Copilot JSONL into activity events and a readable agent log."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def stream_events(activity_path: Path, log_path: Path) -> None:
    fallback: list[str] = []
    wrote_message = False
    with activity_path.open("wb") as activity, log_path.open("w") as log:
        for raw_line in sys.stdin.buffer:
            activity.write(raw_line)
            activity.flush()
            line = raw_line.decode(errors="replace")
            if not wrote_message:
                fallback.append(line)
            try:
                record = json.loads(line)
            except (TypeError, ValueError):
                continue
            if not isinstance(record, dict) or record.get("type") != "assistant.message":
                continue
            data = record.get("data")
            if not isinstance(data, dict):
                continue
            content = data.get("content")
            if not isinstance(content, str) or not content.strip():
                continue
            if wrote_message:
                log.write("\n")
            log.write(content.strip() + "\n")
            log.flush()
            fallback.clear()
            wrote_message = True

        # Preserve useful error/plain-text output when Copilot exits before it
        # emits a message or an older CLI ignores --output-format=json.
        if not wrote_message:
            log.write("".join(fallback))


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: copilot_events.py ACTIVITY_JSONL LOG_FILE", file=sys.stderr)
        return 2
    try:
        stream_events(Path(argv[0]), Path(argv[1]))
    except OSError as exc:
        print(f"copilot activity extraction failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
