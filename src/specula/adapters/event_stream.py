"""Tee adapter JSONL into an activity sidecar and readable agent log."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def _message(adapter: str, record: object) -> str:
    if not isinstance(record, dict):
        return ""
    if adapter == "copilot" and record.get("type") == "assistant.message":
        data = record.get("data")
        content = data.get("content") if isinstance(data, dict) else None
        return content.strip() if isinstance(content, str) else ""
    if adapter == "codex" and record.get("type") == "item.completed":
        item = record.get("item")
        if isinstance(item, dict) and item.get("type") == "agent_message":
            text = item.get("text")
            return text.strip() if isinstance(text, str) else ""
    return ""


def stream_events(adapter: str, activity_path: Path, log_path: Path) -> None:
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
            message = _message(adapter, record)
            if not message:
                continue
            if wrote_message:
                log.write("\n")
            log.write(message + "\n")
            log.flush()
            fallback.clear()
            wrote_message = True

        if not wrote_message:
            log.write("".join(fallback))


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[0] not in {"codex", "copilot"}:
        print("usage: event_stream.py {codex|copilot} ACTIVITY_JSONL LOG_FILE", file=sys.stderr)
        return 2
    try:
        stream_events(argv[0], Path(argv[1]), Path(argv[2]))
    except OSError as exc:
        print(f"adapter event stream failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
