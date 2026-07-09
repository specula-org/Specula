"""Tee adapter JSONL into raw and incrementally readable activity logs."""

from __future__ import annotations

import sys
from collections.abc import Iterable
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import specula.activity as activity

_ADAPTER_NAMES = {
    "claude": "claude-code",
    "claude-code": "claude-code",
    "codex": "codex",
    "copilot": "copilot-cli",
    "copilot-cli": "copilot-cli",
}


def stream_events(
    adapter: str,
    activity_path: Path,
    log_path: Path,
    source: Iterable[bytes] | None = None,
) -> None:
    """Persist raw JSONL and flush readable activity after every event."""
    source = source if source is not None else sys.stdin.buffer
    adapter_name = _ADAPTER_NAMES[adapter]
    last_event = ""
    with activity_path.open("wb") as raw_log, log_path.open("w") as log:
        for raw_line in source:
            raw_log.write(raw_line)
            raw_log.flush()
            line = raw_line.decode(errors="replace")
            for event in activity.parse_events(adapter_name, [line], concise=False):
                if not event or event == last_event:
                    continue
                log.write(event.rstrip("\n") + "\n")
                log.flush()
                last_event = event


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[0] not in _ADAPTER_NAMES:
        print("usage: event_stream.py {claude|codex|copilot} ACTIVITY_JSONL LOG_FILE", file=sys.stderr)
        return 2
    try:
        stream_events(argv[0], Path(argv[1]), Path(argv[2]))
    except OSError as exc:
        print(f"adapter event stream failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
