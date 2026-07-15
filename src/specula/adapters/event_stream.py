"""Compatibility entry point for the shared adapter event stream."""

from __future__ import annotations

import sys

if __package__:
    from .utils.event_stream import main, parse_events, stream_events
    from .utils.text import summary
else:
    from utils.event_stream import main, parse_events, stream_events  # type: ignore[import-not-found, no-redef]
    from utils.text import summary  # type: ignore[import-not-found, no-redef]

__all__ = ["main", "parse_events", "stream_events", "summary"]


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
