"""Installed command dispatcher for Specula's agent adapters."""

from __future__ import annotations

import sys


def main(argv: list[str] | None = None) -> int:
    """Dispatch an internal adapter command from the packaged installation."""
    args = sys.argv[1:] if argv is None else argv
    if not args or args[0] in {"-h", "--help"}:
        print("usage: specula-adapter {claude-code|opencode|pi|event-stream} [OPTIONS ...]")
        return 0 if args else 2

    adapter_name, adapter_args = args[0], args[1:]
    if adapter_name == "claude-code":
        from .claude_code import main as adapter_main
    elif adapter_name == "opencode":
        from .opencode import main as adapter_main
    elif adapter_name == "pi":
        from .pi import main as adapter_main
    elif adapter_name == "event-stream":
        from .utils.event_stream import main as adapter_main
    else:
        print(f"specula-adapter: unknown adapter command: {adapter_name}", file=sys.stderr)
        return 2
    return adapter_main(adapter_args)


if __name__ == "__main__":
    raise SystemExit(main())
