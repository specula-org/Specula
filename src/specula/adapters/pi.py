"""Adapter: pi.

Options:
  --prompt=...          Task prompt (mutually exclusive with --prompt-file)
  --prompt-file=FILE    Read prompt from file (mutually exclusive with --prompt)
  --max-turns=N         Accepted for launcher compatibility; ignored
  --claude-alias=NAME   Accepted for launcher compatibility; ignored
  --effort=LEVEL        Pi thinking level (default: PI_EFFORT)
  --model=NAME          Provider/model (default: PI_MODEL)
  --log=FILE            Log file path (required)
  --resume-state=PATH   Persist/resume the exact native Pi session
  --background          Accepted; caller handles backgrounding
  --help                Show this help
"""

from __future__ import annotations

import os
import sys

if __package__:
    from .utils.json_cli import AdapterArgumentError, parse_options, run_json_cli
    from .utils.resume import ResumeStateError, read_session_id
else:
    from utils.json_cli import (  # type: ignore[import-not-found, no-redef]
        AdapterArgumentError,
        parse_options,
        run_json_cli,
    )
    from utils.resume import ResumeStateError, read_session_id  # type: ignore[import-not-found, no-redef]

HELP = __doc__


def main(argv: list[str]) -> int:
    if len(argv) == 1 and argv[0] in {"--help", "-h"}:
        print(HELP)
        return 0
    try:
        options = parse_options(
            argv,
            adapter_name="pi",
            model_env="PI_MODEL",
            effort_env="PI_EFFORT",
        )
    except AdapterArgumentError as exc:
        print(exc, file=sys.stderr)
        return 1

    try:
        session_id = read_session_id(
            options.resume_state,
            adapter="pi",
            cwd=os.getcwd(),
            model=options.model,
            effort=options.effort,
        )
    except ResumeStateError as exc:
        options.cleanup()
        print(f"pi adapter: {exc}", file=sys.stderr)
        return 1

    command = ["pi", "--print", "--mode", "json"]
    if options.resume_state is None:
        # Preserve the standalone adapter's historical ephemeral behavior.
        command.append("--no-session")
    elif session_id is not None:
        # Pi accepts either a session path or ID. The full ID captured from
        # this logical turn avoids its unsafe --continue/latest selection.
        command += ["--session", session_id]
    command.append("--approve")
    if options.model:
        command += ["--model", options.model]
    if options.effort:
        command += ["--thinking", options.effort]
    return run_json_cli("pi", command, options)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
