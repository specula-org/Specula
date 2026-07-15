"""Adapter: opencode.

Options:
  --prompt=...          Task prompt (mutually exclusive with --prompt-file)
  --prompt-file=FILE    Read prompt from file (mutually exclusive with --prompt)
  --max-turns=N         Accepted for launcher compatibility; ignored
  --claude-alias=NAME   Accepted for launcher compatibility; ignored
  --effort=LEVEL        OpenCode variant (default: OPENCODE_EFFORT)
  --model=NAME          Provider/model (default: OPENCODE_MODEL)
  --log=FILE            Log file path (required)
  --background          Accepted; caller handles backgrounding
  --help                Show this help
"""

from __future__ import annotations

import os
import sys

if __package__:
    from .utils.json_cli import AdapterArgumentError, parse_options, run_json_cli
else:
    from utils.json_cli import (  # type: ignore[import-not-found, no-redef]
        AdapterArgumentError,
        parse_options,
        run_json_cli,
    )

HELP = __doc__


def main(argv: list[str]) -> int:
    if len(argv) == 1 and argv[0] in {"--help", "-h"}:
        print(HELP)
        return 0
    try:
        options = parse_options(
            argv,
            adapter_name="opencode",
            model_env="OPENCODE_MODEL",
            effort_env="OPENCODE_EFFORT",
        )
    except AdapterArgumentError as exc:
        print(exc, file=sys.stderr)
        return 1

    command = ["opencode", "run", "--format=json", "--thinking"]
    if options.model:
        command += ["--model", options.model]
    if options.effort:
        command += ["--variant", options.effort]
    child_env = os.environ.copy()
    child_env["OPENCODE_FAKE_VCS"] = "git"
    return run_json_cli("opencode", command, options, child_env=child_env)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
