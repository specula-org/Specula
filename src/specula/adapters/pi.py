"""Adapter: pi.

Options:
  --prompt=...          Task prompt (mutually exclusive with --prompt-file)
  --prompt-file=FILE    Read prompt from file (mutually exclusive with --prompt)
  --max-turns=N         Accepted for launcher compatibility; ignored
  --claude-alias=NAME   Accepted for launcher compatibility; ignored
  --effort=LEVEL        Pi thinking level (default: PI_EFFORT; max maps to xhigh)
  --model=NAME          Provider/model (default: PI_MODEL)
  --log=FILE            Log file path (required)
  --background          Accepted; caller handles backgrounding
  --help                Show this help
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from specula.adapters.json_cli import AdapterArgumentError, parse_options, run_json_cli
elif __package__:
    from .json_cli import AdapterArgumentError, parse_options, run_json_cli
else:
    from json_cli import AdapterArgumentError, parse_options, run_json_cli

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

    effort = "xhigh" if options.effort == "max" else options.effort
    command = ["pi", "--print", "--mode", "json", "--no-session", "--approve"]
    if options.model:
        command += ["--model", options.model]
    if effort:
        command += ["--thinking", effort]
    return run_json_cli("pi", command, options)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
