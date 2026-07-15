#!/usr/bin/env python3
"""specula — unified command-line entrypoint for the Specula pipeline.

Python port of the repo-root `specula` bash dispatcher (now a thin shim to
this file); also installed as the `specula` console script by `pip install
-e .`. It is a thin passthrough: every argument after <command> is forwarded
verbatim to the underlying launch script via exec, so per-phase flags
(--agent, --artifact, --max-parallel, --dry-run, ...) behave exactly as
before and `specula <command> --help` shows that script's own help.

Dispatch targets are the bash launch scripts under scripts/ — they need a
repo checkout, so the console script works from an editable install (or the
shim from any checkout), not from a plain wheel install.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

PROG = "specula"
VERSION = "0.2.0"

SPECULA_ROOT = Path(__file__).resolve().parents[2]
SCRIPTS_DIR = SPECULA_ROOT / "scripts"

# command | script (relative to scripts/) | one-line help.
# The order here is the order shown in `specula --help`.
COMMANDS: list[tuple[str, str, str]] = [
    ("run", "launch/launch_pipeline.sh", "Run the full pipeline (all phases: analysis -> classification)"),
    ("batch", "exp/scheduler.sh", "Batch-run the pipeline over a task queue (workers, quota gate, retries)"),
    ("analyze", "launch/launch_code_analysis.sh", "Phase 1 - static code analysis -> modeling brief"),
    ("specgen", "launch/launch_spec_generation.sh", "Phase 2 - generate TLA+ specs from the modeling brief"),
    ("harness", "launch/launch_harness_generation.sh", "Phase 2.5 - instrument the system + collect traces"),
    ("validate", "launch/launch_spec_validation.sh", "Phase 3 - trace validation + model checking (bug hunting)"),
    ("confirm", "launch/launch_bug_confirmation.sh", "Phase 4a - confirm & reproduce model-checking bugs"),
    ("classify", "launch/launch_bug_classification.sh", "Phase 4b - assign severity tiers to confirmed bugs"),
    ("review", "launch/launch_review.sh", "Run an inter-phase review agent"),
    ("setup", "infra/setup.sh", "Install Specula agent skills + MCP tools"),
]


def help_text() -> str:
    width = max(len(cmd) for cmd, _, _ in COMMANDS)
    lines = [
        f'usage: {PROG} <command> [options] "name|github|lang|reference" [...]',
        "",
        "A framework for finding deep bugs in system code using TLA+.",
        "",
        "commands:",
    ]
    lines += [f"  {cmd:<{width}}  {desc}" for cmd, _, desc in COMMANDS]
    lines += [
        "",
        "Every argument after <command> is forwarded verbatim to the underlying",
        f"launch script. Run '{PROG} <command> --help' for a command's full flag set.",
    ]
    return "\n".join(lines) + "\n"


def _exec(argv: list[str]) -> int:
    """Replace this process with the launch script, like the bash `exec`.
    Split out so tests can capture the dispatch without leaving the process."""
    os.execvp(argv[0], argv)  # noqa: S606  # never returns


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if args == ["--version"]:
        sys.stdout.write(f"{PROG} {VERSION}\n")
        return 0
    if not args or args[0] in ("-h", "--help", "help"):
        sys.stdout.write(help_text())
        return 0
    sub, rest = args[0], args[1:]
    if sub == "_adapter":
        from specula.adapters.cli import main as adapter_main

        return adapter_main(rest)
    for cmd, script, _ in COMMANDS:
        if sub == cmd:
            return _exec(["bash", str(SCRIPTS_DIR / script), *rest])
    sys.stderr.write(f"{PROG}: unknown command '{sub}'\n\n")
    sys.stderr.write(help_text())
    return 2


if __name__ == "__main__":
    sys.exit(main())
