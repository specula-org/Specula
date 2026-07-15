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

import json
import os
import sys
from pathlib import Path

if __package__:
    from .utils.json_cli import AdapterArgumentError, parse_options, run_json_cli
else:
    from utils.json_cli import (  # type: ignore[import-not-found, no-redef]
        AdapterArgumentError,
        parse_options,
        run_json_cli,
    )

HELP = __doc__
SPECULA_ROOT = Path(__file__).resolve().parents[3]


def _allow_external_directories(env: dict[str, str]) -> None:
    candidates = [
        env.get("SPECULA_ROOT") or str(SPECULA_ROOT),
        env.get("SPECULA_TARGET_REPO_DIR", ""),
        env.get("SPECULA_WORK_DIR", ""),
    ]
    directories: list[Path] = []
    seen: set[Path] = set()
    for candidate in candidates:
        if not candidate:
            continue
        try:
            path = Path(candidate).expanduser().resolve()
        except OSError:
            continue
        if path not in seen:
            directories.append(path)
            seen.add(path)
    if not directories:
        return

    raw_permission = env.get("OPENCODE_PERMISSION", "")
    if raw_permission:
        try:
            loaded = json.loads(raw_permission)
        except json.JSONDecodeError:
            # Preserve invalid native configuration so OpenCode reports it
            # instead of silently running with different permissions.
            return
        if isinstance(loaded, str) and loaded == "allow":
            return
        if isinstance(loaded, str) and loaded in {"ask", "deny"}:
            permission: dict[str, object] = {"*": loaded}
        elif isinstance(loaded, dict):
            permission = dict(loaded)
        else:
            return
    else:
        permission = {}

    external = permission.get("external_directory")
    if external == "allow":
        return
    native_rules = (
        dict(external)
        if isinstance(external, dict)
        else {"*": external}
        if isinstance(external, str) and external in {"ask", "deny"}
        else {}
    )
    generated_rules: dict[str, str] = {}
    for directory in directories:
        raw = str(directory)
        if raw not in native_rules:
            generated_rules[raw] = "allow"
        if f"{raw}/**" not in native_rules:
            generated_rules[f"{raw}/**"] = "allow"

    # OpenCode applies the last matching pattern.  Keep every native rule in
    # its original relative position, inserting Specula's paths after the
    # native catch-all (or before all native rules when there is no catch-all).
    # That lets the generated paths override only a default, while later native
    # path-specific denies/asks still win.
    rules: dict[str, object] = {}
    if "*" not in native_rules:
        rules.update(generated_rules)
    for pattern, action in native_rules.items():
        rules[pattern] = action
        if pattern == "*":
            rules.update(generated_rules)
    permission["external_directory"] = rules
    env["OPENCODE_PERMISSION"] = json.dumps(permission, separators=(",", ":"))


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

    # OpenCode auto-rejects permission prompts in non-interactive runs unless
    # this auto-approval flag is present.
    command = ["opencode", "run", "--format=json", "--thinking", "--dangerously-skip-permissions"]
    if options.model:
        command += ["--model", options.model]
    if options.effort:
        command += ["--variant", options.effort]
    child_env = os.environ.copy()
    child_env["OPENCODE_FAKE_VCS"] = "git"
    _allow_external_directories(child_env)
    return run_json_cli("opencode", command, options, child_env=child_env)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
