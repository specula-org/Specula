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

import contextlib
import json
import os
import sys
import tempfile
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


def _allow_external_directory_config(env: dict[str, str]) -> Path | None:
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
        return None

    config: dict[str, object] = {"$schema": "https://opencode.ai/config.json"}
    existing_config = env.get("OPENCODE_CONFIG", "")
    if existing_config:
        try:
            loaded = json.loads(Path(existing_config).read_text())
            if isinstance(loaded, dict):
                config.update(loaded)
        except (OSError, json.JSONDecodeError):
            pass

    permission = config.get("permission")
    if not isinstance(permission, dict):
        permission = {}
        config["permission"] = permission
    external = permission.get("external_directory")
    if external == "allow":
        return None
    rules = dict(external) if isinstance(external, dict) else {}
    for directory in directories:
        raw = str(directory)
        rules.setdefault(raw, "allow")
        rules.setdefault(f"{raw}/**", "allow")
    permission["external_directory"] = rules

    fd, raw_path = tempfile.mkstemp(prefix="specula-opencode-", suffix=".json")
    config_path = Path(raw_path)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(config, stream, indent=2, sort_keys=True)
            stream.write("\n")
    except BaseException:
        with contextlib.suppress(OSError):
            os.close(fd)
        with contextlib.suppress(OSError):
            config_path.unlink()
        raise
    env["OPENCODE_CONFIG"] = str(config_path)
    return config_path


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
    config_path = _allow_external_directory_config(child_env)
    try:
        return run_json_cli("opencode", command, options, child_env=child_env)
    finally:
        if config_path is not None:
            with contextlib.suppress(OSError):
                config_path.unlink()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
