"""Shared runtime for stdin-driven agent CLIs that emit JSONL."""

from __future__ import annotations

import contextlib
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import FrameType
from typing import Any

from .event_stream import StreamStatus, stream_events
from .text import summary
from .usage import augment_opencode_usage, augment_pi_usage

RATE_LIMIT_RC = 75  # EX_TEMPFAIL; this is the scheduler contract in specula.quota.


class AdapterArgumentError(ValueError):
    """Invalid launcher-facing adapter arguments."""

    def __init__(self, adapter_name: str, message: str) -> None:
        super().__init__(f"{adapter_name} adapter: {message}")


@dataclass
class AdapterOptions:
    prompt_path: Path
    temporary_prompt: bool
    log_path: Path
    model: str
    effort: str

    def cleanup(self) -> None:
        if self.temporary_prompt:
            with contextlib.suppress(OSError):
                self.prompt_path.unlink()


def parse_options(
    argv: list[str],
    *,
    adapter_name: str,
    model_env: str,
    effort_env: str,
) -> AdapterOptions:
    """Parse the common Specula adapter options without reading prompt files."""
    prompt: str | None = None
    prompt_file: str | None = None
    log_file: str | None = None
    model: str | None = None
    effort: str | None = None

    for arg in argv:
        if arg.startswith("--prompt="):
            prompt = arg.removeprefix("--prompt=")
        elif arg.startswith("--prompt-file="):
            prompt_file = arg.removeprefix("--prompt-file=")
        elif arg.startswith("--log="):
            log_file = arg.removeprefix("--log=")
        elif arg.startswith("--model="):
            model = arg.removeprefix("--model=")
        elif arg.startswith("--effort="):
            effort = arg.removeprefix("--effort=")
        elif arg.startswith("--max-turns=") or arg.startswith("--claude-alias=") or arg == "--background":
            pass
        else:
            raise AdapterArgumentError(adapter_name, f"unknown option: {arg}")

    resolved_model = os.environ.get(model_env, "") if model is None else model
    resolved_effort = os.environ.get(effort_env, "") if effort is None else effort
    os.environ.pop(model_env, None)
    os.environ.pop(effort_env, None)

    if prompt and prompt_file:
        raise AdapterArgumentError(adapter_name, "--prompt and --prompt-file are mutually exclusive")
    if not prompt and not prompt_file:
        raise AdapterArgumentError(adapter_name, "one of --prompt or --prompt-file is required")
    if not log_file:
        raise AdapterArgumentError(adapter_name, "--log is required")

    if prompt_file:
        prompt_path = Path(prompt_file).resolve()
        if not prompt_path.is_file():
            raise AdapterArgumentError(adapter_name, f"prompt file not found: {prompt_file}")
        temporary_prompt = False
    else:
        fd, raw_path = tempfile.mkstemp(prefix=f"specula-{adapter_name}-prompt-", suffix=".txt", text=True)
        prompt_path = Path(raw_path)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as prompt_stream:
                prompt_stream.write(prompt or "")
        except BaseException:
            with contextlib.suppress(OSError):
                os.close(fd)
            with contextlib.suppress(OSError):
                prompt_path.unlink()
            raise
        temporary_prompt = True

    return AdapterOptions(
        prompt_path=prompt_path,
        temporary_prompt=temporary_prompt,
        log_path=Path(log_file),
        model=resolved_model,
        effort=resolved_effort,
    )


def _empty_usage(adapter_name: str) -> dict[str, object]:
    return {
        "agent": adapter_name,
        "session_id": None,
        "session_file": None,
        "total_cost_usd": None,
        "usage": {
            "input_tokens": 0,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 0,
            "reasoning_output_tokens": 0,
            "total_tokens": 0,
        },
    }


def _write_usage(path: Path, payload: dict[str, object]) -> bool:
    temporary_path: Path | None = None
    try:
        fd, raw_path = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
        temporary_path = Path(raw_path)
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(payload, stream, indent=2, sort_keys=True)
            stream.write("\n")
        os.replace(temporary_path, path)
        temporary_path = None
        return True
    except OSError as exc:
        print(f"adapter usage write failed: {summary(str(exc), None)}", file=sys.stderr)
        return False
    finally:
        if temporary_path is not None:
            with contextlib.suppress(OSError):
                temporary_path.unlink()


def _write_spawn_failure(adapter_name: str, command: list[str], options: AdapterOptions, exc: OSError) -> None:
    executable = command[0] if command else "command"
    diagnostic = summary(f"{adapter_name} adapter: failed to launch {executable}: {exc}", None)
    try:
        options.log_path.write_text(diagnostic + "\n", encoding="utf-8", errors="replace")
    except OSError as log_exc:
        print(f"{adapter_name} adapter: readable log write failed: {summary(str(log_exc), None)}", file=sys.stderr)
    _write_usage(options.log_path.with_suffix(".usage.json"), _empty_usage(adapter_name))
    print(diagnostic, file=sys.stderr)


def _opencode_database_path(env: Mapping[str, str]) -> Path | None:
    data_home = env.get("XDG_DATA_HOME")
    if data_home:
        return Path(data_home) / "opencode" / "opencode.db"
    home = env.get("HOME")
    if home:
        return Path(home) / ".local" / "share" / "opencode" / "opencode.db"
    return None


@contextlib.contextmanager
def _cleanup_on_signal(
    process_ref: Callable[[], subprocess.Popen[bytes] | None],
) -> Iterator[None]:
    """Turn termination signals into an unwinding exit and stop the native CLI."""

    def _cancel(signum: int, _frame: FrameType | None) -> None:
        process = process_ref()
        if process is not None and process.poll() is None:
            with contextlib.suppress(OSError, ProcessLookupError):
                process.send_signal(signum)
        raise SystemExit(128 + signum)

    installed: list[tuple[int, Callable[[int, FrameType | None], Any] | int | None]] = []
    for name in ("SIGTERM", "SIGHUP"):
        signum = getattr(signal, name, None)
        if signum is None:  # pragma: no cover - non-POSIX
            continue
        with contextlib.suppress(ValueError, OSError):
            installed.append((signum, signal.signal(signum, _cancel)))
    try:
        yield
    finally:
        for signum, previous in installed:
            with contextlib.suppress(ValueError, OSError):
                handler = signal.Handlers(previous) if isinstance(previous, int) else previous
                signal.signal(signum, handler)


def run_json_cli(
    adapter_name: str,
    command: list[str],
    options: AdapterOptions,
    child_env: dict[str, str] | None = None,
) -> int:
    """Run a JSONL CLI and persist its raw, readable, and usage sidecars."""
    effective_env = child_env
    pi_session_root: Path | None = None
    activity_path: Path | None = None
    temporary_activity = False
    process: subprocess.Popen[bytes] | None = None
    inherited_env = child_env if child_env is not None else os.environ
    with _cleanup_on_signal(lambda: process):
        try:
            if adapter_name == "pi":
                try:
                    raw_root = tempfile.mkdtemp(
                        prefix="specula-pi-sessions-",
                        dir=inherited_env.get("TMPDIR") or None,
                    )
                    pi_session_root = Path(raw_root)
                    effective_env = dict(inherited_env)
                    effective_env["TMPDIR"] = raw_root
                except OSError as exc:
                    print(
                        f"adapter usage warning: isolated Pi session directory: {summary(str(exc), None)}",
                        file=sys.stderr,
                    )

            activity_value = inherited_env.get("SPECULA_ACTIVITY_LOG", "")
            if activity_value:
                activity_path = Path(activity_value)
            else:
                try:
                    fd, raw_path = tempfile.mkstemp(prefix=f"specula-{adapter_name}-activity-", suffix=".jsonl")
                    os.close(fd)
                    activity_path = Path(raw_path)
                    temporary_activity = True
                except OSError as exc:
                    print(
                        f"adapter event stream warning: temporary activity log: {summary(str(exc), None)}",
                        file=sys.stderr,
                    )
                    activity_path = Path(os.devnull)

            try:
                prompt_stream = options.prompt_path.open("rb")
                try:
                    process = subprocess.Popen(
                        command,
                        stdin=prompt_stream,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                        env=effective_env,
                    )
                finally:
                    prompt_stream.close()
            except OSError as exc:
                _write_spawn_failure(adapter_name, command, options, exc)
                return 127

            status: StreamStatus | None = None
            stream_failed = False
            try:
                if process.stdout is None:
                    raise OSError("child stdout pipe unavailable")
                status = stream_events(adapter_name, activity_path, options.log_path, process.stdout)
            except OSError as exc:
                stream_failed = True
                print(f"{adapter_name} adapter: event stream failed: {summary(str(exc), None)}", file=sys.stderr)
            finally:
                if process.stdout is not None:
                    with contextlib.suppress(OSError):
                        process.stdout.close()
                native_status = process.wait()

            usage = status.usage if status is not None else _empty_usage(adapter_name)
            if status is not None:
                if adapter_name == "pi":
                    usage = augment_pi_usage(usage, status.session_files, pi_session_root)
                elif adapter_name == "opencode":
                    usage = augment_opencode_usage(usage, _opencode_database_path(inherited_env))
            usage_ok = _write_usage(options.log_path.with_suffix(".usage.json"), usage)
            if status is not None and status.rate_limit_error is not None:
                print(
                    f"{adapter_name} adapter: rate limit hit: {summary(status.rate_limit_error, None)}", file=sys.stderr
                )
                return RATE_LIMIT_RC
            if native_status != 0:
                return native_status
            if stream_failed or status is None or not status.log_ok or not usage_ok:
                return 1
            failure = status.structured_error or status.terminal_error
            if failure:
                print(f"{adapter_name} adapter: {summary(failure, None)}", file=sys.stderr)
                return 1
            return 0
        finally:
            if temporary_activity and activity_path is not None:
                with contextlib.suppress(OSError):
                    activity_path.unlink()
            if pi_session_root is not None:
                with contextlib.suppress(OSError):
                    shutil.rmtree(pi_session_root)
            options.cleanup()
