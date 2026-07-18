"""Durable native-session identity for adapter retries and resumes.

The phase runner owns the state-file path for one logical agent turn.  An
adapter records the exact native session ID emitted by that invocation and
loads it again only when the runner deliberately reuses the same path.  The
binding fields prevent a stale or cross-adapter state file from silently
resuming the wrong conversation.
"""

from __future__ import annotations

import contextlib
import json
import os
import stat
import sys
import tempfile
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1
MAX_STATE_BYTES = 64 * 1024
MAX_SESSION_ID_CHARS = 1024
# Private event-stream status. Shell adapters normalize this to a generic
# failure before returning to the phase runner; it must never be confused with
# native rate-limit (75) or policy (76) statuses.
RESUME_STATE_FAILURE_RC = 79


class ResumeStateError(ValueError):
    """A resume-state file is unsafe, corrupt, or belongs to another run."""


def _text(value: str | None) -> str:
    return value or ""


def _cwd(value: str) -> str:
    if not value:
        raise ResumeStateError("cwd is empty")
    return os.path.realpath(value)


def _validate_session_id(value: object) -> str:
    if not isinstance(value, str) or not value or value != value.strip():
        raise ResumeStateError("session_id must be a non-empty trimmed string")
    if len(value) > MAX_SESSION_ID_CHARS or any(ord(char) < 32 for char in value):
        raise ResumeStateError("session_id contains invalid characters")
    if value.startswith("-"):
        # Every supported CLI receives this value as the operand of a resume
        # option. Refuse option-like IDs even though wrappers use argv arrays:
        # native parsers are not consistent about accepting them as values.
        raise ResumeStateError("session_id must not begin with '-'")
    return value


def _load_payload(path: Path) -> dict[str, Any] | None:
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ResumeStateError(f"cannot inspect {path}: {exc}") from exc
    if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
        raise ResumeStateError(f"resume state is not a regular file: {path}")
    if metadata.st_size > MAX_STATE_BYTES:
        raise ResumeStateError(f"resume state is too large: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ResumeStateError(f"cannot read {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ResumeStateError(f"resume state must be a JSON object: {path}")
    return payload


def _validate_binding(
    payload: dict[str, Any],
    *,
    path: Path,
    adapter: str,
    cwd: str,
    model: str,
    effort: str,
) -> str:
    expected = {
        "version": SCHEMA_VERSION,
        "adapter": adapter,
        "cwd": _cwd(cwd),
        "model": _text(model),
        "effort": _text(effort),
    }
    for key, value in expected.items():
        if payload.get(key) != value:
            raise ResumeStateError(f"resume state {path} has {key}={payload.get(key)!r}; expected {value!r}")
    return _validate_session_id(payload.get("session_id"))


def read_session_id(
    path: str | Path | None,
    *,
    adapter: str,
    cwd: str,
    model: str = "",
    effort: str = "",
) -> str | None:
    """Return the bound native session ID, or ``None`` for a fresh turn."""
    if path is None or not str(path):
        return None
    state_path = Path(path)
    payload = _load_payload(state_path)
    if payload is None:
        return None
    return _validate_binding(
        payload,
        path=state_path,
        adapter=adapter,
        cwd=cwd,
        model=model,
        effort=effort,
    )


def capture_session_id(
    path: str | Path | None,
    *,
    adapter: str,
    session_id: str,
    cwd: str,
    model: str = "",
    effort: str = "",
) -> None:
    """Atomically bind ``path`` to one exact native session.

    Re-observing the same ID is harmless.  A different ID is an integrity
    failure: continuing would merge independent agent histories.
    """
    if path is None or not str(path):
        return
    state_path = Path(path)
    session_id = _validate_session_id(session_id)

    def accept_existing() -> bool:
        existing = _load_payload(state_path)
        if existing is None:
            return False
        bound = _validate_binding(
            existing,
            path=state_path,
            adapter=adapter,
            cwd=cwd,
            model=model,
            effort=effort,
        )
        if bound != session_id:
            raise ResumeStateError(f"resume state {state_path} changed session ID from {bound!r} to {session_id!r}")
        return True

    if accept_existing():
        return

    payload = {
        "version": SCHEMA_VERSION,
        "adapter": adapter,
        "session_id": session_id,
        "cwd": _cwd(cwd),
        "model": _text(model),
        "effort": _text(effort),
    }
    try:
        state_path.parent.mkdir(parents=True, exist_ok=True)
        fd, raw_temporary = tempfile.mkstemp(prefix=f".{state_path.name}.", suffix=".tmp", dir=state_path.parent)
        temporary = Path(raw_temporary)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as stream:
                json.dump(payload, stream, indent=2, sort_keys=True)
                stream.write("\n")
                stream.flush()
                os.fsync(stream.fileno())
            # `replace` would let two simultaneous first events silently
            # overwrite each other. A same-directory hard-link publishes the
            # fully fsynced temporary inode with create-if-absent semantics.
            # The loser then validates the winner's exact binding below.
            try:
                os.link(temporary, state_path, follow_symlinks=False)
            except FileExistsError:
                if not accept_existing():  # pragma: no cover - EEXIST guarantees an entry
                    raise ResumeStateError(f"resume state disappeared during capture: {state_path}") from None
            else:
                directory_fd = os.open(
                    state_path.parent,
                    os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
                )
                try:
                    os.fsync(directory_fd)
                finally:
                    os.close(directory_fd)
        finally:
            with contextlib.suppress(FileNotFoundError):
                temporary.unlink()
    except OSError as exc:
        raise ResumeStateError(f"cannot write {state_path}: {exc}") from exc


def _main(argv: list[str]) -> int:
    if len(argv) != 6 or argv[0] != "read":
        print("usage: resume.py read PATH ADAPTER CWD MODEL EFFORT", file=sys.stderr)
        return 2
    _, path, adapter, cwd, model, effort = argv
    try:
        session_id = read_session_id(
            path,
            adapter=adapter,
            cwd=cwd,
            model=model,
            effort=effort,
        )
    except ResumeStateError as exc:
        print(f"adapter resume state failed: {exc}", file=sys.stderr)
        return 1
    if session_id is not None:
        print(session_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(_main(sys.argv[1:]))
