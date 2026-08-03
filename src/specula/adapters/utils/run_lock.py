"""Run-lock lease propagation for native provider processes."""

from __future__ import annotations

import os
import stat
from collections.abc import Mapping

RUN_LOCK_FD_ENV = "SPECULA_RUN_LOCK_FD"


class RunLockError(OSError):
    """The inherited run-lock lease is missing or unsafe to propagate."""


def inherited_run_lock_fds(env: Mapping[str, str] | None = None) -> tuple[int, ...]:
    """Return the validated run-lock lease inherited from the dispatcher."""
    source = os.environ if env is None else env
    raw = source.get(RUN_LOCK_FD_ENV)
    if raw is None:
        return ()
    try:
        fd = int(raw)
        info = os.fstat(fd)
    except (OSError, ValueError) as exc:
        raise RunLockError("inherited Specula run lock is unavailable") from exc
    if fd < 3 or not stat.S_ISREG(info.st_mode):
        raise RunLockError("inherited Specula run lock is invalid")
    return (fd,)
