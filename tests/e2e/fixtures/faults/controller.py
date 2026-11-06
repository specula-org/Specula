"""Run the real pipeline controller with deterministic fault points (fixture only).

Usage: controller.py SPECROOT_SRC [pipeline arguments...]

FAULT_DIR    directory for the markers below.
FAULT_BLOCK  comma-separated ``module:qualname`` callables. Each call publishes
             ``reached-<qualname>.json`` (this pid) and waits for
             ``release-<qualname>`` before running the original, so a test can
             deliver a real signal at that exact point.
FAULT_QUOTA  when set, a quota wait publishes ``reached-quota.json`` and waits
             for ``release-quota`` instead of sleeping for the reset time.

Nothing else is changed: the controller, phases, and adapters run unmodified.
"""

from __future__ import annotations

import functools
import importlib
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

src, *argv = sys.argv[1:]
sys.path.insert(0, src)
fault_dir = Path(os.environ["FAULT_DIR"])


def hold(label: str) -> None:
    reached = fault_dir / f"reached-{label}.json"
    temporary = reached.with_name(f".{reached.name}.tmp")
    temporary.write_text(json.dumps({"pid": os.getpid()}))
    temporary.replace(reached)
    while not (fault_dir / f"release-{label}").exists():
        time.sleep(0.02)


def blocking(original: Any, label: str) -> Any:
    @functools.wraps(original)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        hold(label)
        return original(*args, **kwargs)

    return wrapper


for target in filter(None, os.environ.get("FAULT_BLOCK", "").split(",")):
    module_name, qualname = target.split(":")
    owner: Any = importlib.import_module(module_name)
    *parents, attribute = qualname.split(".")
    for part in parents:
        owner = getattr(owner, part)
    setattr(owner, attribute, blocking(getattr(owner, attribute), qualname))

from specula import pipelinelib

if os.environ.get("FAULT_QUOTA"):
    real_wait = pipelinelib._wait_for_quota

    def held_wait(**kwargs: Any) -> int:
        kwargs["sleep_fn"] = lambda _seconds: hold("quota")
        return real_wait(**kwargs)

    pipelinelib._wait_for_quota = held_wait

raise SystemExit(pipelinelib.main(argv))
