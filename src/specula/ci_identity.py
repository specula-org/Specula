"""Content identities used to reuse a completed CI result, not semantic grading."""

from __future__ import annotations

import hashlib
import json
import os
from functools import lru_cache
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from specula.ci_workflow import CIPipeline

SPECULA_ROOT = Path(__file__).resolve().parents[2]


@lru_cache(maxsize=1)
def method_digest() -> str:
    digest = hashlib.sha256()
    for folder in ("src/specula", "skills", "scripts/launch"):
        for path in sorted((SPECULA_ROOT / folder).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix in {".py", ".md", ".sh", ".yaml"}:
                digest.update(path.relative_to(SPECULA_ROOT).as_posix().encode())
                digest.update(b"\0")
                digest.update(path.read_bytes())
                digest.update(b"\0")
    return digest.hexdigest()


def check_key(pipeline: CIPipeline, guidance: str) -> str | None:
    selection = pipeline._agent_selection()
    model, effort = pipeline._resolved_run_tuning(selection)
    # Unspecified native model defaults can change outside Specula's control.
    if not model:
        return None
    document = {
        "method": method_digest(),
        "agent": selection.agent,
        "model": model,
        "effort": effort,
        "profile": pipeline.claude_alias,
        "max_turns": pipeline.max_turns,
        "guidance": guidance,
        "memory": pipeline.tlc_memory_limit or os.environ.get("SPECULA_TLC_MEMORY_LIMIT") or "auto",
        "workers": pipeline.tlc_worker_limit or os.environ.get("SPECULA_TLC_WORKER_LIMIT"),
        "environment": os.environ.get("SPECULA_CI_ENVIRONMENT", ""),
    }
    return hashlib.sha256(json.dumps(document, sort_keys=True).encode()).hexdigest()
