"""Reuse completed PR results when the merged source and check inputs match."""

from __future__ import annotations

import hashlib
import json
import secrets
from pathlib import Path
from typing import Any

from specula import ci_init
from specula.ci_store import CIError, CIStore, git, read_json, write_json


def result_key(base: str, tree: str, configuration: str) -> str:
    return hashlib.sha256(json.dumps([base, tree, configuration]).encode()).hexdigest()


def register_candidate(store: CIStore, token: str) -> None:
    candidate = store.snapshot(token)
    configuration = candidate.get("check_key")
    if not configuration or candidate.get("dirty") is not False:
        return
    directory = ci_init._directory(store.root, ".github-ci/candidates")
    key = result_key(candidate["previous"], candidate["source_tree"], configuration)
    write_json(directory / f"{key}.json", {"snapshot": token})


def candidate_for(store: CIStore, current: dict[str, Any], tree: str, configuration: str) -> dict[str, Any] | None:
    key = result_key(current["token"], tree, configuration)
    path = store.path(f".github-ci/candidates/{key}.json")
    if not path.exists():
        return None
    candidate = store.snapshot(read_json(path)["snapshot"])
    if (candidate.get("previous"), candidate.get("source_tree"), candidate.get("check_key")) != (
        current["token"],
        tree,
        configuration,
    ):
        raise CIError("candidate index does not match its immutable check inputs")
    source = store.path(candidate["source"])
    if (
        candidate.get("dirty") is not False
        or git(source, "rev-parse", f"{candidate['snapshot_commit']}^{{tree}}") != tree
    ):
        return None
    return candidate


def inherit(store: CIStore, source: Path, commit: str, configuration: str | None) -> dict[str, Any] | None:
    """Caller holds the ordinary CI store lease; no Agent or TLC is launched."""
    if configuration is None:
        return None
    current = store.current()
    tree = git(source, "rev-parse", f"{commit}^{{tree}}")
    from_current = current.get("source_tree") == tree and current.get("check_key") == configuration
    if from_current:
        candidate = current
    else:
        found = candidate_for(store, current, tree, configuration)
        if found is None:
            return None
        candidate = found
    checked_source = store.path(candidate["source"])
    if (
        candidate.get("dirty") is not False
        or git(checked_source, "rev-parse", f"{candidate['snapshot_commit']}^{{tree}}") != tree
    ):
        return None
    git(source, "merge-base", "--is-ancestor", current["source_commit"], commit)
    if from_current and current["source_commit"] == commit:
        return {**current, "reuse_kind": "current"}
    destination = ci_init._directory(store.root, f"inheritances/{secrets.token_hex(16)}")
    inputs = {
        **candidate,
        "previous": current["token"],
        "artifact": str(source),
        "source_commit": commit,
        "checked_source_commit": candidate.get("checked_source_commit", candidate["source_commit"]),
        "evidence_run_id": candidate.get("evidence_run_id", candidate["run_id"]),
    }
    store.publish(destination, Path(candidate["model_path"]), inputs)
    return {**store.current(), "reuse_kind": "current" if from_current else "candidate"}
