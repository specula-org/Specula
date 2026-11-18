"""Reduce Claude Code session totals to the usage of one invocation.

On ``--resume`` Claude Code restores the running totals saved in the session
transcript (its last ``cost-state`` record), so the ``total_cost_usd`` and
``modelUsage`` of a resumed invocation also count every earlier invocation of
the session. Specula records usage per invocation, so a result is reduced to
what its own process added:

1. A fresh session's totals are already per invocation; its final result's
   running total is exact.
2. For a resumed session, ``model_usage_since_last_result`` (stream-json
   results of recent CLI versions) states what the process counted since its
   previous result; summed over every result from ``result_index`` 0 it is the
   invocation's usage. A missing result (a gap in ``result_index``) loses usage.
3. Otherwise a resumed result is reduced by the totals the CLI restored, read
   from the transcript before launch.

A resumed result with neither source has no known per-invocation cost.
Stdlib only: the adapter runs under any python3 without an install.
"""

from __future__ import annotations

import glob
import json
import math
import unicodedata
from collections.abc import Mapping, Sequence
from pathlib import Path

# Running-total fields of a modelUsage entry. Other fields (context window,
# pricing basis, canonical model) describe the latest request and are copied.
_ADDITIVE_FIELDS = (
    "inputTokens",
    "outputTokens",
    "thinkingTokens",
    "cacheReadInputTokens",
    "cacheCreationInputTokens",
    "cacheCreationEphemeral5mInputTokens",
    "cacheCreationEphemeral1hInputTokens",
    "webSearchRequests",
    "costUSD",
)
# Float noise in the CLI's cost sums; anything below this is not a reset.
_COST_TOLERANCE = 1e-9
# The fields and bounds Claude Code requires of a ``cost-state`` record before
# restoring it on resume (2.1.316 transcript schema); it skips any other record.
_STATE_LIMIT = 1e15
_STATE_COST_LIMIT = 1e9
_STATE_FIELDS = (
    "totalAPIDuration",
    "totalAPIDurationWithoutRetries",
    "totalToolDuration",
    "totalLinesAdded",
    "totalLinesRemoved",
    "totalDuration",
    "startTime",
)
_STATE_MODEL_FIELDS = (
    "inputTokens",
    "outputTokens",
    "cacheReadInputTokens",
    "cacheCreationInputTokens",
    "webSearchRequests",
    "costUSD",
)
_STATE_OPTIONAL_MODEL_FIELDS = (
    "thinkingTokens",
    "cacheCreationEphemeral5mInputTokens",
    "cacheCreationEphemeral1hInputTokens",
)
_STATE_SUMMED_FIELDS = ("inputTokens", "outputTokens", "cacheReadInputTokens", "cacheCreationInputTokens")


def _number(value: object) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    number = float(value)
    return number if math.isfinite(number) and number >= 0 else None


def session_transcript(config_dir: str | Path, session_id: str) -> Path | None:
    """The single native transcript of *session_id* under *config_dir*, if any."""
    if not session_id or "/" in session_id or session_id in {".", ".."}:
        return None
    try:
        matches = [path for path in (Path(config_dir) / "projects").glob(f"*/{glob.escape(session_id)}.jsonl")]
        files = [path for path in matches if path.is_file()]
    except OSError:
        return None
    return files[0] if len(files) == 1 else None


def _bounded(value: object, limit: float = _STATE_LIMIT) -> bool:
    number = _number(value)
    return number is not None and number <= limit


def _restorable_cost_state(record: Mapping[str, object], session_id: str) -> bool:
    """Whether the CLI would restore *record* (mirrors its cost-state schema)."""
    if record.get("type") != "cost-state" or record.get("sessionId") != session_id:
        return False
    if not _bounded(record.get("totalCostUSD"), _STATE_COST_LIMIT):
        return False
    if not all(_bounded(record.get(field)) for field in _STATE_FIELDS):
        return False
    if "hasUnknownModelCost" in record and not isinstance(record["hasUnknownModelCost"], bool):
        return False
    models = record.get("modelUsage")
    if not isinstance(models, dict):
        return False
    for model, entry in models.items():
        if not model or any(unicodedata.category(char) in {"Cc", "Cf"} for char in model):
            return False
        if not isinstance(entry, dict) or not all(_bounded(entry.get(field)) for field in _STATE_MODEL_FIELDS):
            return False
        if not all(field not in entry or _bounded(entry[field]) for field in _STATE_OPTIONAL_MODEL_FIELDS):
            return False
    return all(
        math.fsum(_number(entry[field]) or 0.0 for entry in models.values()) <= _STATE_LIMIT
        for field in _STATE_SUMMED_FIELDS
    )


def restored_totals(config_dir: str | Path, session_id: str) -> dict[str, object] | None:
    """Totals ``claude --resume <session_id>`` starts from, or None when unknown.

    The CLI restores the transcript's last ``cost-state`` record for the session
    that satisfies its schema, skipping malformed ones; a transcript without one
    restores nothing (zero totals).
    """
    transcript = session_transcript(config_dir, session_id)
    if transcript is None:
        return None
    restored: dict[str, object] = {"total_cost_usd": 0.0, "model_usage": {}}
    try:
        with transcript.open(encoding="utf-8", errors="replace") as source:
            for line in source:
                if '"cost-state"' not in line:
                    continue
                try:
                    record = json.loads(line)
                except ValueError:
                    continue
                if isinstance(record, dict) and _restorable_cost_state(record, session_id):
                    restored = {"total_cost_usd": float(record["totalCostUSD"]), "model_usage": record["modelUsage"]}
    except (OSError, UnicodeError):
        return None
    return restored


def _combine(left: object, right: object, sign: int) -> int | float | None:
    """left + sign * right for two valid counts, keeping integer counts integral."""
    first = _number(left)
    second = _number(right)
    if first is None or second is None:
        return None
    if isinstance(left, int) and isinstance(right, int):
        return left + sign * right
    return first + sign * second


def _sum_models(snapshots: Sequence[Mapping[str, object]]) -> dict[str, dict[str, object]] | None:
    total: dict[str, dict[str, object]] = {}
    for snapshot in snapshots:
        for model, entry in snapshot.items():
            if not isinstance(entry, dict):
                return None
            merged = total.setdefault(model, {})
            for key, value in entry.items():
                if key not in _ADDITIVE_FIELDS:
                    merged[key] = value
                    continue
                combined = _combine(merged.get(key, 0), value, 1)
                if combined is None:
                    return None
                merged[key] = combined
    return total


def _subtract_models(
    current: Mapping[str, object], restored: Mapping[str, object]
) -> dict[str, dict[str, object]] | None:
    added: dict[str, dict[str, object]] = {}
    for model, entry in current.items():
        if not isinstance(entry, dict):
            return None
        before = restored.get(model, {})
        if not isinstance(before, dict):
            return None
        delta: dict[str, object] = {}
        changed = False
        for key, value in entry.items():
            if key not in _ADDITIVE_FIELDS:
                delta[key] = value
                continue
            difference = _combine(value, before.get(key, 0), -1)
            if difference is None:
                return None
            tolerance = _COST_TOLERANCE if key == "costUSD" else 0
            if difference < -tolerance:
                return None  # The running total was reset; the restore point is unknown.
            difference = max(difference, 0)
            changed = changed or difference > 0
            delta[key] = difference
        if changed:
            added[model] = delta
    for model in restored:
        if model not in current:
            return None  # A restored model vanished, so these totals are not a continuation.
    return added


def _token_usage(models: Mapping[str, dict[str, object]]) -> dict[str, int]:
    def total(key: str) -> int:
        return sum(int(_number(entry.get(key, 0)) or 0) for entry in models.values())

    return {
        "input_tokens": total("inputTokens"),
        "cache_creation_input_tokens": total("cacheCreationInputTokens"),
        "cache_read_input_tokens": total("cacheReadInputTokens"),
        "output_tokens": total("outputTokens"),
    }


def _model_cost(models: Mapping[str, dict[str, object]]) -> float | None:
    costs = [_number(entry.get("costUSD")) for entry in models.values()]
    if any(cost is None for cost in costs):
        return None
    return math.fsum(cost for cost in costs if cost is not None)


def invocation_usage(
    results: Sequence[Mapping[str, object]],
    *,
    resumed: bool,
    restored: Mapping[str, object] | None,
) -> dict[str, object]:
    """Usage fields for one invocation from its result records (last = final).

    Returns ``total_cost_usd``, ``usage`` and ``model_usage`` for this
    invocation, plus ``usage_scope``, ``cost_basis`` and, for a resumed session,
    the CLI's ``session_total_cost_usd``. ``total_cost_usd`` is None when the
    invocation's own cost cannot be determined.
    """
    final = results[-1]
    reported_models = final.get("modelUsage")
    fields: dict[str, object] = {"usage_scope": "invocation"}
    if resumed:
        fields["session_total_cost_usd"] = final.get("total_cost_usd")

    if not resumed:
        return {
            "total_cost_usd": final.get("total_cost_usd", 0),
            "usage": final.get("usage", {}),
            "model_usage": reported_models if reported_models is not None else {},
            **fields,
            "cost_basis": "new_session",
        }

    since = [result.get("model_usage_since_last_result") for result in results]
    # Each result states only the usage since the previous one, so the sum is
    # complete only when every result of the process was observed.
    numbered = [result.get("result_index") for result in results] == list(range(len(results))) and all(
        type(result.get("result_index")) is int for result in results
    )
    if numbered and all(isinstance(snapshot, dict) for snapshot in since):
        models = _sum_models([snapshot for snapshot in since if isinstance(snapshot, dict)])
        if models is not None:
            return {
                "total_cost_usd": _model_cost(models),
                "usage": _token_usage(models),
                "model_usage": models,
                **fields,
                "cost_basis": "model_usage_since_last_result",
            }

    reported_cost = _number(final.get("total_cost_usd"))
    restored_cost = _number(restored.get("total_cost_usd")) if restored is not None else None
    restored_models = restored.get("model_usage") if restored is not None else None
    if (
        reported_cost is not None
        and restored_cost is not None
        and isinstance(reported_models, dict)
        and isinstance(restored_models, dict)
        and reported_cost + _COST_TOLERANCE >= restored_cost
    ):
        models = _subtract_models(reported_models, restored_models)
        if models is not None:
            return {
                "total_cost_usd": max(reported_cost - restored_cost, 0.0),
                "usage": _token_usage(models),
                "model_usage": models,
                **fields,
                "cost_basis": "restored_session_totals",
            }

    return {
        "total_cost_usd": None,
        "usage": {},
        "model_usage": {},
        **fields,
        "cost_basis": "unavailable",
        "usage_complete": False,
    }
