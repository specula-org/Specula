"""Per-invocation Claude Code usage for resumed sessions and native compaction.

Fixtures are trimmed copies of real Claude Code results and transcript
``cost-state`` records: 2.1.316 (orchestration-v2 arc-swap run, one session
resumed twice with a native compaction between) and 2.1.280 (a confirmation
turn resumed without ``model_usage_since_last_result``).
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import pytest

from specula import context_runner as runner
from specula.adapters.utils.claude_usage import invocation_usage, restored_totals, session_transcript
from specula.resource_summary import _claude_usage

SESSION = "1fff9301-91b4-4eee-a8a1-dfe595f89d92"
OLD_SESSION = "d96c2822-12df-43af-9d4d-6c6818d5b9a3"


def _models(opus55: tuple[int, int, int, int, float], opus48: tuple[int, int, int, int, float] | None = None) -> Any:
    def entry(values: tuple[int, int, int, int, float]) -> dict[str, Any]:
        input_tokens, output, cache_read, cache_write, cost = values
        return {
            "inputTokens": input_tokens,
            "outputTokens": output,
            "cacheReadInputTokens": cache_read,
            "cacheCreationInputTokens": cache_write,
            "costUSD": cost,
            "contextWindow": 1000000,
        }

    models = {"claude-opus-5-5": entry(opus55)}
    if opus48 is not None:
        models["claude-opus-4-8"] = entry(opus48)
    return models


SUBAGENT_48 = (26, 56945, 1380258, 137665, 2.97429025)
# Claude Code 2.1.316: fresh main invocation, two resumes, compaction between.
FIRST = {
    "type": "result",
    "session_id": SESSION,
    "total_cost_usd": 26.95365824999999,
    "modelUsage": _models((446, 406247, 47579380, 1164561, 23.97936799999999), SUBAGENT_48),
    "model_usage_since_last_result": _models((446, 406247, 47579380, 1164561, 23.97936799999999), SUBAGENT_48),
    "result_index": 0,
}
SECOND = {
    "type": "result",
    "session_id": SESSION,
    "total_cost_usd": 49.28661325000002,
    "modelUsage": _models((652, 773974, 95323375, 1843160, 46.31232300000003), SUBAGENT_48),
    "model_usage_since_last_result": _models((206, 367727, 47743995, 678599, 22.332954999999988)),
    "result_index": 0,
}
COMPACTION = {
    "type": "result",
    "subtype": "success",
    "is_error": False,
    "local_command": "compact",
    "session_id": SESSION,
    "total_cost_usd": 49.80214985000002,
    "usage": {"input_tokens": 0, "cache_creation_input_tokens": 0, "cache_read_input_tokens": 0, "output_tokens": 0},
    "modelUsage": _models((2768, 792404, 96012363, 1843295, 46.827859600000025), SUBAGENT_48),
    "model_usage_since_last_result": _models((2116, 18430, 688988, 135, 0.5155365999999999)),
    "result_index": 0,
}
THIRD = {
    "type": "result",
    "session_id": SESSION,
    "total_cost_usd": 63.767727649999976,
    "modelUsage": _models((940, 958013, 132410327, 2265884, 60.79343739999998), SUBAGENT_48),
    "model_usage_since_last_result": _models((288, 184039, 37086952, 422724, 14.481114399999996)),
    "result_index": 0,
}
# The session's cost-state records: one per main invocation, none for /compact.
COST_STATES = [
    {"totalCostUSD": FIRST["total_cost_usd"], "modelUsage": FIRST["modelUsage"]},
    {"totalCostUSD": SECOND["total_cost_usd"], "modelUsage": SECOND["modelUsage"]},
    {"totalCostUSD": THIRD["total_cost_usd"], "modelUsage": THIRD["modelUsage"]},
]
# Claude Code 2.1.280: no model_usage_since_last_result.
OLD_SUBAGENT = (2, 0, 11213, 238817, 2.3937865)
OLD_FIRST = {
    "type": "result",
    "session_id": OLD_SESSION,
    "total_cost_usd": 9.178999300000001,
    "modelUsage": _models((170, 78605, 14820724, 281036, 6.785212800000001), OLD_SUBAGENT),
}
OLD_RESUMED = {
    "type": "result",
    "session_id": OLD_SESSION,
    "total_cost_usd": 14.138606899999996,
    "modelUsage": _models((212, 123461, 21316402, 626434, 11.744820399999996), OLD_SUBAGENT),
}


def _transcript(config: Path, session: str, states: list[dict[str, Any]], *, project: str = "-work-dir") -> Path:
    path = config / "projects" / project / f"{session}.jsonl"
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [json.dumps({"type": "user", "message": {"content": "cost-state is mentioned here"}})]
    for state in states:
        lines.append(json.dumps({"type": "cost-state", "sessionId": session, "startTime": 1793978192556, **state}))
        lines.append(json.dumps({"type": "assistant", "message": {"usage": {"output_tokens": 1}}}))
    path.write_text("\n".join(lines) + "\n")
    return path


def test_resumed_invocations_report_only_their_own_usage() -> None:
    first = invocation_usage([FIRST], resumed=False, restored=None)
    second: Any = invocation_usage([SECOND], resumed=True, restored=None)
    third = invocation_usage([THIRD], resumed=True, restored=None)
    assert first["total_cost_usd"] == pytest.approx(26.95365825)
    assert second["total_cost_usd"] == pytest.approx(22.332955)
    assert third["total_cost_usd"] == pytest.approx(14.4811144)
    assert second["cost_basis"] == "model_usage_since_last_result"
    assert second["session_total_cost_usd"] == SECOND["total_cost_usd"]
    # The idle subagent model is not re-counted on resume.
    assert set(second["model_usage"]) == {"claude-opus-5-5"}
    assert second["usage"] == {
        "input_tokens": 206,
        "cache_creation_input_tokens": 678599,
        "cache_read_input_tokens": 47743995,
        "output_tokens": 367727,
    }
    record = _claude_usage({"session_id": SESSION, **second})
    assert record.complete and record.total_tokens == 206 + 678599 + 47743995 + 367727


def test_compaction_receipt_counts_the_compaction_not_the_session() -> None:
    receipt = {"status": "completed", "usage_payload": COMPACTION, "restored_usage": None}
    record = runner.compaction_usage("claude-code", receipt)
    assert record is not None and record.complete
    assert record.cost_usd == pytest.approx(0.5155366)
    assert record.total_tokens == 2116 + 18430 + 688988 + 135
    # Receipts written before restored_usage existed are reduced the same way.
    legacy = runner.compaction_usage("claude-code", {"status": "completed", "usage_payload": COMPACTION})
    assert legacy is not None and legacy.cost_usd == pytest.approx(0.5155366)


def test_whole_session_total_is_the_sum_of_increments(tmp_path: Path) -> None:
    """Old accounting summed 26.95 + 49.29 + 49.80 + 63.77 = 189.81 for this session."""
    turns = [
        _claude_usage({"session_id": SESSION, **invocation_usage([FIRST], resumed=False, restored=None)}),
        _claude_usage({"session_id": SESSION, **invocation_usage([SECOND], resumed=True, restored=None)}),
        runner.compaction_usage("claude-code", {"usage_payload": COMPACTION}),
        _claude_usage({"session_id": SESSION, **invocation_usage([THIRD], resumed=True, restored=None)}),
    ]
    target = tmp_path / "main.usage.json"
    runner.publish_usage(target, "claude-code", SESSION, list(turns))
    published = json.loads(target.read_text())
    # The final running total (63.77) omits the compaction, which no cost-state saved.
    assert published["total_cost_usd"] == pytest.approx(64.28326415)
    assert published["usage_complete"] is True


def test_restored_totals_follow_the_transcript_cost_state(tmp_path: Path) -> None:
    config = tmp_path / "profile"
    assert restored_totals(config, SESSION) is None  # no transcript: unknown, not zero
    _transcript(config, SESSION, [])
    assert restored_totals(config, SESSION) == {"total_cost_usd": 0.0, "model_usage": {}}
    path = _transcript(config, SESSION, COST_STATES[:2])
    with path.open("a") as out:
        out.write(json.dumps({"type": "cost-state", "sessionId": "other", "totalCostUSD": 99.0, "modelUsage": {}}))
        out.write("\n" + json.dumps({"type": "cost-state", "sessionId": SESSION, "totalCostUSD": -1}) + "\n")
        out.write('{"type": "cost-state", truncated\n')
    restored = restored_totals(config, SESSION)
    assert restored is not None and restored["total_cost_usd"] == SECOND["total_cost_usd"]
    # The compaction resumes from the second invocation's saved totals.
    receipt = {"usage_payload": {k: v for k, v in COMPACTION.items() if k != "model_usage_since_last_result"}}
    record = runner.compaction_usage("claude-code", {**receipt, "restored_usage": restored})
    assert record is not None and record.cost_usd == pytest.approx(0.5155366)
    assert record.total_tokens == 2116 + 18430 + 688988 + 135
    # Two transcripts for one session id leave the restore point unknown.
    _transcript(config, SESSION, [], project="-elsewhere")
    assert session_transcript(config, SESSION) is None
    assert restored_totals(config, SESSION) is None


def test_old_cli_resume_is_reduced_by_restored_totals(tmp_path: Path) -> None:
    config = tmp_path / "profile"
    _transcript(
        config,
        OLD_SESSION,
        [{"totalCostUSD": OLD_FIRST["total_cost_usd"], "modelUsage": OLD_FIRST["modelUsage"]}],
    )
    usage = invocation_usage([OLD_RESUMED], resumed=True, restored=restored_totals(config, OLD_SESSION))
    assert usage["cost_basis"] == "restored_session_totals"
    assert usage["total_cost_usd"] == pytest.approx(4.9596076)
    assert usage["model_usage"] == {
        "claude-opus-5-5": {
            "inputTokens": 42,
            "outputTokens": 44856,
            "cacheReadInputTokens": 6495678,
            "cacheCreationInputTokens": 345398,
            "costUSD": pytest.approx(4.959607599999995),
            "contextWindow": 1000000,
        }
    }
    fresh = invocation_usage([OLD_FIRST], resumed=False, restored=None)
    assert fresh["cost_basis"] == "new_session" and fresh["total_cost_usd"] == OLD_FIRST["total_cost_usd"]


def test_unknown_or_reset_restore_point_is_not_guessed() -> None:
    unknown = invocation_usage([OLD_RESUMED], resumed=True, restored=None)
    assert unknown["total_cost_usd"] is None and unknown["usage_complete"] is False
    assert unknown["session_total_cost_usd"] == OLD_RESUMED["total_cost_usd"]
    record = _claude_usage({"session_id": OLD_SESSION, **unknown})
    assert not record.complete and record.cost_usd is None and record.total_tokens is None
    # A running total below the restored one (e.g. after /clear) has no known delta.
    reset = invocation_usage(
        [OLD_FIRST],
        resumed=True,
        restored={"total_cost_usd": OLD_RESUMED["total_cost_usd"], "model_usage": OLD_RESUMED["modelUsage"]},
    )
    assert reset["cost_basis"] == "unavailable" and reset["total_cost_usd"] is None


def test_usage_stated_per_result_is_summed_over_results() -> None:
    later = {**THIRD, "result_index": 1, "model_usage_since_last_result": _models((1, 2, 3, 4, 0.25))}
    usage: Any = invocation_usage([SECOND, later], resumed=True, restored=None)
    assert math.isclose(usage["total_cost_usd"], 22.332955 + 0.25)
    assert usage["usage"]["output_tokens"] == 367727 + 2
    # Nothing counted is zero usage, not a missing record.
    idle: Any = invocation_usage([{**SECOND, "model_usage_since_last_result": {}}], resumed=True, restored=None)
    assert idle["total_cost_usd"] == 0.0 and idle["usage"]["output_tokens"] == 0
