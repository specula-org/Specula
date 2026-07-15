"""Normalized usage accounting and provider-specific child-session collection."""

from __future__ import annotations

import contextlib
import json
import math
import sqlite3
import stat
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

from .text import summary


@dataclass
class UsageTotals:
    session_id: str | None = None
    total_cost_usd: float | None = None
    input_tokens: int = 0
    cached_input_tokens: int = 0
    cache_write_input_tokens: int = 0
    output_tokens: int = 0
    reasoning_output_tokens: int = 0
    output_includes_reasoning: bool = False

    def add(self, other: UsageTotals) -> None:
        self.input_tokens += other.input_tokens
        self.cached_input_tokens += other.cached_input_tokens
        self.cache_write_input_tokens += other.cache_write_input_tokens
        self.output_tokens += other.output_tokens
        self.reasoning_output_tokens += other.reasoning_output_tokens
        self.output_includes_reasoning = self.output_includes_reasoning or other.output_includes_reasoning
        if other.total_cost_usd is not None:
            self.total_cost_usd = (self.total_cost_usd or 0.0) + other.total_cost_usd

    def add_cost(self, value: object) -> None:
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            try:
                cost = float(value)
            except OverflowError:
                return
            if cost >= 0 and math.isfinite(cost):
                self.total_cost_usd = (self.total_cost_usd or 0.0) + cost

    def as_payload(self, agent: str) -> dict[str, object]:
        return {
            "agent": agent,
            "session_id": self.session_id,
            "session_file": None,
            "total_cost_usd": self.total_cost_usd,
            "usage": self.as_usage(),
        }

    def as_usage(self) -> dict[str, int]:
        total = self.input_tokens + self.cached_input_tokens + self.cache_write_input_tokens + self.output_tokens
        if not self.output_includes_reasoning:
            total += self.reasoning_output_tokens
        return {
            "input_tokens": self.input_tokens,
            "cached_input_tokens": self.cached_input_tokens,
            "cache_write_input_tokens": self.cache_write_input_tokens,
            "output_tokens": self.output_tokens,
            "reasoning_output_tokens": self.reasoning_output_tokens,
            "total_tokens": total,
        }

    @classmethod
    def from_payload(cls, payload: dict[str, object]) -> UsageTotals:
        session_id = payload.get("session_id")
        totals = cls(
            session_id=session_id if isinstance(session_id, str) else None,
            output_includes_reasoning=payload.get("agent") == "opencode",
        )
        totals.add_cost(payload.get("total_cost_usd"))
        usage = payload.get("usage")
        if isinstance(usage, dict):
            totals.input_tokens = token_count(usage.get("input_tokens"))
            totals.cached_input_tokens = token_count(usage.get("cached_input_tokens"))
            totals.cache_write_input_tokens = token_count(usage.get("cache_write_input_tokens"))
            totals.output_tokens = token_count(usage.get("output_tokens"))
            totals.reasoning_output_tokens = token_count(usage.get("reasoning_output_tokens"))
        return totals


def token_count(value: object) -> int:
    if isinstance(value, bool):
        return 0
    if isinstance(value, int):
        return value if value >= 0 else 0
    if not isinstance(value, float):
        return 0
    if value < 0 or not math.isfinite(value) or not value.is_integer():
        return 0
    return int(value)


def accumulate_usage(adapter_name: str, record: object, totals: UsageTotals) -> None:
    """Accumulate one provider event into normalized counters."""
    if not isinstance(record, dict):
        return
    if adapter_name == "opencode":
        totals.output_includes_reasoning = True
        session_id = record.get("sessionID")
        if totals.session_id is None and isinstance(session_id, str):
            totals.session_id = session_id
        if record.get("type") != "step_finish":
            return
        part = record.get("part")
        if not isinstance(part, dict):
            return
        totals.add_cost(part.get("cost"))
        tokens = part.get("tokens")
        if not isinstance(tokens, dict):
            return
        cache = tokens.get("cache")
        totals.input_tokens += token_count(tokens.get("input"))
        totals.output_tokens += token_count(tokens.get("output"))
        totals.reasoning_output_tokens += token_count(tokens.get("reasoning"))
        if isinstance(cache, dict):
            totals.cached_input_tokens += token_count(cache.get("read"))
            totals.cache_write_input_tokens += token_count(cache.get("write"))
        return
    if adapter_name != "pi":
        return
    if record.get("type") == "session":
        session_id = record.get("id")
        if totals.session_id is None and isinstance(session_id, str):
            totals.session_id = session_id
        return
    if record.get("type") != "message_end":
        return
    message = record.get("message")
    if not isinstance(message, dict) or message.get("role") != "assistant":
        return
    usage = message.get("usage")
    if not isinstance(usage, dict):
        return
    totals.input_tokens += token_count(usage.get("input"))
    totals.output_tokens += token_count(usage.get("output"))
    totals.cached_input_tokens += token_count(usage.get("cacheRead"))
    totals.cache_write_input_tokens += token_count(usage.get("cacheWrite"))
    cost = usage.get("cost")
    if isinstance(cost, dict):
        totals.add_cost(cost.get("total"))


@dataclass(frozen=True)
class PiSubagentResult:
    """One Pi subagent result and either of its available usage sources."""

    totals: UsageTotals | None
    session_file: str | None
    session_id: str | None
    agent: str | None
    model: str | None


def _pi_usage_totals(value: object) -> UsageTotals | None:
    """Normalize the compact usage object emitted by pi-subagents."""
    if not isinstance(value, dict) or not any(
        key in value for key in ("input", "inputTokens", "output", "outputTokens", "cacheRead", "cacheWrite", "cost")
    ):
        return None
    totals = UsageTotals(
        input_tokens=token_count(value.get("input", value.get("inputTokens"))),
        output_tokens=token_count(value.get("output", value.get("outputTokens"))),
        cached_input_tokens=token_count(value.get("cacheRead")),
        cache_write_input_tokens=token_count(value.get("cacheWrite")),
    )
    cost = value.get("cost")
    totals.add_cost(cost.get("total") if isinstance(cost, dict) else cost)
    return totals


def _optional_string(value: object) -> str | None:
    return value if isinstance(value, str) and value else None


def _pi_results_from_details(details: object) -> list[PiSubagentResult]:
    if not isinstance(details, dict) or not isinstance(details.get("results"), list):
        return []
    found: list[PiSubagentResult] = []

    def visit(result: object) -> None:
        if not isinstance(result, dict):
            return
        found.append(
            PiSubagentResult(
                totals=_pi_usage_totals(result.get("usage")),
                session_file=_optional_string(result.get("sessionFile")) or _optional_string(result.get("sessionPath")),
                session_id=_optional_string(result.get("sessionId")),
                agent=_optional_string(result.get("agent")),
                model=_optional_string(result.get("model")),
            )
        )
        for key in ("results", "children"):
            nested = result.get(key)
            if isinstance(nested, list):
                for child in nested:
                    visit(child)
        nested_details = result.get("details")
        if isinstance(nested_details, dict) and isinstance(nested_details.get("results"), list):
            for child in nested_details["results"]:
                visit(child)

    for result in details["results"]:
        visit(result)
    return found


def pi_subagent_results(record: object) -> list[PiSubagentResult]:
    """Extract inline usage and session fallbacks from a Pi subagent result."""
    if (
        not isinstance(record, dict)
        or record.get("type") != "tool_execution_end"
        or record.get("toolName") != "subagent"
    ):
        return []
    result = record.get("result")
    details = result.get("details") if isinstance(result, dict) else None
    return _pi_results_from_details(details)


def _read_pi_session_usage(path: Path) -> tuple[UsageTotals, list[PiSubagentResult]] | None:
    try:
        metadata = path.lstat()
        if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
            return None
        stream = path.open(encoding="utf-8", errors="replace")
    except OSError as exc:
        print(f"adapter usage warning: {summary(str(exc), None)}", file=sys.stderr)
        return None

    totals = UsageTotals()
    nested_results: list[PiSubagentResult] = []
    header_seen = False
    try:
        with stream:
            for line in stream:
                try:
                    record = json.loads(line)
                except (TypeError, ValueError):
                    continue
                if not header_seen:
                    if not isinstance(record, dict) or record.get("type") != "session":
                        return None
                    header_seen = True
                    session_id = record.get("id")
                    if isinstance(session_id, str):
                        totals.session_id = session_id
                    continue
                if not isinstance(record, dict) or record.get("type") != "message":
                    continue
                message = record.get("message")
                if not isinstance(message, dict):
                    continue
                if message.get("role") == "assistant":
                    accumulate_usage("pi", {"type": "message_end", "message": message}, totals)
                elif message.get("role") == "toolResult" and message.get("toolName") == "subagent":
                    nested_results.extend(_pi_results_from_details(message.get("details")))
    except OSError as exc:
        print(f"adapter usage warning: {summary(str(exc), None)}", file=sys.stderr)
        return None
    return (totals, nested_results) if header_seen else None


def _combined_usage_payload(
    agent: str,
    parent_payload: dict[str, object],
    subagent_totals: UsageTotals,
    sessions: list[dict[str, object]],
    *,
    complete: bool,
    warning: str | None = None,
) -> dict[str, object]:
    sessions.sort(key=lambda item: str(item.get("session_id") or ""))
    parent_totals = UsageTotals.from_payload(parent_payload)
    combined_totals = UsageTotals(
        session_id=parent_totals.session_id,
        output_includes_reasoning=parent_totals.output_includes_reasoning,
    )
    combined_totals.add(parent_totals)
    combined_totals.add(subagent_totals)
    combined_payload = combined_totals.as_payload(agent)
    combined_payload.update(
        {
            "usage_scope": "combined" if complete else "partial",
            "usage_complete": complete,
            "parent": {
                "session_id": parent_totals.session_id,
                "total_cost_usd": parent_totals.total_cost_usd,
                "usage": parent_totals.as_usage(),
            },
            "subagents": {
                "complete": complete,
                "session_count": len(sessions),
                "total_cost_usd": subagent_totals.total_cost_usd,
                "usage": subagent_totals.as_usage(),
                "sessions": sessions,
            },
            "combined": {
                "complete": complete,
                "total_cost_usd": combined_totals.total_cost_usd,
                "usage": combined_totals.as_usage(),
            },
        }
    )
    if warning is not None:
        combined_payload["usage_warning"] = warning
    return combined_payload


def augment_pi_usage(
    parent_payload: dict[str, object],
    subagent_results: Iterable[PiSubagentResult],
    session_root: Path | None = None,
) -> dict[str, object]:
    """Combine inline Pi child usage with session-file fallbacks."""
    complete = session_root is not None
    warnings: list[str] = []
    pending: list[Path] = []
    result_queue = list(subagent_results)
    inline_by_path: dict[Path, PiSubagentResult] = {}
    inline_without_path: list[PiSubagentResult] = []
    sessions_by_path: dict[Path, UsageTotals] = {}
    seen: set[Path] = set()

    def resolve(candidate: str | Path) -> Path | None:
        nonlocal complete
        try:
            return Path(candidate).expanduser().resolve()
        except OSError as exc:
            complete = False
            warnings.append(summary(str(exc), None))
            return None

    if session_root is None:
        warnings.append("isolated Pi session directory unavailable")
    else:
        try:
            pending.extend(session_root.rglob("session.jsonl"))
        except OSError as exc:
            complete = False
            warnings.append(summary(str(exc), None))

    while result_queue or pending:
        while result_queue:
            child = result_queue.pop()
            resolved = resolve(child.session_file) if child.session_file is not None else None
            if resolved is not None:
                pending.append(resolved)
            if child.totals is not None:
                if resolved is None:
                    inline_without_path.append(child)
                else:
                    inline_by_path.setdefault(resolved, child)
            elif resolved is None:
                complete = False
                label = f" for {child.agent}" if child.agent is not None else ""
                warnings.append(f"Pi subagent result usage unavailable{label}")

        if not pending:
            break
        candidate = pending.pop()
        resolved = resolve(candidate)
        if resolved is None or resolved in seen:
            continue
        seen.add(resolved)
        session_result = _read_pi_session_usage(resolved)
        if session_result is None:
            complete = False
            warnings.append(f"could not read Pi session {resolved.name}")
            continue
        totals, nested_results = session_result
        sessions_by_path[resolved] = totals
        result_queue.extend(nested_results)

    sessions: list[dict[str, object]] = []
    subagent_totals = UsageTotals()
    for child in [*inline_by_path.values(), *inline_without_path]:
        assert child.totals is not None
        subagent_totals.add(child.totals)
        session_payload = child.totals.as_payload("pi")
        session_payload.pop("agent", None)
        session_payload.pop("session_file", None)
        session_payload["session_id"] = child.session_id
        session_payload["source"] = "inline"
        if child.agent is not None:
            session_payload["agent"] = child.agent
        if child.model is not None:
            session_payload["model"] = child.model
        sessions.append(session_payload)

    for path, totals in sessions_by_path.items():
        if path in inline_by_path:
            continue
        subagent_totals.add(totals)
        session_payload = totals.as_payload("pi")
        session_payload.pop("agent", None)
        session_payload.pop("session_file", None)
        sessions.append(session_payload)

    warning = "; ".join(dict.fromkeys(warnings)) or None
    return _combined_usage_payload(
        "pi",
        parent_payload,
        subagent_totals,
        sessions,
        complete=complete,
        warning=warning,
    )


def augment_opencode_usage(
    parent_payload: dict[str, object],
    database_path: Path | None,
) -> dict[str, object]:
    """Aggregate persisted descendants of the streamed OpenCode session."""
    parent_totals = UsageTotals.from_payload(parent_payload)
    subagent_totals = UsageTotals(output_includes_reasoning=True)
    sessions: list[dict[str, object]] = []
    if parent_totals.session_id is None:
        return _combined_usage_payload(
            "opencode",
            parent_payload,
            subagent_totals,
            sessions,
            complete=False,
            warning="OpenCode parent session ID unavailable",
        )
    if database_path is None or not database_path.is_file():
        return _combined_usage_payload(
            "opencode",
            parent_payload,
            subagent_totals,
            sessions,
            complete=False,
            warning="OpenCode session database unavailable",
        )

    by_session: dict[str, UsageTotals] = {}
    try:
        resolved = database_path.expanduser().resolve(strict=True)
        uri = f"{resolved.as_uri()}?mode=ro"
        with contextlib.closing(sqlite3.connect(uri, uri=True)) as database:
            if (
                database.execute(
                    "SELECT 1 FROM session WHERE id = ?",
                    (parent_totals.session_id,),
                ).fetchone()
                is None
            ):
                return _combined_usage_payload(
                    "opencode",
                    parent_payload,
                    subagent_totals,
                    sessions,
                    complete=False,
                    warning="OpenCode parent session not found in session database",
                )
            rows = database.execute(
                """
                WITH RECURSIVE descendants(id) AS (
                    SELECT id FROM session WHERE parent_id = ?
                    UNION
                    SELECT child.id
                    FROM session AS child
                    JOIN descendants AS parent ON child.parent_id = parent.id
                )
                SELECT descendants.id, part.data
                FROM descendants
                LEFT JOIN part
                  ON part.session_id = descendants.id
                 AND json_valid(part.data)
                 AND json_extract(part.data, '$.type') = 'step-finish'
                ORDER BY descendants.id, part.time_created, part.id
                """,
                (parent_totals.session_id,),
            )
            for session_id, raw_part in rows:
                if not isinstance(session_id, str):
                    continue
                totals = by_session.setdefault(
                    session_id,
                    UsageTotals(session_id=session_id, output_includes_reasoning=True),
                )
                if not isinstance(raw_part, str):
                    continue
                try:
                    part = json.loads(raw_part)
                except (TypeError, ValueError):
                    continue
                accumulate_usage(
                    "opencode",
                    {"type": "step_finish", "sessionID": session_id, "part": part},
                    totals,
                )
    except (OSError, sqlite3.Error) as exc:
        warning = f"OpenCode session database: {summary(str(exc), None)}"
        print(f"adapter usage warning: {warning}", file=sys.stderr)
        return _combined_usage_payload(
            "opencode",
            parent_payload,
            subagent_totals,
            sessions,
            complete=False,
            warning=warning,
        )

    for totals in by_session.values():
        subagent_totals.add(totals)
        session_payload = totals.as_payload("opencode")
        session_payload.pop("agent", None)
        session_payload.pop("session_file", None)
        sessions.append(session_payload)
    return _combined_usage_payload(
        "opencode",
        parent_payload,
        subagent_totals,
        sessions,
        complete=True,
    )
