"""CI gates use explicit current dispositions and retain prior finding coverage."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from specula import ci_verdict
from specula.ci_store import CIError


def write_record(work: Path, statuses: list[str], **overrides: Any) -> None:
    work.mkdir(exist_ok=True)
    (work / "evidence.md").write_text("Current fixture confirmation evidence; no real verification performed.\n")
    record = {
        "version": 1,
        "run_id": "current",
        "findings": [
            {"id": f"MC-{i}", "status": status, "evidence": "evidence.md"} for i, status in enumerate(statuses)
        ],
        **overrides,
    }
    (work / ci_verdict.FILENAME).write_text(json.dumps(record))


@pytest.mark.parametrize(
    ("statuses", "verdict", "code"),
    [
        ([], "PASS", 0),
        (["REPRODUCED"], "FAIL", 2),
        (["ENV_LIMITED"], "FAIL", 2),
        (["MASKED"], "WARNING", 0),
        (["FALSE POSITIVE", "FIXED", "DROPPED"], "PASS", 0),
        (["MASKED", "REPRODUCED"], "FAIL", 2),
        (["NEEDS MORE INFO", "DEFERRED"], "PASS", 0),
        (["NEEDS MORE INFO", "REPRODUCED"], "FAIL", 2),
        (["DEFERRED", "MASKED"], "WARNING", 0),
    ],
)
def test_verdict_is_computed_from_all_dispositions(
    tmp_path: Path, statuses: list[str], verdict: str, code: int
) -> None:
    write_record(tmp_path, statuses)
    assert ci_verdict.read(tmp_path, "current") == verdict
    assert ci_verdict.exit_code(verdict) == code


@pytest.mark.parametrize("status", ["PENDING REPAIR", "INCOMPLETE", "unknown"])
def test_unresolved_disposition_cannot_pass(tmp_path: Path, status: str) -> None:
    write_record(tmp_path, [status])
    with pytest.raises(CIError, match="did not converge|unresolved or invalid"):
        ci_verdict.read(tmp_path, "current")


@pytest.mark.parametrize(
    "overrides",
    [
        {"run_id": "old"},
        {"version": True},
        {"findings": None},
        {"findings": [None]},
        {"findings": [{"id": "MC-0", "status": "REPRODUCED"}]},
        {"findings": [{"id": "MC-0", "status": [], "evidence": "evidence.md"}]},
        {"findings": [{"id": "MC-0", "status": "MASKED", "evidence": "evidence.md"}] * 2},
    ],
)
def test_stale_or_malformed_record_cannot_pass(tmp_path: Path, overrides: dict[str, Any]) -> None:
    write_record(tmp_path, [], **overrides)
    with pytest.raises(CIError):
        ci_verdict.read(tmp_path, "current")


def test_missing_and_unsafe_evidence_cannot_pass(tmp_path: Path) -> None:
    with pytest.raises(CIError, match="missing current"):
        ci_verdict.read(tmp_path, "current")
    write_record(tmp_path, ["REPRODUCED"])
    evidence = tmp_path / "evidence.md"
    evidence.write_text("")
    with pytest.raises(CIError, match="confirmation evidence"):
        ci_verdict.read(tmp_path, "current")
    evidence.unlink()
    evidence.symlink_to(tmp_path / ci_verdict.FILENAME)
    with pytest.raises(CIError, match="confirmation evidence"):
        ci_verdict.read(tmp_path, "current")


def test_prior_bug_cannot_disappear_from_the_next_run(tmp_path: Path) -> None:
    prior, current = tmp_path / "old", tmp_path / "new"
    write_record(prior, ["REPRODUCED", "ENV_LIMITED", "MASKED"])
    write_record(current, [])
    with pytest.raises(CIError, match="prior findings need current confirmation"):
        ci_verdict.read(current, "current", previous=prior)
    write_record(current, ["FIXED", "FIXED", "MASKED"])
    assert ci_verdict.read(current, "current", previous=prior) == "WARNING"
    write_record(current, ["DROPPED", "FIXED", "MASKED"])
    with pytest.raises(CIError, match="cannot be dropped"):
        ci_verdict.read(current, "current", previous=prior)


def test_prior_information_does_not_require_further_processing(tmp_path: Path) -> None:
    prior, current = tmp_path / "old", tmp_path / "new"
    write_record(prior, ["NEEDS MORE INFO", "DEFERRED"])
    retained = (prior / ci_verdict.FILENAME).read_bytes()
    write_record(current, [])
    assert ci_verdict.read(current, "current", previous=prior) == "PASS"
    assert (prior / ci_verdict.FILENAME).read_bytes() == retained


@pytest.mark.parametrize(
    ("status", "verdict"),
    [
        ("REPRODUCED", "FAIL"),
        ("ENV_LIMITED", "FAIL"),
        ("MASKED", "WARNING"),
        ("NEEDS MORE INFO", "PASS"),
        ("DEFERRED (repair loop exhausted; RR-001 in deferred/)", "PASS"),
        ("PENDING REPAIR (RR-001)", None),
    ],
)
def test_initialization_uses_final_confirmation_dispositions(tmp_path: Path, status: str, verdict: str | None) -> None:
    (tmp_path / "confirmed-bugs.md").write_text(
        "# Confirmation Report\n\n"
        "| Entry | Finding | Status | Counts as final bug? |\n"
        "|---|---|---|---|\n"
        f"| 1 | MC-1 | {status} | no |\n\n"
    )
    if verdict is None:
        with pytest.raises(CIError, match="did not converge"):
            ci_verdict.from_confirmation(tmp_path, "init")
    else:
        assert ci_verdict.from_confirmation(tmp_path, "init") == verdict


def test_missing_or_malformed_cached_verdict_is_not_green() -> None:
    values: list[object] = [None, "", "complete", [], {}]
    for value in values:
        with pytest.raises(CIError, match="missing or invalid CI verdict"):
            ci_verdict.exit_code(value)
