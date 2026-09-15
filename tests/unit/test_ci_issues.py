"""Issue reuse checks dependency and evidence identity, not semantic correctness."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any
from unittest.mock import patch

import pytest

from specula import ci_init, ci_issues, ci_verdict
from specula.ci_store import CIError, write_json


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def verdict(work: Path, run: str, status: str | None) -> None:
    write_json(
        work / ci_verdict.FILENAME,
        {
            "version": 1,
            "run_id": run,
            "findings": [{"id": "MC-1", "status": status, "evidence": "evidence.md"}] if status else [],
        },
    )


def proposal(fid: str = "MC-1", status: str = "REPRODUCED") -> dict[str, Any]:
    return {
        "id": fid,
        "title": "Reply accepted before term validation",
        "status": status,
        "cause": "Reply updates state before validating term.",
        "trigger": "Old reply arrives late.",
        "consequence": "Consumer reads old data.",
        "sites": ["protocol.go:reply"],
        "actions": ["ReceiveReply"],
        "invariants": ["ReplySafety"],
        "premises": ["Delayed replies can reach the consumer; fixture evidence only."],
        "dependencies": [
            {"root": "source", "path": "protocol.go", "start": "func reply() {", "end": "// end reply"},
            {"root": "source", "path": "caller.go"},
            {"root": "work", "path": "spec/base.tla", "start": "ReceiveReply ==", "end": "\\* end reply"},
            {"root": "work", "path": "spec/MC.cfg"},
            {"root": "work", "path": "spec/Invariant.tla"},
        ],
        "evidence": ["evidence.md", "repro/check.sh"],
    }


@pytest.fixture
def baseline(tmp_path: Path) -> tuple[Path, Path]:
    source, old = tmp_path / "source", tmp_path / "old"
    write(source / "protocol.go", "func reply() {\n  accept()\n}\n// end reply\nfunc logging() {}\n")
    write(source / "caller.go", "reply()\n")
    for args in (
        ["init", "-q"],
        ["add", "."],
        ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.com", "commit", "-qm", "fixture"],
    ):
        subprocess.run(["git", "-C", str(source), *args], check=True, capture_output=True)
    write(old / "spec/base.tla", "ReceiveReply ==\n  accept\n\\* end reply\nUnrelated == TRUE\n")
    write(old / "spec/MC.cfg", "INVARIANT ReplySafety\n")
    write(old / "spec/Invariant.tla", "ReplySafety == TRUE\n")
    write(old / "evidence.md", "Fixture confirmation only, no real verification performed.\n")
    write(old / "repro/check.sh", "#!/bin/sh\n# Fixture only\nexit 0\n")
    write(old / "ci-report.md", "# Fixture CI report\n")
    verdict(old, "v1", "REPRODUCED")
    ci_issues.record_issue(old, source, "v1", proposal())
    assert ci_verdict.finalize(old, source, "v1") == "FAIL"
    return source, old


def next_work(old: Path, run: str = "v2") -> Path:
    work = old.parent / run
    work.mkdir()
    ci_init._copy_assets(old, work)
    verdict(work, run, None)
    return work


def test_unrelated_source_and_model_edits_reuse_without_reconfirmation(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    before = (old / ci_issues._record_path("MC-1")).read_bytes()
    write(source / "unrelated.txt", "new unrelated file\n")
    p = source / "protocol.go"
    p.write_text("// shifted lines\n" + p.read_text().replace("logging() {}", "logging() { log() }"))
    p = work / "spec/base.tla"
    p.write_text(p.read_text().replace("Unrelated == TRUE", "Unrelated == FALSE"))
    subprocess.run(["git", "-C", str(source), "add", "."], check=True)
    subprocess.run(
        [
            "git",
            "-C",
            str(source),
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.com",
            "commit",
            "-qm",
            "unrelated",
        ],
        check=True,
    )
    assert ci_issues.check(work, source, "MC-1") == []
    ci_issues.reuse_issue(work, source, "v2", "MC-1", "Same mechanism/consequence and unchanged premises.")
    # No new finding and no current confirmation: the checked receipt carries it.
    (work / "evidence.md").unlink()
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert (work / ci_issues._record_path("MC-1")).read_bytes() == before
    assert (old / ci_issues._record_path("MC-1")).read_bytes() == before
    assert (work / "ci-report.md").read_text().count("historical conclusion reused") == 1
    assert "Original run: v1" in (work / ci_issues.RECEIPTS / "MC-1.md").read_text()


@pytest.mark.parametrize(
    ("root", "path", "old_text", "new_text"),
    [
        ("source", "protocol.go", "accept()", "validate(); accept()"),
        ("source", "caller.go", "reply()", "filter(); reply()"),
        ("work", "spec/base.tla", "  accept", "  validate /\\ accept"),
        ("work", "spec/MC.cfg", "ReplySafety", "OtherSafety"),
        ("work", "spec/Invariant.tla", "TRUE", "FALSE"),
    ],
)
def test_relevant_changes_invalidate_only_the_affected_issue(
    baseline: tuple[Path, Path], root: str, path: str, old_text: str, new_text: str
) -> None:
    source, old = baseline
    work = next_work(old)
    p = (source if root == "source" else work) / path
    p.write_text(p.read_text().replace(old_text, new_text))
    with pytest.raises(CIError, match="reanalysis required"):
        ci_issues.reuse_issue(work, source, "v2", "MC-1", "Prior match")
    assert not (work / ci_issues.RECEIPTS / "MC-1.json").exists()


def test_late_edits_are_checked_again_at_finalization(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    ci_issues.reuse_issue(work, source, "v2", "MC-1", "Premises still apply.")
    write(work / "spec/Invariant.tla", "ReplySafety == FALSE\n")
    with pytest.raises(CIError, match="reanalysis required"):
        ci_verdict.finalize(work, source, "v2", previous=old)


def test_relevant_change_does_not_invalidate_another_issue(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    second = proposal("MC-2", "MASKED")
    second["dependencies"] = [{"root": "source", "path": "caller.go"}]
    second["actions"], second["invariants"] = [], []
    ci_issues.record_issue(old, source, "v1", second)
    work = next_work(old)
    write(work / "spec/Invariant.tla", "changed\n")
    assert ci_issues.check(work, source, "MC-1")
    assert ci_issues.check(work, source, "MC-2") == []


@pytest.mark.parametrize("mutation", ["missing", "modified", "symlink"])
def test_unavailable_or_changed_historical_evidence_cannot_be_reused(
    baseline: tuple[Path, Path], mutation: str
) -> None:
    source, old = baseline
    work = next_work(old)
    p = work / ci_issues.load(work, "MC-1")["evidence"][0]["path"]
    if mutation == "modified":
        p.write_text("different evidence")
    else:
        p.unlink()
        if mutation == "symlink":
            p.symlink_to(work / "evidence.md")
    with pytest.raises(CIError, match="reanalysis required"):
        ci_issues.reuse_issue(work, source, "v2", "MC-1", "Premises unchanged.")


@pytest.mark.parametrize("kind", ["record", "receipt", "status", "note", "reason"])
def test_reuse_receipt_is_bound_to_run_record_classification_and_evidence(
    baseline: tuple[Path, Path], kind: str
) -> None:
    source, old = baseline
    work = next_work(old)
    finding = ci_issues.reuse_issue(work, source, "v2", "MC-1", "Premises still apply.")
    if kind == "record":
        record = ci_issues.load(work, "MC-1")
        record["premises"] = ["Different assumptions"]
        write_json(work / ci_issues._record_path("MC-1"), record)
    elif kind == "receipt":
        finding["reuse"]["run_id"] = "v1"
    elif kind == "status":
        finding["status"] = "FIXED"
    elif kind == "note":
        (work / finding["evidence"]).write_text("Pretend this was a new reproduction.")
    else:
        finding["reuse"]["reason"] = ""
    with pytest.raises(CIError):
        ci_issues.validate_reuse(work, source, "v2", finding, old)


def test_rehashed_historical_record_cannot_override_published_evidence(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    record = ci_issues.load(work, "MC-1")
    record["premises"] = ["Changed premise, cannot inherit the original conclusion"]
    write_json(work / ci_issues._record_path("MC-1"), record)
    finding = ci_issues.reuse_issue(work, source, "v2", "MC-1", "Claim unchanged")
    with pytest.raises(CIError, match="differs from the prior published"):
        ci_issues.validate_reuse(work, source, "v2", finding, old)


@pytest.mark.parametrize("status,expected", [("REPRODUCED", "FAIL"), ("ENV_LIMITED", "FAIL"), ("MASKED", "WARNING")])
def test_all_allowed_classifications_keep_their_ci_effect(
    baseline: tuple[Path, Path], status: str, expected: str
) -> None:
    source, old = baseline
    verdict(old, "v1", status)
    ci_issues.record_issue(old, source, "v1", proposal(status=status))
    work = next_work(old)
    ci_issues.reuse_issue(work, source, "v2", "MC-1", "Environment/masking assumptions still hold.")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == expected
    assert ci_issues.lookup(work, ["ReplySafety"])[0]["status"] == status


@pytest.mark.parametrize("status", ["FALSE POSITIVE", "PENDING REPAIR", "NEEDS MORE INFO", "FIXED", "DROPPED"])
def test_other_dispositions_never_enter_the_issue_registry(baseline: tuple[Path, Path], status: str) -> None:
    source, old = baseline
    with pytest.raises(CIError, match="only REPRODUCED"):
        ci_issues.record_issue(old, source, "v1", proposal("MC-2", status))
    assert "MC-2" not in ci_issues.index(old)


def test_fix_deletes_record_evidence_and_lookup_entry(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    verdict(work, "v2", "FIXED")
    write(work / "evidence.md", "Fixture targeted fix review and control for v2.\n")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "PASS"
    assert ci_issues.lookup(work, []) == []
    assert not (work / ci_issues._record_path("MC-1")).exists()
    assert not (work / ci_issues.DIRECTORY / "evidence/MC-1").exists()
    assert (old / ci_issues._record_path("MC-1")).exists()  # immutable original run


def test_later_fix_removes_an_earlier_reuse_summary_in_the_same_run(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    ci_issues.reuse_issue(work, source, "v2", "MC-1", "Initially unchanged.")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    verdict(work, "v2", "FIXED")
    write(work / "evidence.md", "Current fixture source fix and control evidence.\n")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "PASS"
    assert "historical conclusion reused" not in (work / "ci-report.md").read_text()
    assert not (work / ci_issues.RECEIPTS / "MC-1.json").exists()


def test_no_rediscovery_does_not_delete_or_clear_the_issue(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    for status in (None, "NEEDS MORE INFO", "DEFERRED"):
        verdict(work, "v2", status)
        with pytest.raises(CIError, match="prior"):
            ci_verdict.finalize(work, source, "v2", previous=old)
        assert ci_issues.load(work, "MC-1")["status"] == "REPRODUCED"


def test_lookup_reads_only_index_and_limits_context(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    for i in range(2, 9):
        ci_issues.record_issue(old, source, "v1", proposal(f"MC-{i}"))
    original = ci_issues._bytes

    def read_index_only(work: Path, relative: str) -> bytes:
        assert relative == ci_issues.INDEX
        return original(work, relative)

    with patch.object(ci_issues, "_bytes", side_effect=read_index_only):
        assert len(ci_issues.lookup(old, ["ReplySafety"])) == 5
        assert len(ci_issues.lookup(old, [], offset=5)) == 3
        assert ci_issues.lookup(old, ["unrelated-symbol"]) == []
    # A shared invariant retrieves candidates, never automatically reuses them.
    assert not (old / ci_issues.RECEIPTS).exists()


def test_legacy_records_need_analysis_once_before_reuse(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    import shutil

    shutil.rmtree(old / ci_issues.DIRECTORY)
    work = next_work(old)
    ci_verdict.seed_issues(work, source, old)
    assert ci_issues.lookup(work, ["MC-1"])[0]["reusable"] is False
    with pytest.raises(CIError, match="No complete dependency record"):
        ci_issues.reuse_issue(work, source, "v2", "MC-1", "unchanged")
    # Completing its current analysis registers a reusable record.
    write(work / "repro/check.sh", "fixture recipe\n")
    write(work / "spec/issue-input/MC-1.json", json.dumps(proposal()))
    verdict(work, "v2", "REPRODUCED")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert ci_issues.load(work, "MC-1")["reusable"] is True


def test_missing_or_ambiguous_dependency_boundaries_require_analysis(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    p = source / "protocol.go"
    p.write_text(p.read_text() + "// end reply\n")
    assert "ambiguous" in ci_issues.check(work, source, "MC-1")[0]
    with pytest.raises(CIError, match="ambiguous"):
        ci_issues.record_issue(work, source, "v2", {**proposal(), "revises": ci_issues.record_digest(work, "MC-1")})


def test_worker_proposal_uses_final_status_and_retains_only_selected_evidence(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    write(work / "repro/check.sh", "fixture recipe\n")
    updated = {**proposal(), "revises": ci_issues.record_digest(work, "MC-1")}
    write(work / "confirmation/MC-1/issue.json", json.dumps(updated))
    write(work / "confirmation/unrelated.md", "unrelated expensive analysis\n")
    verdict(work, "v2", "MASKED")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "WARNING"
    record = ci_issues.load(work, "MC-1")
    assert record["status"] == "MASKED"
    assert record["reusable"] is False  # earlier REPRODUCED metadata lacks the final mask premise
    assert {item["original"] for item in record["evidence"]} == {"evidence.md", "repro/check.sh"}


def test_registered_current_issue_cannot_be_silently_deleted(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    verdict(old, "v1", None)
    with pytest.raises(CIError, match="prior findings need current confirmation"):
        ci_verdict.finalize(old, source, "v1")
    assert ci_issues.lookup(old, ["MC-1"])


def test_reused_local_number_cannot_replace_an_unrelated_historical_issue(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    write(work / "repro/check.sh", "fixture recipe\n")
    new = proposal()
    new["cause"] = "Different defect, accidentally assigned the same local MC number"
    with pytest.raises(CIError, match="ID already belongs"):
        ci_issues.record_issue(work, source, "v2", new)
    assert ci_issues.load(work, "MC-1") == ci_issues.load(old, "MC-1")
    new["id"] = "MC-2"
    ci_issues.record_issue(work, source, "v2", new)
    assert set(ci_issues.index(work)) == {"MC-1", "MC-2"}


def test_historical_evidence_cannot_be_passed_off_as_a_fresh_fix(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    record = json.loads((work / ci_verdict.FILENAME).read_text())
    record["findings"] = [
        {"id": "MC-1", "status": "FIXED", "evidence": ci_issues.load(work, "MC-1")["evidence"][0]["path"]}
    ]
    write_json(work / ci_verdict.FILENAME, record)
    with pytest.raises(CIError, match="historical evidence requires"):
        ci_verdict.finalize(work, source, "v2", previous=old)


def test_recorded_dependencies_are_not_rehashed_by_a_stale_proposal(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    write(old / "spec/issue-input/MC-1.json", json.dumps(proposal()))
    write(old / "spec/Invariant.tla", "changed after recording\n")
    with pytest.raises(CIError, match="recorded conclusion changed"):
        ci_verdict.finalize(old, source, "v1")


def test_initialization_bundles_one_findings_confirmation(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    write(
        old / "confirmed-bugs.md",
        (
            "| Entry | Finding | Status | Counts as final bug? |\n|---|---|---|---|\n"
            "| 1 | MC-1 | REPRODUCED | yes |\n\nUnrelated findings and long analysis here.\n"
        ),
    )
    write(
        old / "confirmation/MC-1/verdict.json",
        json.dumps({"status": "REPRODUCED", "body": "Only MC-1's completed confirmation evidence."}),
    )
    assert ci_verdict.from_confirmation(old, "v1") == "FAIL"
    findings = json.loads((old / ci_verdict.FILENAME).read_text())["findings"]
    assert "Unrelated findings" not in (old / findings[0]["evidence"]).read_text()
