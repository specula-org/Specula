"""Single-input CI reporting, with the existing one-shot-compatible issue store."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path
from typing import Any

import pytest

from specula import ci_init, ci_result, ci_verdict
from specula import persistent_findings as issues
from specula.ci_store import CIError, write_json
from specula.resource_summary import _confirmation_finding_statuses, findings_fragment_issue


def finding(fid: str = "CR-3", status: str = "REPRODUCED") -> dict[str, Any]:
    return {
        "id": fid,
        "title": "Configuration admission released before application",
        "status": status,
        "source": "code-review",
        "cause": "The admission cursor advances before membership application.",
        "trigger": "Advance the first entry, then propose another change before applying it.",
        "consequence": "A second membership entry commits before the first takes effect.",
        "evidence": ["spec/confirmation.md"],
        "severity": "High",
        "persistence": {
            "premises": ["The caller may acknowledge work before applying membership."],
            "dependencies": [{"root": "source", "path": "raft.go"}],
        },
    }


def result(work: Path, rows: list[dict[str, Any]], run: str = "v2") -> None:
    write_json(
        work / ci_result.FILENAME,
        {
            "version": 1,
            "run_id": run,
            "summary": "Fixture update checked; no real verification performed.",
            "validation_limits": ["Fixture tests only."],
            "findings": rows,
        },
    )


@pytest.fixture
def workspace(tmp_path: Path) -> tuple[Path, Path, Path]:
    source, old, work = (tmp_path / name for name in ("ci-source", "old", "work"))
    source.mkdir()
    (source / "raft.go").write_text("advance before apply\n")
    for args in (
        ["init", "-q"],
        ["add", "."],
        ["-c", "user.name=Fixture", "-c", "user.email=f@example.com", "commit", "-qm", "fixture"],
    ):
        subprocess.run(["git", "-C", str(source), *args], check=True, capture_output=True)
    for directory in (old, work):
        (directory / "spec").mkdir(parents=True)
        (directory / "spec/confirmation.md").write_text("Fixture confirmation, not a real experiment.\n")
    issues.configure(work, source, "v2", old)
    write_json(tmp_path / "ci-input.json", {ci_result.VERSION_KEY: 1, "old_model": str(old)})
    return source, old, work


def seed(source: Path, old: Path, work: Path, fid: str = "CR-3") -> None:
    item = finding(fid)
    metadata = item.pop("persistence")
    issues.record_issue(old, source, "v1", {**item, **metadata, "sites": [], "actions": [], "invariants": []})
    issues.import_history(work, old)
    issues.configure(work, source, "v2", old)


def test_rechecked_cr3_requires_only_one_result_file(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    seed(source, old, work)
    original = (old / issues._record_path("CR-3")).read_bytes()
    result(work, [finding()])
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    record = issues.load(work, "CR-3")
    assert record["origin_run"] == "v2"
    assert record["reusable"]
    assert issues.check(work, source, "CR-3") == []
    assert (old / issues._record_path("CR-3")).read_bytes() == original
    assert all((work / name).is_file() for name in ci_result.REPORTS)
    assert _confirmation_finding_statuses((work / "confirmed-bugs.md").read_text()) == {"CR-3": "REPRODUCED"}
    assert (
        findings_fragment_issue((work / ".summary-findings.md").read_text(), (work / "confirmed-bugs.md").read_text())
        is None
    )
    # Publication repeats the existing validator, without another proposal or AI write.
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    assert (work / "confirmed-bugs.md").read_text().count("## Entry 1:") == 1


@pytest.mark.parametrize(
    "metadata",
    [
        None,
        {},
        {"premises": []},
        {"dependencies": "wrong"},
        {"premises": ["Valid premise"], "dependencies": [{"root": [], "path": "raft.go"}]},
        {"premises": ["Valid premise"], "dependencies": [{"root": "source", "path": "missing.go"}]},
    ],
)
def test_missing_reuse_metadata_keeps_current_bug_and_disables_reuse(
    workspace: tuple[Path, Path, Path], metadata: Any
) -> None:
    source, old, work = workspace
    seed(source, old, work)
    row = finding()
    row["persistence"] = metadata
    result(work, [row])
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    assert not issues.load(work, "CR-3")["reusable"]
    assert issues.check(work, source, "CR-3")
    assert "Not automatically reusable" in (work / "confirmed-bugs.md").read_text()
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"


def test_model_linked_finding_needs_model_dependencies_for_reuse(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    row = finding()
    row["persistence"]["invariants"] = ["ConfigSafety"]
    result(work, [row])
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    assert not issues.load(work, "CR-3")["reusable"]


def test_reuse_keeps_original_record_and_checks_changed_dependencies(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    seed(source, old, work)
    original = issues.load(old, "CR-3")
    result(work, [{"id": "CR-3", "reuse": "Same mechanism, consequence, and caller contract."}])
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    assert issues.load(work, "CR-3") == original
    assert "historical conclusion reused" in (work / "confirmed-bugs.md").read_text()
    (source / "raft.go").write_text("apply before advance\n")
    with pytest.raises(CIError, match="reanalysis required"):
        ci_result.generate(work, source, "v2", old)


def test_fixed_record_is_removed_but_retained_in_current_report(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    seed(source, old, work, "MC-1")
    result(work, [finding("MC-1", "FIXED")])
    assert ci_result.generate(work, source, "v2", old) == "PASS"
    assert issues.index(work) == {}
    assert "FIXED" in (work / "confirmed-bugs.md").read_text()
    assert issues.index(old)
    assert ci_result.generate(work, source, "v2", old) == "PASS"


def test_mixed_fixed_and_unresolved_results_remain_parseable(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    seed(source, old, work, "MC-1")
    result(work, [finding("MC-1", "FIXED"), finding("CR-3")])
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    report = (work / "confirmed-bugs.md").read_text()
    fragment = (work / ".summary-findings.md").read_text()
    assert findings_fragment_issue(fragment, report) is None
    assert _confirmation_finding_statuses(report, impact_only=False) == {"MC-1": "FIXED", "CR-3": "REPRODUCED"}
    assert _confirmation_finding_statuses(report) == {"CR-3": "REPRODUCED"}
    assert set(issues.index(work)) == {"CR-3"}
    assert not (work / issues._record_path("MC-1")).exists()
    assert not (work / issues.DIRECTORY / "evidence/MC-1").exists()


@pytest.mark.parametrize(
    "status,verdict",
    [
        ("REPRODUCED", "FAIL"),
        ("ENV_LIMITED", "FAIL"),
        ("MASKED", "WARNING"),
        ("FALSE POSITIVE", "PASS"),
        ("DROPPED", "PASS"),
        ("FIXED", "PASS"),
        ("NEEDS MORE INFO", "PASS"),
        ("DEFERRED", "PASS"),
    ],
)
def test_status_semantics_are_unchanged(workspace: tuple[Path, Path, Path], status: str, verdict: str) -> None:
    source, old, work = workspace
    result(work, [finding(status=status)])
    assert ci_result.generate(work, source, "v2", old) == verdict
    assert bool(issues.index(work)) == (status in issues.LIVE)


def test_no_findings_generates_empty_valid_reports(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    result(work, [])
    assert ci_result.generate(work, source, "v2", old) == "PASS"
    assert (
        findings_fragment_issue((work / ".summary-findings.md").read_text(), (work / "confirmed-bugs.md").read_text())
        is None
    )


@pytest.mark.parametrize("field", ["id", "title", "status", "source", "cause", "trigger", "consequence", "evidence"])
def test_missing_core_fields_do_not_write_deliverables(workspace: tuple[Path, Path, Path], field: str) -> None:
    source, old, work = workspace
    row = finding()
    del row[field]
    result(work, [row])
    with pytest.raises(CIError):
        ci_result.generate(work, source, "v2", old)
    assert not (work / "ci-report.md").exists()
    assert issues.index(work) == {}


@pytest.mark.parametrize(
    "evidence", [[], ["missing.md"], ["../outside.md"], ["/etc/passwd"], ["ci-report.md"], [ci_result.FILENAME]]
)
def test_missing_or_unsafe_evidence_cannot_be_published(workspace: tuple[Path, Path, Path], evidence: Any) -> None:
    source, old, work = workspace
    row = finding()
    row["evidence"] = evidence
    result(work, [row])
    with pytest.raises(CIError):
        ci_result.generate(work, source, "v2", old)


def test_symlinked_or_empty_evidence_is_rejected(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    result(work, [finding()])
    path = work / "spec/confirmation.md"
    path.write_text("")
    with pytest.raises(CIError, match="evidence"):
        ci_result.generate(work, source, "v2", old)
    path.unlink()
    path.symlink_to(old / "spec/confirmation.md")
    with pytest.raises(CIError, match="evidence"):
        ci_result.generate(work, source, "v2", old)


def test_old_bug_cannot_be_omitted_or_downgraded(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    seed(source, old, work)
    for rows in ([], [finding(status="DROPPED")], [finding(status="NEEDS MORE INFO")]):
        result(work, rows)
        with pytest.raises(CIError, match="prior"):
            ci_result.generate(work, source, "v2", old)


def test_generated_ci_records_can_be_imported_and_reused_by_oneshot(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    result(work, [finding("MC-2")])
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    later = work.parent / "oneshot"
    later.mkdir()
    ci_init._copy_assets(work, later)
    issues.configure(later, source, "oneshot", work)
    issues.reuse_issue(later, source, "oneshot", "MC-2", "Same implementation and applicable premises.")
    issues.finalize_confirmation(later)
    assert issues.load(later, "MC-2") == issues.load(work, "MC-2")


def test_cli_reports_error_then_accepts_corrected_input(
    workspace: tuple[Path, Path, Path], capsys: pytest.CaptureFixture[str]
) -> None:
    _, _, work = workspace
    args = ["--work", str(work)]
    assert ci_result.main(args) == 1
    assert "resume" in capsys.readouterr().err
    result(work, [finding()])
    assert ci_result.main(args) == 0
    assert "FAIL" in capsys.readouterr().out


def test_legacy_and_initialization_are_not_opted_in(workspace: tuple[Path, Path, Path]) -> None:
    source, _, work = workspace
    assert not ci_result.enabled({})
    for marker in (None, True, 2, "1"):
        with pytest.raises(CIError, match="version"):
            ci_result.enabled({ci_result.VERSION_KEY: marker})
    write_json(source.parent / "ci-input.json", {"version": 1})
    assert ci_result.main(["--work", str(work)]) == 1


@pytest.mark.parametrize("mutation", ["stale", "version", "duplicate", "pending", "malformed"])
def test_invalid_final_documents_are_rejected(workspace: tuple[Path, Path, Path], mutation: str) -> None:
    source, old, work = workspace
    result(work, [finding()])
    path = work / ci_result.FILENAME
    document = json.loads(path.read_text())
    if mutation == "malformed":
        path.write_text("{")
    else:
        if mutation == "stale":
            document["run_id"] = "v1"
        elif mutation == "version":
            document["version"] = True
        elif mutation == "duplicate":
            document["findings"].append(finding())
        else:
            document["findings"][0]["status"] = "PENDING REPAIR"
        write_json(path, document)
    with pytest.raises((CIError, ValueError)):
        ci_result.generate(work, source, "v2", old)
    assert not (work / "ci-verdict.json").exists()


def test_regeneration_cannot_follow_an_output_symlink(workspace: tuple[Path, Path, Path]) -> None:
    source, old, work = workspace
    protected = old / "report.md"
    protected.write_text("Prior report must stay intact.\n")
    (work / "ci-report.md").symlink_to(protected)
    result(work, [])
    assert ci_result.generate(work, source, "v2", old) == "PASS"
    assert protected.read_text() == "Prior report must stay intact.\n"
    assert not (work / "ci-report.md").is_symlink()


def test_repeated_generation_recovers_after_partial_report_write(
    workspace: tuple[Path, Path, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    source, old, work = workspace
    result(work, [finding()])
    original = ci_result._reports

    def interrupted(document: dict[str, Any]) -> dict[str, str]:
        raise OSError("fixture interruption after registration")

    monkeypatch.setattr(ci_result, "_reports", interrupted)
    with pytest.raises(OSError):
        ci_result.generate(work, source, "v2", old)
    monkeypatch.setattr(ci_result, "_reports", original)
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    snapshot = work.parent / "snapshot"
    shutil.copytree(work, snapshot)
    assert ci_result.generate(work, source, "v2", old) == "FAIL"
    for path in snapshot.rglob("*"):
        if path.is_file():
            assert path.read_bytes() == (work / path.relative_to(snapshot)).read_bytes()
