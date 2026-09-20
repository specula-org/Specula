"""Issue reuse checks dependency and evidence identity, not semantic correctness."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path
from typing import Any
from unittest.mock import patch

import pytest

from specula import ci_init, ci_verdict, persistent_findings
from specula.ci_store import CIError, write_json
from specula.pipelinelib import Pipeline

ERRORS = (CIError, persistent_findings.FindingsError)


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
        "source": "model-checking",
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
    persistent_findings.record_issue(old, source, "v1", proposal())
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
    before = (old / persistent_findings._record_path("MC-1")).read_bytes()
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
    assert persistent_findings.check(work, source, "MC-1") == []
    persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Same mechanism/consequence and unchanged premises.")
    # No new finding and no current confirmation: the checked receipt carries it.
    (work / "evidence.md").unlink()
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert (work / persistent_findings._record_path("MC-1")).read_bytes() == before
    assert (old / persistent_findings._record_path("MC-1")).read_bytes() == before
    assert (work / "ci-report.md").read_text().count("historical conclusion reused") == 1
    assert "Original run: v1" in (work / persistent_findings.RECEIPTS / "MC-1.md").read_text()


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
    with pytest.raises(ERRORS, match="reanalysis required"):
        persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Prior match")
    assert not (work / persistent_findings.RECEIPTS / "MC-1.json").exists()


def test_late_edits_are_checked_again_at_finalization(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Premises still apply.")
    write(work / "spec/Invariant.tla", "ReplySafety == FALSE\n")
    with pytest.raises(ERRORS, match="reanalysis required"):
        ci_verdict.finalize(work, source, "v2", previous=old)


def test_relevant_change_does_not_invalidate_another_issue(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    second = proposal("MC-2", "MASKED")
    second["dependencies"] = [{"root": "source", "path": "caller.go"}]
    second["actions"], second["invariants"] = [], []
    persistent_findings.record_issue(old, source, "v1", second)
    work = next_work(old)
    write(work / "spec/Invariant.tla", "changed\n")
    assert persistent_findings.check(work, source, "MC-1")
    assert persistent_findings.check(work, source, "MC-2") == []


@pytest.mark.parametrize("mutation", ["missing", "modified", "symlink"])
def test_unavailable_or_changed_historical_evidence_cannot_be_reused(
    baseline: tuple[Path, Path], mutation: str
) -> None:
    source, old = baseline
    work = next_work(old)
    p = work / persistent_findings.load(work, "MC-1")["evidence"][0]["path"]
    if mutation == "modified":
        p.write_text("different evidence")
    else:
        p.unlink()
        if mutation == "symlink":
            p.symlink_to(work / "evidence.md")
    with pytest.raises(ERRORS, match="reanalysis required"):
        persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Premises unchanged.")


@pytest.mark.parametrize("kind", ["record", "receipt", "status", "note", "reason"])
def test_reuse_receipt_is_bound_to_run_record_classification_and_evidence(
    baseline: tuple[Path, Path], kind: str
) -> None:
    source, old = baseline
    work = next_work(old)
    finding = persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Premises still apply.")
    if kind == "record":
        record = persistent_findings.load(work, "MC-1")
        record["premises"] = ["Different assumptions"]
        write_json(work / persistent_findings._record_path("MC-1"), record)
    elif kind == "receipt":
        finding["reuse"]["run_id"] = "v1"
    elif kind == "status":
        finding["status"] = "FIXED"
    elif kind == "note":
        (work / finding["evidence"]).write_text("Pretend this was a new reproduction.")
    else:
        finding["reuse"]["reason"] = ""
    with pytest.raises(ERRORS):
        persistent_findings.validate_reuse(work, source, "v2", finding, old)


def test_rehashed_historical_record_cannot_override_published_evidence(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    record = persistent_findings.load(work, "MC-1")
    record["premises"] = ["Changed premise, cannot inherit the original conclusion"]
    write_json(work / persistent_findings._record_path("MC-1"), record)
    finding = persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Claim unchanged")
    with pytest.raises(ERRORS, match="differs from the prior published"):
        persistent_findings.validate_reuse(work, source, "v2", finding, old)


@pytest.mark.parametrize("status,expected", [("REPRODUCED", "FAIL"), ("ENV_LIMITED", "FAIL"), ("MASKED", "WARNING")])
def test_all_allowed_classifications_keep_their_ci_effect(
    baseline: tuple[Path, Path], status: str, expected: str
) -> None:
    source, old = baseline
    verdict(old, "v1", status)
    persistent_findings.record_issue(old, source, "v1", proposal(status=status))
    work = next_work(old)
    persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Environment/masking assumptions still hold.")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == expected
    assert persistent_findings.lookup(work, ["ReplySafety"])[0]["status"] == status


@pytest.mark.parametrize("status", ["FALSE POSITIVE", "PENDING REPAIR", "NEEDS MORE INFO", "FIXED", "DROPPED"])
def test_other_dispositions_never_enter_the_issue_registry(baseline: tuple[Path, Path], status: str) -> None:
    source, old = baseline
    with pytest.raises(ERRORS, match="only REPRODUCED"):
        persistent_findings.record_issue(old, source, "v1", proposal("MC-2", status))
    assert "MC-2" not in persistent_findings.index(old)


def test_fix_deletes_record_evidence_and_lookup_entry(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    verdict(work, "v2", "FIXED")
    write(work / "evidence.md", "Fixture targeted fix review and control for v2.\n")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "PASS"
    assert persistent_findings.lookup(work, []) == []
    assert not (work / persistent_findings._record_path("MC-1")).exists()
    assert not (work / persistent_findings.DIRECTORY / "evidence/MC-1").exists()
    assert (old / persistent_findings._record_path("MC-1")).exists()  # immutable original run


def test_later_fix_removes_an_earlier_reuse_summary_in_the_same_run(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Initially unchanged.")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    verdict(work, "v2", "FIXED")
    write(work / "evidence.md", "Current fixture source fix and control evidence.\n")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "PASS"
    assert "historical conclusion reused" not in (work / "ci-report.md").read_text()
    assert not (work / persistent_findings.RECEIPTS / "MC-1.json").exists()


def test_no_rediscovery_does_not_delete_or_clear_the_issue(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    for status in (None, "NEEDS MORE INFO", "DEFERRED"):
        verdict(work, "v2", status)
        with pytest.raises(ERRORS, match="prior"):
            ci_verdict.finalize(work, source, "v2", previous=old)
        assert persistent_findings.load(work, "MC-1")["status"] == "REPRODUCED"


def test_lookup_reads_only_index_and_limits_context(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    for i in range(2, 9):
        persistent_findings.record_issue(old, source, "v1", proposal(f"MC-{i}"))
    original = persistent_findings._bytes

    def read_index_only(work: Path, relative: str) -> bytes:
        assert relative == persistent_findings.INDEX
        return original(work, relative)

    with patch.object(persistent_findings, "_bytes", side_effect=read_index_only):
        assert len(persistent_findings.lookup(old, ["ReplySafety"])) == 5
        assert len(persistent_findings.lookup(old, [], offset=5)) == 3
        assert persistent_findings.lookup(old, ["unrelated-symbol"]) == []
    # A shared invariant retrieves candidates, never automatically reuses them.
    assert not (old / persistent_findings.RECEIPTS).exists()


def test_legacy_records_need_analysis_once_before_reuse(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    import shutil

    shutil.rmtree(old / persistent_findings.DIRECTORY)
    work = next_work(old)
    ci_verdict.seed_issues(work, source, old)
    assert persistent_findings.lookup(work, ["MC-1"])[0]["reusable"] is False
    with pytest.raises(ERRORS, match="No complete dependency record"):
        persistent_findings.reuse_issue(work, source, "v2", "MC-1", "unchanged")
    # Completing its current analysis registers a reusable record.
    write(work / "repro/check.sh", "fixture recipe\n")
    write(work / "spec/issue-input/MC-1.json", json.dumps(proposal()))
    verdict(work, "v2", "REPRODUCED")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "FAIL"
    assert persistent_findings.load(work, "MC-1")["reusable"] is True


def test_missing_or_ambiguous_dependency_boundaries_require_analysis(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    p = source / "protocol.go"
    p.write_text(p.read_text() + "// end reply\n")
    assert "ambiguous" in persistent_findings.check(work, source, "MC-1")[0]
    with pytest.raises(ERRORS, match="ambiguous"):
        persistent_findings.record_issue(
            work, source, "v2", {**proposal(), "revises": persistent_findings.record_digest(work, "MC-1")}
        )


def test_worker_proposal_uses_final_status_and_retains_only_selected_evidence(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    write(work / "repro/check.sh", "fixture recipe\n")
    updated = {**proposal(), "revises": persistent_findings.record_digest(work, "MC-1")}
    write(work / "confirmation/MC-1/issue.json", json.dumps(updated))
    write(work / "confirmation/unrelated.md", "unrelated expensive analysis\n")
    verdict(work, "v2", "MASKED")
    assert ci_verdict.finalize(work, source, "v2", previous=old) == "WARNING"
    record = persistent_findings.load(work, "MC-1")
    assert record["status"] == "MASKED"
    assert record["reusable"] is False  # earlier REPRODUCED metadata lacks the final mask premise
    assert {item["original"] for item in record["evidence"]} == {"evidence.md", "repro/check.sh"}


def test_registered_current_issue_cannot_be_silently_deleted(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    verdict(old, "v1", None)
    with pytest.raises(ERRORS, match="prior findings need current confirmation"):
        ci_verdict.finalize(old, source, "v1")
    assert persistent_findings.lookup(old, ["MC-1"])


def test_reused_local_number_cannot_replace_an_unrelated_historical_issue(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    write(work / "repro/check.sh", "fixture recipe\n")
    new = proposal()
    new["cause"] = "Different defect, accidentally assigned the same local MC number"
    with pytest.raises(ERRORS, match="ID already belongs"):
        persistent_findings.record_issue(work, source, "v2", new)
    assert persistent_findings.load(work, "MC-1") == persistent_findings.load(old, "MC-1")
    new["id"] = "MC-2"
    persistent_findings.record_issue(work, source, "v2", new)
    assert set(persistent_findings.index(work)) == {"MC-1", "MC-2"}


@pytest.mark.parametrize("prefix", ["", "./"])
def test_historical_evidence_cannot_be_passed_off_as_a_fresh_fix(baseline: tuple[Path, Path], prefix: str) -> None:
    source, old = baseline
    work = next_work(old)
    record = json.loads((work / ci_verdict.FILENAME).read_text())
    record["findings"] = [
        {
            "id": "MC-1",
            "status": "FIXED",
            "evidence": prefix + persistent_findings.load(work, "MC-1")["evidence"][0]["path"],
        }
    ]
    write_json(work / ci_verdict.FILENAME, record)
    with pytest.raises(ERRORS, match="historical evidence requires"):
        ci_verdict.finalize(work, source, "v2", previous=old)


def test_recorded_dependencies_are_not_rehashed_by_a_stale_proposal(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    write(old / "spec/issue-input/MC-1.json", json.dumps(proposal()))
    write(old / "spec/Invariant.tla", "changed after recording\n")
    with pytest.raises(ERRORS, match="recorded conclusion changed"):
        ci_verdict.finalize(old, source, "v1")


def test_reconfirmation_updates_the_current_record_from_its_worker_proposal(baseline: tuple[Path, Path]) -> None:
    source, work = baseline
    before = persistent_findings.record_digest(work, "MC-1")
    write(work / "spec/Invariant.tla", "repaired model property\n")
    write(work / "evidence.md", "Fresh confirmation after model repair.\n")
    fresh = {**proposal(), "cause": "Freshly reconfirmed cause."}
    write(work / "confirmation/MC-1/issue.json", json.dumps(fresh))
    # A leftover proposal must not shadow the completed worker's result.
    write(work / "spec/issue-input/MC-1.json", json.dumps(proposal()))
    findings = [{"id": "MC-1", "status": "REPRODUCED", "source": "model-checking", "evidence": "evidence.md"}]
    assert persistent_findings.check(work, source, "MC-1")
    with pytest.raises(ERRORS, match="recorded conclusion changed"):
        persistent_findings.reconcile(work, source, "v1", findings, confirmed_ids=["MC-2"])
    assert persistent_findings.record_digest(work, "MC-1") == before
    persistent_findings.reconcile(work, source, "v1", findings, confirmed_ids=["MC-1"])
    assert not persistent_findings.check(work, source, "MC-1")
    assert persistent_findings.load(work, "MC-1")["cause"] == fresh["cause"]
    assert persistent_findings.record_digest(work, "MC-1") != before
    accepted = persistent_findings.record_digest(work, "MC-1")
    persistent_findings.reconcile(work, source, "v1", findings, confirmed_ids=["MC-1"])
    assert persistent_findings.record_digest(work, "MC-1") == accepted


@pytest.mark.parametrize("worker_proposal", [None, {"id": "wrong"}])
def test_reconfirmation_without_a_valid_proposal_keeps_the_previous_record(
    baseline: tuple[Path, Path], worker_proposal: dict[str, Any] | None
) -> None:
    source, work = baseline
    before = persistent_findings.record_digest(work, "MC-1")
    write(work / "spec/Invariant.tla", "repaired model property\n")
    if worker_proposal is not None:
        write(work / "confirmation/MC-1/issue.json", json.dumps(worker_proposal))
    with pytest.raises(ERRORS, match="recorded conclusion changed|invalid issue proposal"):
        persistent_findings.reconcile(
            work,
            source,
            "v1",
            [{"id": "MC-1", "status": "REPRODUCED", "evidence": "evidence.md"}],
            confirmed_ids=["MC-1"],
        )
    assert persistent_findings.record_digest(work, "MC-1") == before


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


def test_standalone_cli_initializes_records_and_reuses_without_ci_or_git(tmp_path: Path) -> None:
    source, first, second = tmp_path / "source", tmp_path / "first", tmp_path / "second"
    write(source / "logic.txt", "unchanged logic\n")
    write(first / "evidence.md", "Standalone fixture evidence only.\n")
    entry = proposal("CR-1", "ENV_LIMITED")
    entry.update(
        actions=[], invariants=[], dependencies=[{"root": "source", "path": "logic.txt"}], evidence=["evidence.md"]
    )
    data = tmp_path / "finding.json"
    data.write_text(json.dumps(entry))
    run = persistent_findings.main
    assert run(["--work", str(first), "--source", str(source), "--run-id", "one", "init"]) == 0
    assert run(["--work", str(first), "record", "--input", str(data)]) == 0
    assert "unversioned" in persistent_findings.load(first, "CR-1")["source_revision"]
    assert (
        run(["--work", str(second), "--source", str(source), "--run-id", "two", "--previous", str(first), "init"]) == 0
    )
    assert run(["--work", str(second), "reuse", "--id", "CR-1", "--reason", "Same fixture premises."]) == 0
    receipt = persistent_findings.receipts(second)[0]
    persistent_findings.validate_reuse(second, source, "two", receipt, first)
    assert persistent_findings.load(second, "CR-1")["origin_run"] == "one"
    assert not list(tmp_path.rglob("ci-input.json"))
    assert not list(tmp_path.rglob("ci-verdict.json"))
    write(source / "logic.txt", "changed logic\n")
    assert run(["--work", str(second), "reuse", "--id", "CR-1", "--reason", "Must reanalyze."]) == 1


def test_one_shot_missing_rediscovery_does_not_delete_records(baseline: tuple[Path, Path]) -> None:
    source, old = baseline
    work = next_work(old)
    persistent_findings.configure(work, source, "v2", old)
    write(work / "confirmed-bugs.md", "| Entry | Finding | Status | Counts as final bug? |\n|---|---|---|---|\n\n")
    persistent_findings.finalize_confirmation(work)
    assert persistent_findings.load(work, "MC-1") == persistent_findings.load(old, "MC-1")


def test_same_workspace_history_is_bound_at_run_start(baseline: tuple[Path, Path]) -> None:
    source, work = baseline
    persistent_findings.configure(work, source, "v2")
    receipt = persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Same fixture premises.")
    persistent_findings.validate_reuse(work, source, "v2", receipt, None)
    with pytest.raises(ERRORS, match="inputs changed"):
        persistent_findings.configure(work, source, "v2", work.parent)


def test_standalone_discovery_is_empty_without_history(tmp_path: Path) -> None:
    assert persistent_findings.lookup(tmp_path, ["ReplySafety"]) == []


def test_initialize_new_nested_output_directory(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    work = tmp_path / "new" / "output"
    persistent_findings.configure(work, source, "new-run")
    assert persistent_findings.context(work) == (source, "new-run", None)


def test_supplied_history_can_be_searched_before_checkout(baseline: tuple[Path, Path]) -> None:
    source, previous = baseline
    work = previous.parent / "new" / "output"
    persistent_findings.import_history(work, previous)
    assert persistent_findings.lookup(work, ["ReplySafety"])[0]["id"] == "MC-1"
    assert not (work / persistent_findings.CONTEXT).exists()
    persistent_findings.configure(work, source, "next", previous)
    assert persistent_findings.context(work) == (source, "next", previous)


def test_reused_code_review_is_not_relabelled_as_model_checking(baseline: tuple[Path, Path]) -> None:
    source, work = baseline
    entry = {**proposal("CR-2"), "source": "code-review"}
    persistent_findings.record_issue(work, source, "v1", entry)
    body = persistent_findings.reused_body(work, "CR-2")
    assert "- **Source**: Code Review" in body
    assert "- **Source**: MC" not in body


def test_ci_initialization_keeps_one_shot_reuse_receipts(baseline: tuple[Path, Path]) -> None:
    source, previous = baseline
    work = next_work(previous)
    persistent_findings.configure(work, source, "v2", previous)
    persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Same fixture defect and premises.")
    write(
        work / "confirmed-bugs.md",
        (
            "| Entry | Finding | Status | Counts as final bug? |\n|---|---|---|---|\n"
            "| 1 | MC-1 | REPRODUCED | yes |\n\nHistorical fixture conclusion reused.\n"
        ),
    )
    assert ci_verdict.from_confirmation(work, "v2") == "FAIL"
    record = json.loads((work / ci_verdict.FILENAME).read_text())
    assert record["findings"][0]["reuse"]["run_id"] == "v2"
    assert ci_verdict.finalize(work, source, "v2") == "FAIL"
    assert persistent_findings.load(work, "MC-1")["origin_run"] == "v1"


def test_cli_does_not_silently_ignore_source_overrides(baseline: tuple[Path, Path]) -> None:
    source, work = baseline
    persistent_findings.configure(work, source, "v2")
    assert (
        persistent_findings.main(
            ["--work", str(work), "--source", str(source), "reuse", "--id", "MC-1", "--reason", "Unchanged."]
        )
        == 1
    )
    assert not persistent_findings.receipts(work)


def test_fresh_context_rebinds_changed_source_and_retains_findings(baseline: tuple[Path, Path]) -> None:
    source_a, previous = baseline
    work = next_work(previous)
    pipeline = Pipeline()
    pipeline.targets, pipeline.artifact, pipeline.run_id = ["T"], str(source_a), "v2"
    with patch.object(pipeline, "get_work_dir", return_value=str(work)):
        pipeline.prepare_persistent_findings(["T"])
        receipt = persistent_findings.reuse_issue(work, source_a, "v2", "MC-1", "A still matches.")
        context_before = (work / persistent_findings.CONTEXT).read_bytes()
        pipeline.prepare_persistent_findings(["T"])
        assert (work / persistent_findings.CONTEXT).read_bytes() == context_before
        assert persistent_findings.receipts(work) == [receipt]
        resumed = Pipeline()
        resumed.targets, resumed.artifact, resumed.run_id = ["T"], str(source_a), "v2"
        with patch.object(resumed, "get_work_dir", return_value=str(work)):
            resumed.prepare_persistent_findings(["T"])
        assert persistent_findings.receipts(work) == [receipt]

        source_b = source_a.parent / "source-b"
        shutil.copytree(source_a, source_b)
        write(source_b / "caller.go", "changed dependency in B\n")
        with pytest.raises(ERRORS, match="inputs changed"):
            persistent_findings.configure(work, source_b, "v2")
        stored = (work / persistent_findings._record_path("MC-1")).read_bytes()
        pipeline.artifact, pipeline.fresh_context = str(source_b), True
        pipeline.prepare_persistent_findings(["T"])
        assert persistent_findings.context(work)[0] == source_b
        assert persistent_findings.receipts(work) == []
        assert not (work / receipt["evidence"]).exists()
        assert (work / persistent_findings._record_path("MC-1")).read_bytes() == stored
        assert persistent_findings.check(work, persistent_findings.context(work)[0], "MC-1")
        with pytest.raises(ERRORS, match="reanalysis required"):
            persistent_findings.reuse_issue(work, persistent_findings.context(work)[0], "v2", "MC-1", "B differs.")
        # The second preparation of this fresh invocation must not clear new work.
        marker = work / persistent_findings.RECEIPTS / "new-stage.md"
        write(marker, "new stage's work\n")
        pipeline.prepare_persistent_findings(["T"])
        assert marker.exists()


def test_fresh_source_reanalysis_can_replace_the_same_run_record(baseline: tuple[Path, Path]) -> None:
    source_a, work = baseline
    persistent_findings.configure(work, source_a, "v1")
    source_b = source_a.parent / "source-b"
    shutil.copytree(source_a, source_b)
    write(source_b / "caller.go", "changed dependency in B\n")
    persistent_findings.configure(work, source_b, "v1", fresh_context=True)
    write(work / "evidence.md", "Fresh fixture confirmation on B.\n")
    write(work / "spec/issue-input/MC-1.json", json.dumps(proposal()))
    persistent_findings.reconcile(
        work, source_b, "v1", [{"id": "MC-1", "status": "REPRODUCED", "evidence": "evidence.md"}]
    )
    assert not persistent_findings.check(work, source_b, "MC-1")


def test_no_isolate_keeps_one_findings_id_and_reports_phase1_reuse(baseline: tuple[Path, Path]) -> None:
    from specula import confirmlib
    from specula.phaselib import Workspace

    source, previous = baseline
    work = next_work(previous)
    pipeline = Pipeline()
    pipeline.targets, pipeline.artifact, pipeline.isolate = ["T"], str(source), False
    with patch("specula.pipelinelib.generate_run_id", side_effect=["invocation-one", "invocation-two"]):
        with patch.object(pipeline, "get_work_dir", return_value=str(work)):
            pipeline.prepare_persistent_findings(["T"])
            first_id = persistent_findings.context(work)[1]
            receipt = persistent_findings.reuse_issue(work, source, first_id, "MC-1", "Phase 1 matched history.")
            pipeline.prepare_persistent_findings(["T"])
        assert persistent_findings.context(work)[1] == first_id
        assert persistent_findings.receipts(work) == [receipt]
        assert pipeline.run_id == "" and pipeline.run_dir is None

        # No later rediscovery: the real confirmation driver must still report it.
        write(work / "spec/candidates.json", '{"findings": []}\n')
        ws = Workspace(["T"], artifact=str(source))
        cfg = confirmlib.ConfirmConfig("T", ws, Path("/unused-adapter"), repo_dir=str(source), worktree=False)
        with (
            patch.object(ws, "work_dir", return_value=work),
            patch.object(
                confirmlib, "run_agent_blocking", side_effect=AssertionError("must reuse without confirmation")
            ),
        ):
            assert confirmlib.run_parallel_confirmation(cfg) == 0
        assert "historical conclusion reused" in (work / "confirmed-bugs.md").read_text()
        assert "MC-1" in (work / "confirmed-bugs.md").read_text()

        next_pipeline = Pipeline()
        next_pipeline.targets, next_pipeline.artifact, next_pipeline.isolate = ["T"], str(source), False
        with patch.object(next_pipeline, "get_work_dir", return_value=str(work)):
            next_pipeline.prepare_persistent_findings(["T"])
        assert persistent_findings.context(work)[1] != first_id
        assert not persistent_findings.receipts(work)


@pytest.mark.parametrize("listed", [False, True])
def test_ci_merges_receipt_into_listed_or_unlisted_finding(baseline: tuple[Path, Path], listed: bool) -> None:
    source, previous = baseline
    work = next_work(previous)
    receipt = persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Unchanged fixture.")
    if listed:
        record = json.loads((work / ci_verdict.FILENAME).read_text())
        record["findings"] = [{key: receipt[key] for key in ("id", "status", "evidence")}]
        write_json(work / ci_verdict.FILENAME, record)
    assert ci_verdict.finalize(work, source, "v2", previous=previous) == "FAIL"
    assert ci_verdict.exit_code(ci_verdict.read(work, "v2", source=source, previous=previous)) == 2
    assert json.loads((work / ci_verdict.FILENAME).read_text())["findings"] == [receipt]


def test_listed_reuse_still_rejects_invalid_receipt(baseline: tuple[Path, Path]) -> None:
    source, previous = baseline
    work = next_work(previous)
    receipt = persistent_findings.reuse_issue(work, source, "v2", "MC-1", "Unchanged fixture.")
    record = json.loads((work / ci_verdict.FILENAME).read_text())
    record["findings"] = [{key: receipt[key] for key in ("id", "status", "evidence")}]
    write_json(work / ci_verdict.FILENAME, record)
    receipt["reuse"]["run_id"] = "stale-run"
    write_json(work / persistent_findings.RECEIPTS / "MC-1.json", receipt)
    with pytest.raises(ERRORS, match="reuse receipt does not match"):
        ci_verdict.finalize(work, source, "v2", previous=previous)
