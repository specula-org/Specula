"""Contract tests for durable unfinished-conversation ownership."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

import pytest

from specula import resumelib


@dataclass(frozen=True)
class TurnFiles:
    cwd: Path
    resume_state: Path
    prompt_file: Path
    log_file: Path


def _enable_resume(
    run_dir: Path,
    monkeypatch: pytest.MonkeyPatch,
    *,
    invocation: str = "invocation-1",
) -> None:
    resumelib.initialize_run(run_dir)
    resumelib.save_configuration(run_dir, {"agent": "codex"})
    monkeypatch.setenv("SPECULA_RUN_DIR", str(run_dir))
    monkeypatch.setenv(resumelib.INVOCATION_ENV, invocation)
    monkeypatch.delenv(resumelib.MANUAL_ENV, raising=False)
    monkeypatch.delenv(resumelib.FRESH_ENV, raising=False)


def _turn_files(run_dir: Path) -> TurnFiles:
    work_dir = run_dir / "target" / ".specula-output"
    work_dir.mkdir(parents=True)
    return TurnFiles(
        cwd=run_dir / "source",
        resume_state=work_dir / "phase.resume.json",
        prompt_file=work_dir / "phase.prompt.md",
        log_file=work_dir / "phase.log",
    )


def _prepare(
    files: TurnFiles,
    *,
    logical: tuple[str, ...] = ("phase", "validation", "target"),
    phase: str = "validation",
    model: str | None = "model-a",
) -> resumelib.ResumeClaim:
    return resumelib.prepare_turn(
        logical,
        phase=phase,
        target="target",
        kind="phase",
        adapter=Path("/adapters/codex.py"),
        model=model,
        effort="high",
        claude_alias="claude",
        cwd=files.cwd,
        resume_state=files.resume_state,
        prompt_file=files.prompt_file,
        log_file=files.log_file,
    )


def _start_manual_resume(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(resumelib.INVOCATION_ENV, "invocation-2")
    monkeypatch.setenv(resumelib.MANUAL_ENV, "1")


def test_fresh_turn_registration(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)

    claim = _prepare(files)

    assert claim == resumelib.ResumeClaim(attempt=1, manual=False, resumable=False)
    entries = resumelib.active_entries()
    assert len(entries) == 1
    assert entries[0]["logical"] == ["phase", "validation", "target"]
    assert entries[0]["owner"] == "invocation-1"


def test_same_invocation_automatically_claims_native_session(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files)
    files.resume_state.write_text('{"session_id": "session-1"}\n')

    claim = _prepare(files)

    assert claim == resumelib.ResumeClaim(attempt=2, manual=False, resumable=True)


def test_new_invocation_manually_claims_exact_native_session(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files)
    files.resume_state.write_text('{"session_id": "session-1"}\n')
    _start_manual_resume(monkeypatch)

    claim = _prepare(files)

    assert claim == resumelib.ResumeClaim(attempt=2, manual=True, resumable=True)
    assert resumelib.active_entries()[0]["owner"] == "invocation-2"


def test_manual_claim_restores_retry_cursor(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    logical = ("phase", "validation", "target")
    _prepare(files, logical=logical)
    resumelib.update_turn(
        logical,
        rate_limit_attempt=3,
        policy_attempt=2,
        transient_attempt=1,
        invocation_attempt=6,
        retry_reason="rate_limit",
    )
    files.resume_state.write_text('{"session_id": "session-1"}\n')
    _start_manual_resume(monkeypatch)

    claim = _prepare(files, logical=logical)

    assert claim.rate_limit_attempt == 3
    assert claim.policy_attempt == 2
    assert claim.transient_attempt == 1
    assert claim.invocation_attempt == 6
    assert claim.retry_reason == "rate_limit"


def test_completed_turn_is_not_resumed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    logical = ("phase", "validation", "target")
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files, logical=logical)
    files.resume_state.write_text('{"session_id": "completed-session"}\n')
    resumelib.complete_turn(logical)
    _start_manual_resume(monkeypatch)

    claim = _prepare(files, logical=logical)

    assert claim == resumelib.ResumeClaim(attempt=1, manual=False, resumable=False)
    assert resumelib.active_entries()[0]["owner"] == "invocation-2"


@pytest.mark.parametrize("state_kind", ["missing", "directory"])
def test_manual_resume_fails_closed_for_unusable_native_state(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    state_kind: str,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files)
    if state_kind == "directory":
        files.resume_state.mkdir()
    _start_manual_resume(monkeypatch)

    with pytest.raises(resumelib.ResumeError, match="native session state|unsafe native session state"):
        _prepare(files)

    assert resumelib.active_entries()[0]["owner"] == "invocation-1"


def test_manual_resume_fails_closed_for_binding_mismatch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files)
    files.resume_state.write_text('{"session_id": "session-1"}\n')
    _start_manual_resume(monkeypatch)

    with pytest.raises(resumelib.ResumeError, match=r"recorded model='model-a'.*current value is 'model-b'"):
        _prepare(files, model="model-b")

    assert resumelib.active_entries()[0]["owner"] == "invocation-1"


def test_manual_resume_preserves_phase_and_turn_order(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files)
    _start_manual_resume(monkeypatch)

    resumelib.ensure_phase("validation")
    with pytest.raises(resumelib.ResumeError, match="unfinished conversation.*validation"):
        resumelib.ensure_phase("model-checking")
    with pytest.raises(resumelib.ResumeError, match="native session state path already belongs"):
        _prepare(files, logical=("phase", "validation", "other-target"))


@pytest.mark.parametrize("linked_component", ["root", "active", "completed"])
def test_fresh_reset_rejects_resume_directory_symlinks_without_deleting_outside(
    tmp_path: Path,
    linked_component: str,
) -> None:
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    victim = outside / "victim.json"
    victim.write_text('{"keep": true}\n')

    if linked_component == "root":
        resumelib.resume_dir(run_dir).symlink_to(outside, target_is_directory=True)
    else:
        resumelib.resume_dir(run_dir).mkdir()
        linked_dir = resumelib.active_dir(run_dir) if linked_component == "active" else resumelib.completed_dir(run_dir)
        linked_dir.symlink_to(outside, target_is_directory=True)

    with pytest.raises(resumelib.ResumeError, match="not a real directory"):
        resumelib.initialize_run(run_dir, reset=True)

    assert victim.read_text() == '{"keep": true}\n'


def test_corrupt_active_record_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files)
    record = next(resumelib.active_dir(tmp_path).glob("*.json"))
    data = json.loads(record.read_text())
    data["attempt"] = "two"
    record.write_text(json.dumps(data))

    with pytest.raises(resumelib.ResumeError, match="invalid active conversation attempt"):
        resumelib.active_entries()


@pytest.mark.parametrize("record_state", ["active", "completed"])
def test_record_with_noncanonical_filename_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    record_state: str,
) -> None:
    logical = ("phase", "validation", "target")
    _enable_resume(tmp_path, monkeypatch)
    files = _turn_files(tmp_path)
    _prepare(files, logical=logical)
    if record_state == "completed":
        resumelib.mark_completed(logical)
        directory = resumelib.completed_dir(tmp_path)
    else:
        directory = resumelib.active_dir(tmp_path)
    record = next(directory.glob("*.json"))
    record.rename(directory / "wrong.json")

    reader = resumelib.completed_entries if record_state == "completed" else resumelib.active_entries
    with pytest.raises(resumelib.ResumeError, match="invalid .* filename"):
        reader()
