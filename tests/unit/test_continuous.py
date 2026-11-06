"""Continuous orchestration: mode selection, durable state, prompts, and handoffs."""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
from collections.abc import Iterator
from pathlib import Path

import pytest

from specula import context_control as control
from specula import context_runner as runner
from specula import continuous, resumelib, rules, stop_gate
from specula import pipelinelib as pl
from specula.agent_config import AgentConfigError, AgentSelection, load_agent_routing
from specula.notes import NOTES_ENV, notes_section
from specula.phaselib import Workspace, _retry_prompt
from specula.resource_summary import PhaseState, RunDetails, TargetState, render_summary


@pytest.fixture(autouse=True)
def _clean_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    for key in (
        "SPECULA_RUN_DIR",
        "SPECULA_PHASE",
        "SPECULA_WORK_DIR",
        resumelib.INVOCATION_ENV,
        resumelib.MANUAL_ENV,
        resumelib.FRESH_ENV,
        control.REQUEST_ENV,
        control.TOKEN_ENV,
        "MAX_REPAIR_ROUNDS",
    ):
        monkeypatch.delenv(key, raising=False)
    for key in (rules.RULES_ENV, NOTES_ENV):
        # Registered so values the code under test writes are undone too.
        monkeypatch.setenv(key, "")
        monkeypatch.delenv(key)


def parse(argv: list[str]) -> tuple[pl.Pipeline, int | None, str]:
    pipeline = pl.Pipeline()
    err = io.StringIO()
    with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
        rc = pipeline.parse_args(argv)
    return pipeline, rc, err.getvalue()


# ── mode selection ──────────────────────────────────────────────────────────


def test_continuous_is_the_cli_default_and_phased_stays_selectable() -> None:
    default, rc, _ = parse(["t|g|l|r"])
    assert rc is None and default.orchestration == "continuous" and default._orchestration_fallback is None
    phased, rc, _ = parse(["--orchestration=phased", "t|g|l|r"])
    assert rc is None and phased.orchestration == "phased"
    for argv in (["--orchestration=serial", "t"], ["--orchestration=phased", "--orchestration=continuous", "t"]):
        _, rc, err = parse(argv)
        assert rc == 1 and "--orchestration requires one value" in err
    assert pl.Pipeline().orchestration == "phased"  # embedders opt in explicitly


@pytest.mark.parametrize(
    "flag",
    [
        "--skip-analysis",
        "--skip-specgen",
        "--skip-harness",
        "--skip-validate",
        "--enable-reviews",
        "--no-isolate",
        "--confirm-first=only",
        "--confirm-first=continue",
        "--ci-init",
    ],
)
def test_unsupported_options_fall_back_by_default_and_fail_when_explicit(flag: str) -> None:
    fallback, rc, _ = parse([flag, "t|g|l|r"])
    assert rc is None
    assert fallback.orchestration == "phased"
    assert fallback._orchestration_fallback is not None and flag in fallback._orchestration_fallback
    _, rc, err = parse(["--orchestration=continuous", flag, "t|g|l|r"])
    assert rc == 1
    assert f"--orchestration=continuous does not support {flag}" in err
    assert "--orchestration=phased" in err


def test_path_options_fall_back(tmp_path: Path) -> None:
    model = tmp_path / "model.tla"
    model.write_text("---- MODULE model ----\n====\n")
    prior = tmp_path / "prior"
    prior.mkdir()
    for flag in (f"--byom={model}", f"--findings-from={prior}"):
        fallback, rc, _ = parse([flag, "t|g|l|r"])
        assert rc is None and fallback.orchestration == "phased"
        _, rc, err = parse(["--orchestration=continuous", flag, "t|g|l|r"])
        assert rc == 1 and "does not support" in err


def write_config(path: Path, phases: dict[str, str]) -> Path:
    path.write_text(
        json.dumps(
            {
                "version": 1,
                "default_profile": "base",
                "profiles": {
                    "base": {"agent": "claude-code", "model": "base-model"},
                    "main": {"agent": "codex", "model": "main-model"},
                    "same": {"agent": "codex", "model": "main-model"},
                    "check": {"agent": "claude-code", "model": "check-model"},
                },
                "phases": phases,
            }
        )
    )
    return path


def test_agent_config_main_route_rules(tmp_path: Path) -> None:
    config = tmp_path / "agents.json"
    routing = load_agent_routing(write_config(config, {"main": "main", "confirm": "check"}))
    assert routing.main_selection() == AgentSelection("codex", "main-model")
    assert routing.main_session_differences() == []
    uniform = load_agent_routing(
        write_config(config, {"analyze": "main", "specgen": "same", "harness": "main", "validate": "main"})
    )
    assert uniform.main_selection() == AgentSelection("codex", "main-model")
    split = load_agent_routing(write_config(config, {"analyze": "main", "harness": "check"}))
    assert split.main_session_differences() == ["specgen", "harness", "validate"]
    with pytest.raises(AgentConfigError, match="single profile"):
        split.main_selection()
    repair = load_agent_routing(write_config(config, {"main": "main", "repair": "check"}))
    assert repair.main_session_differences() == ["repair"]
    # Unlisted phased routes are covered by an explicit main route.
    assert load_agent_routing(write_config(config, {"main": "base"})).main_session_differences() == []


def test_agent_config_conflict_falls_back_or_errors(tmp_path: Path) -> None:
    config = write_config(tmp_path / "agents.json", {"analyze": "main", "validate": "check"})
    fallback, rc, _ = parse([f"--agent-config={config}", "t|g|l|r"])
    assert rc is None and fallback.orchestration == "phased"
    assert fallback._orchestration_fallback is not None and "--agent-config" in fallback._orchestration_fallback
    _, rc, err = parse(["--orchestration=continuous", f"--agent-config={config}", "t|g|l|r"])
    assert rc == 1 and "--agent-config routing" in err
    good = write_config(tmp_path / "good.json", {"main": "main", "confirm": "check", "classify": "base"})
    pipeline, rc, _ = parse([f"--agent-config={good}", "t|g|l|r"])
    assert rc is None and pipeline.orchestration == "continuous"
    assert set(pipeline._route_specs()) == {"main", "confirm", "classify"}
    assert pipeline._agent_selection("main") == AgentSelection("codex", "main-model")
    assert pipeline._agent_selection("confirm") == AgentSelection("claude-code", "check-model")


def test_incremental_keeps_its_own_path() -> None:
    from specula.ci_workflow import CIPipeline

    pipeline = CIPipeline()
    pipeline.incremental = True
    assert pipeline._resolve_orchestration() is None and pipeline.orchestration == "phased"
    pipeline._orchestration_requested = "continuous"
    assert pipeline._resolve_orchestration() == "--orchestration does not apply to --incremental"


# ── resume configuration ─────────────────────────────────────────────────────


def test_resume_configuration_records_and_restores_the_mode() -> None:
    continuous_run, _, _ = parse(["t|g|l|r"])
    document = continuous_run._resume_configuration_document()
    assert document["orchestration"] == "continuous"
    phased_run, _, _ = parse(["--orchestration=phased", "t|g|l|r"])
    assert "orchestration" not in phased_run._resume_configuration_document()  # identical to older runs

    attach, _, _ = parse(["--run-id=x"])
    attach._restore_resume_configuration(document)
    assert attach.orchestration == "continuous"
    legacy, _, _ = parse(["--run-id=x"])
    legacy._restore_resume_configuration(phased_run._resume_configuration_document())
    assert legacy.orchestration == "phased"

    explicit, _, _ = parse(["--run-id=x", "--orchestration=phased"])
    with pytest.raises(resumelib.ResumeError, match="uses continuous orchestration"):
        explicit._restore_resume_configuration(document)
    switched, _, _ = parse(["--run-id=x", "--orchestration=continuous"])
    with pytest.raises(resumelib.ResumeError, match="uses phased orchestration"):
        switched._restore_resume_configuration(phased_run._resume_configuration_document(), allow_overrides=True)
    skipped, _, _ = parse(["--run-id=x", "--skip-analysis"])
    with pytest.raises(resumelib.ResumeError, match="does not support --skip-analysis"):
        skipped._restore_resume_configuration(document)
    invalid = dict(document, orchestration="serial")
    with pytest.raises(resumelib.ResumeError, match="invalid stored orchestration"):
        parse(["--run-id=x"])[0]._restore_resume_configuration(invalid)


def test_prompt_toggles_are_stored_at_creation_and_restored_on_attach(monkeypatch: pytest.MonkeyPatch) -> None:
    created, _, _ = parse(["t|g|l|r"])
    document = created._resume_configuration_document()
    assert (document["rules"], document["notes"]) == (True, True)
    monkeypatch.setenv(rules.RULES_ENV, "off")
    monkeypatch.setenv(NOTES_ENV, "0")
    legacy = parse(["--orchestration=phased", "t|g|l|r"])[0]._resume_configuration_document()
    assert "rules" not in legacy and "notes" not in legacy  # identical to runs from before the toggles

    attach, _, _ = parse(["--run-id=x"])
    attach._restore_resume_configuration(document)
    assert os.environ[rules.RULES_ENV] == "on" and os.environ[NOTES_ENV] == "on"
    assert rules.enabled() and notes_section(Path("/w"), first=False)
    assert len(attach.resume_notices) == 2
    assert all("keeping that instead of the current off" in notice for notice in attach.resume_notices)

    same, _, _ = parse(["--run-id=x"])
    same._restore_resume_configuration(document)
    assert same.resume_notices == [] and os.environ[rules.RULES_ENV] == "on"

    old_run, _, _ = parse(["--run-id=x"])
    old_run._restore_resume_configuration(legacy)
    assert os.environ[rules.RULES_ENV] == "off" and not rules.enabled()
    assert len(old_run.resume_notices) == 2

    monkeypatch.setenv(rules.RULES_ENV, "off")
    fresh, _, _ = parse(["--run-id=x", "--fresh-context"])
    fresh._restore_resume_configuration(document, allow_overrides=True)
    assert os.environ[rules.RULES_ENV] == "off" and fresh.resume_notices == []
    with pytest.raises(resumelib.ResumeError, match="invalid stored rules"):
        parse(["--run-id=x"])[0]._restore_resume_configuration(dict(document, rules="yes"))


def test_routed_resume_configuration_uses_main_routes(tmp_path: Path) -> None:
    config = write_config(tmp_path / "agents.json", {"main": "main", "confirm": "check"})
    pipeline, _, _ = parse([f"--agent-config={config}", "t|g|l|r"])
    document = pipeline._resume_configuration_document()
    assert set(document["routes"]) == {"main", "confirm", "classify"}
    attach, _, _ = parse(["--run-id=x"])
    attach._restore_resume_configuration(document)
    assert attach._agent_selection("main").model == "main-model"
    assert attach._agent_selection("classify").model == "base-model"


def test_resume_phase_positions_continuous_attach() -> None:
    assert continuous.resume_phase({"main"}) == "main"
    assert continuous.resume_phase({"main", "bug_confirmation"}) == "main"
    assert continuous.resume_phase({"bug_confirmation"}) == "bug_confirmation"
    assert continuous.resume_phase({"bug_classification"}) == "bug_classification"
    with pytest.raises(resumelib.ResumeError):
        continuous.resume_phase({"main", "bug_classification"})


# ── durable state ────────────────────────────────────────────────────────────


def test_state_round_trip_and_fail_closed(tmp_path: Path) -> None:
    assert continuous.load_state(tmp_path, "t") is None
    state = continuous.MainState(stage="confirm", repair_round=2, session_id="s-1")
    continuous.save_state(tmp_path, "t", state, "yield")
    loaded = continuous.load_state(tmp_path, "t")
    assert loaded is not None
    assert (loaded.stage, loaded.repair_round, loaded.session_id) == ("confirm", 2, "s-1")
    assert loaded.history[-1]["event"] == "yield"
    with pytest.raises(continuous.ContinuousError):
        continuous.load_state(tmp_path, "other-target")
    path = continuous.state_path(tmp_path)
    for broken in ("{", json.dumps({**json.loads(path.read_text()), "stage": "running"})):
        path.write_text(broken)
        with pytest.raises(continuous.ContinuousError):
            continuous.load_state(tmp_path, "t")
    request = tmp_path / control.CONFIRMATION_REQUEST
    request.write_text(json.dumps({"session_id": "", "status": "pending"}))
    with pytest.raises(continuous.ContinuousError):
        continuous.load_request(tmp_path)


# ── the main-session phase ───────────────────────────────────────────────────


@pytest.fixture
def run_workspace(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Iterator[tuple[Workspace, Path]]:
    run = tmp_path / "run"
    run.mkdir()
    resumelib.initialize_run(run)
    source = tmp_path / "source"
    source.mkdir()
    monkeypatch.setenv("SPECULA_RUN_DIR", str(run))
    monkeypatch.setenv(resumelib.INVOCATION_ENV, "a" * 32)
    ws = Workspace(["t|org/t|Go|Raft"], artifact=str(source), run_dir=run)
    work = ws.work_dir("t")
    work.mkdir(parents=True)
    yield ws, work


def seed_active_main(ws: Workspace, work: Path, *, resumable: bool) -> None:
    phase = continuous.ContinuousPhase()
    files = phase.agent_files(ws, "t")
    resumelib.prepare_turn(
        ("phase", "main", "t"),
        phase="main",
        target="t",
        kind="phase",
        adapter=Path("fake"),
        model=None,
        effort=None,
        claude_alias="claude",
        cwd=Path.cwd(),
        resume_state=work / "main.resume.json",
        prompt_file=files["prompt"],
        log_file=files["log"],
    )
    if resumable:
        (work / "main.resume.json").write_text(json.dumps({"adapter": "fake", "session_id": "s-1"}))


def seed_repair_round(work: Path, round_: int = 1) -> None:
    (work / "spec/repair-requests").mkdir(parents=True)
    (work / "spec/repair-requests/RR-001.md").write_text("---\nid: RR-001\nstatus: OPEN\n---\n")
    (work / control.REPAIR_SNAPSHOT).write_text(
        json.dumps({"version": 2, "round": round_, "commit_token": "0" * 32, "requests": {"RR-001.md": "..."}})
    )
    continuous.save_state(work, "t", continuous.MainState(repair_round=round_, session_id="s-1"), "repair")


def test_first_launch_uses_the_full_prompt_with_phase_output_contract(run_workspace: tuple[Workspace, Path]) -> None:
    ws, work = run_workspace
    prompt = continuous.ContinuousPhase().build_prompt(ws, "t|org/t|Go|Raft")
    assert prompt.startswith("# Specula Main Session: t")
    for expected in (
        "code-analysis",
        "spec-generation",
        "harness-generation",
        "validation-workflow",
        f"{work}/modeling-brief.md",
        f"{work}/spec/instrumentation-spec.md",
        f"{work}/harness/run.sh",
        f"{work}/spec/findings.json",
        "request_bug_confirmation",
        "request_context_compaction",
        "BLOCKED.md",
    ):
        assert expected in prompt
    assert "Continue From Existing Work" not in prompt


def test_repair_resume_sends_only_the_continuation(
    run_workspace: tuple[Workspace, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    ws, work = run_workspace
    seed_active_main(ws, work, resumable=True)
    seed_repair_round(work)
    seen: list[str] = []

    def hook(text: str, *, work_dir: Path | None = None, notes: bool = False) -> str:
        assert not notes
        seen.append(text)
        assert work_dir == work
        return "HOOKED " + text

    monkeypatch.setattr(continuous, "_continuation_prompt", hook)
    prompt = continuous.ContinuousPhase().build_prompt(ws, "t|org/t|Go|Raft")
    assert prompt.startswith("HOOKED ## Repair Round 1")
    assert "RR-001" in prompt and "CONSUMED" in prompt
    assert "# Specula Main Session" not in prompt
    assert len(seen) == 1


def test_unresumable_repair_restarts_with_full_prompt_and_context(run_workspace: tuple[Workspace, Path]) -> None:
    ws, work = run_workspace
    seed_active_main(ws, work, resumable=False)
    seed_repair_round(work)
    prompt = strip_rules(continuous.ContinuousPhase().build_prompt(ws, "t|org/t|Go|Raft"))
    assert prompt.startswith("# Specula Main Session: t")
    assert "## Repair Round 1" in prompt


def test_fresh_context_lists_existing_work(run_workspace: tuple[Workspace, Path]) -> None:
    ws, work = run_workspace
    (work / "spec").mkdir()
    (work / "modeling-brief.md").write_text("brief")
    (work / "spec/base.tla").write_text("model")
    continuous.save_state(work, "t", continuous.MainState(context="fresh"), "fresh-context")
    prompt = continuous.ContinuousPhase().build_prompt(ws, "t|org/t|Go|Raft")
    assert "## Continue From Existing Work" in prompt
    assert f"`{work / 'modeling-brief.md'}`" in prompt and f"`{work / 'spec/base.tla'}`" in prompt
    assert "not results of this session" in prompt


def test_manual_resume_extra_carries_rejection_and_repair(
    run_workspace: tuple[Workspace, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    ws, work = run_workspace
    seed_repair_round(work)
    state = continuous.load_state(work, "t")
    assert state is not None
    state.rejection = "Repair requests handed to this session were not consumed: RR-001=OPEN."
    continuous.save_state(work, "t", state, "rejected")
    extra = continuous.ContinuousPhase()._manual_prompt_extra(ws, "t")
    assert "Confirmation Request Not Accepted" in extra and "RR-001=OPEN" in extra
    assert "## Repair Round 1" in extra


def test_a_main_session_that_simply_succeeds_is_not_accepted(run_workspace: tuple[Workspace, Path]) -> None:
    ws, _work = run_workspace
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        failures = continuous.ContinuousPhase().finalize_outputs(ws, ["t"], adapter=Path("fake"), dry_run=False)
    assert failures == [("t", 1)] and "without a controller handoff" in out.getvalue()


# ── context control, runner, and stop gate ──────────────────────────────────


def configure_request(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, phase: str = "main") -> Path:
    work = tmp_path / "work"
    (work / "spec").mkdir(parents=True)
    monkeypatch.setenv("SPECULA_PHASE", phase)
    monkeypatch.setenv("SPECULA_WORK_DIR", str(work))
    monkeypatch.setenv(control.REQUEST_ENV, str(tmp_path / "request.json"))
    monkeypatch.setenv(control.TOKEN_ENV, "token")
    return work


def test_main_confirmation_request_requires_consumed_repairs(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    work = configure_request(monkeypatch, tmp_path)
    (work / "modeling-brief.md").write_text("brief")
    (work / "spec/bug-report.md").write_text("report")
    result = control.request_confirmation()
    assert "only if repair work is needed" in result["instruction"]
    assert "final CI reports" not in result["instruction"]
    seed_repair_round(work)
    with pytest.raises(ValueError, match="RR-001=OPEN"):
        control.request_confirmation()
    rr = work / "spec/repair-requests/RR-001.md"
    rr.write_text(rr.read_text().replace("OPEN", "CONSUMED"))
    assert control.request_confirmation()["status"] == "requested"
    monkeypatch.setenv("SPECULA_PHASE", "spec_validation")
    with pytest.raises(ValueError, match="continuous Specula main session"):
        control.request_confirmation()


def test_stop_gate_main_contract_pauses_only_for_compaction(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    work = configure_request(monkeypatch, tmp_path)
    monkeypatch.setenv("SPECULA_CONTEXT_REQUEST", str(tmp_path / "request.json"))
    monkeypatch.setenv("SPECULA_CONTEXT_TOKEN", "token")
    assert stop_gate.CONTRACTS["main"] == "spec/bug-report.md"
    allowed, reason = stop_gate.decide("main", work)
    assert not allowed and "spec/bug-report.md" in reason
    (tmp_path / "request.json").write_text(json.dumps({"token": "other", "handoff_path": "h.md"}))
    assert not stop_gate.decide("main", work)[0]
    (tmp_path / "request.json").write_text(json.dumps({"token": "token", "action": "confirm"}))
    assert not stop_gate.decide("main", work)[0]
    (tmp_path / "request.json").write_text(json.dumps({"token": "token", "handoff_path": "h.md"}))
    assert stop_gate.decide("main", work)[0]
    (tmp_path / "request.json").unlink()
    (work / "spec/bug-report.md").write_text("report")
    assert stop_gate.decide("main", work)[0]


def fake_adapter(tmp_path: Path, name: str, body: str) -> Path:
    real_src = Path(control.__file__).resolve().parents[1]
    adapter = tmp_path / f"{name}.sh"
    adapter.write_text(
        f"#!{sys.executable}\n"
        "import json,os,sys\nfrom pathlib import Path\n"
        f"sys.path.insert(0,{str(real_src)!r})\n"
        "from specula.context_control import request_compaction, request_confirmation\n"
        "opts=dict(x[2:].split('=',1) for x in sys.argv[1:] if x.startswith('--') and '=' in x)\n"
        "work=Path(os.environ['SPECULA_WORK_DIR']); log=Path(opts['log']); resume=Path(opts['resume-state'])\n"
        "prompt=Path(opts['prompt-file']).read_text()\n"
        "def respond(text):\n"
        " log.write_text(text+'\\n'); log.with_suffix('.last-message.txt').write_text(text+'\\n')\n" + body
    )
    adapter.chmod(0o755)
    return adapter


def runner_args(work: Path) -> list[str]:
    prompt = work / "prompt.md"
    prompt.write_text("Original main task")
    system = work / "prompt.system.md"
    system.write_text("pinned rules")
    return [
        f"--log={work / 'main.log'}",
        f"--resume-state={work / 'main.resume.json'}",
        f"--prompt-file={prompt}",
        f"--system-prompt-file={system}",
    ]


@pytest.mark.parametrize("agent", ["codex", "claude-code", "pi", "opencode", "copilot-cli"])
def test_runner_turns_an_ordinary_main_ending_into_a_bound_handoff(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, agent: str
) -> None:
    work = configure_request(monkeypatch, tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    adapter = fake_adapter(
        tmp_path,
        agent,
        f"resume.write_text(json.dumps({{'adapter':{agent!r},'session_id':'native-1'}}))\n"
        "respond('Validation complete.')\n",
    )
    assert runner.run(adapter, runner_args(work)) == control.CONFIRMATION_YIELD_RC
    request = json.loads((work / control.CONFIRMATION_REQUEST).read_text())
    assert request == {"session_id": "native-1", "status": "pending", "phase": "main", "implicit": True}


def test_runner_fails_closed_without_a_native_session(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    work = configure_request(monkeypatch, tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    adapter = fake_adapter(tmp_path, "codex", "respond('done')\n")
    with pytest.raises(OSError):
        runner.run(adapter, runner_args(work))
    assert not (work / control.CONFIRMATION_REQUEST).exists()


def test_runner_rejects_an_unsupervised_main_session(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    work = configure_request(monkeypatch, tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    (work / ".context-control").write_text("not a directory")
    adapter = fake_adapter(tmp_path, "codex", "raise SystemExit(0)\n")
    assert runner.run(adapter, runner_args(work)) == 1


@pytest.mark.parametrize("agent", ["codex", "claude-code", "pi", "opencode", "copilot-cli"])
def test_runner_compacts_main_then_records_explicit_confirmation(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, agent: str
) -> None:
    work = configure_request(monkeypatch, tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(continuous, "_continuation_prompt", lambda text, *, work_dir=None, notes=False: "HOOK " + text)
    tool = tmp_path / "tools/context_control"
    (tool / ".venv/bin").mkdir(parents=True)
    (tool / ".venv/bin/python").symlink_to(sys.executable)
    (tool / "compact.py").write_text(
        "import json,sys\nfrom pathlib import Path\n"
        "assert json.loads(Path(sys.argv[1]).read_text())['session_id']=='native-1'\n"
        "Path(sys.argv[2]).write_text(json.dumps({'status':'completed'}))\n"
    )
    (work / "modeling-brief.md").write_text("brief")
    adapter = fake_adapter(
        tmp_path,
        agent,
        "second=resume.exists()\n"
        f"resume.write_text(json.dumps({{'adapter':{agent!r},'session_id':'native-1'}}))\n"
        "assert any(a.startswith('--system-prompt-file=') for a in sys.argv[1:]), sys.argv\n"
        "if second:\n"
        " assert prompt.startswith('HOOK Continue the same Specula main session'), prompt\n"
        " (work/'spec/bug-report.md').write_text('report')\n"
        " request_confirmation()\n"
        "else:\n"
        " (work/'handoff.md').write_text('Stage 2 done; next: harness.')\n"
        " request_compaction('handoff.md')\n"
        "respond('SPECULA_CONTEXT_YIELD '+os.environ['SPECULA_CONTEXT_TOKEN'])\n",
    )
    assert runner.run(adapter, runner_args(work)) == control.CONFIRMATION_YIELD_RC
    request = json.loads((work / control.CONFIRMATION_REQUEST).read_text())
    assert request == {"session_id": "native-1", "status": "pending", "phase": "main", "implicit": False}
    assert len(list(work.glob(".context-control/invocation-*/1/compaction.json"))) == 1


def test_incremental_ordinary_ending_is_still_not_a_handoff(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    work = configure_request(monkeypatch, tmp_path, phase="incremental")
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    adapter = fake_adapter(tmp_path, "codex", "respond('SPECULA_INCREMENTAL_COMPLETE run')\n")
    assert runner.run(adapter, runner_args(work)) == 0
    assert not (work / control.CONFIRMATION_REQUEST).exists()


def strip_rules(text: str) -> str:
    assert text.count(rules.RULES_TITLE) == 1, text[:200]
    assert text.startswith(rules.RULES_TITLE)
    return text.split(rules.RULES_SEPARATOR, 1)[1]


def test_continuations_pin_rules_exactly_once(run_workspace: tuple[Workspace, Path]) -> None:
    ws, work = run_workspace
    seed_active_main(ws, work, resumable=True)
    seed_repair_round(work)
    phase = continuous.ContinuousPhase()
    built = phase.build_prompt(ws, "t|org/t|Go|Raft")
    # phaselib's generic launch path wraps again; the block must not repeat.
    launched = _retry_prompt(built, "fresh", resumable=True)
    assert launched == built
    assert strip_rules(launched).startswith("## Repair Round 1")
    compaction = continuous.compaction_continue_prompt("completed", str(work / "handoff.md"), work)
    body = strip_rules(compaction)
    assert body.startswith("Continue the same Specula main session")
    assert "## Working Notes" in body and "Earlier phases may have left notes" in body
    assert strip_rules(_retry_prompt(compaction, "fresh", resumable=False)) == body


def test_main_prompt_opens_notes_and_fresh_context_continues_them(run_workspace: tuple[Workspace, Path]) -> None:
    ws, work = run_workspace
    phase = continuous.ContinuousPhase()
    first = phase.build_prompt(ws, "t|org/t|Go|Raft")
    assert first.count("## Working Notes") == 1
    assert "Start notes whenever something is worth keeping" in first
    assert first.index("## If You Cannot Finish") < first.index("## Working Notes")
    (work / "modeling-brief.md").write_text("brief")
    continuous.save_state(work, "t", continuous.MainState(context="fresh"), "fresh-context")
    fresh = strip_rules(phase.build_prompt(ws, "t|org/t|Go|Raft"))
    assert fresh.count("## Working Notes") == 1
    assert "Earlier phases may have left notes" in fresh
    assert "## Continue From Existing Work" in fresh


def test_rules_and_notes_off_leave_continuations_bare(
    run_workspace: tuple[Workspace, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    ws, work = run_workspace
    monkeypatch.setenv(rules.RULES_ENV, "off")
    monkeypatch.setenv(NOTES_ENV, "off")
    prompt = continuous.ContinuousPhase().build_prompt(ws, "t|org/t|Go|Raft")
    assert prompt.startswith("# Specula Main Session: t")
    assert "## Working Notes" not in prompt and rules.RULES_TITLE not in prompt
    compaction = continuous.compaction_continue_prompt("failed", "h.md", work)
    assert compaction.startswith("Continue the same Specula main session") and "Working Notes" not in compaction


def test_incremental_compaction_continue_prompt_is_pinned_once(monkeypatch: pytest.MonkeyPatch) -> None:
    prompt = runner._continue_prompt("incremental", "completed", "h.md", Path("/w"))
    assert strip_rules(prompt).startswith("Continue the same incremental CI task.")
    monkeypatch.setenv(rules.RULES_ENV, "off")
    assert runner._continue_prompt("incremental", "completed", "h.md", Path("/w")).startswith("Continue the same")


# ── resource summary ─────────────────────────────────────────────────────────


def test_summary_attributes_the_main_session_as_one_phase() -> None:
    state = TargetState(target="t", run_details=RunDetails())
    state.phases["main"] = PhaseState(runtime_seconds=60, runtime_observed=True, tokens_observed=True, total_tokens=5)
    text = render_summary(state)
    assert "| Main session (Phases 1-3) |" in text
    assert "| Phase 4a |" in text and "| Phase 4b |" in text
    assert "| Phase 1 |" not in text


def test_has_unfinished_work(tmp_path: Path) -> None:
    pipeline = pl.Pipeline()
    pipeline.targets = ["t|g|l|r"]
    pipeline.run_dir = tmp_path
    work = Path(pipeline.get_work_dir("t"))
    assert not continuous.has_unfinished_work(pipeline)
    continuous.save_state(work, "t", continuous.MainState(stage="closed"), "closed")
    assert continuous.has_unfinished_work(pipeline)
    continuous.save_state(work, "t", continuous.MainState(stage="complete"), "complete")
    assert not continuous.has_unfinished_work(pipeline)


# ── adapters wire the context tools for every continuous phase ──────────────


@pytest.mark.parametrize("phase", ["main", "incremental", "spec_validation"])
@pytest.mark.parametrize("agent", ["claude-code", "codex", "copilot-cli", "opencode", "pi"])
def test_adapters_expose_context_tools_to_continuous_phases(tmp_path: Path, phase: str, agent: str) -> None:
    import test_adapters as adapters

    work = tmp_path / "work"
    work.mkdir()
    directory = tmp_path / "control"
    directory.mkdir()
    env = runner.tool_environment(directory, work, Path(sys.executable), agent)
    env = {key: env[key] for key in env if key.startswith("SPECULA_CONTEXT")}
    env.update({"SPECULA_PHASE": phase, "SPECULA_WORK_DIR": str(work), "SPECULA_STOP_GATE": "off"})
    env["COPILOT_HELP_TEXT"] = "--autopilot --additional-mcp-config"
    fake = {"claude-code": "claude", "copilot-cli": "copilot"}.get(agent, agent)
    fixture = json.dumps(adapters.CLAUDE_JSON) if agent == "claude-code" else ""
    if agent == "opencode":
        fixture = json.dumps({"type": "step_finish", "part": {"reason": "stop", "tokens": {}, "cost": 0}})
    elif agent == "pi":
        fixture = json.dumps(
            {"type": "message_end", "message": {"role": "assistant", "content": [], "stopReason": "stop"}}
        )
    case = adapters.AdapterCase()
    try:
        observed = case.run_adapter(
            [str(Path(runner.ROOT) / "scripts/launch/adapters" / f"{agent}.sh")],
            ["--prompt=context tool smoke", "--max-turns=1", f"--log={tmp_path / 'agent.log'}"],
            fake_name=fake,
            fixture_text=fixture,
            env_extra=env,
            timeout=10,
            run_dir=tmp_path,
        )
    finally:
        case.doCleanups()
    assert observed["returncode"] == 0, observed["stderr"]
    argv = observed["argv"]
    wired = phase != "spec_validation"
    if agent == "claude-code":
        assert ("--mcp-config" in argv and argv[argv.index("--mcp-config") + 1] == env[control.MCP_ENV]) is wired
    elif agent == "codex":
        assert ("mcp_servers.specula_context=" + env["SPECULA_CONTEXT_CODEX_CONFIG"] in argv) is wired
    elif agent == "copilot-cli":
        assert ("--additional-mcp-config" in argv) is wired
    elif agent == "opencode":
        config = json.loads(observed["opencode_config"] or "{}")
        assert ("specula_context" in config.get("mcp", {})) is wired
    else:
        extension = str(Path(runner.ROOT) / "tools/context_control/pi-extension.js")
        assert (extension in argv) is wired


def test_pi_extension_accepts_every_continuous_phase() -> None:
    source = (Path(runner.ROOT) / "tools/context_control/pi-extension.js").read_text()
    for phase in control.CONTINUOUS_PHASES:
        assert f'"{phase}"' in source
