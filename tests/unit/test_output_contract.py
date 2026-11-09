"""The continuous main session's output contract: required set, validity checks, strict switch."""

from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

import pytest

from specula import output_contract as oc
from specula.prompts import render

FAKE_SANY = Path(__file__).resolve().parents[1] / "e2e/fixtures/fake_sany.py"


@pytest.fixture(autouse=True)
def _clean_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv(oc.STRICT_ENV, raising=False)
    monkeypatch.delenv("SPECULA_ROOT", raising=False)


@pytest.fixture
def sany(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """A fake SANY: a placeholder jar in this tree's lib/ and a fake java first on PATH; returns its call log."""
    root = tmp_path / "specula-root"
    (root / "lib").mkdir(parents=True)
    (root / "lib/tla2tools.jar").write_bytes(b"")
    bindir = tmp_path / "bin"
    bindir.mkdir()
    java = bindir / "java"
    java.write_text(f'#!/bin/sh\nexec "{sys.executable}" "{FAKE_SANY}" "$@"\n')
    java.chmod(0o755)
    monkeypatch.setattr(oc, "_ROOT", root)
    monkeypatch.setenv("PATH", f"{bindir}:/usr/bin:/bin")
    log = tmp_path / "sany-calls.jsonl"
    monkeypatch.setenv("FIXTURE_SANY_LOG", str(log))
    return log


def write_required(work: Path) -> None:
    for relative in oc.REQUIRED_FILES:
        path = work / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"fixture {relative}\n")
    (work / "spec/findings.json").write_text(json.dumps({"findings": []}))
    (work / "traces/run-1").mkdir(parents=True)
    (work / "traces/run-1/t.ndjson").write_text('{"event":"x"}\n')


def calls(log: Path) -> list[str]:
    return [json.loads(line)["module"] for line in log.read_text().splitlines()] if log.exists() else []


# ── strict switch ───────────────────────────────────────────────────────────


@pytest.mark.parametrize("value", ["on", "ON", " 1 ", "true", "yes"])
def test_strict_accepts_the_on_spellings(value: str, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(oc.STRICT_ENV, value)
    assert oc.strict()


@pytest.mark.parametrize("value", ["", "off", "OFF", "0", "false", "no"])
def test_strict_is_off_by_default_and_for_the_off_spellings(value: str, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(oc.STRICT_ENV, value)
    assert not oc.strict()


def test_strict_requires_every_advisory_file_too() -> None:
    assert set(oc.required_files(strict=False)) == set(oc.REQUIRED_FILES)
    assert set(oc.required_files(strict=True)) == set(oc.REQUIRED_FILES) | set(oc.ADVISORY_FILES)
    assert not set(oc.REQUIRED_FILES) & set(oc.ADVISORY_FILES)


# ── the handoff check ───────────────────────────────────────────────────────


def test_required_set_alone_is_a_valid_handoff(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    assert oc.handoff_problems(work, strict=False) == []
    # Every required module is parsed, in the spec directory, by name.
    assert calls(sany) == ["base.tla", "MC.tla", "Trace.tla"]
    first = json.loads(sany.read_text().splitlines()[0])
    assert first["cwd"] == str(work / "spec") and first["args"][0].startswith("-Djava.io.tmpdir=")
    for relative in oc.ADVISORY_FILES:
        assert not (work / relative).exists()


def test_each_missing_or_empty_required_file_is_named_with_what_to_write(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    (work / "spec/MC.cfg").unlink()
    (work / "harness/run.sh").write_text("  \n")
    (work / "modeling-brief.md").unlink()
    problems = oc.handoff_problems(work, strict=False)
    assert problems == [
        "`modeling-brief.md` is missing: write the code-analysis skill's modeling brief; "
        "confirmation reads its code-review Scenarios.",
        "`spec/MC.cfg` is missing: write the model-checking configuration.",
        "`harness/run.sh` is empty.",
    ]


def test_a_module_sany_rejects_is_reported_with_its_errors_and_rerun_command(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    (work / "spec/Trace.tla").write_text("---- MODULE Trace ----\nSANY-ERROR\n====\n")
    (problem,) = oc.handoff_problems(work, strict=False)
    assert problem.startswith("`spec/Trace.tla` does not parse with SANY (exit 255).")
    assert "tla2sany.SANY Trace.tla" in problem and f"cd {work / 'spec'}" in problem
    assert "***Parse Error***" in problem and "Fatal errors while parsing" in problem
    assert "Parsing file" not in problem  # progress noise is dropped


def test_semantic_errors_fail_even_when_sany_exits_zero(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    (work / "spec/MC.tla").write_text("---- MODULE MC ----\nSANY-SEMANTIC\n====\n")
    (problem,) = oc.handoff_problems(work, strict=False)
    assert problem.startswith("`spec/MC.tla` does not parse with SANY (semantic errors).")
    assert "Unknown operator" in problem


def test_a_java_that_does_not_start_sany_is_unavailable_not_a_parse_error(
    tmp_path: Path, sany: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    work = tmp_path / "work"
    write_required(work)
    broken = tmp_path / "broken-bin"
    broken.mkdir()
    (broken / "java").write_text(
        "#!/bin/sh\necho 'Error: Could not find or load main class tla2sany.SANY' >&2\nexit 1\n"
    )
    (broken / "java").chmod(0o755)
    monkeypatch.setenv("PATH", f"{broken}:/usr/bin:/bin")
    with pytest.raises(oc.SanyUnavailable, match="SANY did not start: Error: Could not find or load main class"):
        oc.handoff_problems(work, strict=False)
    # The agent-side precheck skips the parse instead; the other checks still run.
    assert oc.handoff_problems(work, strict=False, sany_optional=True) == []
    (work / "spec/MC.cfg").unlink()
    assert oc.handoff_problems(work, strict=False, sany_optional=True) == [
        "`spec/MC.cfg` is missing: write the model-checking configuration."
    ]


def test_findings_use_the_dispatcher_validation(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    finding = {
        "id": "MC-1",
        "source": "model-checking",
        "invariant": "Inv",
        "config": "MC_hunt.cfg",
        "counterexample": "spec/output/missing.out",
    }
    (work / "spec/findings.json").write_text(json.dumps({"findings": [finding]}))
    assert oc.handoff_problems(work, strict=False) == [
        "`spec/findings.json`: MC-1 counterexample is missing or empty (see the validation skill's findings format)"
    ]
    (work / "spec/findings.json").write_text("{not json")
    (problem,) = oc.handoff_problems(work, strict=False)
    assert problem.startswith("`spec/findings.json`: Expecting property name")


def test_missing_traces_are_a_validation_limit_not_a_rejection(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    assert oc.traces_collected(work) and oc.handoff_limits(work) == []
    (work / "traces/run-1/t.ndjson").write_text("")
    for strict in (False, True):
        problems = oc.handoff_problems(work, strict=strict)
        assert not any("traces" in problem for problem in problems)
    assert oc.handoff_limits(work) == [oc.TRACES_LIMIT]
    shutil.rmtree(work / "traces")
    assert oc.handoff_problems(work, strict=False) == [] and oc.handoff_limits(work) == [oc.TRACES_LIMIT]
    (work / "harness/run.sh").unlink()  # the harness entry point stays required
    assert oc.handoff_problems(work, strict=False) == [
        "`harness/run.sh` is missing: write the one-command script that builds the instrumented code, "
        "runs it, and collects traces."
    ]


def test_strict_requires_the_advisory_files_and_harness_sources(tmp_path: Path, sany: Path) -> None:
    work = tmp_path / "work"
    write_required(work)
    problems = oc.handoff_problems(work, strict=True)
    assert len(problems) == len(oc.ADVISORY_FILES) + 1
    assert "`spec/instrumentation-spec.md` is missing: write the instrumentation mapping." in problems
    assert "`harness/src/` is missing or empty: write the harness sources it holds." in problems
    for relative in oc.ADVISORY_FILES:
        (work / relative).write_text("present\n")
    (work / "harness/src").mkdir()
    (work / "harness/src/trace.go").write_text("package trace\n")
    assert oc.handoff_problems(work, strict=True) == []


def test_sany_unavailable_is_an_error_not_a_pass(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    work = tmp_path / "work"
    write_required(work)
    monkeypatch.setattr(oc, "_ROOT", tmp_path / "no-root")
    with pytest.raises(oc.SanyUnavailable, match=r"tla2tools\.jar not found in .*no-root/lib"):
        oc.handoff_problems(work, strict=False)
    # Like run_model_check.sh, $SPECULA_ROOT supplies the jars when this tree has none.
    (tmp_path / "other/lib").mkdir(parents=True)
    (tmp_path / "other/lib/tla2tools.jar").write_bytes(b"")
    (tmp_path / "other/lib/CommunityModules-deps.jar").write_bytes(b"")
    monkeypatch.setenv("SPECULA_ROOT", str(tmp_path / "other"))
    monkeypatch.setenv("PATH", str(tmp_path / "empty-bin"))
    with pytest.raises(oc.SanyUnavailable, match="java was not found on PATH"):
        oc.handoff_problems(work, strict=False)
    monkeypatch.setattr(shutil, "which", lambda name: "/usr/bin/java")
    java, jars = oc.sany_tools()
    assert jars == [tmp_path / "other/lib/tla2tools.jar", tmp_path / "other/lib/CommunityModules-deps.jar"]


def _real_sany() -> tuple[str, list[Path]] | None:
    try:
        return oc.sany_tools()
    except oc.SanyUnavailable:
        return None


REAL_SANY = _real_sany()  # resolved before the fixtures clear SPECULA_ROOT


@pytest.mark.skipif(REAL_SANY is None, reason="no TLA+ tools in this environment")
def test_real_sany_accepts_a_module_and_rejects_parse_and_semantic_errors(tmp_path: Path) -> None:
    assert REAL_SANY is not None
    (tmp_path / "Good.tla").write_text("---- MODULE Good ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n====\n")
    (tmp_path / "Bad.tla").write_text("fixture Bad.tla\n")
    (tmp_path / "Undefined.tla").write_text("---- MODULE Undefined ----\nVARIABLE x\nInit == y = 0\n====\n")
    assert oc.sany_problem(tmp_path, "Good.tla", *REAL_SANY) is None
    bad = oc.sany_problem(tmp_path, "Bad.tla", *REAL_SANY)
    assert bad is not None and "does not parse with SANY" in bad and "Parse Error" in bad
    undefined = oc.sany_problem(tmp_path, "Undefined.tla", *REAL_SANY)
    assert undefined is not None and "Unknown operator" in undefined


# ── the prompt states the same contract ─────────────────────────────────────


def _sections(strict: bool) -> tuple[str, str]:
    text = render("continuous/outputs-strict" if strict else "continuous/outputs", work_dir="/W", spec_dir="/W/spec")
    required, _, recommended = text.partition("### Recommended")
    return required, recommended


def test_default_prompt_splits_required_and_recommended_like_the_check() -> None:
    required, recommended = _sections(strict=False)
    for relative in oc.REQUIRED_FILES:
        assert f"`/W/{relative}`" in required and f"`/W/{relative}`" not in recommended
    assert "`/W/traces/*.ndjson`" in required
    for relative in oc.ADVISORY_FILES:
        assert f"`/W/{relative}`" in recommended and f"`/W/{relative}`" not in required
    assert "`/W/harness/src/`" in recommended
    assert "Only the set of files is relaxed; the skills' steps and depth are not." in required


def test_strict_prompt_lists_every_output_as_required() -> None:
    required, recommended = _sections(strict=True)
    assert recommended == ""
    for relative in (*oc.REQUIRED_FILES, *oc.ADVISORY_FILES):
        assert f"`/W/{relative}`" in required
    assert "Every output below is required" in required and "relaxed" not in required
