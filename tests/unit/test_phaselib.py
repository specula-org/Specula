"""Behavior tests for the phase launchers (src/specula/phaselib.py).

With the characterization goldens retired there is no bash to diff against, so
these tests ARE the pin for each `launch_<phase>.sh`'s observable contract — the
part no other test crosses (the e2e dry-run stops at the pipeline layer, which
only *prints* the launcher command lines and never enters phaselib):

  - the precondition gate: missing inputs -> the phase's own fail message and
    exit 1 (the deleted gate_* goldens);
  - the --dry-run adapter command line + the prompt file each phase assembles:
    the adapter invocation, the per-phase log/prompt filenames, the --prompt vs
    --prompt-file quirk, the skill guide each defers to, and the output paths
    (the deleted dryrun_* / check_ok_* goldens);
  - the review agent's prompt contract (the deleted review_* goldens).

Each phase runs in-process under an isolated SPECULA_RUN_DIR, so every output
lands in a tmp run dir; --dry-run means no adapter is spawned and no network is
touched. SPECULA_ROOT is patched to a tmp tree so skill/case-dir paths resolve
hermetically (LAUNCH_DIR — the real adapter the gate checks exists — is a
module global and stays pointed at the repo).

stdlib unittest, collected natively by pytest:

    uv run python -m unittest tests.unit.test_phaselib -v
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import shlex
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from dataclasses import replace
from pathlib import Path
from typing import Any, TypedDict, cast
from unittest import mock

SRC = Path(__file__).resolve().parents[2] / "src"
if str(SRC) not in sys.path:  # test the tree this file lives in, installed or not
    sys.path.insert(0, str(SRC))

import specula.progress as progress_module  # noqa: E402
import specula.quota as quota  # noqa: E402
from specula import phaselib  # noqa: E402
from specula.progress import ProgressConfig, RunningAgent  # noqa: E402
from specula.skill_refs import CODEX_PLUGIN_NAME, prompt_skill_ids  # noqa: E402

NAME = "footest"


class PhaseSpec(TypedDict):
    key: str
    artifact: bool  # whether the phase accepts --artifact (bug_classification does not)
    inputs: list[str]  # files, relative to the work dir, check() needs to pass
    fail: str  # gate message when a prerequisite is missing
    ok: str  # --check success message
    log: str  # agent log filename
    prompt: str  # written prompt filename
    flag: str  # dry-run prompt flag: --prompt or --prompt-file
    skill: str  # installed skill name the prompt invokes
    out: str  # a key output/input path the prompt must carry


# Per-phase contract table. `fail`/`ok`/`skill`/`out` are spelled out here rather
# than read back off the phase object, so a reworded gate, a typo'd skill name,
# or a dropped output path is caught rather than mirrored.
PHASES: list[PhaseSpec] = [
    {
        "key": "code_analysis",
        "artifact": True,
        "inputs": [],
        "fail": "Some repositories are missing",
        "ok": "All repos OK.",
        "log": "agent.log",
        "prompt": ".prompt.md",
        "flag": "--prompt",
        "skill": "code-analysis",
        "out": "modeling-brief.md",
    },
    {
        "key": "spec_generation",
        "artifact": True,
        "inputs": ["modeling-brief.md"],
        "fail": "Run code analysis first.",
        "ok": "All prerequisites OK.",
        "log": "spec-gen.log",
        "prompt": ".spec-gen-prompt.md",
        "flag": "--prompt",
        "skill": "spec-generation",
        "out": "spec/base.tla",
    },
    {
        "key": "harness_generation",
        "artifact": True,
        "inputs": ["spec/base.tla", "spec/Trace.tla", "spec/instrumentation-spec.md"],
        "fail": "Run spec generation (Phase 2) first.",
        "ok": "All prerequisites OK.",
        "log": "harness-gen.log",
        "prompt": ".harness-gen-prompt.md",
        "flag": "--prompt",
        "skill": "harness-generation",
        "out": "harness",
    },
    {
        "key": "spec_validation",
        "artifact": True,
        "inputs": ["spec/base.tla", "spec/MC.tla", "spec/Trace.tla", "spec/instrumentation-spec.md"],
        "fail": "Run spec generation first.",
        "ok": "Required path checks passed; review any warnings above.",
        "log": "spec-validation.log",
        "prompt": ".spec-validation-prompt.md",
        "flag": "--prompt",
        "skill": "validation-workflow",
        "out": "modeling-brief.md",
    },
    {
        "key": "bug_confirmation",
        "artifact": True,
        "inputs": ["spec/bug-report.md", "modeling-brief.md"],
        "fail": "Run full pipeline first.",
        "ok": "All prerequisites OK.",
        "log": "bug-confirmation.log",
        "prompt": ".bug-confirmation-prompt.md",
        "flag": "--prompt",
        "skill": "bug-confirmation",
        "out": "spec/confirmed-bugs.md",
    },
    {
        # the outlier: no --artifact (accepts_artifact=False) and its dry-run
        # line shows --prompt-file, not --prompt.
        "key": "bug_classification",
        "artifact": False,
        "inputs": ["spec/confirmed-bugs.md"],
        "fail": "Run Phase 4a ('specula confirm') first.",
        "ok": "All prerequisites OK.",
        "log": "bug-classification.log",
        "prompt": ".bug-classification-prompt.md",
        "flag": "--prompt-file",
        "skill": "bug-classification",
        "out": "spec/bug-severity.md",
    },
]
BY_KEY = {p["key"]: p for p in PHASES}
PUBLIC_COMMANDS = {
    "code_analysis": "analyze",
    "spec_generation": "specgen",
    "harness_generation": "harness",
    "spec_validation": "validate",
    "bug_confirmation": "confirm",
    "bug_classification": "classify",
}


class PhaseCase(unittest.TestCase):
    """A phase run in-process under an isolated, hermetic tmp SPECULA_ROOT +
    SPECULA_RUN_DIR."""

    def setUp(self) -> None:
        self.root = self.tmp()  # patched SPECULA_ROOT: skills/case dirs resolve here
        self.run_dir = self.tmp()  # SPECULA_RUN_DIR: every output lands here
        self.patch_attr(phaselib, "SPECULA_ROOT", self.root)
        # Env the driver reads; restore so one test can't leak into the next.
        for var in (
            "SPECULA_RUN_DIR",
            "SPECULA_PHASE",
            "SPECULA_WORK_DIR",
            "SPECULA_STOP_GATE",
            "SPECULA_STOP_GATE_WORK_DIR",
            "SPECULA_SANDBOX",
            "SPECULA_SANDBOX_CONFIG",
            "SPECULA_PROGRESS",
            "SPECULA_ACTIVITY_LOG",
            "SPECULA_RATE_LIMIT_REACTIVE",
            "SPECULA_RATE_LIMIT_RETRIES",
            "SPECULA_TLC_SCOPE",
            "SPECULA_TLC_MEMORY_LIMIT",
            "SPECULA_TLC_WORKER_LIMIT",
            "SPECULA_QUOTA_5H",
            "SPECULA_QUOTA_7D",
            "SPECULA_QUOTA_MAX_WAITS",
            "SPECULA_CLAUDE_ALIAS",
            "SPECULA_MODEL",
            "SPECULA_EFFORT",
            "CLAUDE_ALIAS",
            "CLAUDE_EFFORT",
        ):
            self.set_env(var, str(self.run_dir) if var == "SPECULA_RUN_DIR" else None)

    def tmp(self) -> Path:
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return Path(d.name).resolve()

    def patch_attr(self, module: Any, attr: str, value: Any) -> None:
        old = getattr(module, attr)

        def restore() -> None:
            setattr(module, attr, old)

        self.addCleanup(restore)
        setattr(module, attr, value)

    def set_env(self, var: str, value: str | None) -> None:
        old = os.environ.get(var)

        def restore() -> None:
            if old is None:
                os.environ.pop(var, None)
            else:
                os.environ[var] = old

        self.addCleanup(restore)
        if value is None:
            os.environ.pop(var, None)
        else:
            os.environ[var] = value

    def work_dir(self, name: str = NAME) -> Path:
        return self.run_dir / name / ".specula-output"

    def seed(self, inputs: list[str], name: str = NAME) -> None:
        for rel in inputs:
            p = self.work_dir(name) / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("seeded\n")  # non-empty: some gates check st_size > 0

    def artifact_flag(self) -> str:
        repo = self.tmp() / "repo"
        repo.mkdir()
        return f"--artifact={repo}"

    def run_phase(self, key: str, args: list[str]) -> tuple[int, str]:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = phaselib.PHASES[key].run(args)
        return rc, buf.getvalue()

    def dry_run(self, spec: PhaseSpec, extra: list[str] | None = None, name: str = NAME) -> tuple[int, str]:
        self.seed(spec["inputs"], name)
        args = ["--dry-run", *(extra or [])]
        if spec["artifact"]:
            args.append(self.artifact_flag())
        args.append(name)
        return self.run_phase(spec["key"], args)


class TestDirectExecution(unittest.TestCase):
    def test_clean_path_invocation_bootstraps_package_imports(self) -> None:
        with tempfile.TemporaryDirectory() as cwd:
            env = os.environ.copy()
            env.pop("PYTHONPATH", None)
            env["PYTHONNOUSERSITE"] = "1"
            proc = subprocess.run(
                [sys.executable, "-S", str(SRC / "specula" / "phaselib.py"), "bug_confirmation", "--help"],
                cwd=cwd,
                env=env,
                capture_output=True,
                text=True,
            )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("Bug confirmation", proc.stdout)


class TestPreconditionGate(PhaseCase):
    """Missing inputs -> the phase's fail message on stdout + exit 1, before any
    agent is launched."""

    def test_each_phase_gate_fails_without_inputs(self) -> None:
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                rc, out = self.run_phase(spec["key"], [NAME])  # no inputs, no --artifact
                self.assertEqual(rc, 1, out)
                self.assertIn(spec["fail"], out)  # the phase's own, distinct fail message
                self.assertNotIn("[DRY RUN]", out)  # gate stops before the launch loop


class TestCheckOnly(PhaseCase):
    """--check with prerequisites satisfied -> the ok message + exit 0, no launch."""

    def test_each_phase_check_ok(self) -> None:
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                self.seed(spec["inputs"])
                args = ["--check"]
                if spec["artifact"]:
                    args.append(self.artifact_flag())
                args.append(NAME)
                rc, out = self.run_phase(spec["key"], args)
                self.assertEqual(rc, 0, out)
                self.assertIn(spec["ok"], out)
                self.assertNotIn("[DRY RUN]", out)

    def test_each_artifact_phase_expands_home_directory(self) -> None:
        home = self.tmp()
        repo = home / "cass-operator"
        repo.mkdir()
        self.set_env("HOME", str(home))

        for spec in PHASES:
            if not spec["artifact"]:
                continue
            with self.subTest(phase=spec["key"]):
                self.seed(spec["inputs"])
                rc, out = self.run_phase(spec["key"], ["--check", "--artifact=~/cass-operator", NAME])
                self.assertEqual(rc, 0, out)
                self.assertIn(spec["ok"], out)

    def test_validation_check_remains_a_shallow_preflight(self) -> None:
        spec_dir = self.work_dir() / "spec"
        spec_dir.mkdir(parents=True)
        for name in ("base.tla", "MC.tla", "Trace.tla", "instrumentation-spec.md"):
            (spec_dir / name).touch()

        rc, out = self.run_phase("spec_validation", ["--check", self.artifact_flag(), NAME])

        self.assertEqual(rc, 0, out)
        self.assertIn("specs OK (0L)", out)
        self.assertIn("traces WARN (0 ndjson files)", out)
        self.assertIn("Required path checks passed; review any warnings above.", out)


class TestDryRunCommand(PhaseCase):
    """The dry-run adapter command line + the assembled prompt file."""

    def test_each_phase_command_and_prompt(self) -> None:
        adapter = phaselib.LAUNCH_DIR / "adapters" / "claude-code.sh"
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                # bug_confirmation now defaults to parallel per-finding; the
                # single-agent adapter command this test pins is the
                # --legacy-confirm path (parallel default has its own test below).
                extra = ["--legacy-confirm"] if spec["key"] == "bug_confirmation" else None
                rc, out = self.dry_run(spec, extra=extra)
                self.assertEqual(rc, 0, out)

                wd = self.work_dir()
                log = wd / spec["log"]
                prompt = wd / spec["prompt"]

                # the [DRY RUN] adapter line, piece by piece
                self.assertIn("[DRY RUN]", out)
                self.assertIn(str(adapter), out)
                self.assertIn(f"{spec['flag']}=<prompt>", out)  # --prompt vs --prompt-file quirk
                self.assertIn("--max-turns=0", out)
                self.assertIn("--effort=max", out)  # Claude phase safety default
                self.assertIn(f"--log={log}", out)
                self.assertIn("--background", out)
                self.assertIn(f"Prompt saved: {prompt}", out)

                # the prompt file the agent would receive
                self.assertTrue(prompt.is_file(), "prompt file not written")
                body = prompt.read_text()
                self.assertIn(f"**{spec['skill']}**", body)  # standalone installed skill ID
                self.assertNotIn(f"${spec['skill']}", body)
                self.assertNotIn(f"${CODEX_PLUGIN_NAME}:{spec['skill']}", body)
                self.assertNotIn("<!-- specula-skill:", body)
                self.assertNotIn("/skills/", body)
                self.assertNotIn(".claude/skills", body)
                self.assertIn(str(wd / spec["out"]), body)  # a key output/inputs path

    def test_codex_prompt_materializes_exactly_one_installed_id(self) -> None:
        spec = BY_KEY["code_analysis"]
        for plugin_enabled in (False, True):
            with (
                self.subTest(plugin_enabled=plugin_enabled),
                mock.patch(
                    "specula.skill_refs._codex_plugin_enabled",
                    return_value=plugin_enabled,
                ),
            ):
                rc, out = self.dry_run(spec, extra=["--agent=codex"])
                self.assertEqual(rc, 0, out)
                body = (self.work_dir() / spec["prompt"]).read_text()
                selected = f"${CODEX_PLUGIN_NAME}:{spec['skill']}" if plugin_enabled else f"${spec['skill']}"
                rejected = f"${spec['skill']}" if plugin_enabled else f"${CODEX_PLUGIN_NAME}:{spec['skill']}"
                self.assertIn(selected, body)
                self.assertNotIn(rejected, body)
                self.assertNotIn("<!-- specula-skill:", body)

    def test_local_skill_adapter_prompt_includes_skill_file_path(self) -> None:
        spec = BY_KEY["code_analysis"]
        for adapter in ("opencode", "pi"):
            with self.subTest(adapter=adapter):
                rc, out = self.dry_run(spec, extra=[f"--agent={adapter}"])
                self.assertEqual(rc, 0, out)
                body = (self.work_dir() / spec["prompt"]).read_text()

                self.assertIn("**code-analysis**", body)
                self.assertIn("/skills/code_analysis/SKILL.md", body)
                self.assertIn("read the local Specula skill file", body)
                self.assertNotIn("<!-- specula-skill:", body)

    def test_bug_confirmation_defaults_to_parallel(self) -> None:
        # No --legacy-confirm: Phase 4a runs parallel per-finding confirmation
        # (confirmlib), NOT the single-agent adapter launch.
        rc, out = self.dry_run(BY_KEY["bug_confirmation"])
        self.assertEqual(rc, 0, out)
        self.assertIn("Max parallel: 4", out)
        self.assertIn("Parallel confirmation", out)
        self.assertIn("max_parallel=4", out)
        self.assertNotIn("--background", out)  # not the single-agent _launch command

    def test_bug_confirmation_explicit_one_is_a_hard_limit(self) -> None:
        rc, out = self.dry_run(BY_KEY["bug_confirmation"], extra=["--max-parallel=1"])
        self.assertEqual(rc, 0, out)
        self.assertIn("Max parallel: 1", out)
        self.assertIn("Parallel confirmation", out)
        self.assertIn("max_parallel=1", out)

    def test_bug_confirmation_legacy_default_stays_one(self) -> None:
        rc, out = self.dry_run(BY_KEY["bug_confirmation"], extra=["--legacy-confirm"])
        self.assertEqual(rc, 0, out)
        self.assertIn("Max parallel: 1", out)
        self.assertNotIn("Parallel confirmation", out)

    def test_bug_confirmation_legacy_prompt_has_canonical_report_contract(self) -> None:
        rc, out = self.dry_run(BY_KEY["bug_confirmation"], extra=["--legacy-confirm"])
        self.assertEqual(rc, 0, out)
        body = (self.work_dir() / ".bug-confirmation-prompt.md").read_text()
        self.assertIn("Dispositions: <N> total =", body)
        self.assertIn("<I> incomplete + <DEF> deferred", body)
        self.assertIn("| Bug | Finding | Status |", body)
        self.assertIn("## Bug N: <title>", body)
        self.assertIn("Number sections consecutively from 1", body)
        self.assertIn("exactly one row and one section for each entry", body)

    def test_bug_classification_uses_current_phase4_status_contract(self) -> None:
        rc, out = self.dry_run(BY_KEY["bug_classification"])
        self.assertEqual(rc, 0, out)
        body = (self.work_dir() / ".bug-classification-prompt.md").read_text()
        for status in (
            "REPRODUCED",
            "ENV_LIMITED",
            "MASKED",
            "FALSE POSITIVE",
            "NEEDS MORE INFO",
            "DROPPED",
            "PENDING REPAIR",
            "DEFERRED",
            "INCOMPLETE",
        ):
            self.assertIn(status, body)

        guide = (SRC.parent / "skills" / "bug-classification" / "guide.md").read_text()
        self.assertNotIn("REPRODUCTION FAILED", guide)
        self.assertIn("- Total entries: N", guide)
        self.assertIn("- Reproduced bugs: N", guide)
        self.assertIn("- Findings: N", guide)
        self.assertIn("- No-severity dispositions: N", guide)

    def test_confirmation_docs_have_no_recheck_pass_and_allow_deferred_terminal(self) -> None:
        skill = SRC.parent / "skills" / "bug-confirmation"
        reproduction = (skill / "phases" / "02-reproduction.md").read_text()
        self.assertNotIn("returns it to you in re-check", reproduction)

        repair_format = (skill / "references" / "repair-request-format.md").read_text()
        self.assertIn("OPEN | IN_REPAIR | CONSUMED | DEFERRED", repair_format)
        self.assertIn("| `OPEN` → `DEFERRED` | pipeline orchestrator |", repair_format)
        self.assertIn("Terminal states: `CONSUMED`", repair_format)

    def test_ordinary_phase_default_max_parallel_stays_one(self) -> None:
        rc, out = self.dry_run(BY_KEY["code_analysis"])
        self.assertEqual(rc, 0, out)
        self.assertIn("Max parallel: 1", out)

    def test_bug_confirmation_forwards_max_turns(self) -> None:
        from specula import confirmlib

        seen: list[tuple[int, str]] = []

        def fake_confirmation(cfg: confirmlib.ConfirmConfig) -> int:
            seen.append((cfg.max_parallel, cfg.max_turns))
            return 0

        self.patch_attr(confirmlib, "run_parallel_confirmation", fake_confirmation)
        rc, out = self.dry_run(
            BY_KEY["bug_confirmation"],
            extra=["--max-parallel=1", "--max-turns=7"],
        )
        self.assertEqual(rc, 0, out)
        self.assertEqual(seen, [(1, "7")])

    def test_max_turns_forwarded_verbatim(self) -> None:
        rc, out = self.dry_run(BY_KEY["code_analysis"], extra=["--max-turns=7"])
        self.assertEqual(rc, 0, out)
        self.assertIn("--max-turns=7", out)

    def test_model_effort_and_explicit_empty_visible_in_dry_run(self) -> None:
        rc, out = self.dry_run(
            BY_KEY["code_analysis"],
            extra=["--model=gpt-5.5", "--effort=high"],
        )
        self.assertEqual(rc, 0, out)
        self.assertIn("--model=gpt-5.5", out)
        self.assertIn("--effort=high", out)
        self.assertNotIn("--effort=max", out)

        self.set_env("SPECULA_MODEL", "env-model")
        self.set_env("SPECULA_EFFORT", "low")
        rc, out = self.dry_run(
            BY_KEY["code_analysis"],
            extra=["--model=", "--effort="],
        )
        self.assertEqual(rc, 0, out)
        self.assertIn("--model= ", out)
        self.assertIn("--effort= ", out)
        self.assertNotIn("env-model", out)
        self.assertNotIn("--effort=low", out)
        self.assertNotIn("--effort=max", out)

    def test_bug_classification_rejects_artifact(self) -> None:
        rc, out = self.run_phase("bug_classification", ["--artifact=/x", NAME])
        self.assertEqual(rc, 1)
        self.assertEqual(
            out,
            "ERROR: classify does not accept --artifact; this phase reads the existing "
            ".specula-output/spec/confirmed-bugs.md and does not inspect source code.\n",
        )


class TestRepairMode(PhaseCase):
    """Spec-validation repair mode swaps the prompt template and the log/prompt
    filenames (but keeps the canonical .pid)."""

    def test_spec_validation_repair(self) -> None:
        rc, out = self.dry_run(BY_KEY["spec_validation"], extra=["--repair"])
        self.assertEqual(rc, 0, out)
        wd = self.work_dir()
        self.assertIn(f"--log={wd / 'spec-repair.log'}", out)
        body = (wd / ".spec-repair-prompt.md").read_text()
        self.assertIn("REPAIR MODE", body)
        self.assertIn("request's cited evidence", body)
        self.assertIn("do not optimize merely for making the artifact disappear", body)
        for skill in ("bug-confirmation", "validation-workflow", "tla-trace-workflow", "tla-checking-workflow"):
            self.assertIn(f"**{skill}**", body)
            self.assertNotIn(f"${skill}", body)
            self.assertNotIn(f"${CODEX_PLUGIN_NAME}:{skill}", body)
        self.assertNotIn("<!-- specula-skill:", body)
        self.assertNotIn("/skills/", body)
        self.assertNotIn(".claude/skills", body)


class TestArgErrors(PhaseCase):
    def test_unknown_agent(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--agent=bogus", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown agent 'bogus'", out)

    def test_unknown_option(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--bogus", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown option", out)

    def test_bad_max_parallel(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--max-parallel=abc", self.artifact_flag(), NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Invalid --max-parallel", out)

    def test_nonpositive_max_parallel(self) -> None:
        for value in ("0", "-1"):
            with self.subTest(value=value):
                rc, out = self.run_phase("code_analysis", [f"--max-parallel={value}", self.artifact_flag(), NAME])
                self.assertEqual(rc, 1)
                self.assertIn("expected an integer >= 1", out)

    def test_missing_artifact_directory_is_rejected(self) -> None:
        missing = self.tmp() / "missing"
        rc, out = self.run_phase("code_analysis", ["--check", f"--artifact={missing}", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("--artifact must be an existing directory", out)

    def test_empty_artifact_value_is_rejected(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--check", "--artifact=", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("--artifact must be an existing directory", out)

    def test_artifact_expansion_failure_uses_existing_error_contract(self) -> None:
        with mock.patch.object(Path, "expanduser", side_effect=RuntimeError("home unavailable")):
            rc, out = self.run_phase("code_analysis", ["--check", "--artifact=~/repo", NAME])

        self.assertEqual(rc, 1)
        self.assertEqual(out, "ERROR: --artifact must be an existing directory: ~/repo\n")

    def test_bug_confirmation_rejects_invalid_rounds(self) -> None:
        for value in ("abc", "0", "-1", "6"):
            with self.subTest(value=value):
                rc, out = self.run_phase("bug_confirmation", [f"--rounds={value}", NAME])
                self.assertEqual(rc, 1)
                self.assertIn("Invalid --rounds", out)
                self.assertIn("integer from 1 to 5", out)

    def test_bug_confirmation_accepts_round_five(self) -> None:
        rc, out = self.dry_run(BY_KEY["bug_confirmation"], extra=["--rounds=5"])
        self.assertEqual(rc, 0, out)

    def test_bug_confirmation_rejects_legacy_debate_combination(self) -> None:
        rc, out = self.run_phase("bug_confirmation", ["--legacy-confirm", "--debate", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("--legacy-confirm and --debate cannot be used together", out)

    def test_help_prints_usage(self) -> None:
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                rc, out = self.run_phase(spec["key"], ["--help"])
                self.assertEqual(rc, 0)
                self.assertIn("Usage:", out)
                self.assertIn(f"specula {PUBLIC_COMMANDS[spec['key']]}", out)
                self.assertNotIn("bash scripts/", out)
                self.assertNotIn("launch_", out)
                self.assertIn("--model=NAME", out)
                self.assertIn("--effort=LEVEL", out)


class TestBugConfirmationAlternate(PhaseCase):
    def _patch_confirmation(self, codes: list[int]) -> list[tuple[int, str]]:
        from specula import confirmlib

        calls: list[tuple[int, str]] = []

        def fake_confirmation(cfg: confirmlib.ConfirmConfig) -> int:
            calls.append((cfg.max_parallel, cfg.max_turns))
            return codes[min(len(calls) - 1, len(codes) - 1)]

        self.patch_attr(confirmlib, "run_parallel_confirmation", fake_confirmation)
        return calls

    def test_permanent_failure_propagates(self) -> None:
        calls = self._patch_confirmation([9])
        rc, out = self.dry_run(BY_KEY["bug_confirmation"])
        self.assertEqual(rc, 9, out)
        self.assertEqual(calls, [(4, "0")])

    def test_rate_limit_retries_current_target(self) -> None:
        calls = self._patch_confirmation([quota.RATE_LIMIT_RC, 0])
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        self.set_env("SPECULA_RATE_LIMIT_RETRIES", "1")
        rc, out = self.dry_run(BY_KEY["bug_confirmation"])
        self.assertEqual(rc, 0, out)
        self.assertEqual(len(calls), 2)
        self.assertEqual(waits, [1])
        self.assertIn("Rate limited: waiting before retrying", out)

    def test_rate_limit_retries_are_bounded(self) -> None:
        calls = self._patch_confirmation([quota.RATE_LIMIT_RC])
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        self.set_env("SPECULA_RATE_LIMIT_RETRIES", "1")
        rc, out = self.dry_run(BY_KEY["bug_confirmation"])
        self.assertEqual(rc, quota.RATE_LIMIT_RC, out)
        self.assertEqual(len(calls), 2)
        self.assertEqual(waits, [1])

    def test_successful_live_confirmation_requires_classification_prerequisites(self) -> None:
        from specula import confirmlib

        self.seed(BY_KEY["bug_confirmation"]["inputs"])
        self.patch_attr(phaselib.Phase, "_acceptance", lambda _self, _ws, _names: None)

        def fake_confirmation(cfg: confirmlib.ConfirmConfig) -> int:
            return 0

        self.patch_attr(confirmlib, "run_parallel_confirmation", fake_confirmation)
        rc, out = self.run_phase("bug_confirmation", [self.artifact_flag(), NAME])

        self.assertEqual(rc, 1, out)
        self.assertIn("confirmed-bugs MISSING", out)
        self.assertIn("Handoff validation failures:", out)

    def test_successful_live_confirmation_hands_nonempty_report_to_classification(self) -> None:
        from specula import confirmlib

        self.seed(BY_KEY["bug_confirmation"]["inputs"])
        self.patch_attr(phaselib.Phase, "_acceptance", lambda _self, _ws, _names: None)

        def fake_confirmation(cfg: confirmlib.ConfirmConfig) -> int:
            report = cfg.ws.work_dir(cfg.name) / "spec" / "confirmed-bugs.md"
            report.parent.mkdir(parents=True, exist_ok=True)
            report.write_text("# Confirmed Bugs\n")
            return 0

        self.patch_attr(confirmlib, "run_parallel_confirmation", fake_confirmation)
        rc, out = self.run_phase("bug_confirmation", [self.artifact_flag(), NAME])

        self.assertEqual(rc, 0, out)
        self.assertIn("confirmed-bugs OK", out)


class TestHandoffGate(PhaseCase):
    def setUp(self) -> None:
        super().setUp()
        adapters = self.tmp() / "adapters"
        adapters.mkdir()
        self.patch_attr(phaselib, "LAUNCH_DIR", adapters.parent)
        self.patch_attr(phaselib.Phase, "_acceptance", lambda _self, _ws, _names: None)
        self.set_env("SPECULA_PROGRESS", "off")
        self.adapter = adapters / "fake.sh"

    def write_adapter(self, body: str) -> None:
        self.adapter.write_text("#!/usr/bin/env sh\nset -eu\n" + body)
        self.adapter.chmod(0o755)

    def run_analysis(self, targets: list[str] | None = None) -> tuple[int, str]:
        return self.run_phase(
            "code_analysis",
            [f"--agent={self.adapter.stem}", self.artifact_flag(), *(targets or [NAME])],
        )

    def test_zero_adapter_exit_without_brief_fails_the_analysis_handoff(self) -> None:
        self.write_adapter(":\n")

        rc, out = self.run_analysis()

        self.assertEqual(rc, 1, out)
        self.assertIn("Checking handoff to spec_generation...", out)
        self.assertIn("MISSING modeling-brief.md", out)
        self.assertIn("Handoff validation failures:", out)

    def test_analysis_handoff_reuses_spec_generation_check(self) -> None:
        calls: list[list[str]] = []

        def check(_self: phaselib.SpecGenerationPhase, _ws: phaselib.Workspace, names: list[str]) -> bool:
            calls.append(names)
            return True

        self.patch_attr(phaselib.SpecGenerationPhase, "check", check)
        self.write_adapter(":\n")

        rc, out = self.run_analysis()

        self.assertEqual(rc, 0, out)
        self.assertEqual(calls, [[NAME]])

    def test_handoff_checks_only_successful_targets(self) -> None:
        calls: list[list[str]] = []

        def check(_self: phaselib.SpecGenerationPhase, _ws: phaselib.Workspace, names: list[str]) -> bool:
            calls.append(names)
            return True

        self.patch_attr(phaselib.SpecGenerationPhase, "check", check)
        self.write_adapter('name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n[ "$name" != failed ] || exit 9\n')

        rc, out = self.run_analysis(["failed|g|Go|r", "passed|g|Go|r"])

        self.assertEqual(rc, 9, out)
        self.assertEqual(calls, [["passed"]])

    def test_handoff_failures_are_attributed_per_target(self) -> None:
        self.write_adapter(
            'name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n'
            '[ "$name" != passed ] || printf "brief\\n" > "$SPECULA_WORK_DIR/modeling-brief.md"\n'
        )

        rc, out = self.run_analysis(["missing|g|Go|r", "passed|g|Go|r"])

        self.assertEqual(rc, 1, out)
        self.assertIn("FAILED  missing: next-phase prerequisites not met", out)
        self.assertNotIn("FAILED  passed: next-phase prerequisites not met", out)


class TestLegacyRepairIdentityFinalization(PhaseCase):
    def setUp(self) -> None:
        super().setUp()
        adapters = self.tmp() / "adapters"
        adapters.mkdir()
        self.patch_attr(phaselib, "LAUNCH_DIR", adapters.parent)
        self.patch_attr(phaselib.Phase, "_acceptance", lambda _self, _ws, _names: None)
        self.patch_attr(
            phaselib.Phase,
            "progress_config",
            replace(phaselib.Phase.progress_config, poll_seconds=0.005),
        )
        self.adapter = adapters / "fake.sh"
        self.adapter.write_text(
            "#!/usr/bin/env sh\n"
            "set -eu\n"
            'cp "$LEGACY_REPORT_FIXTURE" "$SPECULA_WORK_DIR/spec/confirmed-bugs.md"\n'
            'if [ "${LEGACY_NO_RR:-0}" != 1 ]; then\n'
            '  mkdir -p "$SPECULA_WORK_DIR/spec/repair-requests"\n'
            '  if [ "${LEGACY_DELETE_RR:-0}" = 1 ]; then rm -f "$SPECULA_WORK_DIR/spec/repair-requests/RR-001.md"; fi\n'
            '  cp "$LEGACY_RR_FIXTURE" "$SPECULA_WORK_DIR/spec/repair-requests/${LEGACY_RR_NAME:-RR-001.md}"\n'
            "fi\n"
            'exit "${LEGACY_ADAPTER_RC:-0}"\n'
        )
        self.adapter.chmod(0o755)
        self.seed(BY_KEY["bug_confirmation"]["inputs"])

    def _legacy_fixture(
        self,
        report: str,
        *,
        emitted_finding_id: str | None = None,
        emitted_rid: str = "RR-001",
    ) -> Path:
        from specula import confirmlib

        rr = confirmlib._merge_rr(
            emitted_rid,
            "Bug 1",
            "fallback.out",
            (
                "---\n"
                "target: SPEC_REPAIR\n"
                "counterexample: spec/output/x.out\n"
                "scope:\n"
                "  actions: [Foo]\n"
                "  invariants: [Inv]\n"
                "  hunt_cfgs: [MC_hunt.cfg]\n"
                "  fault_actions: []\n"
                "---\n\n"
                "## Trigger\n"
                "The counterexample requires a transition the implementation rejects.\n\n"
                "## Evidence\n"
                "The trace disagrees with src/node.py:42.\n"
            ),
            finding_id=emitted_finding_id or "MC-1",
        )
        if emitted_finding_id is None:
            rr = rr.replace("finding_id: MC-1\n", "", 1)
        fixtures = self.tmp()
        report_path = fixtures / "confirmed-bugs.md"
        request_path = fixtures / f"{emitted_rid}.md"
        report_path.write_text(report)
        request_path.write_text(rr)
        self.set_env("LEGACY_REPORT_FIXTURE", str(report_path))
        self.set_env("LEGACY_RR_FIXTURE", str(request_path))
        return request_path

    def _run_legacy(self) -> tuple[int, str]:
        return self.run_phase(
            "bug_confirmation",
            ["--legacy-confirm", f"--agent={self.adapter.stem}", self.artifact_flag(), NAME],
        )

    def _seed_consumed_audit(self) -> tuple[Path, bytes]:
        from specula import confirmlib

        rr_dir = self.work_dir() / "spec" / "repair-requests"
        rr_dir.mkdir(parents=True, exist_ok=True)
        request = rr_dir / "RR-001.md"
        request.write_text(
            confirmlib._merge_rr(
                "RR-001",
                "Bug 7",
                "fallback.out",
                (
                    "---\n"
                    "target: SPEC_REPAIR\n"
                    "counterexample: spec/output/x.out\n"
                    "scope:\n"
                    "  actions: [Foo]\n"
                    "  invariants: [Inv]\n"
                    "  hunt_cfgs: [MC_hunt.cfg]\n"
                    "  fault_actions: []\n"
                    "---\n\n"
                    "## Trigger\n"
                    "Historical trigger.\n\n"
                    "## Evidence\n"
                    "Historical evidence at src/node.py:42.\n"
                ),
                finding_id="MC-1",
                allocation_key="terminal-key",
                status="CONSUMED",
                history=["- immutable consumed audit"],
            )
        )
        return request, request.read_bytes()

    def _seed_active_audit(self) -> tuple[Path, bytes]:
        request, _ = self._seed_consumed_audit()
        request.write_text(request.read_text().replace("status: CONSUMED", "status: OPEN", 1))
        return request, request.read_bytes()

    def test_successful_legacy_phase_enriches_agent_output_with_stable_identity(self) -> None:
        self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: one\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-001)\n"
        )

        rc, out = self._run_legacy()

        self.assertEqual(rc, 0, out)
        request = self.work_dir() / "spec" / "repair-requests" / "RR-001.md"
        text = request.read_text()
        self.assertIn("finding_id: MC-1", text)
        self.assertRegex(text, r"(?m)^allocation_key: [0-9a-f]{64}$")

    def test_ambiguous_legacy_identity_turns_zero_adapter_exit_into_failure(self) -> None:
        original = self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n"
            "| 2 | MC-2 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: one\n\n"
            "- **Finding ID**: MC-1\n\n"
            "## Bug 2: two\n\n"
            "- **Finding ID**: MC-2\n"
        ).read_bytes()

        rc, out = self._run_legacy()

        self.assertEqual(rc, 1, out)
        self.assertIn("legacy repair identity validation FAILED", out)
        self.assertIn("expected exactly one RR-bearing report row, found 2", out)
        self.assertIn("Output validation failures:", out)
        request = self.work_dir() / "spec" / "repair-requests" / "RR-001.md"
        self.assertEqual(request.read_bytes(), original)
        self.assertNotIn("finding_id:", request.read_text())

    def test_legacy_phase_rejects_agent_supplied_finding_id_that_conflicts_with_report(self) -> None:
        self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: one\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-001)\n",
            emitted_finding_id="MC-WRONG",
        )

        rc, out = self._run_legacy()

        self.assertEqual(rc, 1, out)
        self.assertIn("finding_id 'MC-WRONG' conflicts with report identity 'MC-1'", out)

    def test_report_referenced_terminal_rr_cannot_bypass_identity_check(self) -> None:
        request = self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: one\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-001)\n",
            emitted_finding_id="MC-WRONG",
        )
        request.write_text(request.read_text().replace("status: OPEN", "status: CONSUMED", 1))

        rc, out = self._run_legacy()

        self.assertEqual(rc, 1, out)
        self.assertIn("finding_id 'MC-WRONG' conflicts with report identity 'MC-1'", out)

    def test_legacy_report_without_repair_requests_is_a_noop(self) -> None:
        self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | FALSE POSITIVE |\n\n"
            "## Bug 1: one\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: FALSE POSITIVE\n"
        )
        self.set_env("LEGACY_NO_RR", "1")

        rc, out = self._run_legacy()

        self.assertEqual(rc, 0, out)
        self.assertFalse((self.work_dir() / "spec" / "repair-requests").exists())

    def test_legacy_preflight_migrates_old_rr_before_zero_pending_report_overwrite(self) -> None:
        from specula import confirmlib

        work_spec = self.work_dir() / "spec"
        (work_spec / "confirmed-bugs.md").write_text(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: old\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-001)\n"
        )
        rr_dir = work_spec / "repair-requests"
        rr_dir.mkdir()
        request = rr_dir / "RR-001.md"
        request.write_text(
            confirmlib._merge_rr(
                "RR-001",
                "Bug 1",
                "fallback.out",
                (
                    "---\n"
                    "target: SPEC_REPAIR\n"
                    "counterexample: spec/output/x.out\n"
                    "scope:\n"
                    "  actions: [Foo]\n"
                    "  invariants: [Inv]\n"
                    "  hunt_cfgs: [MC_hunt.cfg]\n"
                    "  fault_actions: []\n"
                    "---\n\n"
                    "## Trigger\n"
                    "The counterexample requires an impossible transition.\n\n"
                    "## Evidence\n"
                    "The real guard is at src/node.py:42.\n"
                ),
                finding_id="MC-1",
            ).replace("finding_id: MC-1\n", "", 1)
        )
        self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | FALSE POSITIVE |\n\n"
            "## Bug 1: fresh\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: FALSE POSITIVE\n"
        )
        self.set_env("LEGACY_NO_RR", "1")

        rc, out = self._run_legacy()

        self.assertEqual(rc, 1, out)
        self.assertIn("RR-001 is OPEN but is not linked", out)
        self.assertNotIn("RR-001", (work_spec / "confirmed-bugs.md").read_text())
        migrated = request.read_text()
        self.assertIn("finding_id: MC-1", migrated)
        self.assertRegex(migrated, r"(?m)^allocation_key: [0-9a-f]{64}$")

    def test_failed_legacy_agent_leaves_partial_request_untouched(self) -> None:
        original = self._legacy_fixture(
            "# Confirmed Bugs — footest\n\n"
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: one\n\n"
            "- **Finding ID**: MC-1\n"
        ).read_bytes()
        self.set_env("LEGACY_ADAPTER_RC", "9")

        rc, out = self._run_legacy()

        self.assertEqual(rc, 9, out)
        request = self.work_dir() / "spec" / "repair-requests" / "RR-001.md"
        self.assertEqual(request.read_bytes(), original)
        self.assertNotIn("legacy repair identity validation", out)

    def test_successful_legacy_agent_cannot_overwrite_consumed_audit(self) -> None:
        request, original = self._seed_consumed_audit()
        self._legacy_fixture(
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: fresh\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-001)\n"
        )

        rc, out = self._run_legacy()

        self.assertEqual(rc, 1, out)
        self.assertEqual(request.read_bytes(), original)
        self.assertIn("RR-001 terminal audit was modified, moved, or deleted and was restored", out)
        self.assertIn("Output integrity failures:", out)

    def test_failed_legacy_agent_tamper_is_restored_before_returning_adapter_error(self) -> None:
        request, original = self._seed_consumed_audit()
        self._legacy_fixture(
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-001) |\n\n"
            "## Bug 1: fresh\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-001)\n"
        )
        self.set_env("LEGACY_ADAPTER_RC", "9")

        rc, out = self._run_legacy()

        self.assertEqual(rc, 9, out)
        self.assertEqual(request.read_bytes(), original)
        self.assertIn("RR-001 terminal audit was modified, moved, or deleted and was restored", out)
        self.assertIn("Output integrity failures:", out)

    def test_legacy_agent_cannot_delete_active_id_and_reallocate_same_finding(self) -> None:
        request, original = self._seed_active_audit()
        self._legacy_fixture(
            "| Bug | Finding | Status |\n"
            "|---|---|---|\n"
            "| 1 | MC-1 | PENDING REPAIR (RR-002) |\n\n"
            "## Bug 1: fresh\n\n"
            "- **Finding ID**: MC-1\n"
            "- **Status**: PENDING REPAIR (RR-002)\n",
            emitted_finding_id="MC-1",
            emitted_rid="RR-002",
        )
        self.set_env("LEGACY_DELETE_RR", "1")
        self.set_env("LEGACY_RR_NAME", "RR-002.md")

        rc, out = self._run_legacy()

        self.assertEqual(rc, 1, out)
        self.assertEqual(request.read_bytes(), original)
        self.assertIn("RR-001 active identity was modified, moved, or deleted and was restored", out)


class TestRunAgentBlocking(PhaseCase):
    def test_turn_phase_scopes_stop_gate_sets_cwd_and_removes_stale_log(self) -> None:
        adapter = self.tmp() / "adapter.sh"
        capture = self.tmp() / "capture.txt"
        adapter.write_text(
            "#!/bin/sh\n"
            'printf \'%s\\n\' "$SPECULA_PHASE" "${SPECULA_STOP_GATE-unset}" '
            '"$SPECULA_WORK_DIR" "$SPECULA_STOP_GATE_WORK_DIR" "$PWD" '
            '"${SPECULA_SANDBOX_CONFIG-unset}" "$@" > "$CAPTURE_FILE"\n'
            "exit 9\n"
        )
        adapter.chmod(0o755)
        prompt_file = self.tmp() / "prompt.md"
        log_file = self.tmp() / "turn.log"
        log_file.write_text("stale output\n")
        target_work_dir = self.work_dir()
        target_work_dir.mkdir(parents=True)
        gate_work_dir = self.tmp() / "finding"
        gate_work_dir.mkdir()
        agent_cwd = self.tmp()
        malicious_config = agent_cwd / ".specula" / "sandbox.json"
        malicious_config.parent.mkdir()
        malicious_config.write_text('{"enabled": false}\n')
        self.set_env("CAPTURE_FILE", str(capture))
        self.set_env("SPECULA_STOP_GATE", "on")
        self.set_env("SPECULA_SANDBOX", "on")

        rc, text = phaselib.run_agent_blocking(
            adapter,
            "prompt body",
            prompt_file,
            log_file,
            phase_key="bug_confirmation",
            work_dir=target_work_dir,
            claude_alias="profile",
            gate_work_dir=gate_work_dir,
            cwd=agent_cwd,
            max_turns="7",
        )

        self.assertEqual(rc, 9)
        self.assertEqual(text, "")
        self.assertFalse(log_file.exists())
        recorded = capture.read_text().splitlines()
        self.assertEqual(
            recorded[:5],
            ["bug_confirmation_turn", "on", str(target_work_dir), str(gate_work_dir), str(agent_cwd)],
        )
        trusted_config = Path(recorded[5])
        self.assertTrue(trusted_config.is_absolute())
        self.assertTrue(trusted_config.is_file())
        self.assertNotEqual(trusted_config, malicious_config)
        self.assertIn("--max-turns=7", recorded)

    def test_relative_paths_are_absolutized_before_cwd_switch(self) -> None:
        base = self.tmp()
        adapter = base / "adapter.sh"
        capture = base / "capture.txt"
        adapter.write_text(
            "#!/bin/sh\n"
            'printf \'%s\\n\' "$PWD" "$SPECULA_WORK_DIR" "$SPECULA_STOP_GATE_WORK_DIR" "$@" > "$CAPTURE_FILE"\n'
        )
        adapter.chmod(0o755)
        for directory in ("target", "gate", "agent"):
            (base / directory).mkdir()
        old_cwd = Path.cwd()
        os.chdir(base)
        self.addCleanup(os.chdir, old_cwd)
        self.set_env("CAPTURE_FILE", str(capture))

        rc, _ = phaselib.run_agent_blocking(
            Path("adapter.sh"),
            "prompt body",
            Path("finding/prompt.md"),
            Path("finding/turn.log"),
            phase_key="bug_confirmation",
            work_dir=Path("target"),
            gate_work_dir=Path("gate"),
            cwd=Path("agent"),
            claude_alias="profile",
        )

        self.assertEqual(rc, 0)
        recorded = capture.read_text().splitlines()
        self.assertEqual(recorded[:3], [str(base / "agent"), str(base / "target"), str(base / "gate")])
        self.assertIn(f"--prompt-file={base / 'finding' / 'prompt.md'}", recorded)
        self.assertIn(f"--log={base / 'finding' / 'turn.log'}", recorded)

    def test_opencode_trusted_cwd_synchronizes_real_cwd_and_pwd(self) -> None:
        base = self.tmp()
        adapter = base / "opencode"
        capture = base / "capture.json"
        adapter.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os\n"
            "from pathlib import Path\n"
            "Path(os.environ['CAPTURE_FILE']).write_text("
            "json.dumps({'cwd': os.getcwd(), 'pwd': os.environ.get('PWD')}))\n"
        )
        adapter.chmod(0o755)
        trusted_cwd = base / ".agent-cwd"
        trusted_cwd.mkdir()
        stale_cwd = base / "untrusted-repository"
        stale_cwd.mkdir()
        self.set_env("CAPTURE_FILE", str(capture))
        self.set_env("PWD", str(stale_cwd))

        rc, _ = phaselib.run_agent_blocking(
            adapter,
            "prompt body",
            base / "finding" / "prompt.md",
            base / "finding" / "turn.log",
            phase_key="bug_confirmation",
            work_dir=self.work_dir(),
            cwd=trusted_cwd,
            claude_alias="profile",
        )

        self.assertEqual(rc, 0)
        recorded = json.loads(capture.read_text())
        self.assertEqual(recorded, {"cwd": str(trusted_cwd), "pwd": str(trusted_cwd)})

    def test_codex_returns_final_message_and_keeps_transcript(self) -> None:
        adapter = self.tmp() / "codex.sh"
        adapter.write_text("#!/bin/sh\nexit 0\n")
        adapter.chmod(0o755)
        prompt_file = self.tmp() / "prompt.md"
        log_file = self.tmp() / "turn.log"

        class _Result:
            returncode = 0

        def fake_run(_cmd: list[str], **_kwargs: Any) -> _Result:
            log_file.write_text("Codex CLI transcript\ncommand output\n")
            log_file.with_suffix(".last-message.txt").write_text("VERDICT: REPRODUCED\n")
            return _Result()

        with mock.patch("specula.phaselib.subprocess.run", fake_run):
            rc, text = phaselib.run_agent_blocking(
                adapter,
                "prompt body",
                prompt_file,
                log_file,
                phase_key="bug_confirmation",
                work_dir=self.work_dir(),
                claude_alias="profile",
            )

        self.assertEqual(rc, 0)
        self.assertEqual(text, "VERDICT: REPRODUCED\n")
        self.assertEqual(log_file.read_text(), "Codex CLI transcript\ncommand output\n")

    def test_codex_missing_final_message_does_not_return_transcript(self) -> None:
        adapter = self.tmp() / "codex.sh"
        adapter.write_text("#!/bin/sh\nexit 0\n")
        adapter.chmod(0o755)
        prompt_file = self.tmp() / "prompt.md"
        log_file = self.tmp() / "turn.log"

        class _Result:
            returncode = 0

        def fake_run(_cmd: list[str], **_kwargs: Any) -> _Result:
            log_file.write_text("successful CLI transcript without a final-message sidecar\n")
            return _Result()

        with mock.patch("specula.phaselib.subprocess.run", fake_run):
            rc, text = phaselib.run_agent_blocking(
                adapter,
                "prompt body",
                prompt_file,
                log_file,
                phase_key="bug_confirmation",
                work_dir=self.work_dir(),
                claude_alias="profile",
            )

        self.assertEqual(rc, 0)
        self.assertEqual(text, "")
        self.assertIn("successful CLI transcript", log_file.read_text())

    def test_codex_non_log_suffix_uses_bash_compatible_sidecar(self) -> None:
        adapter = self.tmp() / "codex.sh"
        adapter.write_text("#!/bin/sh\nexit 0\n")
        adapter.chmod(0o755)
        prompt_file = self.tmp() / "prompt.md"
        log_file = self.tmp() / "turn.output"
        last_message_file = Path(str(log_file) + ".last-message.txt")

        class _Result:
            returncode = 0

        def fake_run(_cmd: list[str], **_kwargs: Any) -> _Result:
            log_file.write_text("transcript\n")
            last_message_file.write_text("final answer\n")
            return _Result()

        with mock.patch("specula.phaselib.subprocess.run", fake_run):
            rc, text = phaselib.run_agent_blocking(
                adapter,
                "prompt body",
                prompt_file,
                log_file,
                phase_key="bug_confirmation",
                work_dir=self.work_dir(),
                claude_alias="profile",
            )

        self.assertEqual(rc, 0)
        self.assertEqual(text, "final answer\n")
        self.assertTrue(last_message_file.is_file())

    def test_codex_does_not_reuse_stale_final_message(self) -> None:
        adapter = self.tmp() / "codex.sh"
        adapter.write_text("#!/bin/sh\nexit 9\n")
        adapter.chmod(0o755)
        prompt_file = self.tmp() / "prompt.md"
        log_file = self.tmp() / "turn.log"
        log_file.write_text("old transcript\n")
        log_file.with_suffix(".last-message.txt").write_text("old answer\n")

        rc, text = phaselib.run_agent_blocking(
            adapter,
            "prompt body",
            prompt_file,
            log_file,
            phase_key="bug_confirmation",
            work_dir=self.work_dir(),
            claude_alias="profile",
        )

        self.assertEqual(rc, 9)
        self.assertEqual(text, "")
        self.assertFalse(log_file.with_suffix(".last-message.txt").exists())


class TestProgressReporting(PhaseCase):
    """Portable workspace monitoring plus richer events where supported."""

    def setUp(self) -> None:
        super().setUp()
        adapters = self.tmp() / "adapters"
        adapters.mkdir()
        self.patch_attr(phaselib, "LAUNCH_DIR", adapters.parent)
        self.patch_attr(phaselib.Phase, "_acceptance", lambda _self, _ws, _names: None)
        # These tests exercise process/progress handling, not the analysis or
        # handoff gates. Keep their optional probes out of subprocess accounting.
        self.patch_attr(phaselib.CodeAnalysisPhase, "check", lambda _self, _ws, _names: True)
        self.patch_attr(phaselib.SpecGenerationPhase, "check", lambda _self, _ws, _names: True)
        self.config = ProgressConfig(
            poll_seconds=0.005,
            change_report_seconds=0.0,
            status_after_seconds=0.01,
            status_repeat_seconds=0.01,
            quiet_after_seconds=0.025,
            quiet_repeat_seconds=0.01,
        )
        self.patch_attr(phaselib.Phase, "progress_config", self.config)
        self.adapter = adapters / "fake.sh"

    def write_adapter(self, body: str) -> None:
        self.adapter.write_text("#!/usr/bin/env sh\nset -eu\n" + body)
        self.adapter.chmod(0o755)

    def run_fake(self) -> tuple[int, str]:
        return self.run_phase(
            "code_analysis",
            [f"--agent={self.adapter.stem}", self.artifact_flag(), NAME],
        )

    def test_reports_agent_created_workspace_files(self) -> None:
        self.write_adapter('printf "draft\\n" > "$SPECULA_WORK_DIR/modeling-brief.md"\nsleep 0.04\n')
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: created modeling-brief.md", out)
        self.assertIn(f"{NAME}: completed (exit 0)", out)

    def test_direct_multi_target_command_shares_one_tlc_scope(self) -> None:
        launch_dir = self.tmp()
        capture_dir = self.tmp()
        self.set_env("SPECULA_RUN_DIR", None)
        self.set_env("SPECULA_TLC_SCOPE", None)
        self.write_adapter(
            'name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n'
            f'printf "%s\\n" "$SPECULA_TLC_SCOPE" > "{capture_dir}/$name"\n'
        )
        previous = Path.cwd()
        os.chdir(launch_dir)
        self.addCleanup(os.chdir, previous)

        rc, out = self.run_phase(
            "code_analysis",
            [f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )

        self.assertEqual(rc, 0, out)
        scopes = {(capture_dir / name).read_text().strip() for name in ("a", "b")}
        self.assertEqual(len(scopes), 1)
        self.assertTrue(Path(scopes.pop()).is_absolute())

    def test_direct_phase_restores_isolated_run_tlc_policy(self) -> None:
        capture = self.tmp() / "resources"
        (self.run_dir / "tlc-resources.json").write_text(
            '{"version": 1, "memory_limit": "64G", "worker_limit": "12"}\n'
        )
        self.write_adapter(f'printf "%s\\n" "$SPECULA_TLC_MEMORY_LIMIT" "$SPECULA_TLC_WORKER_LIMIT" > "{capture}"\n')

        rc, out = self.run_fake()

        self.assertEqual(rc, 0, out)
        self.assertEqual(capture.read_text().splitlines(), ["64G", "12"])

    def test_changes_during_cooldown_are_flushed_on_completion(self) -> None:
        self.patch_attr(phaselib.Phase, "progress_config", replace(self.config, change_report_seconds=10.0))
        self.write_adapter(
            'printf "first\\n" > "$SPECULA_WORK_DIR/first.md"\n'
            "sleep 0.03\n"
            'printf "second\\n" > "$SPECULA_WORK_DIR/second.md"\n'
            "sleep 0.03\n"
        )
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn("first.md", out)
        self.assertIn("second.md", out)

    def test_sustained_agent_output_gets_sparse_status(self) -> None:
        self.write_adapter(
            'printf "starting\\n" > "$SPECULA_WORK_DIR/agent.log"\n'
            "sleep 0.02\n"
            'printf "working\\n" >> "$SPECULA_WORK_DIR/agent.log"\n'
            "sleep 0.02\n"
        )
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: agent output is active", out)
        self.assertIn(f"{NAME}: agent output is still active", out)

    def test_codex_stream_events_are_shown_in_cli_output(self) -> None:
        self.adapter = self.adapter.with_name("codex.sh")
        events = [
            json.dumps(
                {
                    "type": "item.started",
                    "item": {
                        "type": "command_execution",
                        "command": "/bin/bash -lc rg editorRefreshScreen kilo.c",
                    },
                }
            ),
            json.dumps(
                {
                    "type": "item.completed",
                    "item": {"type": "agent_message", "text": "I am tracing editor state."},
                }
            ),
        ]
        self.write_adapter(
            f"printf '%s\\n' {' '.join(shlex.quote(event) for event in events)} "
            '> "$SPECULA_ACTIVITY_LOG"\n'
            "sleep 0.04\n"
        )
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: running rg editorRefreshScreen kilo.c", out)
        self.assertIn(f"{NAME}: I am tracing editor state.", out)

    def test_claude_stream_events_are_shown_in_cli_output(self) -> None:
        self.adapter = self.adapter.with_name("claude-code.sh")
        event = json.dumps(
            {
                "type": "assistant",
                "message": {
                    "content": [
                        {"type": "text", "text": "Inspecting editor state."},
                        {"type": "tool_use", "name": "Read", "input": {"file_path": "kilo.c"}},
                    ]
                },
            }
        )
        self.write_adapter(f"printf '%s\\n' {shlex.quote(event)} > \"$SPECULA_ACTIVITY_LOG\"\nsleep 0.04\n")
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: Inspecting editor state.", out)
        self.assertIn(f"{NAME}: reading kilo.c", out)

    def test_copilot_stream_events_are_shown_in_cli_output(self) -> None:
        self.adapter = self.adapter.with_name("copilot-cli.sh")
        events = [
            json.dumps({"type": "assistant.message", "data": {"content": "Tracing input handling."}}),
            json.dumps(
                {
                    "type": "tool.execution_start",
                    "data": {"toolName": "bash", "arguments": {"command": "rg editorReadKey kilo.c"}},
                }
            ),
        ]
        self.write_adapter(
            f"printf '%s\\n' {' '.join(shlex.quote(event) for event in events)} "
            '> "$SPECULA_ACTIVITY_LOG"\n'
            "sleep 0.04\n"
        )
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: Tracing input handling.", out)
        self.assertIn(f"{NAME}: running rg editorReadKey kilo.c", out)

    def test_structured_adapter_errors_are_shown_in_cli_output(self) -> None:
        self.adapter = self.adapter.with_name("copilot-cli.sh")
        event = json.dumps({"type": "session.error", "data": {"message": "BYOK providers require an explicit model."}})
        self.write_adapter(f"printf '%s\\n' {shlex.quote(event)} > \"$SPECULA_ACTIVITY_LOG\"\nexit 1\n")
        rc, out = self.run_fake()
        self.assertEqual(rc, 1, out)
        self.assertIn(f"{NAME}: adapter error: BYOK providers require an explicit model.", out)
        self.assertIn(f"FAILED  {NAME}: adapter exited 1", out)

    def test_quiet_liveness_is_sparse_and_can_be_disabled(self) -> None:
        self.write_adapter("sleep 0.06\n")
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: no observable activity", out)
        self.assertIn(f"{NAME}: quiet for", out)

        self.set_env("SPECULA_PROGRESS", "off")
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertNotIn(f"{NAME}: no observable activity", out)
        self.assertNotIn(f"{NAME}: quiet for", out)
        self.assertNotIn(f"{NAME}: completed (exit", out)

    def test_progress_off_is_a_full_opt_out_not_a_mute(self) -> None:
        # off must also restore the adapters' legacy argv: without the sidecar env
        # they stay on --output-format json. It is the only escape hatch for a CLI
        # that predates the streaming flags, and adapter failures now abort the run.
        seen = self.work_dir() / "seen-env"
        self.write_adapter(f'printf "%s\\n" "${{SPECULA_ACTIVITY_LOG:-<unset>}}" > "{seen}"\n')

        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertTrue(seen.read_text().strip().endswith(".activity.jsonl"), seen.read_text())

        self.set_env("SPECULA_PROGRESS", "off")
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertEqual(seen.read_text().strip(), "<unset>")

    def test_progress_off_ignores_an_inherited_activity_log(self) -> None:
        seen = self.work_dir() / "seen-env"
        self.set_env("SPECULA_PROGRESS", "off")
        self.set_env("SPECULA_ACTIVITY_LOG", "/tmp/leaked.jsonl")
        self.write_adapter(f'printf "%s\\n" "${{SPECULA_ACTIVITY_LOG:-<unset>}}" > "{seen}"\n')
        rc, out = self.run_fake()
        self.assertEqual(rc, 0, out)
        self.assertEqual(seen.read_text().strip(), "<unset>")

    def test_sigterm_reaches_the_agent_cleanup_path(self) -> None:
        # agents live in their own session now, so a `kill <launcher>` that does
        # not unwind through run()'s cleanup would orphan them
        previous = signal.getsignal(signal.SIGTERM)
        with self.assertRaises(SystemExit) as ctx, phaselib._cleanup_on_signal():
            self.assertIsNot(signal.getsignal(signal.SIGTERM), previous)  # armed before we fire
            os.kill(os.getpid(), signal.SIGTERM)
            for _ in range(200):  # the handler runs at the next bytecode boundary
                time.sleep(0.005)
        self.assertEqual(ctx.exception.code, 128 + signal.SIGTERM)
        self.assertIs(signal.getsignal(signal.SIGTERM), previous)

    def test_interrupt_cleanup_terminates_agent_process_group(self) -> None:
        proc = subprocess.Popen(["sh", "-c", "sleep 30"], start_new_session=True)

        def cleanup() -> None:
            if proc.poll() is None:
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()

        self.addCleanup(cleanup)
        root = self.work_dir()
        root.mkdir(parents=True, exist_ok=True)
        agent = RunningAgent(
            name=NAME,
            proc=proc,
            work_dir=root,
            log=root / "agent.log",
            activity_log=root / "agent.activity.jsonl",
            ignored=set(),
            snapshot={},
            reported_snapshot={},
            last_observed_at=0.0,
            log_stamp=None,
            activity_stamp=None,
            adapter_name="fake",
        )
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            phaselib.Phase._terminate_agents([agent])
        self.assertIsNotNone(proc.poll())
        self.assertIn("stopping 1 agent", output.getvalue())

    @unittest.skipUnless(Path("/proc").is_dir(), "requires procfs")
    def test_cleanup_kills_descendant_after_group_leader_exits(self) -> None:
        child_code = (
            "import os,signal,time; "
            "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
            "print(os.getpid(), flush=True); time.sleep(30)"
        )
        parent_code = (
            "import subprocess,sys,time; "
            "child=subprocess.Popen([sys.executable,'-c',sys.argv[1]], stdout=subprocess.PIPE, text=True); "
            "print(child.stdout.readline().strip(), flush=True); time.sleep(30)"
        )
        proc = subprocess.Popen(
            [sys.executable, "-c", parent_code, child_code],
            stdout=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        assert proc.stdout is not None
        child_pid = int(proc.stdout.readline())
        self.patch_attr(phaselib, "AGENT_TERMINATION_GRACE_SECONDS", 0.05)
        root = self.work_dir()
        root.mkdir(parents=True, exist_ok=True)
        agent = RunningAgent(
            name=NAME,
            proc=proc,  # type: ignore[arg-type]  # text mode does not affect process-group operations
            work_dir=root,
            log=root / "agent.log",
            activity_log=root / "agent.activity.jsonl",
            ignored=set(),
            snapshot={},
            reported_snapshot={},
            last_observed_at=0.0,
            log_stamp=None,
            activity_stamp=None,
            adapter_name="fake",
        )
        try:
            phaselib.Phase._terminate_agents([agent], announce=False)
            deadline = time.time() + 1.0
            while Path(f"/proc/{child_pid}/status").exists() and time.time() < deadline:
                status = Path(f"/proc/{child_pid}/status").read_text(errors="replace")
                if "State:\tZ" in status:
                    break
                time.sleep(0.01)
            status_path = Path(f"/proc/{child_pid}/status")
            self.assertTrue(
                not status_path.exists() or "State:\tZ" in status_path.read_text(errors="replace"),
                "SIGTERM-ignoring descendant remained active",
            )
        finally:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(proc.pid, signal.SIGKILL)
            with contextlib.suppress(subprocess.TimeoutExpired):
                proc.wait(timeout=1)

    def test_cleanup_still_signals_when_progress_output_is_closed(self) -> None:
        class BrokenOutput(io.StringIO):
            def write(self, value: str) -> int:
                raise BrokenPipeError

        proc = subprocess.Popen(["sleep", "30"], start_new_session=True)
        self.patch_attr(phaselib, "AGENT_TERMINATION_GRACE_SECONDS", 0.05)
        root = self.work_dir()
        root.mkdir(parents=True, exist_ok=True)
        agent = RunningAgent(
            name=NAME,
            proc=proc,
            work_dir=root,
            log=root / "agent.log",
            activity_log=root / "agent.activity.jsonl",
            ignored=set(),
            snapshot={},
            reported_snapshot={},
            last_observed_at=0.0,
            log_stamp=None,
            activity_stamp=None,
            adapter_name="fake",
        )
        with contextlib.redirect_stdout(BrokenOutput()):
            phaselib.Phase._terminate_agents([agent])
        self.assertIsNotNone(proc.poll())

    def test_cleanup_reaps_leader_after_process_group_disappears(self) -> None:
        class ExitedProc:
            pid = 12345
            waits = 0

            def wait(self, timeout: float | None = None) -> int:
                self.waits += 1
                return 0

        proc = ExitedProc()
        self.patch_attr(phaselib.Phase, "_group_exists", staticmethod(lambda _pgid: False))
        root = self.work_dir()
        agent = RunningAgent(
            name=NAME,
            proc=proc,  # type: ignore[arg-type]
            work_dir=root,
            log=root / "agent.log",
            activity_log=root / "agent.activity.jsonl",
            ignored=set(),
            snapshot={},
            reported_snapshot={},
            last_observed_at=0.0,
            log_stamp=None,
            activity_stamp=None,
            adapter_name="fake",
        )
        phaselib.Phase._terminate_agents([agent], announce=False)
        self.assertEqual(proc.waits, 1)

    def test_final_event_is_drained_when_reaper_first_observes_completion(self) -> None:
        root = self.work_dir()
        root.mkdir(parents=True, exist_ok=True)
        activity = root / "agent.activity.jsonl"
        activity.write_text("")
        proc = subprocess.Popen(["true"], start_new_session=True)
        proc.wait()
        agent = RunningAgent(
            name=NAME,
            proc=proc,
            work_dir=root,
            log=root / "agent.log",
            activity_log=activity,
            ignored=set(),
            snapshot={},
            reported_snapshot={},
            last_observed_at=time.monotonic(),
            log_stamp=None,
            activity_stamp=progress_module.file_stamp(activity),
            adapter_name="codex",
        )
        activity.write_text(json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "final"}}))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            live, completed = phaselib.Phase()._reap_agents([agent], show_progress=True)
        self.assertEqual(live, [])
        self.assertEqual(completed[0][1], 0)
        self.assertIn(f"{NAME}: final", output.getvalue())
        self.assertIn(f"{NAME}: completed (exit 0)", output.getvalue())

    def test_post_spawn_pid_write_failure_cleans_up_unregistered_agent(self) -> None:
        self.write_adapter("sleep 30\n")
        pid_path = self.work_dir() / "agent.pid"
        pid_path.mkdir(parents=True)
        spawned: list[subprocess.Popen[bytes]] = []
        real_popen = subprocess.Popen

        def recording_popen(*args: Any, **kwargs: Any) -> subprocess.Popen[bytes]:
            proc = cast("subprocess.Popen[bytes]", real_popen(*args, **kwargs))
            spawned.append(proc)
            return proc

        self.patch_attr(subprocess, "Popen", recording_popen)
        with self.assertRaises(IsADirectoryError):
            self.run_fake()
        self.assertEqual(len(spawned), 1)
        self.assertIsNotNone(spawned[0].poll())
        self.assertFalse(phaselib.Phase._group_exists(spawned[0].pid))

    def test_post_spawn_agent_construction_failure_cleans_up_process(self) -> None:
        class ConstructionFailure(Exception):
            pass

        self.write_adapter("sleep 30\n")
        spawned: list[subprocess.Popen[bytes]] = []
        real_popen = subprocess.Popen

        def recording_popen(*args: Any, **kwargs: Any) -> subprocess.Popen[bytes]:
            proc = cast("subprocess.Popen[bytes]", real_popen(*args, **kwargs))
            spawned.append(proc)
            return proc

        def fail_construction(*args: Any, **kwargs: Any) -> RunningAgent:
            raise ConstructionFailure

        self.patch_attr(subprocess, "Popen", recording_popen)
        self.patch_attr(progress_module, "RunningAgent", fail_construction)
        self.patch_attr(phaselib, "AGENT_TERMINATION_GRACE_SECONDS", 0.05)
        with self.assertRaises(ConstructionFailure):
            self.run_fake()
        self.assertEqual(len(spawned), 1)
        self.assertIsNotNone(spawned[0].poll())
        self.assertFalse(phaselib.Phase._group_exists(spawned[0].pid))

    def test_rate_limit_retries_only_the_failed_target(self) -> None:
        marker = self.tmp() / "limited-once"
        counts = self.tmp()
        self.write_adapter(
            'name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n'
            f'printf x >> "{counts}/$name"\n'
            f'if [ "$name" = b ] && [ ! -e "{marker}" ]; then touch "{marker}"; exit 75; fi\n'
        )
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        self.set_env("SPECULA_RATE_LIMIT_RETRIES", "2")
        rc, out = self.run_phase(
            "code_analysis",
            ["--max-parallel=1", f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )
        self.assertEqual(rc, 0, out)
        self.assertEqual((counts / "a").read_text(), "x")
        self.assertEqual((counts / "b").read_text(), "xx")
        self.assertEqual(waits, [1])

    def test_all_agents_launched_is_announced_after_pending_is_empty(self) -> None:
        self.write_adapter("sleep 0.02\n")
        rc, out = self.run_phase(
            "code_analysis",
            ["--max-parallel=1", f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )
        self.assertEqual(rc, 0, out)
        self.assertLess(out.index("Launching agent: b"), out.index("All agents launched. Waiting..."))

    def test_rate_limit_stops_launching_unstarted_targets_without_reactive_retry(self) -> None:
        counts = self.tmp()
        self.write_adapter(
            'name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n'
            f'printf x >> "{counts}/$name"\n'
            '[ "$name" != a ] || exit 75\n'
        )
        rc, out = self.run_phase(
            "code_analysis",
            ["--max-parallel=1", f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )
        self.assertEqual(rc, quota.RATE_LIMIT_RC, out)
        self.assertEqual((counts / "a").read_text(), "x")
        self.assertFalse((counts / "b").exists())
        self.assertIn("skipping 1 unstarted target(s): b", out)
        self.assertNotIn("All agents launched. Waiting...", out)

    def test_rate_limit_retries_are_bounded_per_target(self) -> None:
        count = self.tmp() / "count"
        self.write_adapter(f'printf x >> "{count}"\nexit 75\n')
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        self.set_env("SPECULA_RATE_LIMIT_RETRIES", "1")
        rc, out = self.run_fake()
        self.assertEqual(rc, quota.RATE_LIMIT_RC, out)
        self.assertEqual(count.read_text(), "xx")
        self.assertEqual(waits, [1])

    def test_exhausted_rate_limit_reports_unstarted_targets(self) -> None:
        counts = self.tmp()
        self.write_adapter(
            'name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n'
            f'printf x >> "{counts}/$name"\n'
            '[ "$name" != a ] || exit 75\n'
        )
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        self.set_env("SPECULA_RATE_LIMIT_RETRIES", "1")
        rc, out = self.run_phase(
            "code_analysis",
            ["--max-parallel=1", f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )
        self.assertEqual(rc, quota.RATE_LIMIT_RC, out)
        self.assertEqual((counts / "a").read_text(), "xx")
        self.assertFalse((counts / "b").exists())
        self.assertEqual(waits, [1])
        self.assertIn("skipping 1 unstarted target(s): b", out)

    def test_concurrent_permanent_failure_prevents_rate_limit_retry(self) -> None:
        self.write_adapter('name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n[ "$name" = a ] && exit 75\nexit 9\n')
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        rc, out = self.run_phase(
            "code_analysis",
            ["--max-parallel=2", f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )
        self.assertEqual(rc, 9, out)
        self.assertEqual(waits, [])

    def test_permanent_failure_does_not_skip_independent_pending_targets(self) -> None:
        counts = self.tmp()
        self.write_adapter(
            'name=$(basename "$(dirname "$SPECULA_WORK_DIR")")\n'
            f'printf x >> "{counts}/$name"\n'
            '[ "$name" != a ] || exit 9\n'
        )
        rc, out = self.run_phase(
            "code_analysis",
            ["--max-parallel=1", f"--agent={self.adapter.stem}", self.artifact_flag(), "a|g|Go|r", "b|g|Go|r"],
        )
        self.assertEqual(rc, 9, out)
        self.assertEqual((counts / "a").read_text(), "x")
        self.assertEqual((counts / "b").read_text(), "x")

    def test_permanent_failure_takes_precedence_over_rate_limit(self) -> None:
        self.assertEqual(phaselib.Phase._failure_code([("limited", 75), ("broken", 9)]), 9)


class TestSummarize(PhaseCase):
    """The post-launch Results block each phase prints. Dry-run/--check return
    before the launch loop, so nothing else reaches summarize(); these seed the
    output files and call it directly (no agent). Replaces the retired summary_*
    goldens, incl. the non-UTF-8 _wc_l byte-count case."""

    class Case(TypedDict):
        name: str
        phase: str
        files: dict[str, str | bytes]
        want: list[str]

    CASES: list[Case] = [
        {
            "name": "code_analysis/brief",
            "phase": "code_analysis",
            "files": {"modeling-brief.md": "a\nb\nc\n"},
            "want": [f"OK  {NAME} -> modeling-brief.md (3 lines)"],
        },
        {
            "name": "code_analysis/report-only",
            "phase": "code_analysis",
            "files": {"analysis-report.md": "x\ny\n"},
            "want": [f"~~  {NAME} -> analysis-report.md only (2 lines, no modeling brief)"],
        },
        {
            "name": "code_analysis/none",
            "phase": "code_analysis",
            "files": {},
            "want": [f"--  {NAME} (no output)"],
        },
        {
            # _wc_l counts \n by bytes (wc -l): a \xff line with no trailing newline
            # must count, not crash. Replaces summary_code_analysis_nonutf8.
            "name": "code_analysis/nonutf8-bytes",
            "phase": "code_analysis",
            "files": {"modeling-brief.md": b"line1\n\xff\xfe line2 no newline"},
            "want": [f"OK  {NAME} -> modeling-brief.md (1 lines)"],
        },
        {
            "name": "spec_generation/complete",
            "phase": "spec_generation",
            "files": {f"spec/{f}": "l1\nl2\n" for f in ("base.tla", "MC.tla", "Trace.tla", "instrumentation-spec.md")},
            "want": [f"OK  {NAME} -> 4/4 files (base.tla: 2 lines)"],
        },
        {
            "name": "spec_generation/incomplete",
            "phase": "spec_generation",
            "files": {"spec/MC.tla": "x\n"},
            "want": [f"~~  {NAME} -> 1/4 files (incomplete)", "missing: base.tla"],
        },
        {
            "name": "harness_generation/run+traces",
            "phase": "harness_generation",
            "files": {"harness/run.sh": "#!/bin/sh\n", "traces/t1.ndjson": "{}\n"},
            "want": [f"OK  {NAME} -> run.sh: yes, traces: 1", "warning: missing INSTRUMENTATION.md"],
        },
        {
            "name": "harness_generation/none",
            "phase": "harness_generation",
            "files": {},
            "want": [f"--  {NAME} (no harness output)"],
        },
        {
            "name": "spec_validation/changelog",
            "phase": "spec_validation",
            "files": {"spec/changelog.md": "c1\nc2\nc3\n"},
            "want": [f"{NAME}: changelog written (3 lines)"],
        },
        {
            "name": "spec_validation/empty-changelog",
            "phase": "spec_validation",
            "files": {"spec/changelog.md": ""},
            "want": [f"{NAME}: changelog empty (check log)"],
        },
        {
            "name": "bug_confirmation/repro-count",
            "phase": "bug_confirmation",
            "files": {
                "spec/confirmed-bugs.md": "b1\nb2\n",
                "repro/test_bug1.py": "assert True\n",
                "repro/nested/test_bug2.py": "assert True\n",
            },
            "want": [f"{NAME}: confirmed-bugs.md written (2 lines, repro/ tests: 2)"],
        },
        {
            "name": "bug_classification/severity",
            "phase": "bug_classification",
            "files": {
                "spec/bug-severity.md": (
                    "- Total entries: 9\n"
                    "- Reproduced bugs: 2\n"
                    "- Findings: 2\n"
                    "- Critical: 1\n"
                    "- High: 1\n"
                    "- Medium: 1\n"
                    "- Low: 1\n"
                    "- No-severity dispositions: 5\n"
                )
            },
            "want": [f"{NAME}: entries=9  bugs=2 findings=2  C=1 H=1 M=1 L=1  dispositions=5"],
        },
        {
            "name": "bug_classification/no-report",
            "phase": "bug_classification",
            "files": {},
            "want": [f"{NAME}: (no report — check log)"],
        },
    ]

    def test_results_block(self) -> None:
        for i, tc in enumerate(self.CASES):
            with self.subTest(tc["name"]):
                name = f"t{i}"  # fresh work dir per case so seeds don't leak
                for rel, content in tc["files"].items():
                    p = self.work_dir(name) / rel
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_bytes(content) if isinstance(content, bytes) else p.write_text(content)
                buf = io.StringIO()
                with contextlib.redirect_stdout(buf):
                    phaselib.PHASES[tc["phase"]].summarize(phaselib.Workspace([name]), [name])
                got = buf.getvalue()
                for want in tc["want"]:
                    self.assertIn(want.replace(NAME, name), got)


class TestModelEffortLiveLaunch(PhaseCase):
    """Normal batch launch path (the non-blocking sibling of confirmation)."""

    def setUp(self) -> None:
        super().setUp()
        self.adapters = self.tmp() / "adapters"
        self.adapters.mkdir()
        self.patch_attr(phaselib, "LAUNCH_DIR", self.adapters.parent)
        self.patch_attr(phaselib.Phase, "_acceptance", lambda _self, _ws, _names: None)
        self.patch_attr(phaselib.SpecGenerationPhase, "check", lambda _self, _ws, _names: True)
        self.set_env("SPECULA_PROGRESS", "off")

    def launch(self, adapter_name: str, extra: list[str] | None = None) -> list[str]:
        record = self.tmp() / "argv"
        adapter = self.adapters / f"{adapter_name}.sh"
        adapter.write_text(f'#!/usr/bin/env sh\nprintf "%s\\n" "$@" > "{record}"\n')
        adapter.chmod(0o755)
        rc, out = self.run_phase(
            "code_analysis",
            [f"--agent={adapter_name}", *(extra or []), self.artifact_flag(), NAME],
        )
        self.assertEqual(rc, 0, out)
        return record.read_text().splitlines()

    def test_claude_default_max_blocks_ambient_downgrade(self) -> None:
        self.set_env("CLAUDE_EFFORT", "low")
        argv = self.launch("claude-code")
        self.assertIn("--effort=max", argv)

    def test_non_claude_adapters_have_no_forced_effort(self) -> None:
        for adapter in ("codex", "copilot-cli"):
            with self.subTest(adapter=adapter):
                argv = self.launch(adapter)
                self.assertFalse(any(a.startswith("--effort=") for a in argv))

    def test_specula_env_and_explicit_empty_precedence(self) -> None:
        self.set_env("SPECULA_MODEL", "env-model")
        self.set_env("SPECULA_EFFORT", "high")
        argv = self.launch("codex")
        self.assertIn("--model=env-model", argv)
        self.assertIn("--effort=high", argv)

        argv = self.launch("claude-code", ["--model=", "--effort="])
        self.assertIn("--model=", argv)
        self.assertIn("--effort=", argv)
        self.assertNotIn("--effort=max", argv)
        self.assertNotIn("--model=env-model", argv)
        self.assertNotIn("--effort=high", argv)


class TestReviewPhase(PhaseCase):
    """The review agent overrides run() wholesale; its contract is the prompt it
    assembles (no --dry-run, so drive the pure builders directly to stay off the
    network) plus its arg validation."""

    def review(self) -> phaselib.ReviewPhase:
        return phaselib.ReviewPhase()

    def install_adapter(self, name: str, body: str) -> Path:
        adapters = self.tmp() / "adapters"
        adapters.mkdir()
        self.patch_attr(phaselib, "LAUNCH_DIR", adapters.parent)
        adapter = adapters / f"{name}.sh"
        adapter.write_text("#!/usr/bin/env sh\nset -eu\n" + body)
        adapter.chmod(0o755)
        return adapter

    def test_analysis_prompt_contract(self) -> None:
        wd = self.work_dir()
        body = self.review()._analysis_prompt(wd, NAME)
        self.assertIn(f"Write your review to: {wd}/review-analysis.md", body)
        self.assertIn(str(wd / "modeling-brief.md"), body)
        self.assertIn("## Overall: X/35", body)

    def test_specgen_prompt_contract(self) -> None:
        wd = self.work_dir()
        body = self.review()._specgen_prompt(wd, NAME)
        self.assertIn(str(wd / "spec" / "review-specgen.md"), body)
        self.assertIn(str(wd / "spec" / "base.tla"), body)
        self.assertIn("## Overall: X/40", body)

    def test_validation_prompt_contract(self) -> None:
        wd = self.work_dir()
        body = self.review()._validation_prompt(wd, NAME)
        self.assertIn(str(wd / "spec" / "review-validation.md"), body)
        self.assertIn("Ready for trace validation", body)

    def test_requires_phase_and_targets(self) -> None:
        for argv in ([], ["analysis"]):  # no phase / no targets
            with self.subTest(argv=argv):
                rc, out = self.run_phase("review", argv)
                self.assertEqual(rc, 1)
                self.assertIn("review <analysis|specgen|validation>", out)

    def test_unknown_agent(self) -> None:
        rc, out = self.run_phase("review", ["analysis", "--agent=bogus", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown agent 'bogus'", out)

    def test_help(self) -> None:
        for argv in (["--help"], ["-h"], ["analysis", "--help"], ["analysis", "-h"]):
            with self.subTest(argv=argv):
                rc, out = self.run_phase("review", argv)
                self.assertEqual(rc, 0)
                self.assertIn("Run a review agent", out)
                self.assertIn("specula review <phase>", out)
                self.assertIn("--model=NAME", out)
                self.assertIn("--effort=LEVEL", out)
                self.assertIn(".specula-output/review-analysis.md", out)
                self.assertIn(".specula-output/spec/review-specgen.md", out)
                self.assertIn(".specula-output/spec/review-validation.md", out)

    def test_review_streams_activity_through_shared_monitor(self) -> None:
        event = json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "reviewing"}})
        self.install_adapter("codex", f"printf '%s\\n' {shlex.quote(event)} > \"$SPECULA_ACTIVITY_LOG\"\n")
        self.patch_attr(
            phaselib.Phase,
            "progress_config",
            ProgressConfig(poll_seconds=0.005, change_report_seconds=0.0),
        )
        rc, out = self.run_phase("review", ["analysis", "--agent=codex", NAME])
        self.assertEqual(rc, 0, out)
        self.assertIn(f"{NAME}: reviewing", out)
        pid = self.work_dir() / "review-analysis.pid"
        self.assertTrue(pid.read_text().strip().isdigit())
        self.assertTrue((self.work_dir() / "review-analysis.activity.jsonl").is_file())

    def test_review_progress_off_restores_legacy_adapter_contract(self) -> None:
        seen = self.tmp() / "seen"
        self.install_adapter("fake", f'printf "%s\\n" "${{SPECULA_ACTIVITY_LOG:-<unset>}}" > "{seen}"\n')
        self.set_env("SPECULA_PROGRESS", "off")
        rc, out = self.run_phase("review", ["analysis", "--agent=fake", NAME])
        self.assertEqual(rc, 0, out)
        self.assertEqual(seen.read_text().strip(), "<unset>")
        self.assertFalse((self.work_dir() / "review-analysis.activity.jsonl").exists())

    def test_review_exports_external_workspace_to_adapter(self) -> None:
        seen = self.tmp() / "work-dir"
        self.install_adapter("fake", f'printf "%s\\n" "$SPECULA_WORK_DIR" > "{seen}"\n')
        self.set_env("SPECULA_PROGRESS", "off")
        rc, out = self.run_phase("review", ["analysis", "--agent=fake", NAME])
        self.assertEqual(rc, 0, out)
        self.assertEqual(seen.read_text().strip(), str(self.work_dir()))

    def test_review_claude_default_max_blocks_ambient_downgrade(self) -> None:
        seen = self.tmp() / "argv"
        self.install_adapter("claude-code", f'printf "%s\\n" "$@" > "{seen}"\n')
        self.set_env("SPECULA_PROGRESS", "off")
        self.set_env("CLAUDE_EFFORT", "low")
        rc, out = self.run_phase("review", ["analysis", NAME])
        self.assertEqual(rc, 0, out)
        self.assertIn("--effort=max", seen.read_text().splitlines())

    def test_review_explicit_empty_clears_specula_env(self) -> None:
        seen = self.tmp() / "argv"
        self.install_adapter("claude-code", f'printf "%s\\n" "$@" > "{seen}"\n')
        self.set_env("SPECULA_PROGRESS", "off")
        self.set_env("SPECULA_MODEL", "env-model")
        self.set_env("SPECULA_EFFORT", "high")
        rc, out = self.run_phase("review", ["analysis", "--model=", "--effort=", NAME])
        self.assertEqual(rc, 0, out)
        argv = seen.read_text().splitlines()
        self.assertIn("--model=", argv)
        self.assertIn("--effort=", argv)
        self.assertNotIn("--model=env-model", argv)
        self.assertNotIn("--effort=high", argv)
        self.assertNotIn("--effort=max", argv)

    def test_review_rate_limit_retries_only_current_target(self) -> None:
        count = self.tmp() / "count"
        self.install_adapter(
            "fake",
            f'printf x >> "{count}"\n[ "$(wc -c < "{count}")" -gt 1 ] || exit 75\n',
        )
        waits: list[int] = []
        self.patch_attr(phaselib.Phase, "_wait_for_rate_limit", lambda _self: waits.append(1))
        self.set_env("SPECULA_RATE_LIMIT_REACTIVE", "1")
        self.set_env("SPECULA_RATE_LIMIT_RETRIES", "2")
        rc, out = self.run_phase("review", ["analysis", "--agent=fake", NAME])
        self.assertEqual(rc, 0, out)
        self.assertEqual(count.read_text(), "xx")
        self.assertEqual(waits, [1])

    def test_review_normalizes_signal_exit_status(self) -> None:
        self.install_adapter("fake", "kill -TERM $$\n")
        self.set_env("SPECULA_PROGRESS", "off")
        rc, out = self.run_phase("review", ["analysis", "--agent=fake", NAME])
        self.assertEqual(rc, 128 + signal.SIGTERM, out)

    def test_review_construction_failure_cleans_up_process(self) -> None:
        class ConstructionFailure(Exception):
            pass

        self.install_adapter("fake", "sleep 30\n")
        spawned: list[subprocess.Popen[bytes]] = []
        real_popen = subprocess.Popen

        def recording_popen(*args: Any, **kwargs: Any) -> subprocess.Popen[bytes]:
            proc = cast("subprocess.Popen[bytes]", real_popen(*args, **kwargs))
            spawned.append(proc)
            return proc

        def fail_construction(*args: Any, **kwargs: Any) -> RunningAgent:
            raise ConstructionFailure

        self.patch_attr(subprocess, "Popen", recording_popen)
        self.patch_attr(progress_module, "RunningAgent", fail_construction)
        self.patch_attr(phaselib, "AGENT_TERMINATION_GRACE_SECONDS", 0.05)
        with self.assertRaises(ConstructionFailure):
            self.run_phase("review", ["analysis", "--agent=fake", NAME])
        self.assertEqual(len(spawned), 1)
        self.assertIsNotNone(spawned[0].poll())
        self.assertFalse(phaselib.Phase._group_exists(spawned[0].pid))


class TestModelEffortForwarding(unittest.TestCase):
    """Agent-aware tuning for the blocking confirmation path."""

    def test_argv_helper(self) -> None:
        codex = Path("/x/codex.sh")
        claude = Path("/x/claude-code.sh")
        self.assertEqual(phaselib._model_effort_argv(codex, None, None), [])
        self.assertEqual(phaselib._model_effort_argv(claude, None, None), ["--effort=max"])
        self.assertEqual(phaselib._model_effort_argv(codex, "gpt-5.5", None), ["--model=gpt-5.5"])
        self.assertEqual(phaselib._model_effort_argv(codex, None, "ultra"), ["--effort=ultra"])
        self.assertEqual(
            phaselib._model_effort_argv(claude, "", ""),
            ["--model=", "--effort="],
        )

    def _blocking_cmd(
        self,
        *,
        adapter_name: str = "codex",
        model: str | None = None,
        effort: str | None = None,
    ) -> list[str]:
        captured: list[list[str]] = []

        class _Result:
            returncode = 0

        def fake_run(cmd: list[str], **_: Any) -> _Result:
            captured.append(cmd)
            return _Result()

        with tempfile.TemporaryDirectory() as d, mock.patch("specula.phaselib.subprocess.run", fake_run):
            dp = Path(d)
            phaselib.run_agent_blocking(
                Path(f"/x/{adapter_name}.sh"),
                "prompt",
                dp / "p.md",
                dp / "o.log",
                phase_key="k",
                work_dir=dp,
                claude_alias="claude",
                model=model,
                effort=effort,
            )
        return captured[0]

    def test_forwarded_when_set(self) -> None:
        cmd = self._blocking_cmd(model="gpt-5.5", effort="ultra")
        self.assertIn("--model=gpt-5.5", cmd)
        self.assertIn("--effort=ultra", cmd)

    def test_unspecified_effort_is_agent_specific(self) -> None:
        claude = self._blocking_cmd(adapter_name="claude-code")
        self.assertIn("--effort=max", claude)
        for adapter in ("codex", "copilot-cli"):
            with self.subTest(adapter=adapter):
                cmd = self._blocking_cmd(adapter_name=adapter)
                self.assertFalse(any(c.startswith("--effort=") for c in cmd))

    def test_explicit_empty_is_forwarded_not_defaulted(self) -> None:
        cmd = self._blocking_cmd(adapter_name="claude-code", model="", effort="")
        self.assertIn("--model=", cmd)
        self.assertIn("--effort=", cmd)
        self.assertNotIn("--effort=max", cmd)

    def test_blocking_codex_prompt_materializes_one_plugin_id(self) -> None:
        class _Result:
            returncode = 0

        with (
            tempfile.TemporaryDirectory() as d,
            mock.patch("specula.phaselib.subprocess.run", return_value=_Result()),
            mock.patch("specula.skill_refs._codex_plugin_enabled", return_value=True),
        ):
            root = Path(d)
            prompt_file = root / "prompt.md"
            phaselib.run_agent_blocking(
                Path("/x/codex.sh"),
                f"Use {prompt_skill_ids('bug-confirmation')}",
                prompt_file,
                root / "out.log",
                phase_key="bug_confirmation",
                work_dir=root,
                claude_alias="claude",
            )

            prompt = prompt_file.read_text()
            self.assertIn(f"${CODEX_PLUGIN_NAME}:bug-confirmation", prompt)
            self.assertNotIn("$bug-confirmation", prompt)
            self.assertNotIn("<!-- specula-skill:", prompt)


if __name__ == "__main__":
    unittest.main()
