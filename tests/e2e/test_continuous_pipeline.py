"""Continuous orchestration through the real CLI with a deterministic adapter.

The fixture performs no semantic verification and never calls a model. It
drives the real launcher, context runner, confirmation dispatcher, repair-loop
machinery, and classification through `specula run`.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import unittest
from pathlib import Path
from typing import Any
from unittest import mock

import test_cli_pipeline as fixtures

from specula.phaselib import _MANUAL_SESSION_RESUME_PROMPT
from specula.rules import RULES_SEPARATOR, RULES_TITLE

FIXTURE = Path(__file__).parent / "fixtures/continuous_adapter.py"


class ContinuousCLI(unittest.TestCase):
    def setUp(self) -> None:
        self.helper = fixtures.CliE2E()
        self.addCleanup(self.helper.doCleanups)
        self.root = self.helper.specroot(("footest", "bartest"))
        # SANY checks every handoff: a fake one; no ambient TLA+ tools or strict switch.
        path = f"{self.helper.fake_sany(self.root)}{os.pathsep}{os.environ.get('PATH', '')}"
        patcher = mock.patch.dict(
            os.environ, {"PATH": path, "SPECULA_ROOT": "", "SPECULA_STRICT_OUTPUTS": "", "SPECULA_DELEGATION": ""}
        )
        patcher.start()
        self.addCleanup(patcher.stop)
        self.work = self.helper.workdir()
        self.source = self.work / "source"
        self.source.mkdir()
        for args in (
            ["init", "-q"],
            ["config", "user.name", "Fixture"],
            ["config", "user.email", "fixture@example.com"],
        ):
            subprocess.run(["git", "-C", str(self.source), *args], check=True)
        (self.source / "logic.txt").write_text("initial\n")
        subprocess.run(["git", "-C", str(self.source), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.source), "commit", "-qm", "initial"], check=True)
        self.adapters = self.root / "scripts/launch/adapters"
        shutil.copyfile(FIXTURE, self.adapters / "continuous_adapter.py")
        self.install("fake")

    def install(self, name: str) -> None:
        script = self.adapters / f"{name}.sh"
        script.write_text(
            f'#!/bin/sh\nFIXTURE_ADAPTER={name} exec "{sys.executable}" "{self.adapters / "continuous_adapter.py"}" "$@"\n'
        )
        script.chmod(0o755)

    def flag(self, name: str) -> Path:
        path = self.adapters / name
        path.touch()
        return path

    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return self.helper.run_cli(self.root, ["run", f"--artifact={self.source}", *args], cwd=self.work)

    def run_dir(self) -> Path:
        return self.helper.sole_run_dir(self.root)

    def events(self) -> list[dict[str, Any]]:
        path = self.adapters / "events.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def main_events(self, target: str = "footest") -> list[dict[str, Any]]:
        return [e for e in self.events() if e["name"] == "main" and e["target"] == target]

    def worker_starts(self, name: str) -> int:
        return sum(e["kind"] == "start" and e["name"] == name for e in self.events())

    def state(self, run: Path, target: str = "footest") -> dict[str, Any]:
        value: dict[str, Any] = json.loads(
            (run / target / ".specula-output/.context-control/main-state.json").read_text()
        )
        return value

    def request(self, run: Path, target: str = "footest") -> dict[str, Any]:
        value: dict[str, Any] = json.loads(
            (run / target / ".specula-output/.context-control/confirmation.json").read_text()
        )
        return value

    def prompt(self, call: int, target: str = "footest") -> str:
        """The main-session prompt of one call, after its single pinned rules block."""
        text = (self.adapters / f"main-prompt-{target}-{call}.md").read_text()
        self.assertEqual(text.count(RULES_TITLE), 1, text[:300])
        self.assertTrue(text.startswith(RULES_TITLE))
        return text.split(RULES_SEPARATOR, 1)[1]

    def assert_complete(self, result: subprocess.CompletedProcess[str], run: Path, target: str = "footest") -> None:
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        work = run / target / ".specula-output"
        self.assertEqual(self.state(run, target)["stage"], "complete")
        self.assertEqual(self.request(run, target)["status"], "completed")
        self.assertIn("| CR-1 |", (work / "confirmed-bugs.md").read_text())
        self.assertTrue((work / "bug-severity.md").is_file())
        self.assertEqual(list((run / ".specula-resume/active").glob("*.json")), [])

    # ── default flow ──
    def run_default_flow(self, adapter: str) -> None:
        self.install(adapter)
        result = self.run_cli(f"--agent={adapter}", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        mains = self.main_events()
        self.assertEqual([e["call"] for e in mains], [1])
        self.assertEqual(self.worker_starts("CR-1"), 1)
        phases = [e["phase"] for e in self.events()]
        self.assertNotIn("code_analysis", phases)
        self.assertNotIn("spec_validation", phases)
        self.assertEqual(self.request(run)["session_id"], "main-footest-1")
        meta = json.loads((run / "run.json").read_text())
        self.assertEqual(meta["orchestration"], "continuous")
        self.assertEqual(meta["resume_configuration"]["orchestration"], "continuous")
        self.assertIn("MAIN SESSION: analysis", result.stdout)
        self.assertIn("Orchestration: continuous", result.stdout)
        self.assertEqual(self.prompt(1).count("## Parallel Subagents"), 1)
        self.assertIs(
            json.loads((run / ".specula-resume/config.json").read_text())["configuration"]["delegation"], True
        )
        summary = (run / "footest/.specula-output/summary.md").read_text()
        self.assertIn("| Main session (Phases 1-3) |", summary)
        self.assertIn("`footest/.specula-output/main.log`", (run / "pipeline-summary.md").read_text())

    def test_default_flow_with_fake_adapter(self) -> None:
        self.run_default_flow("fake")

    def test_default_flow_through_codex_runner_path(self) -> None:
        self.run_default_flow("codex")

    def test_default_flow_through_claude_runner_path(self) -> None:
        self.run_default_flow("claude-code")

    def test_ordinary_end_of_turn_is_a_validated_handoff(self) -> None:
        self.flag("implicit")
        result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        self.assertTrue(self.request(run)["implicit"])

    # ── repair back-edge ──
    def test_repair_resumes_the_same_session_and_confirms_only_current_violations(self) -> None:
        self.flag("repair")
        result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        work = run / "footest/.specula-output"
        mains = self.main_events()
        self.assertEqual([e["session"] for e in mains], ["main-footest-1"] * 2)
        repair_prompt = self.prompt(2)
        self.assertTrue(repair_prompt.startswith("## Repair Round 1"), repair_prompt[:200])
        self.assertIn("RR-001", repair_prompt)
        self.assertNotIn("# Specula Main Session", repair_prompt)
        self.assertEqual(self.worker_starts("MC-1"), 1)
        self.assertEqual(self.worker_starts("CR-1"), 1)
        self.assertIn("status: CONSUMED", (work / "spec/repair-requests/RR-001.md").read_text())
        self.assertFalse((work / "spec/.repair-phase3-snapshot.json").exists())
        self.assertFalse((work / "spec/.repair-phase3-commit.json").exists())
        self.assertTrue((work / "confirmed-bugs-round-1.md").is_file())
        loop = json.loads((run / "repair-loop.json").read_text())
        self.assertEqual((loop["round"], loop["pending"]), (1, []))
        self.assertEqual(self.request(run)["repair_round"], 1)
        self.assertIn("REPAIR ROUND 1: MAIN SESSION", result.stdout)

    def test_retry_budgets_reset_for_each_main_session_step(self) -> None:
        self.flag("repair")
        self.flag("policy-1")
        self.flag("policy-3")
        result = self.run_cli("--agent=fake", "--policy-retries=1", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        # The repair round spends its own policy retry, not the initial pass's.
        self.assertEqual([e["call"] for e in self.main_events()], [1, 2, 3, 4])
        self.assertEqual({e["session"] for e in self.main_events()}, {"main-footest-1"})
        self.assertEqual(result.stdout.count("retrying with a revised request (1/1)"), 2)

    def test_repair_cap_defers_without_resuming_main(self) -> None:
        self.flag("repair")
        result = self.run_cli("--agent=fake", "--max-repair-rounds=0", "--skip-repair-loop", "footest")
        run = self.run_dir()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len(self.main_events()), 1)
        self.assertIn("status: OPEN", (run / "footest/.specula-output/spec/repair-requests/RR-001.md").read_text())
        self.assertEqual(self.state(run)["stage"], "complete")

    def test_unconsumed_repair_is_rejected_then_resumed_with_the_reason(self) -> None:
        self.flag("repair")
        unconsumed = self.flag("unconsumed")
        failed = self.run_cli("--agent=fake", "footest")
        self.assertEqual(failed.returncode, 1, failed.stdout + failed.stderr)
        run = self.run_dir()
        self.assertEqual(self.request(run)["status"], "rejected")
        state = self.state(run)
        self.assertEqual((state["stage"], state["repair_round"], state["auto_resumes"]), ("main", 1, 2))
        self.assertIn("RR-001=OPEN", state["rejection"])
        self.assertTrue((run / "footest/.specula-output/spec/.repair-phase3-snapshot.json").is_file())
        self.assertIn("RR-001=OPEN", (self.adapters / "tool-refusal.txt").read_text())
        # The repair turn plus two automatic resumes with the reason, all in this run.
        self.assertEqual([e["call"] for e in self.main_events()], [1, 2, 3, 4])
        for call in (3, 4):
            self.assertIn("Confirmation Request Not Accepted", self.prompt(call))
        self.assertIn("handoff was still not accepted after 2 automatic resumes", failed.stdout)

        # An attach is not a fresh budget: one more rejection fails at once.
        again = self.run_cli(f"--run-id={run.name}")
        self.assertEqual(again.returncode, 1, again.stdout + again.stderr)
        self.assertEqual(len(self.main_events()), 5)
        unconsumed.unlink()

        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        manual = self.prompt(6)
        self.assertTrue(manual.startswith(_MANUAL_SESSION_RESUME_PROMPT))
        self.assertIn("Confirmation Request Not Accepted", manual)
        self.assertIn("## Repair Round 1", manual)
        self.assertEqual({e["session"] for e in self.main_events()}, {"main-footest-1"})
        self.assertEqual(json.loads((run / "repair-loop.json").read_text())["round"], 1)
        self.assertEqual(self.state(run)["auto_resumes"], 0)

    def test_rejected_handoff_resumes_automatically_within_the_run(self) -> None:
        self.flag("repair")
        self.flag("unconsumed")
        self.flag("unconsumed-once")
        result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        self.assertEqual([e["call"] for e in self.main_events()], [1, 2, 3])
        self.assertEqual({e["session"] for e in self.main_events()}, {"main-footest-1"})
        resumed = self.prompt(3)
        self.assertIn("Confirmation Request Not Accepted", resumed)
        self.assertIn("## Repair Round 1", resumed)
        self.assertIn("resuming the main session with the reported problem (1/2)", result.stdout)
        self.assertEqual(json.loads((run / "repair-loop.json").read_text())["round"], 1)

    def test_blocked_main_session_fails_once_without_automatic_resumes(self) -> None:
        self.flag("blocked")
        failed = self.run_cli("--agent=fake", "footest")
        self.assertEqual(failed.returncode, 1, failed.stdout + failed.stderr)
        run = self.run_dir()
        self.assertEqual(len(self.main_events()), 1)
        self.assertEqual(self.request(run)["status"], "rejected")
        self.assertEqual(self.state(run)["auto_resumes"], 0)
        self.assertIn("declared that it cannot finish", failed.stdout)

    # ── output contract ──
    def test_required_outputs_alone_complete_the_run_and_report_cleanly(self) -> None:
        self.flag("minimal")
        sany = self.work / "sany-calls.jsonl"
        with mock.patch.dict(os.environ, {"FIXTURE_SANY_LOG": str(sany)}):
            result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        work = run / "footest/.specula-output"
        for advisory in ("analysis-report.md", "spec/instrumentation-spec.md", "spec/changelog.md"):
            self.assertFalse((work / advisory).exists(), advisory)
        self.assertEqual(
            [json.loads(line)["module"] for line in sany.read_text().splitlines()][:3],
            [
                "base.tla",
                "MC.tla",
                "Trace.tla",
            ],
        )
        self.assertIn("required outputs OK", result.stdout)
        prompt = self.prompt(1)
        self.assertIn("### Required", prompt)
        self.assertIn("### Recommended", prompt)
        # Only the file set is relaxed: the default prompt keeps the phased methodology strength.
        self.assertIn("follow it exactly", prompt)
        self.assertIn("Only the set of files is relaxed", prompt)
        summary = (run / "pipeline-summary.md").read_text()
        self.assertIn("- **Phase 2 (Spec Gen)**: OK (5/5 required files, base: 1 lines)", summary)
        self.assertIn("- **Phase 2.5 (Harness)**: OK (traces: 1)", summary)
        self.assertIn("- **Phase 3 (Validation)**: bug-report.md written (2 lines)", summary)
        self.assertNotIn("INCOMPLETE", summary)
        self.assertNotIn("(Validation)**: SKIPPED", summary)
        index = (work / "index.md").read_text()
        for advisory in ("Analysis report", "Spec coverage", "Instrumentation map", "Validation changelog"):
            self.assertNotIn(advisory, index)
        self.assertIn("| 2 | [Model-checking report](spec/bug-report.md) |", index)

    def test_the_tool_returns_output_problems_so_the_agent_fixes_them_before_yielding(self) -> None:
        self.flag("sany-error")
        self.flag("fix-on-rejection")
        result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        self.assertEqual(len(self.main_events()), 1)  # fixed in the same turn; no rejection round trip
        refusal = (self.adapters / "tool-refusal.txt").read_text()
        self.assertTrue(refusal.startswith("Confirmation was not requested. Required outputs are missing or invalid"))
        self.assertIn("- `spec/Trace.tla` does not parse with SANY (exit 255).", refusal)
        self.assertIn("tla2sany.SANY Trace.tla", refusal)
        self.assertIn('Encountered "SANY-ERROR"', refusal)
        self.assertEqual([e["attempt"] for e in self.events() if e["kind"] == "refusal"], [1])
        fixes = [e for e in self.events() if e["kind"] == "fix"]
        self.assertEqual([e["fixed"] for e in fixes], [["spec/Trace.tla"]])
        self.assertNotIn("Confirmation Request Not Accepted", result.stdout)
        self.assertEqual(self.worker_starts("CR-1"), 1)

    def test_without_sany_in_the_tool_the_controller_rejects_and_resumes_with_sany_errors(self) -> None:
        self.flag("sany-error")
        self.flag("fix-on-rejection")
        self.flag("tool-no-sany")
        result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        self.assertFalse((self.adapters / "tool-refusal.txt").exists())  # the tool did not block
        self.assertEqual([e["session"] for e in self.main_events()], ["main-footest-1"] * 2)
        resumed = self.prompt(2)
        self.assertIn("Confirmation Request Not Accepted", resumed)
        self.assertIn("Required outputs are missing or invalid", resumed)
        self.assertIn("- `spec/Trace.tla` does not parse with SANY (exit 255).", resumed)
        self.assertIn('Encountered "SANY-ERROR"', resumed)
        fixes = [e for e in self.events() if e["kind"] == "fix"]
        self.assertEqual([e["fixed"] for e in fixes], [["spec/Trace.tla"]])
        self.assertEqual(self.worker_starts("CR-1"), 1)

    def test_strict_outputs_restore_the_full_contract_and_survive_an_attach(self) -> None:
        self.flag("minimal")
        with mock.patch.dict(os.environ, {"SPECULA_STRICT_OUTPUTS": "on"}):
            failed = self.run_cli("--agent=fake", "footest")
        self.assertEqual(failed.returncode, 1, failed.stdout + failed.stderr)
        run = self.run_dir()
        config = json.loads((run / ".specula-resume/config.json").read_text())["configuration"]
        self.assertIs(config["strict_outputs"], True)
        self.assertIs(json.loads((run / "run.json").read_text())["resume_configuration"]["strict_outputs"], True)
        self.assertIn("Outputs:       every phase output is required (SPECULA_STRICT_OUTPUTS=on)", failed.stdout)
        first = self.prompt(1)
        self.assertIn("Every output below is required", first)
        self.assertIn("follow it exactly", first.lower())
        self.assertNotIn("### Recommended", first)
        rejection = self.state(run)["rejection"]
        for missing in ("analysis-report.md", "spec/instrumentation-spec.md", "spec/changelog.md", "harness/src/"):
            self.assertIn(f"`{missing}` is missing", rejection)
        self.assertEqual(len(self.main_events()), 3)  # the initial pass plus two automatic resumes

        # The attach keeps the strict contract although the switch is now off.
        self.flag("fix-on-rejection")
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertIn("SPECULA_STRICT_OUTPUTS: this run was created with strict outputs on", resumed.stdout)
        self.assertIn("every phase output (SPECULA_STRICT_OUTPUTS) OK", resumed.stdout)
        work = run / "footest/.specula-output"
        self.assertTrue((work / "spec/instrumentation-spec.md").is_file())
        summary = (run / "pipeline-summary.md").read_text()
        self.assertIn("- **Phase 2 (Spec Gen)**: OK (4/4 files", summary)  # the phased lines

    def test_a_handoff_without_traces_is_confirmed_and_the_gap_is_reported(self) -> None:
        self.flag("no-traces")
        result = self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        self.assert_complete(result, run)
        self.assertEqual(len(self.main_events()), 1)  # accepted at once, not resumed
        self.assertEqual(self.worker_starts("CR-1"), 1)
        self.assertIn("WARN  footest: No execution traces were collected", result.stdout)
        summary = (run / "footest/.specula-output/summary.md").read_text()
        coverage = summary.split("## Run coverage", 1)[1].split("\n## ", 1)[0]
        self.assertIn("- No execution traces were collected, so trace validation did not compare the model", coverage)
        pipeline_summary = (run / "pipeline-summary.md").read_text()
        self.assertIn("- **Phase 2.5 (Harness)**: WARN (run.sh written, no traces collected)", pipeline_summary)

    def test_missing_sany_stops_without_resuming_main_and_attach_rechecks_the_handoff(self) -> None:
        jar = self.root / "lib/tla2tools.jar"
        jar.unlink()
        failed = self.run_cli("--agent=fake", "footest")
        self.assertEqual(failed.returncode, 1, failed.stdout + failed.stderr)
        self.assertIn("cannot check the confirmation handoff: tla2tools.jar not found", failed.stdout)
        run = self.run_dir()
        self.assertIn(f"--run-id={run.name}", failed.stdout)
        self.assertEqual(self.request(run)["status"], "pending")
        self.assertEqual(self.state(run)["auto_resumes"], 0)
        self.assertEqual(self.worker_starts("CR-1"), 0)
        jar.write_bytes(b"")
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertEqual(len(self.main_events()), 1)
        self.assertEqual(self.worker_starts("CR-1"), 1)

    # ── interruption and recovery ──
    def test_interrupted_main_resumes_the_same_native_session(self) -> None:
        failure = self.flag("fail-main-1")
        failed = self.run_cli("--agent=fake", "footest")
        self.assertEqual(failed.returncode, 9, failed.stdout + failed.stderr)
        run = self.run_dir()
        self.assertEqual(self.state(run)["stage"], "main")
        failure.unlink()
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertEqual([e["session"] for e in self.main_events()], ["main-footest-1"] * 2)
        self.assertTrue(self.prompt(2).startswith(_MANUAL_SESSION_RESUME_PROMPT))

    def test_attach_keeps_the_prompt_toggles_the_run_was_created_with(self) -> None:
        failure = self.flag("fail-main-1")
        self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        failure.unlink()
        with mock.patch.dict(os.environ, {"SPECULA_RULES": "off", "SPECULA_NOTES": "off", "SPECULA_DELEGATION": "off"}):
            resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertIn("SPECULA_RULES: this run was created with rules on", resumed.stdout)
        self.assertIn("SPECULA_NOTES: this run was created with notes on", resumed.stdout)
        self.assertIn("SPECULA_DELEGATION: this run was created with delegation guidance on", resumed.stdout)
        self.prompt(2)  # still pinned exactly once
        self.assertIn("SPECULA_RULES: this run was created", (run / "pipeline.log").read_text())

    def test_interrupted_confirmation_resumes_without_relaunching_main(self) -> None:
        self.flag("fail-confirm")
        failed = self.run_cli("--agent=fake", "footest")
        self.assertNotEqual(failed.returncode, 0, failed.stdout + failed.stderr)
        run = self.run_dir()
        self.assertEqual(self.request(run)["status"], "confirming")
        self.assertEqual(self.state(run)["stage"], "confirm")
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertEqual(len(self.main_events()), 1)
        self.assertEqual(self.worker_starts("CR-1"), 2)

    def test_stop_after_yield_dispatches_the_pending_request_once(self) -> None:
        script = (
            "import sys\nfrom unittest.mock import patch\n"
            f"sys.path.insert(0, {str(self.root / 'src')!r})\n"
            "from specula import pipelinelib\n"
            "with patch('specula.continuous.ContinuousRun._dispatch', side_effect=SystemExit(143)):\n"
            "    raise SystemExit(pipelinelib.main(sys.argv[1:]))\n"
        )
        env = {key: value for key, value in os.environ.items() if key not in fixtures._VOLATILE}
        env["HOME"] = str(self.work)
        stopped = subprocess.run(
            [sys.executable, "-c", script, "--agent=fake", f"--artifact={self.source}", "footest"],
            cwd=self.work,
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(stopped.returncode, 143, stopped.stdout + stopped.stderr)
        run = self.run_dir()
        self.assertEqual(self.request(run)["status"], "pending")
        self.assertEqual(self.worker_starts("CR-1"), 0)
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertEqual(len(self.main_events()), 1)
        self.assertEqual(self.worker_starts("CR-1"), 1)
        rejected = self.run_cli(f"--run-id={run.name}")
        self.assertEqual(rejected.returncode, 1)
        self.assertIn("no unfinished agent conversation", rejected.stderr)

    def test_crash_before_the_summary_does_not_repeat_classification(self) -> None:
        script = (
            "import sys\nfrom unittest.mock import patch\n"
            f"sys.path.insert(0, {str(self.root / 'src')!r})\n"
            "from specula import pipelinelib\n"
            "with patch('specula.pipelinelib.Pipeline.generate_summary', side_effect=SystemExit(143)):\n"
            "    raise SystemExit(pipelinelib.main(sys.argv[1:]))\n"
        )
        env = {key: value for key, value in os.environ.items() if key not in fixtures._VOLATILE}
        env["HOME"] = str(self.work)
        stopped = subprocess.run(
            [sys.executable, "-c", script, "--agent=fake", f"--artifact={self.source}", "footest"],
            cwd=self.work,
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(stopped.returncode, 143, stopped.stdout + stopped.stderr)
        run = self.run_dir()
        self.assertEqual(self.state(run)["stage"], "classified")
        self.assertEqual(self.worker_starts("classify"), 1)
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertIn("Phase 4b already completed for every target", resumed.stdout)
        self.assertEqual(self.worker_starts("classify"), 1)
        self.assertTrue((run / "pipeline-summary.md").is_file())

    def test_fresh_context_starts_a_new_session_from_existing_artifacts(self) -> None:
        self.flag("fail-main-1")
        failed = self.run_cli("--agent=fake", "footest")
        self.assertEqual(failed.returncode, 9, failed.stdout + failed.stderr)
        run = self.run_dir()
        work = run / "footest/.specula-output"
        (work / "modeling-brief.md").write_text("# Earlier brief\n")
        (self.adapters / "fail-main-1").unlink()
        fresh = self.run_cli(f"--run-id={run.name}", "--fresh-context")
        self.assert_complete(fresh, run)
        self.assertEqual([e["session"] for e in self.main_events()], ["main-footest-1", "main-footest-2"])
        prompt = self.prompt(2)
        self.assertIn("## Continue From Existing Work", prompt)
        self.assertIn(str(work / "modeling-brief.md"), prompt)
        self.assertEqual(self.request(run)["session_id"], "main-footest-2")
        self.assertEqual(self.state(run)["context"], "fresh")
        self.assertEqual(len(list((work / ".context-control/abandoned").glob("*/main-state.json"))), 1)

    def test_attach_cannot_switch_orchestration(self) -> None:
        self.flag("fail-main-1")
        self.run_cli("--agent=fake", "footest")
        run = self.run_dir()
        rejected = self.run_cli(f"--run-id={run.name}", "--orchestration=phased")
        self.assertEqual(rejected.returncode, 1)
        self.assertIn("this run uses continuous orchestration", rejected.stderr)
        skipped = self.run_cli(f"--run-id={run.name}", "--skip-specgen")
        self.assertEqual(skipped.returncode, 1)
        self.assertIn("does not support --skip-specgen", skipped.stderr)
        # Its unfinished main session performs the analysis; --skip-analysis cannot retarget it.
        retarget = self.run_cli(f"--run-id={run.name}", "--skip-analysis")
        self.assertEqual(retarget.returncode, 1, retarget.stdout + retarget.stderr)
        self.assertIn("--skip-analysis does not apply to this run", retarget.stdout)
        self.assertEqual(len(self.main_events()), 1)

    # ── targets and options ──
    def test_multiple_targets_run_parallel_main_sessions_then_confirm_each(self) -> None:
        result = self.helper.run_cli(
            self.root,
            ["run", "--agent=fake", "--max-parallel=2", "footest|o/f|Go|Raft", "bartest|o/b|Go|Raft"],
            cwd=self.work,
        )
        # Isolated runs read canonical sources from case-studies/<name>/artifact.
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        for name in ("footest", "bartest"):
            artifact = self.root / "case-studies" / name / "artifact" / "repo"
            shutil.copytree(self.source, artifact)
        shutil.rmtree(self.root / "runs")
        result = self.helper.run_cli(
            self.root,
            ["run", "--agent=fake", "--max-parallel=2", "footest|o/f|Go|Raft", "bartest|o/b|Go|Raft"],
            cwd=self.work,
        )
        run = self.run_dir()
        for name in ("footest", "bartest"):
            self.assert_complete(result, run, name)
            self.assertEqual(len(self.main_events(name)), 1)
        self.assertIn("Max parallel: 2", result.stdout)

    def test_skip_confirmation_and_classification_close_the_main_session(self) -> None:
        result = self.run_cli("--agent=fake", "--skip-confirmation", "--skip-classification", "footest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        run = self.run_dir()
        self.assertTrue(self.request(run)["skipped"])
        self.assertEqual(self.state(run)["stage"], "complete")
        self.assertEqual(self.worker_starts("CR-1"), 0)
        self.assertFalse((run / "footest/.specula-output/confirmed-bugs.md").exists())

    def test_unsupported_options_fall_back_or_fail_before_storage(self) -> None:
        explicit = self.run_cli("--orchestration=continuous", "--skip-specgen", "--dry-run", "footest")
        self.assertEqual(explicit.returncode, 1)
        self.assertIn("--orchestration=continuous does not support --skip-specgen", explicit.stderr)
        self.assertFalse((self.root / "runs").exists())
        fallback = self.run_cli("--skip-specgen", "--dry-run", "footest")
        self.assertEqual(fallback.returncode, 0, fallback.stderr)
        self.assertIn(
            "Orchestration: phased (continuous orchestration does not support --skip-specgen", fallback.stdout
        )
        self.assertIn("launch_harness_generation.sh", fallback.stdout)
        self.assertNotIn("launch_spec_generation.sh", fallback.stdout)
        # --skip-analysis keeps continuous orchestration; a dry run, like the phased one, checks no outputs.
        dry = self.run_cli("--skip-analysis", "--dry-run", "footest")
        self.assertEqual(dry.returncode, 0, dry.stdout + dry.stderr)
        self.assertIn("Orchestration: continuous (one main session per target for spec generation", dry.stdout)
        self.assertIn("MAIN SESSION: spec → harness → validation from existing code analysis", dry.stdout)
        self.assertIn("launch_continuous.sh", dry.stdout)

    # ── starting from existing analysis ──
    def seed_analysis(self, run_id: str, target: str = "footest") -> Path:
        work = self.root / "runs" / run_id / target / ".specula-output"
        (work / "analysis").mkdir(parents=True)
        (work / "modeling-brief.md").write_text("# Shared brief\n\n## Scenario 1: Candidate one\n")
        (work / "analysis-report.md").write_text("Shared Phase 1 report.\n")
        (work / "analysis/batch_1.txt").write_text("Shared archaeology batch.\n")
        return work

    def test_skip_analysis_starts_the_main_session_from_existing_analysis(self) -> None:
        work = self.seed_analysis("shared")
        self.flag("fail-main-1")
        failed = self.run_cli("--agent=fake", "--run-id=shared", "--fresh-context", "--skip-analysis", "footest")
        self.assertEqual(failed.returncode, 9, failed.stdout + failed.stderr)
        run = self.run_dir()
        self.assertEqual(run.name, "shared")
        self.assertIn("Orchestration: continuous (one main session per target for spec generation", failed.stdout)
        self.assertIn("MAIN SESSION: spec → harness → validation from existing code analysis", failed.stdout)
        state = self.state(run)
        self.assertEqual((state["analysis"], state["context"]), ("existing", "original"))
        prompt = self.prompt(1)
        self.assertIn("1. **Code analysis**: already complete.", prompt)
        self.assertIn(f"Read `{work}/modeling-brief.md` and `{work}/analysis-report.md` in full", prompt)
        self.assertIn("follow it exactly", prompt)
        self.assertNotIn("**code-analysis**", prompt)
        self.assertNotIn("## Continue From Existing Work", prompt)
        # A plain attach resumes the same session; the durable state keeps the analysis mode.
        (self.adapters / "fail-main-1").unlink()
        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        self.assertEqual([e["session"] for e in self.main_events()], ["main-footest-1", "main-footest-1"])
        self.assertEqual(self.state(run)["analysis"], "existing")
        self.assertEqual([e["kind"] for e in self.events() if e["name"] == "analysis"], ["reused", "stage"])
        self.assertEqual((work / "modeling-brief.md").read_text(), "# Shared brief\n\n## Scenario 1: Candidate one\n")
        self.assertEqual((work / "analysis-report.md").read_text(), "Shared Phase 1 report.\n")
        phases = [e["phase"] for e in self.events()]
        self.assertNotIn("code_analysis", phases)
        self.assertNotIn("spec_generation", phases)

    def test_skip_analysis_without_a_brief_fails_before_any_agent(self) -> None:
        missing = self.run_cli("--agent=fake", "--skip-analysis", "footest")
        self.assertEqual(missing.returncode, 1, missing.stdout + missing.stderr)
        self.assertIn("--skip-analysis starts the main session from existing code-analysis outputs", missing.stdout)
        self.assertIn("modeling-brief.md is missing or empty for footest", missing.stdout)
        self.assertEqual(self.events(), [])
        run = self.run_dir()
        self.assertFalse((run / "footest/.specula-output/.context-control/main-state.json").exists())
        empty = self.seed_analysis("empty")
        (empty / "modeling-brief.md").write_text("\n")
        rejected = self.run_cli("--agent=fake", "--run-id=empty", "--fresh-context", "--skip-analysis", "footest")
        self.assertEqual(rejected.returncode, 1, rejected.stdout + rejected.stderr)
        self.assertIn("modeling-brief.md is missing or empty for footest", rejected.stdout)
        self.assertEqual(self.events(), [])

    def test_agent_config_routes_main_confirmation_and_classification(self) -> None:
        config = self.work / "agents.json"
        config.write_text(
            json.dumps(
                {
                    "version": 1,
                    "default_profile": "base",
                    "profiles": {
                        "base": {"agent": "fake", "model": "base-model"},
                        "main": {"agent": "fake", "model": "main-model"},
                        "check": {"agent": "fake", "model": "check-model"},
                    },
                    "phases": {"main": "main", "confirm": "check"},
                }
            )
        )
        result = self.run_cli(f"--agent-config={config}", "--dry-run", "footest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        lines = result.stdout.splitlines()
        main = next(line for line in lines if "launch_continuous.sh" in line)
        confirm = next(line for line in lines if "launch_bug_confirmation.sh" in line)
        classify = next(line for line in lines if "launch_bug_classification.sh" in line)
        self.assertIn("--model=main-model", main)
        self.assertIn("--model=check-model", confirm)
        self.assertIn("--model=base-model", classify)
        meta = json.loads((self.run_dir() / "run.json").read_text())
        self.assertEqual(set(meta["agent_routes"]), {"main", "confirm", "classify"})


if __name__ == "__main__":
    unittest.main()
