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

import test_cli_pipeline as fixtures

from specula.phaselib import _MANUAL_SESSION_RESUME_PROMPT
from specula.rules import RULES_SEPARATOR, RULES_TITLE

FIXTURE = Path(__file__).parent / "fixtures/continuous_adapter.py"


class ContinuousCLI(unittest.TestCase):
    def setUp(self) -> None:
        self.helper = fixtures.CliE2E()
        self.addCleanup(self.helper.doCleanups)
        self.root = self.helper.specroot(("footest", "bartest"))
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
        self.assertEqual((state["stage"], state["repair_round"]), ("main", 1))
        self.assertIn("RR-001=OPEN", state["rejection"])
        self.assertTrue((run / "footest/.specula-output/spec/.repair-phase3-snapshot.json").is_file())
        self.assertIn("RR-001=OPEN", (self.adapters / "tool-refusal.txt").read_text())
        unconsumed.unlink()

        resumed = self.run_cli(f"--run-id={run.name}")
        self.assert_complete(resumed, run)
        manual = self.prompt(3)
        self.assertTrue(manual.startswith(_MANUAL_SESSION_RESUME_PROMPT))
        self.assertIn("Confirmation Request Not Accepted", manual)
        self.assertIn("## Repair Round 1", manual)
        self.assertEqual({e["session"] for e in self.main_events()}, {"main-footest-1"})
        self.assertEqual(json.loads((run / "repair-loop.json").read_text())["round"], 1)

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
        skipped = self.run_cli(f"--run-id={run.name}", "--skip-analysis")
        self.assertEqual(skipped.returncode, 1)
        self.assertIn("does not support --skip-analysis", skipped.stderr)

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
        explicit = self.run_cli("--orchestration=continuous", "--skip-analysis", "--dry-run", "footest")
        self.assertEqual(explicit.returncode, 1)
        self.assertIn("--orchestration=continuous does not support --skip-analysis", explicit.stderr)
        self.assertFalse((self.root / "runs").exists())
        fallback = self.run_cli("--skip-analysis", "--dry-run", "footest")
        self.assertEqual(fallback.returncode, 0, fallback.stderr)
        self.assertIn(
            "Orchestration: phased (continuous orchestration does not support --skip-analysis", fallback.stdout
        )
        self.assertIn("launch_spec_generation.sh", fallback.stdout)

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
