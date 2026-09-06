"""Exercise the real CLI and native resume wiring with a deterministic adapter.

The fixture does not perform semantic verification or call an LLM.
"""

from __future__ import annotations

import json
import subprocess
import unittest
from pathlib import Path

import test_cli_pipeline as fixtures

from specula.ci_store import CIStore


class IncrementalCLI(unittest.TestCase):
    def setUp(self) -> None:
        self.helper = fixtures.CliE2E()
        self.addCleanup(self.helper.doCleanups)
        self.root = self.helper.specroot()
        self.work = self.helper.workdir()
        self.source = self.work / "source"
        self.source.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.com")
        (self.source / "logic.txt").write_text("initial\n")
        self.commit("initial")
        self.initial_sha = self.git("rev-parse", "HEAD")
        self.ci = self.work / "ci"
        self.adapter = self.helper._ci_init_adapter(self.root)
        script = self.adapter.read_text()
        script = script.replace(
            'case "$SPECULA_PHASE" in\n',
            'case "$SPECULA_PHASE" in\n'
            "  incremental)\n"
            '    if [ -f "$0.fail" ]; then\n'
            '      printf "fixture-native-session\\n" > "$resume"\n'
            '      printf "unfinished edit\\n" > "$SPECULA_WORK_DIR/spec/base.tla"\n'
            '      printf "interrupted\\n" > "$log"\n'
            "      exit 9\n"
            "    fi\n"
            '    if [ -f "$0.reject" ]; then printf "not complete\\n" > "$log"; exit 0; fi\n'
            '    if [ -f "$resume" ]; then cp "$resume" "$0.resumed"; fi\n'
            '    if [ ! -f "$0.nochange" ]; then printf "updated fixture model\\n" > "$SPECULA_WORK_DIR/spec/base.tla"; fi\n'
            '    printf "# CI fixture report\\nNo real verification performed.\\n" > "$SPECULA_WORK_DIR/ci-report.md"\n'
            '    printf \'{"agent":"codex","session_id":"fixture-native-session","usage":{"total_tokens":150,"cached_input_tokens":50},"total_cost_usd":0.01,"usage_complete":true}\\n\' > "${log%.log}.usage.json"\n'
            '    printf "SPECULA_INCREMENTAL_COMPLETE %s\\n" "$(basename "$SPECULA_RUN_DIR")" > "$log"\n'
            "    exit 0\n"
            "    ;;\n",
        )
        self.adapter.write_text(script)

    def git(self, *args: str) -> str:
        return subprocess.run(
            ["git", "-C", str(self.source), *args], check=True, capture_output=True, text=True
        ).stdout.strip()

    def commit(self, message: str) -> None:
        self.git("add", ".")
        self.git("commit", "-qm", message)

    def run_ci(self, *args: str) -> subprocess.CompletedProcess[str]:
        return self.helper.run_cli(self.root, ["run", f"--ci-dir={self.ci}", *args], cwd=self.work)

    def initialize(self) -> None:
        result = self.run_ci("--ci-init", "--agent=fake", f"--artifact={self.source}", "footest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((self.ci / "current/model/spec/base.tla").is_file())

    def change_source(self, text: str) -> None:
        (self.source / "logic.txt").write_text(text)
        self.commit("update")

    def latest(self) -> Path:
        return (self.ci / "runs/latest").resolve()

    def test_initialization_then_single_agent_incremental_update(self) -> None:
        self.initialize()
        old = (self.ci / "current").resolve()
        self.change_source("updated\n")
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        state = CIStore(self.ci).current()
        self.assertEqual(state["source_commit"], self.git("rev-parse", "HEAD"))
        self.assertNotEqual((self.ci / "current").resolve(), old)
        self.assertEqual((old / "model/spec/base.tla").read_text(), "fixture model\n")
        self.assertEqual((self.ci / "current/model/spec/base.tla").read_text(), "updated fixture model\n")
        self.assertIn("-initial\n+updated", (self.latest() / "source.diff").read_text())
        self.assertTrue((self.latest() / "model.diff").is_file())
        self.assertEqual((self.source / "logic.txt").read_text(), "updated\n")
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.assertEqual(Path(str(self.adapter) + ".phases").read_text().splitlines()[-1], "incremental")
        self.assertIn("Incremental workflow", (self.latest() / "footest/.specula-output/summary.md").read_text())
        usage = json.loads((self.latest() / "footest/.specula-output/.resource-summary-state.json").read_text())
        self.assertEqual(usage["phases"]["incremental"]["total_tokens"], 150)
        self.assertEqual(usage["phases"]["incremental"]["cost_usd"], 0.01)
        self.assertTrue(usage["run_complete"])

    def test_failure_keeps_current_and_resume_uses_original_conversation_and_source(self) -> None:
        self.initialize()
        old = (self.ci / "current").resolve()
        self.change_source("version B\n")
        sha_b = self.git("rev-parse", "HEAD")
        flag = Path(str(self.adapter) + ".fail")
        flag.touch()
        first = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(first.returncode, 9, first.stdout + first.stderr)
        self.assertEqual((self.ci / "current").resolve(), old)
        run = self.latest()
        original_diff = (run / "source.diff").read_bytes()
        self.change_source("version C\n")
        flag.unlink()
        resumed = self.run_ci(f"--run-id={run.name}")
        self.assertEqual(resumed.returncode, 0, resumed.stdout + resumed.stderr)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], sha_b)
        self.assertEqual((run / "source.diff").read_bytes(), original_diff)
        self.assertEqual(Path(str(self.adapter) + ".resumed").read_text(), "fixture-native-session\n")
        prompt = Path(str(self.adapter) + ".incremental.prompt").read_text()
        self.assertIn("exact session", prompt)
        self.assertNotIn("# Incremental CI Task", prompt)
        usage = json.loads((run / "footest/.specula-output/.resource-summary-state.json").read_text())
        self.assertEqual(usage["phases"]["incremental"]["total_tokens"], 150)
        self.assertTrue(usage["phases"]["incremental"]["usage_incomplete"])

    def test_no_model_change_still_advances_source_version(self) -> None:
        self.initialize()
        original = (self.ci / "current/model/spec/base.tla").read_bytes()
        self.change_source("documentation-only fixture update\n")
        Path(str(self.adapter) + ".nochange").touch()
        result = self.run_ci("--incremental", "--agent=fake", "--run-id=chosen-id")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.ci / "current/model/spec/base.tla").read_bytes(), original)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], self.git("rev-parse", "HEAD"))

    def test_zero_exit_and_existing_artifacts_are_not_completion(self) -> None:
        self.initialize()
        old = (self.ci / "current").resolve()
        self.change_source("version B\n")
        Path(str(self.adapter) + ".reject").touch()
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.ci / "current").resolve(), old)
        self.assertIn("did not report completion", result.stdout)

    def test_new_run_after_failure_uses_cumulative_diff(self) -> None:
        self.initialize()
        self.change_source("version B\n")
        flag = Path(str(self.adapter) + ".fail")
        flag.touch()
        self.assertEqual(self.run_ci("--incremental", "--agent=fake").returncode, 9)
        failed = self.latest()
        self.change_source("version C\n")
        flag.unlink()
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        diff = (self.latest() / "source.diff").read_text()
        self.assertIn("-initial\n+version C", diff)
        current = (self.ci / "current").resolve()
        stale = self.run_ci(f"--run-id={failed.name}")
        self.assertNotEqual(stale.returncode, 0)
        self.assertEqual((self.ci / "current").resolve(), current)

    def test_ci_directory_lock_rejects_concurrent_invocation(self) -> None:
        self.initialize()
        store = CIStore(self.ci)
        store.acquire()
        try:
            result = self.run_ci("--incremental", "--agent=fake")
        finally:
            store.close()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("another run", result.stderr)

    def test_dirty_initial_source_is_preserved_in_the_update_diff(self) -> None:
        (self.source / "logic.txt").write_text("dirty initial\n")
        (self.source / "untracked.txt").write_text("initial extra\n")
        self.initialize()
        state = CIStore(self.ci).current()
        self.assertTrue(state["dirty"])
        self.assertEqual((self.ci / state["source"] / "logic.txt").read_text(), "dirty initial\n")
        self.change_source("new committed source\n")
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("-dirty initial\n+new committed source", (self.latest() / "source.diff").read_text())

    def test_wrong_target_revision_does_not_launch_agent(self) -> None:
        self.initialize()
        self.change_source("version B\n")
        phases = Path(str(self.adapter) + ".phases").read_text()
        result = self.run_ci("--incremental", "--agent=fake", f"--revision={self.initial_sha}")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(Path(str(self.adapter) + ".phases").read_text(), phases)

    def test_dry_run_does_not_publish_or_instrument(self) -> None:
        result = self.run_ci("--ci-init", "--dry-run", f"--artifact={self.source}", "footest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse((self.ci / "current").exists())
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_saved_inputs_identify_both_versions_and_original_user_guidance(self) -> None:
        guidance = self.work / "guidance.md"
        guidance.write_text("Only the core protocol.\n")
        initial = self.run_ci(
            "--ci-init", "--agent=fake", f"--artifact={self.source}", f"--guidance={guidance}", "footest"
        )
        self.assertEqual(initial.returncode, 0, initial.stdout + initial.stderr)
        self.change_source("update\n")
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        inputs = json.loads((self.latest() / "ci-input.json").read_text())
        self.assertTrue(Path(inputs["old_source"]).is_dir())
        self.assertTrue(Path(inputs["old_model"]).is_dir())
        prompt = Path(str(self.adapter) + ".incremental.prompt").read_text()
        self.assertIn("Only the core protocol.", prompt)
        self.assertNotIn("## CI Initialization Guidance", prompt)
