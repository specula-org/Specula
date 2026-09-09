"""Exercise the real CLI and native resume wiring with a deterministic adapter.

The fixture does not perform semantic verification or call an LLM.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

import test_cli_pipeline as fixtures

from specula.ci_store import CIStore, asset_hashes


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
            "    python3 -c 'import json,sys; from pathlib import Path; "
            "work,run,adapter=map(Path,sys.argv[1:]); "
            'flag=Path(str(adapter)+".findings"); '
            "findings=json.loads(flag.read_text()) if flag.exists() else []; "
            '(work/"spec/confirmation-fixture.md").write_text("Current fixture confirmation for " + run.name); '
            '(work/"ci-verdict.json").write_text(json.dumps({"version":1,"run_id":run.name,"findings":findings}))\' '
            '"$SPECULA_WORK_DIR" "$SPECULA_RUN_DIR" "$0"\n'
            '    if [ -f "$0.omit-verdict" ]; then rm "$SPECULA_WORK_DIR/ci-verdict.json"; fi\n'
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

    def finding_status(self, status: str) -> None:
        Path(f"{self.adapter}.findings").write_text(
            json.dumps([{"id": "MC-1", "status": status, "evidence": "spec/confirmation-fixture.md"}])
        )

    def test_confirmed_bugs_fail_but_publish_a_completed_model(self) -> None:
        self.initialize()
        for status in ("REPRODUCED", "ENV_LIMITED"):
            with self.subTest(status=status):
                previous = (self.ci / "current").resolve()
                self.change_source(f"{status} fixture\n")
                self.finding_status(status)
                result = self.run_ci("--incremental", "--agent=fake")
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn("CI verdict: FAIL", result.stdout)
                self.assertIn("Current CI model updated", result.stdout)
                self.assertNotEqual((self.ci / "current").resolve(), previous)
                state = CIStore(self.ci).current()
                self.assertEqual(state["source_commit"], self.git("rev-parse", "HEAD"))
                self.assertEqual(state["verdict"], "FAIL")
                receipt = json.loads((self.latest() / "ci-result.json").read_text())
                self.assertTrue(receipt["complete"])
                self.assertEqual(receipt["verdict"], "FAIL")
                self.assertIn(
                    "CI verdict: **FAIL**", (self.latest() / "footest/.specula-output/summary.md").read_text()
                )
                usage = json.loads((self.latest() / "footest/.specula-output/.resource-summary-state.json").read_text())
                self.assertTrue(usage["run_complete"])

    def test_warning_and_verified_fix_can_advance_a_red_baseline(self) -> None:
        self.initialize()
        self.change_source("bug fixture\n")
        self.finding_status("REPRODUCED")
        self.assertEqual(self.run_ci("--incremental", "--agent=fake").returncode, 2)
        for status, verdict in (("MASKED", "WARNING"), ("FIXED", "PASS")):
            with self.subTest(status=status):
                self.change_source(f"{status} fixture\n")
                self.finding_status(status)
                result = self.run_ci("--incremental", "--agent=fake")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(CIStore(self.ci).current()["verdict"], verdict)
                self.assertIn(f"CI verdict: {verdict}", result.stdout)
                evidence = (self.ci / "current/model/spec/confirmation-fixture.md").read_text()
                self.assertIn(self.latest().name, evidence)
        self.assertIn("-MASKED fixture\n+FIXED fixture", (self.latest() / "source.diff").read_text())

    def test_old_findings_require_a_current_disposition_even_without_model_changes(self) -> None:
        self.initialize()
        self.change_source("bug fixture\n")
        self.finding_status("REPRODUCED")
        self.assertEqual(self.run_ci("--incremental", "--agent=fake").returncode, 2)
        baseline = (self.ci / "current").resolve()
        self.change_source("unrelated fixture update\n")
        Path(f"{self.adapter}.nochange").touch()
        Path(f"{self.adapter}.findings").unlink()
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("prior findings need current confirmation: MC-1", result.stdout)
        self.assertEqual((self.ci / "current").resolve(), baseline)
        self.assertFalse((self.latest() / "ci-result.json").exists())
        summary = (self.latest() / "footest/.specula-output/summary.md").read_text()
        self.assertNotIn("CI verdict: **PASS**", summary)
        self.assertIn("CI verdict: **INCOMPLETE**", summary)

    def test_completion_marker_without_verdict_is_not_a_passing_check(self) -> None:
        self.initialize()
        baseline = (self.ci / "current").resolve()
        self.change_source("update\n")
        Path(f"{self.adapter}.omit-verdict").touch()
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing current ci-verdict.json", result.stdout)
        self.assertEqual((self.ci / "current").resolve(), baseline)

    def test_compaction_yield_does_not_publish_and_failure_continues(self) -> None:
        self.initialize()
        previous = (self.ci / "current").resolve()
        original_assets = asset_hashes(previous)
        tool = self.root / "tools/context_control"
        (tool / ".venv/bin").mkdir(parents=True)
        (tool / ".venv/bin/python").symlink_to(sys.executable)
        shutil.copy2(fixtures.REAL_ROOT / "tools/context_control/compact.py", tool / "compact.py")
        # The real controller calls the native compactor, which reports that
        # this fixture-only backend has no native compaction API.
        script = self.adapter.read_text().replace(
            "  incremental)\n",
            "  incremental)\n"
            '    if [ ! -f "$0.context-yielded" ]; then\n'
            f'      test "$(readlink -f "{self.ci}/current")" = "{previous}"\n'
            '      printf "Pending fixture check; no semantic verification performed.\\n" > "$SPECULA_WORK_DIR/ci-context.md"\n'
            '      python3 -c \'import json,os,sys; from pathlib import Path; sys.path.insert(0,os.environ["SPECULA_ROOT"]+"/src"); '
            "from specula.context_control import request_compaction; "
            'Path(sys.argv[1]).write_text(json.dumps({"adapter":"fake","session_id":"fixture-context-session","cwd":os.getcwd()})); '
            'request_compaction("ci-context.md")\' "$resume"\n'
            '      printf "SPECULA_CONTEXT_YIELD %s\\n" "$SPECULA_CONTEXT_TOKEN" > "$log"\n'
            '      touch "$0.context-yielded"\n'
            "      exit 0\n"
            "    fi\n",
        )
        self.adapter.write_text(script)
        self.change_source("changed\n")
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Context compaction failed; continuing", result.stdout)
        self.assertNotEqual((self.ci / "current").resolve(), previous)
        self.assertEqual(asset_hashes(previous), original_assets)
        state = json.loads(Path(f"{self.adapter}.resumed").read_text())
        self.assertEqual(state["session_id"], "fixture-context-session")
        work = self.latest() / "footest/.specula-output"
        self.assertEqual(len(list(work.glob(".context-control/*/1/compaction.json"))), 1)
        self.assertFalse((self.ci / "current/model/.context-control").exists())

    def latest(self) -> Path:
        return (self.ci / "runs/latest").resolve()

    def supplied_model(self) -> Path:
        model = self.work / "Supplied.tla"
        model.write_text("---- MODULE Supplied ----\nSuppliedInvariant == TRUE\n====\n")
        return model

    def test_byom_model_initialization_then_incremental_update(self) -> None:
        supplied = self.supplied_model()
        original = supplied.read_bytes()
        guidance = self.work / "guidance.md"
        guidance.write_text("Preserve the supplied election scope.\n")
        result = self.run_ci(
            "--ci-init",
            "--agent=fake",
            f"--artifact={self.source}",
            f"--byom={supplied}",
            f"--guidance={guidance}",
            "footest",
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        run = self.latest()
        old = (self.ci / "current").resolve()
        self.assertEqual((old / "model/spec/base.tla").read_bytes(), original)
        self.assertTrue((old / "model/harness/run.sh").is_file())
        self.assertTrue((old / "model/byom-modification-report.md").is_file())
        self.assertEqual(CIStore(self.ci).current()["source_commit"], self.initial_sha)
        phases = Path(f"{self.adapter}.phases").read_text().splitlines()
        self.assertEqual(
            phases,
            [
                "spec_generation",
                "harness_generation",
                "spec_validation",
                "bug_confirmation_turn",
                "bug_classification",
            ],
        )
        for phase in ("spec_generation", "harness_generation"):
            prompt = Path(f"{self.adapter}.{phase}.prompt").read_text()
            self.assertIn("# BYOM Phase", prompt)
            self.assertIn("## CI Initialization Guidance", prompt)
            self.assertIn(guidance.read_text(), prompt)
        self.assertIn("SKIPPED (BYOM)", (run / "pipeline-summary.md").read_text())
        self.assertIn(
            "[BYOM modification report](byom-modification-report.md)",
            (run / "footest/.specula-output/index.md").read_text(),
        )
        self.assertEqual(supplied.read_bytes(), original)
        self.assertEqual(self.git("status", "--porcelain"), "")

        self.change_source("updated\n")
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], self.git("rev-parse", "HEAD"))
        self.assertEqual((old / "model/spec/base.tla").read_bytes(), original)
        self.assertEqual((self.ci / "current/model/spec/base.tla").read_text(), "updated fixture model\n")
        self.assertTrue((old / "model/byom-modification-report.md").is_file())
        self.assertFalse((self.ci / "current/model/byom-modification-report.md").exists())
        self.assertNotIn("BYOM modification report", (self.latest() / "footest/.specula-output/index.md").read_text())
        self.assertIn("SuppliedInvariant", (self.latest() / "model.diff").read_text())
        self.assertEqual(Path(f"{self.adapter}.incremental.byom").read_text().strip(), "")
        prompt = Path(f"{self.adapter}.incremental.prompt").read_text()
        self.assertIn(guidance.read_text(), prompt)
        self.assertNotIn("## CI Initialization Guidance", prompt)
        self.assertEqual(supplied.read_bytes(), original)

    def test_byom_bundle_is_adopted_and_still_validated(self) -> None:
        supplied = self.work / "bundle"
        assets = {
            "modeling-brief.md": "# Supplied scope\n",
            "spec/base.tla": "supplied reference\n",
            "spec/MC.tla": "supplied MC wrapper\n",
            "spec/MC.cfg": "supplied MC config\n",
            "spec/Trace.tla": "supplied Trace wrapper\n",
            "spec/Trace.cfg": "supplied Trace config\n",
            "spec/instrumentation-spec.md": "supplied mapping\n",
            "harness/run.sh": "#!/bin/sh\n# Supplied harness\nexit 0\n",
            "traces/retained.ndjson": '{"event":"retained"}\n',
            "spec/old-validation.log": "Prior evidence only.\n",
        }
        for name, content in assets.items():
            path = supplied / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        (supplied / "harness/run.sh").chmod(0o755)
        before = asset_hashes(supplied)
        result = self.run_ci("--ci-init", "--agent=fake", f"--artifact={self.source}", f"--byom={supplied}", "footest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name, content in assets.items():
            self.assertEqual((self.ci / "current/model" / name).read_text(), content)
        self.assertEqual(asset_hashes(supplied), before)
        self.assertEqual(Path(f"{self.adapter}.validation-count").read_text(), "x")
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_byom_initialization_failure_and_resume_preserve_inputs(self) -> None:
        supplied = self.supplied_model()
        original = supplied.read_bytes()
        self.adapter = self.helper._ci_init_adapter(self.root, interrupt_validation=True)
        first = self.run_ci("--ci-init", "--agent=fake", f"--artifact={self.source}", f"--byom={supplied}", "footest")
        self.assertEqual(first.returncode, 9, first.stdout + first.stderr)
        run = self.latest()
        self.assertFalse((self.ci / "current").is_symlink())
        self.assertFalse((run / "ci-result.json").exists())
        baseline = (run / "ci-baseline.json").read_bytes()
        self.assertEqual(json.loads(baseline)["validation_status"], "UNVERIFIED")
        phases_before = Path(f"{self.adapter}.phases").read_bytes()

        replacement = self.work / "replacement.tla"
        replacement.write_text("another input\n")
        rejected = self.run_ci(f"--run-id={run.name}", f"--byom={replacement}")
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn("--byom differs", rejected.stderr)
        self.assertIn("start a new run", rejected.stderr)
        self.assertEqual(Path(f"{self.adapter}.phases").read_bytes(), phases_before)
        supplied.rename(self.work / "saved.tla")
        rejected = self.run_ci(f"--run-id={run.name}")
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn("BYOM input is unavailable", rejected.stderr)
        self.assertEqual(Path(f"{self.adapter}.phases").read_bytes(), phases_before)
        (self.work / "saved.tla").rename(supplied)

        self.change_source("later source\n")
        resumed = self.run_ci(f"--run-id={run.name}")
        self.assertEqual(resumed.returncode, 0, resumed.stdout + resumed.stderr)
        self.assertEqual(self.latest(), run)
        self.assertEqual((run / "ci-baseline.json").read_bytes(), baseline)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], self.initial_sha)
        self.assertEqual((self.ci / "current/model/spec/base.tla").read_bytes(), original)
        self.assertEqual(supplied.read_bytes(), original)
        self.assertEqual(Path(f"{self.adapter}.spec_validation.byom").read_text().strip(), str(supplied))
        self.assertIn("exact session", Path(f"{self.adapter}.spec_validation.prompt").read_text())
        phases = Path(f"{self.adapter}.phases").read_text().splitlines()
        self.assertNotIn("code_analysis", phases)
        self.assertEqual(phases.count("spec_generation"), 1)
        self.assertEqual(phases.count("harness_generation"), 1)
        self.assertEqual(phases.count("spec_validation"), 2)
        self.assertTrue((self.ci / "current/model/byom-modification-report.md").is_file())
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_byom_dry_run_and_invalid_modes_do_not_publish(self) -> None:
        supplied = self.supplied_model()
        result = self.run_ci("--ci-init", "--dry-run", f"--artifact={self.source}", f"--byom={supplied}", "footest")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse((self.ci / "current").is_symlink())
        self.assertFalse(Path(f"{self.adapter}.phases").exists())
        runs = set((self.ci / "runs").iterdir())
        for flags in (
            ["--incremental"],
            ["--ci-init", "--ci-candidate"],
            ["--ci-init", "--skip-validate"],
            ["--ci-init", "--no-isolate"],
            ["--ci-init", "--enable-reviews"],
            ["--ci-init", "--run-id=missing"],
        ):
            with self.subTest(flags=flags):
                rejected = self.run_ci(*flags, f"--byom={supplied}", "footest")
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(set((self.ci / "runs").iterdir()), runs)
                self.assertFalse((self.ci / "current").is_symlink())
                self.assertFalse(Path(f"{self.adapter}.phases").exists())
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_byom_cannot_overwrite_an_initialized_ci_directory(self) -> None:
        self.initialize()
        old = (self.ci / "current").resolve()
        before = asset_hashes(old)
        phases = Path(f"{self.adapter}.phases").read_bytes()
        result = self.run_ci("--ci-init", f"--byom={self.supplied_model()}", "footest")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("already initialized", result.stderr)
        self.assertEqual((self.ci / "current").resolve(), old)
        self.assertEqual(asset_hashes(old), before)
        self.assertEqual(Path(f"{self.adapter}.phases").read_bytes(), phases)

    def test_missing_byom_report_prevents_publication(self) -> None:
        supplied = self.supplied_model()
        Path(f"{self.adapter}.omit-byom-report").touch()
        result = self.run_ci("--ci-init", "--agent=fake", f"--artifact={self.source}", f"--byom={supplied}", "footest")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.ci / "current").is_symlink())
        self.assertFalse((self.latest() / "ci-result.json").exists())

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

    def test_repair_can_finish_without_an_intermediate_ci_report(self) -> None:
        self.initialize()
        old = (self.ci / "current").resolve()
        self.change_source("repair fixture\n")
        # Simulate persisted repair evidence before the fixture's final model
        # and report. This checks lifecycle compatibility, not Agent reasoning.
        script = self.adapter.read_text().replace(
            "  incremental)\n",
            "  incremental)\n"
            '    test ! -e "$SPECULA_WORK_DIR/ci-report.md" || exit 10\n'
            '    printf "fixture model needing repair\\n" > "$SPECULA_WORK_DIR/spec/base.tla"\n'
            '    printf "Fixture repair and recheck recorded; no semantic verification performed.\\n" > "$SPECULA_WORK_DIR/spec/changelog.md"\n'
            '    test ! -e "$SPECULA_WORK_DIR/ci-report.md" || exit 10\n',
        )
        self.adapter.write_text(script)
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        model = self.ci / "current/model"
        self.assertNotEqual((self.ci / "current").resolve(), old)
        self.assertEqual((model / "spec/base.tla").read_text(), "updated fixture model\n")
        self.assertIn("Fixture repair and recheck", (model / "spec/changelog.md").read_text())
        self.assertTrue((model / "ci-report.md").is_file())
        phases = Path(f"{self.adapter}.phases").read_text().splitlines()
        self.assertEqual(phases.count("incremental"), 1)
        self.assertEqual(phases[-1], "incremental")

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
        work = run / "footest/.specula-output"
        self.assertFalse((work / "ci-report.md").exists())
        self.assertEqual((work / "spec/base.tla").read_text(), "unfinished edit\n")
        self.assertFalse((run / "ci-result.json").exists())
        original_diff = (run / "source.diff").read_bytes()
        self.change_source("version C\n")
        flag.unlink()
        resumed = self.run_ci(f"--run-id={run.name}")
        self.assertEqual(resumed.returncode, 0, resumed.stdout + resumed.stderr)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], sha_b)
        self.assertEqual((run / "source.diff").read_bytes(), original_diff)
        self.assertEqual(Path(str(self.adapter) + ".resumed").read_text(), "fixture-native-session\n")
        self.assertEqual((self.ci / "current/model/ci-report.md").read_bytes(), (work / "ci-report.md").read_bytes())
        prompt = Path(str(self.adapter) + ".incremental.prompt").read_text()
        self.assertIn("exact session", prompt)
        self.assertNotIn("# Incremental CI Task", prompt)
        usage = json.loads((run / "footest/.specula-output/.resource-summary-state.json").read_text())
        self.assertEqual(usage["phases"]["incremental"]["total_tokens"], 150)
        self.assertTrue(usage["phases"]["incremental"]["usage_incomplete"])

    def test_candidate_resume_cannot_update_the_current_model(self) -> None:
        self.initialize()
        previous = (self.ci / "current").resolve()
        self.change_source("candidate source\n")
        flag = Path(str(self.adapter) + ".fail")
        flag.touch()
        first = self.run_ci("--incremental", "--ci-candidate", "--agent=fake", "--model=fixture-model")
        self.assertEqual(first.returncode, 9, first.stdout + first.stderr)
        run = self.latest()
        flag.unlink()
        result = self.run_ci(f"--run-id={run.name}")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.ci / "current").resolve(), previous)
        receipt = json.loads((run / "ci-result.json").read_text())
        self.assertTrue(receipt["candidate"])
        self.assertTrue(receipt["complete"])
        self.assertTrue((self.ci / receipt["snapshot"] / "model/spec/base.tla").is_file())

    def test_no_model_change_still_advances_source_version(self) -> None:
        self.initialize()
        original = (self.ci / "current/model/spec/base.tla").read_bytes()
        self.change_source("documentation-only fixture update\n")
        Path(str(self.adapter) + ".nochange").touch()
        result = self.run_ci("--incremental", "--agent=fake")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.ci / "current/model/spec/base.tla").read_bytes(), original)
        self.assertEqual(CIStore(self.ci).current()["source_commit"], self.git("rev-parse", "HEAD"))

    def test_unknown_run_id_cannot_start_or_publish_a_new_workflow(self) -> None:
        self.initialize()
        current = (self.ci / "current").resolve()
        state = (current / "state.json").read_bytes()
        model = (current / "model/spec/base.tla").read_bytes()
        runs = set((self.ci / "runs").iterdir())
        phases = Path(str(self.adapter) + ".phases").read_bytes()
        for index, flags in enumerate(([], ["--incremental"], ["--ci-init"], ["--dry-run"])):
            with self.subTest(flags=flags):
                result = self.run_ci(
                    *flags, f"--run-id=missing-{index}", "--agent=fake", f"--artifact={self.source}", "footest"
                )
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("does not exist; cannot resume", result.stderr)
                self.assertEqual(set((self.ci / "runs").iterdir()), runs)
                self.assertEqual(Path(str(self.adapter) + ".phases").read_bytes(), phases)
                self.assertEqual((self.ci / "current").resolve(), current)
                self.assertEqual((current / "state.json").read_bytes(), state)
                self.assertEqual((current / "model/spec/base.tla").read_bytes(), model)

    def test_unknown_run_id_does_not_create_a_ci_directory(self) -> None:
        result = self.run_ci("--run-id=missing", "--agent=fake", f"--artifact={self.source}", "footest")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does not exist; cannot resume", result.stderr)
        self.assertFalse(self.ci.exists())
        self.assertFalse(Path(str(self.adapter) + ".phases").exists())

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
