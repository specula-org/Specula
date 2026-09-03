"""End-to-end dry-run test for the `specula` CLI.

Drives the whole chain a user hits — `cli.py` -> `bash launch_pipeline.sh` (the
exec shim) -> `python3 pipelinelib.py` — with `--dry-run`, and asserts on the
observable result: exit code, the isolated `runs/<run-id>/` layout the 7d flip
made the default, the `runs/latest` symlink, and that neither the launch cwd nor
the canonical case dir is written. No unit test crosses the shim boundary; this
one does. `--dry-run` prints each phase's command instead of spawning an agent,
so it needs no `claude` and no network.

Hermetic via a copied specroot: `SPECULA_ROOT` derives from the entry file's
location (`parents[2]`), so copying the package + launch scripts into a tmp tree
makes the minted `runs/` land there, never in the real repo.

stdlib unittest, collected natively by pytest:

    uv run python -m unittest tests.e2e.test_cli_pipeline -v
"""

from __future__ import annotations

import contextlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

from specula import phaselib

REAL_ROOT = Path(__file__).resolve().parents[2]
REAL_PKG = REAL_ROOT / "src" / "specula"
REAL_LAUNCH = REAL_ROOT / "scripts" / "launch"
REAL_SCHEDULER = REAL_ROOT / "scripts" / "exp" / "scheduler.sh"

# minted run id: generate_run_id() -> YYYYMMDD-HHMMSS-xxxx
RUN_ID_RE = re.compile(r"^\d{8}-\d{6}-[0-9a-f]{4}$")

# env that would steer isolation/agent selection; popped so the default-mint
# path is what runs (an ambient SPECULA_RUN_DIR would reroute the mint).
_VOLATILE = (
    "SPECULA_RUN_DIR",
    "SPECULA_PHASE",
    "SPECULA_WORK_DIR",
    "SPECULA_PIPELINE_LOG",
    "SPECULA_SOURCE_SNAPSHOT",
    "SPECULA_SANDBOX_EXTRA_WRITE",
    "SPECULA_STOP_GATE",
    "SPECULA_MODEL",
    "SPECULA_EFFORT",
    "SPECULA_BYOM_PATH",
    "CLAUDE_CONFIG_DIR",
    "CLAUDE_ALIAS",
    "CLAUDE_EFFORT",
    "CLAUDE_MODEL",
    "CODEX_MODEL",
    "CODEX_EFFORT",
    "COPILOT_MODEL",
    "SPECULA_INVOCATION_ID",
    "SPECULA_MANUAL_RESUME",
    "SPECULA_FRESH_CONTEXT",
    "SPECULA_RUN_LOCK_FD",
)

ALL_PHASE_SKIPS = (
    "--skip-analysis",
    "--skip-specgen",
    "--skip-harness",
    "--skip-validate",
    "--skip-confirmation",
    "--skip-classification",
    "--skip-repair-loop",
)


class CliE2E(unittest.TestCase):
    def specroot(self, case_dirs: tuple[str, ...] = ("footest",)) -> Path:
        """A minimal hermetic copy of the repo: the package (so intra-package
        imports resolve), the launch scripts (the shim + phase launchers), the
        scheduler shim, and empty canonical case dirs."""
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        root = Path(d.name).resolve() / "specroot"
        (root / "src").mkdir(parents=True)
        shutil.copytree(REAL_PKG, root / "src" / "specula", ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(REAL_LAUNCH, root / "scripts" / "launch", ignore=shutil.ignore_patterns("__pycache__"))
        (root / "scripts" / "exp").mkdir(parents=True, exist_ok=True)
        shutil.copy2(REAL_SCHEDULER, root / "scripts" / "exp" / "scheduler.sh")
        for c in case_dirs:
            (root / "case-studies" / c).mkdir(parents=True)
        return root

    def workdir(self) -> Path:
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return Path(d.name).resolve()

    def _instant_sleep_bindir(self) -> Path:
        """The scheduler shells out to `sleep` for its poll cadence (deliberately,
        so it can be stubbed); an instant `sleep` on PATH keeps the batch test from
        waiting through the real 3s/30s sweeps."""
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        bindir = Path(d.name).resolve()
        stub = bindir / "sleep"
        stub.write_text("#!/bin/sh\nexit 0\n")
        stub.chmod(0o755)
        return bindir

    def run_cli(
        self, root: Path, args: list[str], cwd: Path, stub_sleep: bool = False
    ) -> subprocess.CompletedProcess[str]:
        env = {k: v for k, v in os.environ.items() if k not in _VOLATILE}
        env["HOME"] = str(cwd)  # empty HOME -> quota gate finds no creds, proceeds
        if stub_sleep:
            env["PATH"] = f"{self._instant_sleep_bindir()}:" + env.get("PATH", "")
        return subprocess.run(
            [sys.executable, str(root / "src" / "specula" / "cli.py"), *args],
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
        )

    def sole_run_dir(self, root: Path) -> Path:
        runs_dir = root / "runs"
        runs = [d for d in runs_dir.iterdir() if d.is_dir() and not d.is_symlink()] if runs_dir.is_dir() else []
        self.assertEqual(len(runs), 1, f"expected exactly one minted run, got {[r.name for r in runs]}")
        return runs[0]

    # ── default isolated layout (the 7d default) ─────────────────────────────
    def test_run_dry_run_mints_isolated_layout(self) -> None:
        root = self.specroot()
        work = self.workdir()
        proc = self.run_cli(root, ["run", "--dry-run", "footest"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)

        run = self.sole_run_dir(root)
        self.assertRegex(run.name, RUN_ID_RE)
        for artifact in ("run.json", "pipeline.log", "pipeline-summary.md"):
            self.assertTrue((run / artifact).is_file(), f"missing {artifact} at run root")

        latest = root / "runs" / "latest"
        self.assertTrue(latest.is_symlink())
        self.assertEqual(os.readlink(latest), run.name)

        # neither the launch cwd nor the canonical case dir is written
        self.assertFalse((work / ".specula-output").exists(), "launch cwd polluted")
        self.assertFalse((root / "case-studies" / "footest" / ".specula-output").exists(), "case dir polluted")

    def test_run_dry_run_sequences_phases(self) -> None:
        root = self.specroot()
        work = self.workdir()
        proc = self.run_cli(root, ["run", "--dry-run", "footest"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        out = proc.stdout
        # the full-chain banner + a dry-run phase line (proves the shim reached
        # pipelinelib and printed rather than launched) + the completion line
        self.assertIn("Specula", out)
        self.assertIn("[DRY RUN] bash scripts/launch/launch_code_analysis.sh", out)
        self.assertIn("Pipeline completed", out)

    def test_byom_dry_run_skips_analysis_and_keeps_multi_target_pipeline(self) -> None:
        root = self.specroot(case_dirs=("alpha", "beta"))
        work = self.workdir()
        supplied = work / "provided"
        supplied.mkdir()
        proc = self.run_cli(
            root,
            [
                "run",
                "--dry-run",
                f"--byom={supplied}",
                "alpha|o/a|Go|ref",
                "beta|o/b|Rust|ref",
            ],
            cwd=work,
        )

        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("Skipping Phase 1 (--skip-analysis)", proc.stdout)
        self.assertNotIn("launch_code_analysis.sh", proc.stdout)
        for launcher in (
            "launch_spec_generation.sh",
            "launch_harness_generation.sh",
            "launch_spec_validation.sh",
            "launch_bug_confirmation.sh",
            "launch_bug_classification.sh",
        ):
            self.assertIn(launcher, proc.stdout)
        meta = json.loads((self.sole_run_dir(root) / "run.json").read_text())
        self.assertEqual(meta["byom"], str(supplied))
        self.assertEqual(meta["resume_configuration"]["byom"], str(supplied))

    def test_byom_rejects_skips_and_legacy_layout(self) -> None:
        root = self.specroot()
        work = self.workdir()
        supplied = work / "Model.tla"
        supplied.write_text("---- MODULE Model ----\n====\n")
        for flag in (*ALL_PHASE_SKIPS, "--no-isolate"):
            with self.subTest(flag=flag):
                proc = self.run_cli(root, ["run", f"--byom={supplied}", flag, "footest"], cwd=work)
                self.assertNotEqual(proc.returncode, 0)
                self.assertIn("--byom", proc.stderr)

    def test_byom_is_not_a_public_individual_phase_option(self) -> None:
        root = self.specroot()
        work = self.workdir()
        supplied = work / "Model.tla"
        supplied.write_text("---- MODULE Model ----\n====\n")

        proc = self.run_cli(root, ["specgen", f"--byom={supplied}", "footest"], cwd=work)

        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("Unknown option: --byom", proc.stdout)

    def test_byom_fake_adapter_completes_phase2_through_final_report(self) -> None:
        root = self.specroot()
        work = self.workdir()
        artifact = work / "artifact"
        artifact.mkdir()
        supplied = work / "Model.tla"
        supplied.write_text("---- MODULE Model ----\n====\n")
        adapter = root / "scripts" / "launch" / "adapters" / "fake.sh"
        adapter.write_text(
            "#!/bin/sh\n"
            "set -eu\n"
            'printf "%s\\n" "$SPECULA_PHASE" >> "$0.phases"\n'
            'test "$SPECULA_BYOM_PATH" = "' + str(supplied) + '"\n'
            'case "$SPECULA_PHASE" in\n'
            "  spec_generation)\n"
            '    mkdir -p "$SPECULA_WORK_DIR/spec"\n'
            '    printf "# BYOM brief\\n" > "$SPECULA_WORK_DIR/modeling-brief.md"\n'
            "    for file in base.tla MC.tla Trace.tla instrumentation-spec.md; do\n"
            '      printf "seeded\\n" > "$SPECULA_WORK_DIR/spec/$file"\n'
            "    done\n"
            "    ;;\n"
            "  harness_generation)\n"
            '    mkdir -p "$SPECULA_WORK_DIR/harness" "$SPECULA_WORK_DIR/traces"\n'
            '    printf "#!/bin/sh\\n" > "$SPECULA_WORK_DIR/harness/run.sh"\n'
            '    printf \'{"event":"seed"}\\n\' > "$SPECULA_WORK_DIR/traces/seed.ndjson"\n'
            "    ;;\n"
            "  spec_validation)\n"
            '    printf "# Bug report\\n\\nNo violations found.\\n" > "$SPECULA_WORK_DIR/spec/bug-report.md"\n'
            '    printf \'{"schema_version":"2","system":"footest","generated_by":"validation-workflow","findings":[]}\\n\' '
            '> "$SPECULA_WORK_DIR/spec/findings.json"\n'
            '    printf "# Validation changelog\\n" > "$SPECULA_WORK_DIR/spec/changelog.md"\n'
            "    ;;\n"
            "  bug_confirmation_turn)\n"
            '    printf \'{"generated_by":"consolidate","findings":[]}\\n\' '
            '> "$SPECULA_WORK_DIR/spec/candidates.json"\n'
            "    ;;\n"
            "  bug_classification)\n"
            '    printf "# Severity Classification\\n\\n## Summary\\n\\n## Per-entry classification\\n" '
            '> "$SPECULA_WORK_DIR/bug-severity.md"\n'
            '    printf "No impact-bearing findings were recorded.\\n\\n## Findings\\n\\n- Other dispositions: 0.\\n\\n## Validation limits\\n\\nNo finding-specific validation limits were recorded.\\n" '
            '> "$SPECULA_WORK_DIR/.summary-findings.md"\n'
            '    printf "# BYOM Modification Report\\n\\nThe supplied model was reused.\\n" '
            '> "$SPECULA_WORK_DIR/byom-modification-report.md"\n'
            "    ;;\n"
            "  *) exit 97 ;;\n"
            "esac\n"
        )
        adapter.chmod(0o755)

        proc = self.run_cli(
            root,
            [
                "run",
                "--agent=fake",
                f"--artifact={artifact}",
                f"--byom={supplied}",
                "footest|owner/repo|Go|reference",
            ],
            cwd=work,
        )

        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        run = self.sole_run_dir(root)
        target = run / "footest" / ".specula-output"
        self.assertTrue((target / "byom-modification-report.md").is_file())
        self.assertIn(
            "[BYOM modification report](byom-modification-report.md)",
            (target / "index.md").read_text(),
        )
        phases = Path(f"{adapter}.phases").read_text().splitlines()
        self.assertNotIn("code_analysis", phases)
        self.assertIn("spec_generation", phases)
        self.assertIn("harness_generation", phases)
        self.assertIn("spec_validation", phases)
        self.assertIn("bug_confirmation_turn", phases)
        self.assertIn("bug_classification", phases)
        self.assertEqual(supplied.read_text(), "---- MODULE Model ----\n====\n")

    def test_run_id_resumes_interrupted_validation_without_phase_skip_flags(self) -> None:
        root = self.specroot()
        work = self.workdir()
        artifact = work / "artifact"
        artifact.mkdir()
        adapter = root / "scripts" / "launch" / "adapters" / "fake.sh"
        adapter.write_text(
            "#!/bin/sh\n"
            "set -eu\n"
            "prompt= log= resume=\n"
            'for arg do case "$arg" in\n'
            "  --prompt-file=*) prompt=${arg#*=} ;;\n"
            "  --log=*) log=${arg#*=} ;;\n"
            "  --resume-state=*) resume=${arg#*=} ;;\n"
            "esac; done\n"
            'case "$SPECULA_PHASE" in\n'
            "  spec_validation)\n"
            '    printf x >> "$0.validation-count"\n'
            '    attempt=$(wc -c < "$0.validation-count")\n'
            '    if [ "$attempt" -eq 1 ]; then\n'
            '      printf "validation-session\n" > "$resume"\n'
            '      printf "interrupted\n" > "$log"\n'
            "      exit 9\n"
            "    fi\n"
            '    test "$(cat "$resume")" = "validation-session"\n'
            '    cp "$prompt" "$0.validation-prompt"\n'
            '    printf "bug report\n" > "$SPECULA_WORK_DIR/spec/bug-report.md"\n'
            "    ;;\n"
            "  bug_confirmation_turn)\n"
            '    printf \'{"generated_by":"consolidate","findings":[]}\\n\' '
            '> "$SPECULA_WORK_DIR/spec/candidates.json"\n'
            "    ;;\n"
            "  bug_classification)\n"
            '    printf "# Severity Classification\\n\\n## Summary\\n\\n## Per-entry classification\\n" '
            '> "$SPECULA_WORK_DIR/bug-severity.md"\n'
            '    printf "No impact-bearing findings were recorded.\\n\\n## Findings\\n\\n- Other dispositions: 0.\\n\\n## Validation limits\\n\\nNo finding-specific validation limits were recorded.\\n" '
            '> "$SPECULA_WORK_DIR/.summary-findings.md"\n'
            "    ;;\n"
            "  *) exit 97 ;;\n"
            "esac\n"
            'printf "continued\n" > "$log"\n'
        )
        adapter.chmod(0o755)
        target = "footest|owner/repo|Go|reference"
        run_id = "resume-validation"

        setup = self.run_cli(
            root,
            [
                "run",
                f"--run-id={run_id}",
                "--agent=fake",
                f"--artifact={artifact}",
                *ALL_PHASE_SKIPS,
                target,
            ],
            cwd=work,
        )
        self.assertEqual(setup.returncode, 0, setup.stderr)
        run = root / "runs" / run_id
        wd = run / "footest" / ".specula-output"
        for rel in (
            "modeling-brief.md",
            "spec/base.tla",
            "spec/MC.tla",
            "spec/Trace.tla",
            "spec/instrumentation-spec.md",
        ):
            path = wd / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("seeded\n")

        first = self.run_cli(
            root,
            [
                "run",
                f"--run-id={run_id}",
                "--fresh-context",
                "--skip-analysis",
                "--skip-specgen",
                "--skip-harness",
                "--skip-confirmation",
                "--skip-classification",
                "--skip-repair-loop",
            ],
            cwd=work,
        )
        self.assertEqual(first.returncode, 9, first.stdout + first.stderr)

        resumed = self.run_cli(root, ["run", f"--run-id={run_id}"], cwd=work)

        self.assertEqual(resumed.returncode, 0, resumed.stdout + resumed.stderr)
        self.assertEqual(Path(f"{adapter}.validation-count").read_text(), "xx")
        self.assertEqual(
            Path(f"{adapter}.validation-prompt").read_text(),
            phaselib._MANUAL_SESSION_RESUME_PROMPT,
        )
        self.assertTrue((wd / "confirmed-bugs.md").is_file())
        self.assertTrue((wd / "bug-severity.md").is_file())
        self.assertTrue((wd / ".summary-findings.md").is_file())
        summary = (wd / "summary.md").read_text()
        self.assertIn("- Run status: **Complete**", summary)
        self.assertIn("No impact-bearing findings were recorded.", summary)
        self.assertIn("## Findings", summary)
        self.assertIn("## Validation limits", summary)
        self.assertIn("## Detailed reports", summary)
        self.assertIn("## Resource usage", summary)
        self.assertEqual(list((run / ".specula-resume" / "active").glob("*.json")), [])
        self.assertEqual(list((run / ".specula-resume" / "completed").glob("*.json")), [])

    def test_attach_refuses_live_orphan_after_dispatcher_sigkill(self) -> None:
        root = self.specroot()
        work = self.workdir()
        artifact = work / "artifact"
        artifact.mkdir()
        adapter = root / "scripts" / "launch" / "adapters" / "fake.sh"
        adapter.write_text(
            "#!/bin/sh\n"
            "set -eu\n"
            "resume=\n"
            'for arg do case "$arg" in --resume-state=*) resume=${arg#*=} ;; esac; done\n'
            'printf "orphan-session\\n" > "$resume"\n'
            'printf "%s\\n" "$$" > "$0.pid"\n'
            'printf "%s\\n" "$PPID" > "$0.phase-pid"\n'
            'printf x >> "$0.started"\n'
            "trap 'exit 143' TERM INT HUP\n"
            "while :; do sleep 1; done\n"
        )
        adapter.chmod(0o755)
        env = {key: value for key, value in os.environ.items() if key not in _VOLATILE}
        env["HOME"] = str(work)
        run_id = "orphaned-agent"
        first = subprocess.Popen(
            [
                sys.executable,
                str(root / "src" / "specula" / "cli.py"),
                "run",
                f"--run-id={run_id}",
                "--agent=fake",
                f"--artifact={artifact}",
                "--skip-specgen",
                "--skip-harness",
                "--skip-validate",
                "--skip-confirmation",
                "--skip-classification",
                "--skip-repair-loop",
                "footest|owner/repo|Go|reference",
            ],
            cwd=work,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        agent_pid_file = Path(f"{adapter}.pid")

        def cleanup() -> None:
            with contextlib.suppress(OSError, ValueError):
                os.kill(first.pid, signal.SIGKILL)
            with contextlib.suppress(subprocess.TimeoutExpired):
                first.wait(timeout=2)
            if agent_pid_file.is_file():
                with contextlib.suppress(OSError, ValueError):
                    os.killpg(int(agent_pid_file.read_text()), signal.SIGKILL)
            if first.stdout is not None:
                first.stdout.close()

        self.addCleanup(cleanup)
        run = root / "runs" / run_id
        active_dir = run / ".specula-resume" / "active"
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if Path(f"{adapter}.started").is_file() and list(active_dir.glob("*.json")):
                break
            if first.poll() is not None:
                output = first.stdout.read() if first.stdout is not None else ""
                self.fail(f"dispatcher exited before the agent started: {output}")
            time.sleep(0.02)
        self.assertTrue(Path(f"{adapter}.started").is_file())
        active_paths = list(active_dir.glob("*.json"))
        self.assertEqual(len(active_paths), 1)
        before = active_paths[0].read_bytes()

        os.kill(first.pid, signal.SIGKILL)
        first.wait(timeout=5)
        phase_pid = int(Path(f"{adapter}.phase-pid").read_text())
        os.kill(phase_pid, signal.SIGKILL)
        os.kill(int(agent_pid_file.read_text()), 0)
        attached = self.run_cli(root, ["run", f"--run-id={run_id}"], cwd=work)

        self.assertNotEqual(attached.returncode, 0, attached.stdout + attached.stderr)
        self.assertIn("live phase or agent", attached.stderr)
        self.assertIn("terminate it manually", attached.stderr)
        self.assertEqual(Path(f"{adapter}.started").read_text(), "x")
        self.assertEqual(active_paths[0].read_bytes(), before)

    def test_noop_run_writes_two_level_human_indexes(self) -> None:
        root = self.specroot()
        work = self.workdir()
        proc = self.run_cli(root, ["run", *ALL_PHASE_SKIPS, "footest"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)

        run = self.sole_run_dir(root)
        run_index = (run / "index.md").read_text()
        target_dir = run / "footest" / ".specula-output"
        target_index = (target_dir / "index.md").read_text()
        resource_summary = (target_dir / "summary.md").read_text()

        self.assertIn("| footest | [Open results](footest/.specula-output/index.md) |", run_index)
        self.assertIn("- Final summary: [pipeline-summary.md](pipeline-summary.md)", run_index)
        self.assertNotIn("run.json", run_index)
        self.assertNotIn("tlc-resources.json", run_index)

        self.assertIn("# footest Results", target_index)
        self.assertIn("## Final Reports", target_index)
        self.assertIn("[Summary](summary.md)", target_index)
        self.assertIn("## Supporting Analysis", target_index)
        self.assertIn("Modeling brief: Not available", target_index)
        self.assertIn("[pipeline.log](../../pipeline.log)", target_index)
        self.assertNotIn("## Reviews", target_index)
        self.assertNotIn("findings.json", target_index)
        self.assertIn("- Run status: **Complete**", resource_summary)
        self.assertIn("The findings summary is unavailable", resource_summary)
        self.assertIn("Final findings reporting was skipped.", resource_summary)
        self.assertIn("| **Total (incomplete)** | - | - | - |", resource_summary)
        self.assertFalse((run / "reports").exists())
        self.assertFalse((target_dir / "classification").exists())

    def test_noop_multi_target_run_keeps_target_indexes_separate(self) -> None:
        root = self.specroot(case_dirs=("alpha", "beta"))
        work = self.workdir()
        proc = self.run_cli(
            root,
            ["run", *ALL_PHASE_SKIPS, "alpha|o/a|Go|ref", "beta|o/b|Rust|ref"],
            cwd=work,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)

        run = self.sole_run_dir(root)
        run_index = (run / "index.md").read_text()
        self.assertIn("| alpha | [Open results](alpha/.specula-output/index.md) |", run_index)
        self.assertIn("| beta | [Open results](beta/.specula-output/index.md) |", run_index)
        alpha = (run / "alpha" / ".specula-output" / "index.md").read_text()
        beta = (run / "beta" / ".specula-output" / "index.md").read_text()
        self.assertIn("# alpha Results", alpha)
        self.assertNotIn("beta", alpha)
        self.assertIn("# beta Results", beta)
        self.assertNotIn("alpha", beta)
        self.assertTrue((run / "alpha" / ".specula-output" / "summary.md").is_file())
        self.assertTrue((run / "beta" / ".specula-output" / "summary.md").is_file())

    def test_run_tuning_and_retry_budgets_reach_phase_and_review_commands(self) -> None:
        for model, effort in (("gpt-5.5", "high"), ("", "")):
            with self.subTest(model=model, effort=effort):
                root = self.specroot()
                work = self.workdir()
                proc = self.run_cli(
                    root,
                    [
                        "run",
                        "--dry-run",
                        "--enable-reviews",
                        "--agent=codex",
                        f"--model={model}",
                        f"--effort={effort}",
                        "--policy-retries=100",
                        "--transient-resumes=80",
                        "footest",
                    ],
                    cwd=work,
                )
                self.assertEqual(proc.returncode, 0, proc.stderr)
                phase_line = next(line for line in proc.stdout.splitlines() if "launch_code_analysis.sh" in line)
                review_line = next(line for line in proc.stdout.splitlines() if "launch_review.sh" in line)
                for line in (phase_line, review_line):
                    self.assertIn(f"--model={model}", line)
                    self.assertIn(f"--effort={effort}", line)
                    self.assertIn("--policy-retries=100", line)
                    self.assertIn("--transient-resumes=80", line)
                self.assertIn("launch_review.sh analysis --agent=codex", review_line)
                meta = json.loads((self.sole_run_dir(root) / "run.json").read_text())
                self.assertEqual(meta["model"], model or None)
                self.assertEqual(meta["effort"], effort or None)
                self.assertEqual(meta["policy_retries"], 100)
                self.assertEqual(meta["transient_resumes"], 80)

    def test_agent_config_routes_phase_and_review_commands(self) -> None:
        root = self.specroot()
        work = self.workdir()
        config = work / "agents.json"
        config.write_text(
            json.dumps(
                {
                    "version": 1,
                    "default_profile": "reasoning",
                    "profiles": {
                        "reasoning": {
                            "agent": "codex",
                            "model": "gpt-5.6-sol",
                            "effort": "ultra",
                        },
                        "confirmation": {
                            "agent": "copilot-cli",
                            "model": "claude-sonnet-4.5",
                        },
                        "reviewer": {
                            "agent": "opencode",
                            "model": "openai/gpt-5.4",
                        },
                    },
                    "phases": {
                        "confirm": "confirmation",
                        "review": "reviewer",
                    },
                }
            )
        )

        proc = self.run_cli(
            root,
            ["run", "--dry-run", "--enable-reviews", f"--agent-config={config.name}", "footest"],
            cwd=work,
        )

        self.assertEqual(proc.returncode, 0, proc.stderr)
        lines = proc.stdout.splitlines()
        analysis = next(line for line in lines if "launch_code_analysis.sh" in line)
        confirmation = next(line for line in lines if "launch_bug_confirmation.sh" in line)
        review = next(line for line in lines if "launch_review.sh analysis" in line)
        self.assertIn("--agent=codex", analysis)
        self.assertIn("--model=gpt-5.6-sol", analysis)
        self.assertIn("--effort=ultra", analysis)
        self.assertIn("--agent=copilot-cli", confirmation)
        self.assertIn("--model=claude-sonnet-4.5", confirmation)
        self.assertIn("--agent=opencode", review)
        self.assertIn("--model=openai/gpt-5.4", review)

        meta = json.loads((self.sole_run_dir(root) / "run.json").read_text())
        self.assertEqual(meta["agent_config"], str(config))
        self.assertEqual(meta["agent_routes"]["confirm"]["agent"], "copilot-cli")
        self.assertEqual(meta["agent_routes"]["review:analysis"]["agent"], "opencode")

    def test_run_json_records_argv(self) -> None:
        root = self.specroot()
        work = self.workdir()
        self.run_cli(root, ["run", "--dry-run", "footest"], cwd=work)
        run = self.sole_run_dir(root)
        meta = json.loads((run / "run.json").read_text())
        self.assertEqual(meta["targets"], ["footest"])
        self.assertEqual(meta["run_id"], run.name)
        self.assertNotIn("agent_config", meta)

    def test_keep_original_dry_run_records_mode_without_copying(self) -> None:
        root = self.specroot()
        work = self.workdir()
        source = work / "source"
        source.mkdir()
        (source / "file.txt").write_text("unchanged\n")

        proc = self.run_cli(
            root,
            ["run", "--dry-run", "--keep-original", f"--artifact={source}", "footest"],
            cwd=work,
        )

        self.assertEqual(proc.returncode, 0, proc.stderr)
        run = self.sole_run_dir(root)
        self.assertEqual(json.loads((run / "run.json").read_text())["source_mode"], "snapshot")
        self.assertFalse((run / "source-map.json").exists())
        self.assertFalse((run / "footest" / "source").exists())
        self.assertEqual((source / "file.txt").read_text(), "unchanged\n")

    def test_keep_original_noop_pipeline_creates_private_source_and_empty_diff(self) -> None:
        root = self.specroot()
        work = self.workdir()
        source = work / "source"
        source.mkdir()
        (source / "file.txt").write_text("unchanged\n")
        skips = [
            "--skip-analysis",
            "--skip-specgen",
            "--skip-harness",
            "--skip-validate",
            "--skip-confirmation",
            "--skip-classification",
            "--skip-repair-loop",
        ]

        proc = self.run_cli(
            root,
            ["run", "--keep-original", f"--artifact={source}", *skips, "footest"],
            cwd=work,
        )

        self.assertEqual(proc.returncode, 0, proc.stderr)
        run = self.sole_run_dir(root)
        self.assertEqual((run / "footest" / "source" / "file.txt").read_text(), "unchanged\n")
        self.assertEqual((run / "footest" / "changes.patch").read_bytes(), b"")
        self.assertEqual((source / "file.txt").read_text(), "unchanged\n")

    # ── legacy escape hatch ──────────────────────────────────────────────────
    def test_no_isolate_uses_legacy_layout_and_mints_nothing(self) -> None:
        root = self.specroot(case_dirs=())  # no case dir -> pipeline stays in cwd
        work = self.workdir()
        proc = self.run_cli(root, ["run", "--dry-run", "--no-isolate", "nocase"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertTrue((work / ".specula-output" / "pipeline.log").is_file(), "legacy layout not written")
        self.assertFalse((root / "runs").exists(), "--no-isolate must not mint a run dir")

    def test_no_isolate_single_target_uses_one_detailed_index(self) -> None:
        root = self.specroot(case_dirs=())
        work = self.workdir()
        proc = self.run_cli(root, ["run", "--no-isolate", *ALL_PHASE_SKIPS, "nocase"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)

        index = (work / ".specula-output" / "index.md").read_text()
        self.assertIn("# nocase Results", index)
        self.assertIn("## Final Reports", index)
        self.assertIn("## Supporting Analysis", index)
        self.assertNotIn("# Specula Run", index)
        self.assertIn("[pipeline.log](pipeline.log)", index)
        self.assertTrue((work / ".specula-output" / "summary.md").is_file())
        self.assertFalse((root / "runs").exists())

    def test_no_isolate_canonical_single_target_links_launch_log(self) -> None:
        root = self.specroot()
        work = self.workdir()
        proc = self.run_cli(root, ["run", "--no-isolate", *ALL_PHASE_SKIPS, "footest"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)

        target_dir = root / "case-studies" / "footest" / ".specula-output"
        target_index = (target_dir / "index.md").read_text()
        pipeline_log = work / ".specula-output" / "pipeline.log"
        relative_log = os.path.relpath(pipeline_log, start=target_dir).replace(os.sep, "/")
        self.assertIn("# footest Results", target_index)
        self.assertIn(f"[pipeline.log]({relative_log})", target_index)
        self.assertTrue((target_dir / "pipeline-summary.md").is_file())
        self.assertTrue((target_dir / "summary.md").is_file())
        self.assertFalse((work / ".specula-output" / "index.md").exists())

    def test_no_isolate_multi_target_keeps_a_distinct_run_chooser(self) -> None:
        root = self.specroot(case_dirs=())
        work = self.workdir()
        proc = self.run_cli(
            root,
            [
                "run",
                "--no-isolate",
                *ALL_PHASE_SKIPS,
                "alpha|o/a|Go|ref",
                "beta|o/b|Rust|ref",
            ],
            cwd=work,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)

        run_index = (work / ".specula-output" / "index.md").read_text()
        self.assertIn("# Specula Run", run_index)
        self.assertIn("[Open results](../alpha/.specula-output/index.md)", run_index)
        self.assertIn("[Open results](../beta/.specula-output/index.md)", run_index)
        self.assertIn("# alpha Results", (work / "alpha" / ".specula-output" / "index.md").read_text())
        self.assertIn("# beta Results", (work / "beta" / ".specula-output" / "index.md").read_text())

    # ── batch (scheduler) dry-run ────────────────────────────────────────────
    def test_batch_dry_run_over_queue(self) -> None:
        # `specula batch` -> scheduler.sh -> schedulerlib.py. Dry-run logs the
        # per-task clone + pipeline command and never executes them (no network,
        # no mint), so the whole queue runs hermetically.
        root = self.specroot(case_dirs=())
        work = self.workdir()
        queue = work / "soak.queue"
        queue.write_text("alpha|o/alpha|Go|ref\nbeta|o/beta|Rust|ref\n")
        proc = self.run_cli(
            root, ["batch", "--queue", str(queue), "--dry-run", "--workers", "1"], cwd=work, stub_sleep=True
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("Total=2", proc.stdout)
        self.assertIn("Dry=2", proc.stdout)
        # dry-run logs the command it WOULD run, per task, and mints nothing
        self.assertIn("DRY-RUN:", proc.stdout)
        self.assertFalse((root / "runs").exists(), "dry-run batch must not mint run dirs")


if __name__ == "__main__":
    unittest.main()
