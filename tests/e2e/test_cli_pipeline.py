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

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

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
    "CLAUDE_CONFIG_DIR",
    "CLAUDE_ALIAS",
    "CLAUDE_EFFORT",
    "CLAUDE_MODEL",
    "CODEX_MODEL",
    "CODEX_EFFORT",
    "COPILOT_MODEL",
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

    def test_noop_run_writes_two_level_human_indexes(self) -> None:
        root = self.specroot()
        work = self.workdir()
        proc = self.run_cli(root, ["run", *ALL_PHASE_SKIPS, "footest"], cwd=work)
        self.assertEqual(proc.returncode, 0, proc.stderr)

        run = self.sole_run_dir(root)
        run_index = (run / "index.md").read_text()
        target_dir = run / "footest" / ".specula-output"
        target_index = (target_dir / "index.md").read_text()

        self.assertIn("| footest | [Open results](footest/.specula-output/index.md) |", run_index)
        self.assertIn("- Final summary: [pipeline-summary.md](pipeline-summary.md)", run_index)
        self.assertNotIn("run.json", run_index)
        self.assertNotIn("tlc-resources.json", run_index)

        self.assertIn("# footest Results", target_index)
        self.assertIn("## Final Reports", target_index)
        self.assertIn("## Supporting Analysis", target_index)
        self.assertIn("Modeling brief: Not available", target_index)
        self.assertIn("[pipeline.log](../../pipeline.log)", target_index)
        self.assertNotIn("## Reviews", target_index)
        self.assertNotIn("findings.json", target_index)
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
