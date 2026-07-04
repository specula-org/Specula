"""Behavior tests for workspace isolation (migration step 4).

Unlike the characterization goldens there is no bash to diff against — these
tests ARE the definition of the isolation semantics:

  - `SPECULA_RUN_DIR` set  -> every output lands under <run>/<name>/.specula-output
    (uniform batch-style layout; the single-target cd disappears), canonical
    inputs (artifact checkout, .prompt-extra.md) fall back to case-studies/<name>.
  - `SPECULA_RUN_DIR` unset -> byte-identical legacy behavior ($PWD-derived
    layout, single/batch fork) — pinned here at function level and by the
    untouched characterization goldens end-to-end.

stdlib unittest (no pytest/pip needed — the repo .venv is corrupted; pytest
collects unittest.TestCase natively once step 2 wires CI):

    python3 -m unittest tests.unit.test_workspace_isolation -v
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

LAUNCH = Path(__file__).resolve().parents[2] / "scripts" / "launch"
sys.path.insert(0, str(LAUNCH))
import phaselib  # type: ignore[import-not-found]  # noqa: E402
import pipelinelib as pl  # type: ignore[import-not-found]  # noqa: E402

RUN_ID_RE = re.compile(r"^\d{8}-\d{6}-[0-9a-f]{4}$")


class EnvIsolatedCase(unittest.TestCase):
    """Base: never leak SPECULA_RUN_DIR mutations (module code exports it)."""

    def setUp(self) -> None:
        old = os.environ.get("SPECULA_RUN_DIR")

        def restore() -> None:
            if old is None:
                os.environ.pop("SPECULA_RUN_DIR", None)
            else:
                os.environ["SPECULA_RUN_DIR"] = old

        self.addCleanup(restore)
        os.environ.pop("SPECULA_RUN_DIR", None)

    def set_run_dir(self, path: Path) -> None:
        os.environ["SPECULA_RUN_DIR"] = str(path)

    def tmp(self) -> Path:
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return Path(d.name)

    def patch_root(self, module: Any, root: Path) -> None:
        old = module.SPECULA_ROOT

        def restore() -> None:
            module.SPECULA_ROOT = old

        self.addCleanup(restore)
        module.SPECULA_ROOT = root


class TestRunId(EnvIsolatedCase):
    def test_generated_id_format(self) -> None:
        rid = pl.generate_run_id()
        self.assertRegex(rid, RUN_ID_RE)

    def test_invalid_attach_ids_rejected(self) -> None:
        for bad in ("../evil", "a/b", "", ".", "..", "a b", "x\ny"):
            with self.subTest(bad=bad):
                root = self.tmp()  # fresh root per id: one leak cannot mask the next
                self.patch_root(pl, root)
                p = pl.Pipeline()
                self.assertIsNone(p.parse_args([f"--run-id={bad}", "t|o/r|Go|ref"]))
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = p.resolve_run_dir()
                self.assertEqual(rc, 1)
                self.assertIn("invalid --run-id", err.getvalue())
                self.assertFalse((root / "runs").exists(), f"no dir may be created for {bad!r}")

    def test_valid_attach_id_accepted(self) -> None:
        root = self.tmp()
        self.patch_root(pl, root)
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--run-id=exp-1.retry_2", "t|o/r|Go|ref"]))
        self.assertIsNone(p.resolve_run_dir())
        self.assertEqual(p.run_dir, root / "runs" / "exp-1.retry_2")
        self.assertTrue((root / "runs" / "exp-1.retry_2").is_dir())


class TestWorkspacePaths(EnvIsolatedCase):
    def test_legacy_single_target(self) -> None:
        ws = phaselib.Workspace(["foo"], cwd=Path("/launch/dir"))
        self.assertEqual(ws.work_dir("foo"), Path("/launch/dir/.specula-output"))

    def test_legacy_batch(self) -> None:
        ws = phaselib.Workspace(["foo", "bar"], cwd=Path("/launch/dir"))
        self.assertEqual(ws.work_dir("bar"), Path("/launch/dir/bar/.specula-output"))

    def test_isolated_uniform_layout(self) -> None:
        """Single and batch no longer fork: always <run>/<name>/.specula-output."""
        run = self.tmp()
        self.set_run_dir(run)
        for targets in (["foo"], ["foo", "bar"]):
            with self.subTest(targets=targets):
                ws = phaselib.Workspace(targets, cwd=Path("/launch/dir"))
                self.assertEqual(ws.work_dir("foo"), run / "foo" / ".specula-output")

    def test_case_dir_is_canonical(self) -> None:
        root = self.tmp()
        self.patch_root(phaselib, root)
        ws = phaselib.Workspace(["foo"])
        self.assertEqual(ws.case_dir("foo"), root / "case-studies" / "foo")


class TestPipelineWorkDirMirror(EnvIsolatedCase):
    """Pipeline.get_work_dir mirrors Workspace.work_dir — pin both so the two
    implementations cannot drift apart."""

    def test_legacy_single_and_batch(self) -> None:
        cwd = str(pl._logical_cwd())
        p = pl.Pipeline()
        p.parse_args(["foo|o/r|Go|ref"])
        self.assertEqual(p.get_work_dir("foo"), f"{cwd}/.specula-output")
        p2 = pl.Pipeline()
        p2.parse_args(["foo|o/r|Go|ref", "bar|o/r|Go|ref"])
        self.assertEqual(p2.get_work_dir("bar"), f"{cwd}/bar/.specula-output")

    def test_isolated_uniform_layout(self) -> None:
        run = self.tmp()
        self.set_run_dir(run)
        for targets in (["foo|o/r|Go|ref"], ["foo|o/r|Go|ref", "bar|o/r|Go|ref"]):
            with self.subTest(targets=targets):
                p = pl.Pipeline()
                p.parse_args(list(targets))
                self.assertIsNone(p.resolve_run_dir())
                self.assertEqual(p.get_work_dir("foo"), f"{run}/foo/.specula-output")


class TestFindRepoDir(EnvIsolatedCase):
    def _canonical(self, root: Path, name: str, repos: list[str]) -> None:
        for repo in repos:
            d = root / "case-studies" / name / "artifact" / repo
            (d / ".git").mkdir(parents=True)

    def test_explicit_artifact_wins(self) -> None:
        self.set_run_dir(self.tmp())
        ws = phaselib.Workspace(["foo"], artifact="/my/repo")
        self.assertEqual(ws.find_repo_dir("foo"), "/my/repo")

    def test_isolated_canonical_fallback(self) -> None:
        root = self.tmp()
        self.patch_root(phaselib, root)
        self._canonical(root, "foo", [".hidden", "realrepo"])
        self.set_run_dir(self.tmp())
        ws = phaselib.Workspace(["foo"])
        # dot-dirs skipped (bash glob), trailing slash kept (bash `/*/`)
        self.assertEqual(ws.find_repo_dir("foo"), str(root / "case-studies" / "foo" / "artifact" / "realrepo") + "/")

    def test_isolated_no_pwd_rule(self) -> None:
        """Single target + no artifact anywhere -> '' (the legacy 'source is
        $PWD' rule must NOT apply: the run root holds no sources)."""
        root = self.tmp()
        self.patch_root(phaselib, root)
        self.set_run_dir(self.tmp())
        ws = phaselib.Workspace(["foo"], cwd=Path("/launch/dir"))
        self.assertEqual(ws.find_repo_dir("foo"), "")

    def test_legacy_single_pwd_rule_unchanged(self) -> None:
        ws = phaselib.Workspace(["foo"], cwd=Path("/launch/dir"))
        self.assertEqual(ws.find_repo_dir("foo"), "/launch/dir")

    def test_legacy_batch_search_unchanged(self) -> None:
        cwd = self.tmp()
        d = cwd / "foo" / "artifact" / "repo"
        (d / ".git").mkdir(parents=True)
        ws = phaselib.Workspace(["foo", "bar"], cwd=cwd)
        self.assertEqual(ws.find_repo_dir("foo"), str(d) + "/")


class TestPromptExtra(EnvIsolatedCase):
    def _inject(self, ws: object, name: str) -> str:
        return str(phaselib.Phase()._with_extra(ws, name, "PROMPT"))

    def test_isolated_work_dir_copy_wins(self) -> None:
        root, run = self.tmp(), self.tmp()
        self.patch_root(phaselib, root)
        (root / "case-studies" / "foo").mkdir(parents=True)
        (root / "case-studies" / "foo" / ".prompt-extra.md").write_text("canonical\n")
        wd = run / "foo" / ".specula-output"
        wd.mkdir(parents=True)
        (wd / ".prompt-extra.md").write_text("run-local\n")
        self.set_run_dir(run)
        ws = phaselib.Workspace(["foo"])
        self.assertIn("run-local", self._inject(ws, "foo"))

    def test_isolated_canonical_fallback(self) -> None:
        """The gap this step closes: without the case-studies fallback the
        target-specific instructions would silently vanish under isolation."""
        root, run = self.tmp(), self.tmp()
        self.patch_root(phaselib, root)
        (root / "case-studies" / "foo").mkdir(parents=True)
        (root / "case-studies" / "foo" / ".prompt-extra.md").write_text("canonical extra\n")
        self.set_run_dir(run)
        ws = phaselib.Workspace(["foo"])
        out = self._inject(ws, "foo")
        self.assertIn("canonical extra", out)
        self.assertIn("## Target-Specific Instructions", out)

    def test_isolated_neither_is_silent(self) -> None:
        self.patch_root(phaselib, self.tmp())
        self.set_run_dir(self.tmp())
        ws = phaselib.Workspace(["foo"])
        self.assertEqual(self._inject(ws, "foo"), "PROMPT")

    def test_legacy_cwd_fallback_unchanged(self) -> None:
        cwd = self.tmp()
        (cwd / ".prompt-extra.md").write_text("cwd extra\n")
        ws = phaselib.Workspace(["foo", "bar"], cwd=cwd)
        self.assertIn("cwd extra", self._inject(ws, "foo"))


class TestRunMetaAndAttach(EnvIsolatedCase):
    def _pipeline(self, argv: list[str], root: Path) -> pl.Pipeline:
        self.patch_root(pl, root)
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(argv))
        self.assertIsNone(p.resolve_run_dir())
        return p

    def test_isolate_creates_run_and_meta(self) -> None:
        root = self.tmp()
        argv = ["--isolate", "--agent=claude-code", "foo|o/r|Go|ref"]
        p = self._pipeline(argv, root)
        assert p.run_dir is not None
        self.assertEqual(p.run_dir.parent, root / "runs")
        self.assertRegex(p.run_id, RUN_ID_RE)
        meta = json.loads((p.run_dir / "run.json").read_text())
        self.assertEqual(meta["run_id"], p.run_id)
        self.assertEqual(meta["argv"], argv)
        self.assertEqual(meta["targets"], ["foo|o/r|Go|ref"])
        self.assertEqual(meta["agent"], "claude-code")
        self.assertIsNone(meta["artifact_git_sha"])  # no artifact given
        self.assertIn("created", meta)
        # env exported for the phase subprocesses
        self.assertEqual(os.environ["SPECULA_RUN_DIR"], str(p.run_dir))

    def test_meta_records_artifact_sha(self) -> None:
        root = self.tmp()
        repo = self.tmp()
        env = {
            **os.environ,
            "GIT_AUTHOR_NAME": "t",
            "GIT_AUTHOR_EMAIL": "t@t",
            "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@t",
        }
        subprocess.run(["git", "init", "-q", str(repo)], check=True, env=env)
        subprocess.run(["git", "-C", str(repo), "commit", "-q", "--allow-empty", "-m", "x"], check=True, env=env)
        sha = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
        ).stdout.strip()
        p = self._pipeline(["--run-id=withsha", f"--artifact={repo}", "foo|o/r|Go|ref"], root)
        assert p.run_dir is not None
        meta = json.loads((p.run_dir / "run.json").read_text())
        self.assertEqual(meta["artifact_git_sha"], sha)

    def test_attach_reuses_without_clobbering(self) -> None:
        root = self.tmp()
        run = root / "runs" / "myrun"
        (run / "foo" / ".specula-output").mkdir(parents=True)
        (run / "foo" / ".specula-output" / "keep.txt").write_text("keep")
        (run / "run.json").write_text('{"run_id": "myrun", "original": true}\n')
        p = self._pipeline(["--run-id=myrun", "foo|o/r|Go|ref"], root)
        self.assertEqual(p.run_dir, run)
        self.assertEqual((run / "foo" / ".specula-output" / "keep.txt").read_text(), "keep")
        # attach never rewrites the original record
        self.assertTrue(json.loads((run / "run.json").read_text())["original"])

    def test_ambient_env_attach(self) -> None:
        """SPECULA_RUN_DIR already set (scheduler / outer script): honored
        as-is, nothing created under SPECULA_ROOT/runs."""
        root = self.tmp()
        ext = self.tmp() / "external-run"
        self.set_run_dir(ext)
        p = self._pipeline(["foo|o/r|Go|ref"], root)
        self.assertEqual(p.run_dir, ext)
        self.assertEqual(p.run_id, "external-run")
        self.assertTrue(ext.is_dir())
        self.assertFalse((root / "runs").exists())

    def test_legacy_mode_untouched(self) -> None:
        root = self.tmp()
        p = self._pipeline(["foo|o/r|Go|ref"], root)
        self.assertIsNone(p.run_dir)
        self.assertFalse((root / "runs").exists())
        self.assertNotIn("SPECULA_RUN_DIR", os.environ)

    def test_latest_symlink_tracks_newest(self) -> None:
        root = self.tmp()
        self._pipeline(["--run-id=run-a", "foo|o/r|Go|ref"], root)
        latest = root / "runs" / "latest"
        self.assertTrue(latest.is_symlink())
        self.assertEqual(os.readlink(latest), "run-a")
        os.environ.pop("SPECULA_RUN_DIR", None)  # fresh resolve for the second run
        self._pipeline(["--run-id=run-b", "foo|o/r|Go|ref"], root)
        self.assertEqual(os.readlink(latest), "run-b")


class TestEnvThreading(EnvIsolatedCase):
    def test_phase_subprocess_sees_run_dir(self) -> None:
        """resolve_run_dir exports SPECULA_RUN_DIR; _run_launcher's bash child
        must inherit it — that inheritance is the whole transport mechanism."""
        root = self.tmp()
        fake_scripts = self.tmp()
        marker = fake_scripts / "marker.txt"
        (fake_scripts / "launch_code_analysis.sh").write_text(
            f'#!/usr/bin/env bash\nprintf \'%s\' "${{SPECULA_RUN_DIR:-UNSET}}" > "{marker}"\n'
        )
        self.patch_root(pl, root)
        self.addCleanup(setattr, pl, "SCRIPT_DIR", pl.SCRIPT_DIR)
        pl.SCRIPT_DIR = fake_scripts
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--isolate", "foo|o/r|Go|ref"]))
        self.assertIsNone(p.resolve_run_dir())
        with contextlib.redirect_stdout(io.StringIO()):
            p.run_phase1_analysis()
        self.assertEqual(marker.read_text(), str(p.run_dir))


class TestParallelIsolation(EnvIsolatedCase):
    """The step's acceptance property: two pipelines, same target, running
    concurrently — zero file overlap, each summary reflects only its own data,
    and the shared launch cwd stays clean (no .specula-output pollution).

    Runs the real pipelinelib entry (tee plumbing included) as subprocesses in
    env-attach mode so the run roots live in tmp; --isolate's dir creation
    under SPECULA_ROOT/runs is covered in-process by TestRunMetaAndAttach."""

    SKIPS = [
        "--skip-analysis",
        "--skip-specgen",
        "--skip-harness",
        "--skip-validation",
        "--skip-confirmation",
        "--skip-classification",
        "--skip-repair-loop",
    ]
    RR = "---\nid: {rid}\nbug_id: B-1\ntarget: base.tla\nstatus: {status}\nround: 1\n---\n\n## History\n- created\n"

    def _seed_rr(self, run: Path, name: str, statuses: list[str]) -> None:
        d = run / name / ".specula-output" / "spec" / "repair-requests"
        d.mkdir(parents=True)
        for i, status in enumerate(statuses, 1):
            (d / f"RR-{i}.md").write_text(self.RR.format(rid=f"RR-{i}", status=status))

    def test_two_runs_do_not_interfere(self) -> None:
        launch_cwd = self.tmp()
        run_a, run_b = self.tmp() / "runA", self.tmp() / "runB"
        self._seed_rr(run_a, "footest", ["RESOLVED"])
        self._seed_rr(run_b, "footest", ["DEFERRED", "DEFERRED"])

        env = dict(os.environ)
        for var in ("MAX_REPAIR_ROUNDS", "QUOTA_5H", "QUOTA_7D", "QUOTA_MAX_WAITS", "CLAUDE_ALIAS"):
            env.pop(var, None)
        target = "footest|foo/bar|Go|Raft demo"
        procs = []
        for run in (run_a, run_b):
            procs.append(
                subprocess.Popen(
                    [sys.executable, str(LAUNCH / "pipelinelib.py"), *self.SKIPS, target],
                    cwd=launch_cwd,
                    env={**env, "SPECULA_RUN_DIR": str(run)},
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                )
            )
        outs = [p.communicate()[0] for p in procs]
        self.assertEqual([p.returncode for p in procs], [0, 0], outs)

        # each run has its own log + summary, reflecting only its own requests
        sum_a = (run_a / "pipeline-summary.md").read_text()
        sum_b = (run_b / "pipeline-summary.md").read_text()
        self.assertIn("1 request(s) — 1 resolved, 0 deferred", sum_a)
        self.assertIn("2 request(s) — 0 resolved, 2 deferred", sum_b)
        for run, out in zip((run_a, run_b), outs, strict=True):
            self.assertTrue((run / "pipeline.log").is_file())
            self.assertIn(f"Run:          {run.name}", out)
        # zero overlap: all files live under their own run root by construction;
        # the shared launch cwd gained nothing (legacy would have written
        # .specula-output/pipeline.log there)
        self.assertEqual(list(launch_cwd.iterdir()), [])


class TestMonitorLine(EnvIsolatedCase):
    """The 'Monitor: tail -f ...' hint must point where the logs actually land:
    the launch cwd in legacy, the run root under isolation (the legacy relative
    `*/` glob would tail an empty launch cwd the isolated run never writes to)."""

    # (phase class, log filename that appears in the isolated run-rooted hint)
    PHASES = [
        (phaselib.SpecGenerationPhase, "spec-gen.log"),
        (phaselib.HarnessGenerationPhase, "harness-gen.log"),
        (phaselib.BugClassificationPhase, "bug-classification.log"),
        (phaselib.SpecValidationPhase, "spec-validation.log"),
        (phaselib.BugConfirmationPhase, "bug-confirmation.log"),
    ]

    def test_isolated_reroots_under_run(self) -> None:
        run = self.tmp()
        self.set_run_dir(run)
        ws = phaselib.Workspace(["foo"], cwd=Path("/launch/dir"))
        for cls, logname in self.PHASES:
            with self.subTest(phase=cls.__name__):
                line = cls().monitor_line(ws)
                self.assertEqual(line, f"  Monitor: tail -f {run}/*/.specula-output/{logname}")
                # the launch cwd the isolated run does not write to never leaks in
                self.assertNotIn("/launch/dir", line)

    def test_legacy_unchanged(self) -> None:
        """Byte-identical to the bash launchers' hand-written globs (quirks and
        all) — the same strings the characterization goldens pin."""
        ws = phaselib.Workspace(["foo"], cwd=Path("/launch/dir"))
        expected = {
            phaselib.SpecGenerationPhase: "  Monitor: tail -f */.specula-output/spec-gen.log",
            phaselib.HarnessGenerationPhase: "  Monitor: tail -f */.specula-output/harness-gen.log",
            phaselib.BugClassificationPhase: "  Monitor: tail -f */bug-classification.log",
            phaselib.SpecValidationPhase: "  Monitor: tail -f /launch/dir/*/.specula-output/spec-validation.log",
            phaselib.BugConfirmationPhase: "  Monitor: tail -f */bug-confirmation.log",
        }
        for cls, line in expected.items():
            with self.subTest(phase=cls.__name__):
                self.assertEqual(cls().monitor_line(ws), line)

    def test_code_analysis_prints_none_either_mode(self) -> None:
        for isolated in (False, True):
            with self.subTest(isolated=isolated):
                if isolated:
                    self.set_run_dir(self.tmp())
                else:
                    os.environ.pop("SPECULA_RUN_DIR", None)
                ws = phaselib.Workspace(["foo"])
                self.assertIsNone(phaselib.CodeAnalysisPhase().monitor_line(ws))


if __name__ == "__main__":
    unittest.main()
