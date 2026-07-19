"""Behavior tests for workspace isolation (migration step 4).

There is no bash to diff against — these tests ARE the definition of the
isolation semantics:

  - `SPECULA_RUN_DIR` set  -> every output lands under <run>/<name>/.specula-output
    (uniform batch-style layout; the single-target cd disappears), canonical
    inputs (artifact checkout, .prompt-extra.md) fall back to case-studies/<name>.
  - `SPECULA_RUN_DIR` unset -> byte-identical legacy behavior ($PWD-derived
    layout, single/batch fork) — pinned here at function level, with the
    end-to-end chain in tests/e2e.

stdlib unittest, collected natively by pytest; imports the installed package:

    uv run python -m unittest tests.unit.test_workspace_isolation -v
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

PKG = Path(__file__).resolve().parents[2] / "src" / "specula"

from specula import phaselib
from specula import pipelinelib as pl

RUN_ID_RE = re.compile(r"^\d{8}-\d{6}-[0-9a-f]{4}$")


class EnvIsolatedCase(unittest.TestCase):
    """Base: never leak run-directory or TLC-scope environment mutations."""

    def setUp(self) -> None:
        names = (
            "SPECULA_RUN_DIR",
            "SPECULA_TLC_SCOPE",
            "SPECULA_TLC_MEMORY_LIMIT",
            "SPECULA_TLC_WORKER_LIMIT",
            "SPECULA_SOURCE_SNAPSHOT",
            "SPECULA_SANDBOX_EXTRA_WRITE",
        )
        original = {name: os.environ.get(name) for name in names}

        def restore() -> None:
            for name, value in original.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value

        self.addCleanup(restore)
        for name in names:
            os.environ.pop(name, None)

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

    def test_keep_original_rejects_run_storage_inside_source_before_writing(self) -> None:
        original = self.tmp()
        self.patch_root(pl, original)
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--keep-original", f"--artifact={original}", "t|o/r|Go|ref"]))

        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(p.resolve_run_dir(), 1)

        self.assertFalse((original / "runs").exists())


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
        cwd = str(phaselib._logical_cwd())
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

    def test_private_source_wins_over_explicit_artifact(self) -> None:
        run = self.tmp()
        source = run / "foo" / "source"
        source.mkdir(parents=True)
        (run / "source-map.json").write_text("{}\n")
        self.set_run_dir(run)

        ws = phaselib.Workspace(["foo"], artifact="/original/repo")

        self.assertEqual(ws.find_repo_dir("foo"), str(source))

    def test_snapshot_mode_never_falls_back_to_original(self) -> None:
        run = self.tmp()
        self.set_run_dir(run)
        os.environ["SPECULA_SOURCE_SNAPSHOT"] = "1"

        ws = phaselib.Workspace(["foo"], artifact="/original/repo")

        self.assertEqual(ws.find_repo_dir("foo"), "")

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
    def _inject(self, ws: phaselib.Workspace, name: str) -> str:
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
    _TUNING_ENV = (
        "SPECULA_MODEL",
        "SPECULA_EFFORT",
        "CLAUDE_MODEL",
        "CLAUDE_EFFORT",
        "CODEX_MODEL",
        "CODEX_EFFORT",
        "COPILOT_MODEL",
        "OPENCODE_MODEL",
        "OPENCODE_EFFORT",
        "PI_MODEL",
        "PI_EFFORT",
    )

    def setUp(self) -> None:
        super().setUp()
        original = {name: os.environ.get(name) for name in self._TUNING_ENV}

        def restore() -> None:
            for name, value in original.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value

        self.addCleanup(restore)
        for name in self._TUNING_ENV:
            os.environ.pop(name, None)

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
        self.assertIsNone(meta["model"])
        self.assertEqual(meta["effort"], "max")
        self.assertEqual(meta["policy_retries"], 20)
        self.assertEqual(meta["transient_resumes"], 20)
        self.assertIsNone(meta["artifact_git_sha"])  # no artifact given
        self.assertIn("created", meta)
        # env exported for the phase subprocesses
        self.assertEqual(os.environ["SPECULA_RUN_DIR"], str(p.run_dir))
        self.assertEqual(os.environ["SPECULA_TLC_SCOPE"], str(p.run_dir.resolve()))

    def test_snapshot_mode_and_private_source_survive_resume_without_flag(self) -> None:
        root = self.tmp()
        original = self.tmp()
        (original / "source.txt").write_text("original\n")
        first = self._pipeline(
            ["--run-id=private", "--keep-original", f"--artifact={original}", "foo|o/r|Go|ref"],
            root,
        )
        first.prepare_source_snapshots(["foo"])
        assert first.run_dir is not None
        private = first.run_dir / "foo" / "source"
        (private / "agent.txt").write_text("keep\n")
        os.environ.pop("SPECULA_RUN_DIR", None)
        os.environ.pop("SPECULA_TLC_SCOPE", None)
        os.environ.pop("SPECULA_SOURCE_SNAPSHOT", None)

        resumed = self._pipeline(["--run-id=private", "foo|o/r|Go|ref"], root)
        resumed.prepare_source_snapshots(["foo"])

        self.assertTrue(resumed.keep_original)
        self.assertEqual((private / "agent.txt").read_text(), "keep\n")
        self.assertEqual(phaselib.Workspace(["foo"]).find_repo_dir("foo"), str(private))

    def test_meta_records_cli_tuning_over_environment(self) -> None:
        root = self.tmp()
        os.environ["SPECULA_MODEL"] = "env-model"
        os.environ["SPECULA_EFFORT"] = "low"
        os.environ["CODEX_MODEL"] = "adapter-model"
        os.environ["CODEX_EFFORT"] = "medium"
        p = self._pipeline(
            ["--agent=codex", "--model=gpt-5.5", "--effort=high", "foo|o/r|Go|ref"],
            root,
        )
        assert p.run_dir is not None
        meta = json.loads((p.run_dir / "run.json").read_text())
        self.assertEqual(meta["model"], "gpt-5.5")
        self.assertEqual(meta["effort"], "high")

    def test_meta_records_specula_environment_tuning(self) -> None:
        root = self.tmp()
        os.environ["SPECULA_MODEL"] = "env-model"
        os.environ["SPECULA_EFFORT"] = "low"
        os.environ["CODEX_MODEL"] = "adapter-model"
        os.environ["CODEX_EFFORT"] = "medium"
        p = self._pipeline(["--agent=codex", "foo|o/r|Go|ref"], root)
        assert p.run_dir is not None
        meta = json.loads((p.run_dir / "run.json").read_text())
        self.assertEqual(meta["model"], "env-model")
        self.assertEqual(meta["effort"], "low")

    def test_meta_records_adapter_environment_tuning(self) -> None:
        cases = (
            ("claude-code", {"CLAUDE_MODEL": "opus", "CLAUDE_EFFORT": "low"}, "opus", "max"),
            (
                "codex",
                {
                    "SPECULA_MODEL": "",
                    "SPECULA_EFFORT": "",
                    "CODEX_MODEL": "gpt-env",
                    "CODEX_EFFORT": "high",
                },
                "gpt-env",
                "high",
            ),
            ("copilot-cli", {"COPILOT_MODEL": "copilot-env"}, "copilot-env", None),
            ("opencode", {"OPENCODE_MODEL": "zai/glm-5.2", "OPENCODE_EFFORT": "high"}, "zai/glm-5.2", "high"),
            ("pi", {"PI_MODEL": "openai/gpt-5.5", "PI_EFFORT": "xhigh"}, "openai/gpt-5.5", "xhigh"),
        )
        for agent, environment, expected_model, expected_effort in cases:
            with self.subTest(agent=agent):
                for name in self._TUNING_ENV:
                    os.environ.pop(name, None)
                os.environ.update(environment)
                os.environ.pop("SPECULA_RUN_DIR", None)
                p = self._pipeline([f"--agent={agent}", "foo|o/r|Go|ref"], self.tmp())
                assert p.run_dir is not None
                meta = json.loads((p.run_dir / "run.json").read_text())
                self.assertEqual(meta["model"], expected_model)
                self.assertEqual(meta["effort"], expected_effort)

    def test_meta_records_unknown_defaults_as_null(self) -> None:
        for agent in ("codex", "copilot-cli"):
            with self.subTest(agent=agent):
                os.environ.pop("SPECULA_RUN_DIR", None)
                p = self._pipeline([f"--agent={agent}", "foo|o/r|Go|ref"], self.tmp())
                assert p.run_dir is not None
                meta = json.loads((p.run_dir / "run.json").read_text())
                self.assertIsNone(meta["model"])
                self.assertIsNone(meta["effort"])

    def test_meta_records_explicit_resets_as_null(self) -> None:
        root = self.tmp()
        os.environ["SPECULA_MODEL"] = "env-model"
        os.environ["SPECULA_EFFORT"] = "low"
        os.environ["CLAUDE_MODEL"] = "opus"
        os.environ["CLAUDE_EFFORT"] = "high"
        argv = ["--agent=claude-code", "--model=", "--effort=", "foo|o/r|Go|ref"]
        p = self._pipeline(argv, root)
        assert p.run_dir is not None
        meta = json.loads((p.run_dir / "run.json").read_text())
        self.assertIsNone(meta["model"])
        self.assertIsNone(meta["effort"])
        self.assertEqual(meta["argv"], argv)

    def test_meta_records_claude_default_effort_as_unknown(self) -> None:
        root = self.tmp()
        p = self._pipeline(["--agent=claude-code", "--effort=default", "foo|o/r|Go|ref"], root)
        assert p.run_dir is not None
        meta = json.loads((p.run_dir / "run.json").read_text())
        self.assertIsNone(meta["effort"])

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

    def test_attach_restores_run_scoped_tlc_limits(self) -> None:
        root = self.tmp()
        first = self._pipeline(
            ["--run-id=myrun", "--tlc-memory-limit=64G", "--tlc-worker-limit=12", "foo|o/r|Go|ref"],
            root,
        )
        self.assertEqual(first.tlc_memory_limit, "64G")
        os.environ.pop("SPECULA_RUN_DIR", None)
        os.environ.pop("SPECULA_TLC_SCOPE", None)

        resumed = self._pipeline(["--run-id=myrun", "foo|o/r|Go|ref"], root)
        self.assertEqual(resumed.tlc_memory_limit, "64G")
        self.assertEqual(resumed.tlc_worker_limit, "12")

    def test_legacy_run_meta_migrates_tlc_limits_once(self) -> None:
        root = self.tmp()
        run = root / "runs" / "legacy"
        run.mkdir(parents=True)
        (run / "run.json").write_text('{"run_id": "legacy", "original": true}\n')

        configured = self._pipeline(
            ["--run-id=legacy", "--tlc-memory-limit=48G", "--tlc-worker-limit=10", "foo|o/r|Go|ref"],
            root,
        )
        self.assertEqual(configured.tlc_memory_limit, "48G")
        policy = json.loads((run / "tlc-resources.json").read_text())
        self.assertEqual(policy["memory_limit"], "48G")
        self.assertEqual(policy["worker_limit"], "10")
        os.environ.pop("SPECULA_RUN_DIR", None)
        os.environ.pop("SPECULA_TLC_SCOPE", None)

        resumed = self._pipeline(["--run-id=legacy", "foo|o/r|Go|ref"], root)
        self.assertEqual(resumed.tlc_memory_limit, "48G")
        self.assertEqual(resumed.tlc_worker_limit, "10")
        self.assertTrue(json.loads((run / "run.json").read_text())["original"])

    def test_invalid_legacy_audit_metadata_falls_back_without_blocking_attach(self) -> None:
        root = self.tmp()
        run = root / "runs" / "legacy"
        run.mkdir(parents=True)
        (run / "run.json").write_text('{"tlc_memory_limit": 64, "tlc_worker_limit": null}\n')
        self.patch_root(pl, root)
        p = pl.Pipeline()
        self.assertIsNone(p.parse_args(["--run-id=legacy", "foo|o/r|Go|ref"]))

        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertIsNone(p.resolve_run_dir())

        self.assertIn("WARNING: ignoring TLC resource fields in audit metadata", err.getvalue())
        policy = json.loads((run / "tlc-resources.json").read_text())
        self.assertEqual(policy["memory_limit"], "auto")
        self.assertIsNone(policy["worker_limit"])

    def test_attach_rejects_changed_tlc_limits(self) -> None:
        root = self.tmp()
        self._pipeline(
            ["--run-id=myrun", "--tlc-memory-limit=64G", "--tlc-worker-limit=12", "foo|o/r|Go|ref"],
            root,
        )
        os.environ.pop("SPECULA_RUN_DIR", None)
        os.environ.pop("SPECULA_TLC_SCOPE", None)
        resumed = pl.Pipeline()
        self.assertIsNone(
            resumed.parse_args(["--run-id=myrun", "--tlc-memory-limit=32G", "--tlc-worker-limit=8", "foo|o/r|Go|ref"])
        )
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(resumed.resolve_run_dir(), 1)
        self.assertIn("limit cannot change when resuming", err.getvalue())

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

    def test_default_mints_isolated_run(self) -> None:
        # the flip (step 7d): no flags, no ambient env -> a fresh isolated run
        root = self.tmp()
        p = self._pipeline(["foo|o/r|Go|ref"], root)
        assert p.run_dir is not None
        self.assertEqual(p.run_dir.parent, root / "runs")
        self.assertRegex(p.run_id, RUN_ID_RE)
        self.assertEqual(os.environ["SPECULA_RUN_DIR"], str(p.run_dir))

    def test_no_isolate_gives_legacy_mode(self) -> None:
        root = self.tmp()
        p = self._pipeline(["--no-isolate", "foo|o/r|Go|ref"], root)
        self.assertIsNone(p.run_dir)
        self.assertFalse((root / "runs").exists())
        self.assertNotIn("SPECULA_RUN_DIR", os.environ)
        self.assertTrue(Path(os.environ["SPECULA_TLC_SCOPE"]).is_absolute())

    def test_no_isolate_uses_one_unique_tlc_scope_per_invocation(self) -> None:
        root = self.tmp()
        self._pipeline(["--no-isolate", "foo|o/r|Go|ref", "bar|o/r|Go|ref"], root)
        first_scope = os.environ["SPECULA_TLC_SCOPE"]
        self._pipeline(["--no-isolate", "foo|o/r|Go|ref", "bar|o/r|Go|ref"], root)
        second_scope = os.environ["SPECULA_TLC_SCOPE"]
        self.assertNotEqual(first_scope, second_scope)

    def test_no_isolate_overrides_ambient_env(self) -> None:
        # explicit beats ambient: children must not re-isolate off the env
        root = self.tmp()
        self.set_run_dir(self.tmp() / "external-run")
        p = self._pipeline(["--no-isolate", "foo|o/r|Go|ref"], root)
        self.assertIsNone(p.run_dir)
        self.assertNotIn("SPECULA_RUN_DIR", os.environ)

    def test_explicit_isolate_mints_despite_ambient_env(self) -> None:
        # pre-flip behavior preserved: --isolate always minted a fresh run
        root = self.tmp()
        ext = self.tmp() / "external-run"
        self.set_run_dir(ext)
        p = self._pipeline(["--isolate", "foo|o/r|Go|ref"], root)
        assert p.run_dir is not None
        self.assertEqual(p.run_dir.parent, root / "runs")
        self.assertNotEqual(p.run_dir, ext)

    def test_no_isolate_conflicts_with_run_id(self) -> None:
        for argv in (
            ["--no-isolate", "--run-id=x", "foo|o/r|Go|ref"],
            ["--run-id=x", "--no-isolate", "foo|o/r|Go|ref"],
        ):
            with self.subTest(argv=argv):
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    rc = pl.Pipeline().parse_args(argv)
                self.assertEqual(rc, 1)
                self.assertIn("--no-isolate conflicts with --run-id", err.getvalue())

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
        self.addCleanup(setattr, pl, "LAUNCH_DIR", pl.LAUNCH_DIR)
        pl.LAUNCH_DIR = fake_scripts
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

    def _seed_rr(self, run: Path, name: str, statuses: list[str], subdir: str | None = None) -> None:
        d = run / name / ".specula-output" / "spec" / "repair-requests"
        if subdir:
            d = d / subdir
        d.mkdir(parents=True)
        for i, status in enumerate(statuses, 1):
            (d / f"RR-{i}.md").write_text(self.RR.format(rid=f"RR-{i}", status=status))

    def test_two_runs_do_not_interfere(self) -> None:
        launch_cwd = self.tmp()
        run_a, run_b = self.tmp() / "runA", self.tmp() / "runB"
        # run A: one repaired (CONSUMED) request in the active dir
        self._seed_rr(run_a, "footest", ["CONSUMED"])
        # run B: two requests the loop gave up on, filed under deferred/
        self._seed_rr(run_b, "footest", ["OPEN", "OPEN"], subdir="deferred")

        env = dict(os.environ)
        for var in ("MAX_REPAIR_ROUNDS", "QUOTA_5H", "QUOTA_7D", "QUOTA_MAX_WAITS", "CLAUDE_ALIAS"):
            env.pop(var, None)
        target = "footest|foo/bar|Go|Raft demo"
        procs = []
        for run in (run_a, run_b):
            procs.append(
                subprocess.Popen(
                    [sys.executable, str(PKG / "pipelinelib.py"), *self.SKIPS, target],
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
        self.assertIn("1 request(s) — 1 repaired, 0 deferred", sum_a)
        self.assertIn("2 request(s) — 0 repaired, 2 deferred", sum_b)
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
                assert line is not None  # for mypy: proven by the assertEqual
                # the launch cwd the isolated run does not write to never leaks in
                self.assertNotIn("/launch/dir", line)

    def test_legacy_unchanged(self) -> None:
        """Byte-identical to the bash launchers' hand-written globs (quirks and
        all)."""
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
