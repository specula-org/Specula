from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from specula import snapshotlib as sl


def _git(repo: Path, *args: str) -> str:
    env = {
        **os.environ,
        "GIT_AUTHOR_NAME": "Test",
        "GIT_AUTHOR_EMAIL": "test@example.com",
        "GIT_COMMITTER_NAME": "Test",
        "GIT_COMMITTER_EMAIL": "test@example.com",
    }
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    ).stdout


class SnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()

    def _repo(self, name: str = "original") -> Path:
        repo = self.root / name
        repo.mkdir()
        _git(repo, "init", "--quiet")
        (repo / ".gitignore").write_text("ignored-*\n")
        (repo / "tracked.txt").write_text("before\n")
        (repo / "delete.txt").write_text("delete me\n")
        (repo / "binary.bin").write_bytes(b"before\0data\n")
        _git(repo, "add", ".")
        _git(repo, "commit", "--quiet", "-m", "initial")
        (repo / "ignored-cache").write_text("initial ignored bytes\n")
        return repo

    def _plain_source(self, name: str = "plain") -> Path:
        source = self.root / name
        source.mkdir()
        (source / "file.txt").write_text("plain source\n")
        return source

    def test_snapshot_git_environment_removes_only_repository_selectors(self) -> None:
        env = {
            "GIT_DIR": "/outside/.git",
            "GIT_WORK_TREE": "/outside",
            "GIT_INDEX_FILE": "/outside/index",
            "GIT_OBJECT_DIRECTORY": "/outside/objects",
            "GIT_CONFIG": "/outside/config",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_PARAMETERS": "'core.worktree'='/outside'",
            "GIT_CONFIG_KEY_0": "core.worktree",
            "GIT_CONFIG_VALUE_0": "/outside",
            "GIT_CONFIG_GLOBAL": "/developer/global-config",
            "GIT_CONFIG_SYSTEM": "/developer/system-config",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CEILING_DIRECTORIES": "/untrusted",
            "GIT_EXTERNAL_DIFF": "/outside/diff.sh",
            "GIT_NAMESPACE": "developer-namespace",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_REPLACE_REF_BASE": "refs/developer/replace/",
            "GIT_SSH_COMMAND": "ssh -i key",
            "GIT_ASKPASS": "/usr/bin/askpass",
            "GIT_AUTHOR_NAME": "Developer",
            "SSH_AUTH_SOCK": "/tmp/agent.sock",
            "GITHUB_TOKEN": "token",
        }

        sl.sanitize_snapshot_git_environment(env, ceiling="/private")

        for key in (
            "GIT_DIR",
            "GIT_WORK_TREE",
            "GIT_INDEX_FILE",
            "GIT_OBJECT_DIRECTORY",
            "GIT_CONFIG",
            "GIT_CONFIG_COUNT",
            "GIT_CONFIG_PARAMETERS",
            "GIT_CONFIG_KEY_0",
            "GIT_CONFIG_VALUE_0",
            "GIT_EXTERNAL_DIFF",
        ):
            self.assertNotIn(key, env)
        self.assertEqual(env["GIT_CEILING_DIRECTORIES"], "/private")
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], "/developer/global-config")
        self.assertEqual(env["GIT_CONFIG_SYSTEM"], "/developer/system-config")
        self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(env["GIT_NAMESPACE"], "developer-namespace")
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertEqual(env["GIT_REPLACE_REF_BASE"], "refs/developer/replace/")
        self.assertEqual(env["GIT_SSH_COMMAND"], "ssh -i key")
        self.assertEqual(env["GIT_ASKPASS"], "/usr/bin/askpass")
        self.assertEqual(env["GIT_AUTHOR_NAME"], "Developer")
        self.assertEqual(env["SSH_AUTH_SOCK"], "/tmp/agent.sock")
        self.assertEqual(env["GITHUB_TOKEN"], "token")

    def test_full_tree_diff_round_trip_leaves_original_unchanged(self) -> None:
        original = self._repo()
        original_index = (original / ".git" / "index").read_bytes()
        run = self.root / "run"
        run.mkdir()

        snapshot = sl.prepare_sources(run, {"demo": original})["demo"].source
        self.assertNotEqual((snapshot / "tracked.txt").stat().st_ino, (original / "tracked.txt").stat().st_ino)
        self.assertEqual(_git(snapshot, "rev-parse", "HEAD"), _git(original, "rev-parse", "HEAD"))

        (snapshot / "tracked.txt").write_text("after\n")
        (snapshot / "delete.txt").unlink()
        (snapshot / "new.txt").write_text("new\n")
        (snapshot / "ignored-cache").write_text("changed ignored bytes\n")
        (snapshot / "ignored-new").write_text("new ignored bytes\n")
        (snapshot / "binary.bin").write_bytes(b"after\0data\n")
        _git(snapshot, "add", "tracked.txt")
        _git(snapshot, "commit", "--quiet", "-m", "agent commit")

        changed = sl.capture_changes(run)
        patch = run / "demo" / "changes.patch"
        content = patch.read_bytes()

        self.assertEqual(changed, {"demo": True})
        for path in (b"tracked.txt", b"delete.txt", b"new.txt", b"ignored-cache", b"ignored-new"):
            self.assertIn(path, content)
        self.assertIn(b"GIT binary patch", content)
        self.assertNotIn(b"/.git/", content)
        self.assertEqual((original / "tracked.txt").read_text(), "before\n")
        self.assertEqual((original / "ignored-cache").read_text(), "initial ignored bytes\n")
        self.assertEqual((original / ".git" / "index").read_bytes(), original_index)

        _git(original, "apply", str(patch))
        self.assertEqual((original / "tracked.txt").read_text(), "after\n")
        self.assertFalse((original / "delete.txt").exists())
        self.assertEqual((original / "ignored-cache").read_text(), "changed ignored bytes\n")
        self.assertEqual((original / "ignored-new").read_text(), "new ignored bytes\n")
        self.assertEqual((original / "binary.bin").read_bytes(), b"after\0data\n")

    def test_private_git_preserves_index_state(self) -> None:
        original = self._repo()
        (original / "tracked.txt").write_text("staged\n")
        _git(original, "add", "tracked.txt")
        (original / "tracked.txt").write_text("staged and unstaged\n")
        (original / "staged-new.txt").write_text("staged new\n")
        _git(original, "add", "staged-new.txt")
        (original / "untracked.txt").write_text("untracked\n")
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertEqual(_git(source, "status", "--porcelain=v1"), _git(original, "status", "--porcelain=v1"))
        self.assertEqual(_git(source, "diff", "--cached", "--binary"), _git(original, "diff", "--cached", "--binary"))

    def test_private_copy_adds_owner_write_without_changing_original_modes(self) -> None:
        original = self._plain_source()
        locked = original / "locked"
        locked.mkdir()
        readonly = locked / "readonly.txt"
        readonly.write_text("before\n")
        executable = original / "script.sh"
        executable.write_text("#!/bin/sh\n")
        readonly.chmod(0o444)
        locked.chmod(0o555)
        executable.chmod(0o555)
        self.addCleanup(locked.chmod, 0o755)
        self.addCleanup(readonly.chmod, 0o644)
        self.addCleanup(executable.chmod, 0o755)
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertEqual(readonly.stat().st_mode & 0o777, 0o444)
        self.assertEqual(locked.stat().st_mode & 0o777, 0o555)
        self.assertEqual(executable.stat().st_mode & 0o777, 0o555)
        self.assertEqual((source / "locked" / "readonly.txt").stat().st_mode & 0o777, 0o644)
        self.assertEqual((source / "locked").stat().st_mode & 0o777, 0o755)
        self.assertEqual((source / "script.sh").stat().st_mode & 0o777, 0o755)
        (source / "locked" / "readonly.txt").write_text("after\n")
        (source / "locked" / "new.txt").write_text("new\n")

    def test_private_git_preserves_all_local_branches(self) -> None:
        original = self._repo()
        initial_branch = _git(original, "branch", "--show-current").strip()
        _git(original, "switch", "-c", "feature")
        (original / "feature.txt").write_text("feature\n")
        _git(original, "add", "feature.txt")
        _git(original, "commit", "--quiet", "-m", "feature")
        feature_head = _git(original, "rev-parse", "feature").strip()
        _git(original, "switch", initial_branch)
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertIn("feature", _git(source, "branch", "--format=%(refname:short)").splitlines())
        _git(source, "switch", "feature")
        self.assertEqual(_git(source, "rev-parse", "HEAD").strip(), feature_head)

    def test_sparse_checkout_behavior_is_preserved(self) -> None:
        original = self._repo()
        (original / "visible").mkdir()
        (original / "visible" / "file.txt").write_text("visible\n")
        (original / "hidden").mkdir()
        (original / "hidden" / "file.txt").write_text("hidden\n")
        _git(original, "add", "visible", "hidden")
        _git(original, "commit", "--quiet", "-m", "directories")
        initial_branch = _git(original, "branch", "--show-current").strip()
        _git(original, "switch", "-c", "feature")
        (original / "hidden" / "file.txt").write_text("feature hidden\n")
        _git(original, "add", "hidden/file.txt")
        _git(original, "commit", "--quiet", "-m", "feature hidden")
        _git(original, "switch", initial_branch)
        _git(original, "sparse-checkout", "init", "--cone")
        _git(original, "sparse-checkout", "set", "visible")
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertFalse((source / "hidden").exists())
        self.assertEqual(_git(source, "status", "--porcelain=v1"), _git(original, "status", "--porcelain=v1"))
        self.assertEqual(_git(source, "ls-files", "-t"), _git(original, "ls-files", "-t"))
        self.assertEqual(_git(source, "config", "--bool", "core.sparseCheckout").strip(), "true")
        self.assertEqual(
            (source / ".git" / "info" / "sparse-checkout").read_bytes(),
            (original / ".git" / "info" / "sparse-checkout").read_bytes(),
        )
        _git(source, "switch", "feature")
        self.assertFalse((source / "hidden").exists())
        _git(source, "sparse-checkout", "reapply")
        self.assertEqual(_git(source, "sparse-checkout", "list").strip(), "visible")

    def test_private_git_is_self_contained_and_has_no_active_origin(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source
        private_config = (source / ".git" / "config").read_text()
        loose_object = next(
            path for path in (original / ".git" / "objects").glob("[0-9a-f][0-9a-f]/*") if path.is_file()
        )
        private_object = source / ".git" / "objects" / loose_object.relative_to(original / ".git" / "objects")

        self.assertNotIn(str(original), private_config)
        self.assertNotEqual(
            (loose_object.stat().st_dev, loose_object.stat().st_ino),
            (private_object.stat().st_dev, private_object.stat().st_ino),
        )
        original.rename(self.root / "original-moved")
        _git(source, "fsck", "--full")
        self.assertIn("initial", _git(source, "log", "-1", "--format=%s"))
        self.assertEqual(sl.load_sources(run)["demo"].source, source)

    def test_source_object_alternates_are_rejected_transactionally(self) -> None:
        base = self._repo("base")
        original = self.root / "original"
        subprocess.run(["git", "clone", "--quiet", "--shared", str(base), str(original)], check=True)
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "object alternates"):
            sl.prepare_sources(run, {"demo": original})

        self.assertFalse((run / sl.SOURCE_MAP).exists())
        self.assertFalse((run / "demo" / "source").exists())

    def test_partial_clone_object_store_is_rejected(self) -> None:
        original = self._repo()
        _git(original, "repack", "-a", "-d")
        pack = next((original / ".git" / "objects" / "pack").glob("*.pack"))
        pack.with_suffix(".promisor").touch()
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "partial Git clones"):
            sl.prepare_sources(run, {"demo": original})

        self.assertFalse((run / sl.SOURCE_MAP).exists())
        self.assertFalse((run / "demo" / "source").exists())

    def test_no_change_patch_is_empty_even_with_text_attributes(self) -> None:
        original = self._repo()
        (original / ".gitattributes").write_text("*.txt text\n")
        (original / "crlf.txt").write_bytes(b"hello\r\n")
        run = self.root / "run"
        run.mkdir()

        sl.prepare_sources(run, {"demo": original})
        changed = sl.capture_changes(run)

        self.assertEqual(changed, {"demo": False})
        self.assertEqual((run / "demo" / "changes.patch").read_bytes(), b"")

    def test_resume_reuses_private_source(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        first = sl.prepare_sources(run, {"demo": original})["demo"]
        (first.source / "agent.txt").write_text("keep\n")

        resumed = sl.prepare_sources(run, {"demo": original})["demo"]

        self.assertEqual(resumed.source, first.source)
        self.assertEqual((resumed.source / "agent.txt").read_text(), "keep\n")

    def test_snapshot_without_map_is_never_rebound_to_another_source(self) -> None:
        original = self._repo()
        run = self.root / "run"
        (run / "demo" / "source").mkdir(parents=True)
        (run / "demo" / "baseline.git").mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "refusing to reuse"):
            sl.prepare_sources(run, {"demo": original})

    def test_external_symlink_fails_before_copy(self) -> None:
        original = self._repo()
        (original / "external").symlink_to("/dev/null")
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "symlinks outside"):
            sl.prepare_sources(run, {"demo": original})

        self.assertFalse((run / sl.SOURCE_MAP).exists())
        self.assertFalse((run / "demo" / "source").exists())

    def test_relocated_relative_symlink_cannot_escape_to_original(self) -> None:
        original = self.root / "a" / "b" / "original"
        original.mkdir(parents=True)
        victim = original / "victim.txt"
        victim.write_text("original\n")
        (original / "escape").symlink_to("../../../a/b/original/victim.txt")
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "symlinks outside"):
            sl.prepare_sources(run, {"demo": original})

        self.assertEqual(victim.read_text(), "original\n")
        self.assertFalse((run / sl.SOURCE_MAP).exists())
        self.assertFalse((run / "demo" / "source").exists())

    def test_resume_revalidates_private_symlinks(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        source = sl.prepare_sources(run, {"demo": original})["demo"].source
        target = original / "tracked.txt"
        (source / "escape").symlink_to(os.path.relpath(target, source))

        with self.assertRaisesRegex(sl.SnapshotError, "symlinks outside"):
            sl.load_sources(run)

    def test_external_git_common_directory_is_rebuilt_privately(self) -> None:
        original = self._repo()
        (original / ".git" / "commondir").write_text(f"{original / '.git'}\n")
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertFalse((source / ".git" / "commondir").exists())
        self.assertEqual(_git(source, "rev-parse", "--git-common-dir").strip(), ".git")

    def test_repository_local_git_behavior_is_not_copied_or_executed(self) -> None:
        original = self._repo()
        marker = self.root / "original-command-ran"
        hooks = original / "custom-hooks"
        hooks.mkdir()
        pre_commit = hooks / "pre-commit"
        pre_commit.write_text(f'#!/bin/sh\n: > "{marker}"\nexit 0\n')
        pre_commit.chmod(0o755)
        _git(original, "config", "core.hooksPath", str(hooks))
        _git(original, "config", "specula.snapshotSentinel", "original-only")
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source
        private_config = (source / ".git" / "config").read_text()
        private_settings = _git(source, "config", "--local", "--list").casefold()

        self.assertFalse(marker.exists())
        self.assertNotIn(str(original), private_config)
        self.assertNotIn("specula.snapshotsentinel=", private_settings)
        _git(source, "status", "--short")
        (source / "tracked.txt").write_text("private change\n")
        _git(source, "add", "tracked.txt")
        _git(source, "commit", "--quiet", "-m", "private commit")
        self.assertFalse(marker.exists())

    def test_resume_rejects_external_object_alternates(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        source = sl.prepare_sources(run, {"demo": original})["demo"].source
        alternates = source / ".git" / "objects" / "info" / "alternates"
        alternates.write_text(f"{original / '.git' / 'objects'}\n")

        with self.assertRaisesRegex(sl.SnapshotError, "object alternates"):
            sl.load_sources(run)

    def test_source_map_records_and_revalidates_git_kind(self) -> None:
        git_source = self._repo("git-source")
        plain_source = self._plain_source()
        run = self.root / "run"
        run.mkdir()

        snapshots = sl.prepare_sources(run, {"git": git_source, "plain": plain_source})
        document = json.loads((run / sl.SOURCE_MAP).read_text())

        self.assertEqual(document["version"], 3)
        self.assertTrue(snapshots["git"].is_git)
        self.assertFalse(snapshots["plain"].is_git)
        self.assertTrue(document["targets"]["git"]["is_git"])
        self.assertFalse(document["targets"]["plain"]["is_git"])

        shutil.rmtree(snapshots["git"].source / ".git")
        with self.assertRaisesRegex(sl.SnapshotError, "Git type"):
            sl.load_sources(run)

    def test_old_source_map_version_is_rejected(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        sl.prepare_sources(run, {"demo": original})
        map_path = run / sl.SOURCE_MAP
        document = json.loads(map_path.read_text())
        document["version"] = 2
        map_path.write_text(json.dumps(document))

        with self.assertRaisesRegex(sl.SnapshotError, "invalid private source map"):
            sl.load_sources(run)

    def test_resume_rejects_git_created_inside_plain_private_source(self) -> None:
        plain_source = self._plain_source()
        run = self.root / "run"
        run.mkdir()
        snapshot = sl.prepare_sources(run, {"plain": plain_source})["plain"]

        _git(snapshot.source, "init", "--quiet")

        with self.assertRaisesRegex(sl.SnapshotError, "Git type"):
            sl.load_sources(run)

    def test_original_linked_worktree_registration_is_not_copied(self) -> None:
        original = self._repo()
        linked = self.root / "linked"
        _git(original, "worktree", "add", "--quiet", "-b", "linked-test", str(linked))
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertIn(str(linked), _git(original, "worktree", "list", "--porcelain"))
        private_worktrees = _git(source, "worktree", "list", "--porcelain")
        self.assertIn(str(source), private_worktrees)
        self.assertNotIn(str(linked), private_worktrees)

    def test_run_local_confirmation_worktree_registration_is_supported(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        source = sl.prepare_sources(run, {"demo": original})["demo"].source
        worktree = run / "demo" / ".specula-output" / "confirmation" / "MC-1" / "worktree"
        worktree.parent.mkdir(parents=True)
        _git(source, "worktree", "add", "--quiet", "--detach", str(worktree))

        self.assertEqual(sl.load_sources(run)["demo"].source, source)

        # An interrupted process can leave only the registration. It is still
        # confined to this run and must not prevent the next invocation.
        shutil.rmtree(worktree)
        self.assertIn(str(worktree), _git(source, "worktree", "list", "--porcelain"))
        self.assertEqual(sl.load_sources(run)["demo"].source, source)

    def test_multi_target_prepare_failure_rolls_back_and_can_retry(self) -> None:
        first = self._repo("first")
        second = self._repo("second")
        (second / "external").symlink_to("/dev/null")
        run = self.root / "run"
        preserved = run / "first" / "existing.log"
        preserved.parent.mkdir(parents=True)
        preserved.write_text("keep\n")

        with self.assertRaisesRegex(sl.SnapshotError, "symlinks outside"):
            sl.prepare_sources(run, {"first": first, "second": second})

        self.assertEqual(preserved.read_text(), "keep\n")
        self.assertFalse((run / sl.SOURCE_MAP).exists())
        for name in ("first", "second"):
            for artifact in ("source", "baseline.git", ".source.incomplete", ".baseline.git.incomplete"):
                self.assertFalse((run / name / artifact).exists(), f"left behind: {name}/{artifact}")

        (second / "external").unlink()
        snapshots = sl.prepare_sources(run, {"first": first, "second": second})
        self.assertEqual(set(snapshots), {"first", "second"})
        self.assertEqual(preserved.read_text(), "keep\n")

    def test_path_list_separator_is_rejected_before_copy_and_on_resume(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        invalid_name = f"left{os.pathsep}right"

        with (
            mock.patch.object(shutil, "copytree", wraps=shutil.copytree) as copytree,
            self.assertRaisesRegex(sl.SnapshotError, "path-list separator"),
        ):
            sl.prepare_sources(run, {invalid_name: original})
        copytree.assert_not_called()
        self.assertFalse((run / sl.SOURCE_MAP).exists())

        safe_run = self.root / "safe-run"
        safe_run.mkdir()
        sl.prepare_sources(safe_run, {"demo": original})
        unsafe_run = self.root / f"renamed{os.pathsep}run"
        safe_run.rename(unsafe_run)

        with self.assertRaisesRegex(sl.SnapshotError, "path-list separator"):
            sl.load_sources(unsafe_run)

    def test_source_map_target_name_is_rejected_before_copy(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()

        with (
            mock.patch.object(shutil, "copytree", wraps=shutil.copytree) as copytree,
            self.assertRaisesRegex(sl.SnapshotError, "invalid snapshot target name"),
        ):
            sl.prepare_sources(run, {sl.SOURCE_MAP: original})

        copytree.assert_not_called()
        self.assertFalse((run / sl.SOURCE_MAP).exists())

    def test_multi_target_separator_is_rejected_before_any_copy(self) -> None:
        first = self._repo("first")
        second = self._repo("second")
        run = self.root / "run"
        run.mkdir()
        invalid_name = f"second{os.pathsep}invalid"

        with (
            mock.patch.object(shutil, "copytree", wraps=shutil.copytree) as copytree,
            self.assertRaisesRegex(sl.SnapshotError, "path-list separator"),
        ):
            sl.prepare_sources(run, {"first": first, invalid_name: second})

        copytree.assert_not_called()
        self.assertFalse((run / sl.SOURCE_MAP).exists())

    def test_run_path_separator_is_rejected_before_copy(self) -> None:
        original = self._repo()
        run = self.root / f"run{os.pathsep}unsafe"
        run.mkdir()

        with (
            mock.patch.object(shutil, "copytree", wraps=shutil.copytree) as copytree,
            self.assertRaisesRegex(sl.SnapshotError, "path-list separator"),
        ):
            sl.prepare_sources(run, {"demo": original})
        copytree.assert_not_called()
        self.assertFalse((run / sl.SOURCE_MAP).exists())

    def test_map_write_failure_rolls_back_all_prepared_targets(self) -> None:
        first = self._repo("first")
        second = self._repo("second")
        run = self.root / "run"
        run.mkdir()
        write_map = sl._write_map

        def fail_after_write(path: Path, document: dict[str, object]) -> None:
            write_map(path, document)
            raise OSError("simulated map failure")

        with (
            mock.patch.object(sl, "_write_map", side_effect=fail_after_write),
            self.assertRaisesRegex(OSError, "simulated map failure"),
        ):
            sl.prepare_sources(run, {"first": first, "second": second})

        self.assertFalse((run / sl.SOURCE_MAP).exists())
        for name in ("first", "second"):
            self.assertFalse((run / name / "source").exists())
            self.assertFalse((run / name / "baseline.git").exists())

        self.assertEqual(set(sl.prepare_sources(run, {"first": first, "second": second})), {"first", "second"})

    def test_unsupported_git_layouts_and_special_files_fail_fast(self) -> None:
        for kind in ("nested", "linked", "submodule", "external-worktree", "fifo"):
            with self.subTest(kind=kind):
                original = self.root / kind
                original.mkdir()
                if kind == "nested":
                    (original / "nested" / ".git").mkdir(parents=True)
                    expected = "nested repositories"
                elif kind == "linked":
                    (original / ".git").write_text("gitdir: /elsewhere\n")
                    expected = "linked worktrees"
                elif kind == "submodule":
                    (original / ".gitmodules").write_text('[submodule "demo"]\n')
                    expected = "submodules"
                elif kind == "external-worktree":
                    actual = self.root / "actual-worktree"
                    actual.mkdir()
                    _git(original, "init", "--quiet")
                    _git(original, "config", "core.worktree", str(actual))
                    expected = "does not match"
                else:
                    os.mkfifo(original / "pipe")
                    expected = "special source files"
                run = self.root / f"run-{kind}"
                run.mkdir()
                with self.assertRaisesRegex(sl.SnapshotError, expected):
                    sl.prepare_sources(run, {"demo": original})


if __name__ == "__main__":
    unittest.main()
