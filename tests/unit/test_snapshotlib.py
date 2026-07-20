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

    def test_external_git_common_directory_is_rejected(self) -> None:
        original = self._repo()
        (original / ".git" / "commondir").write_text(f"{original / '.git'}\n")
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "common directory points outside"):
            sl.prepare_sources(run, {"demo": original})

    def test_external_git_hooks_path_is_rejected(self) -> None:
        original = self._repo()
        hooks = original / "custom-hooks"
        hooks.mkdir()
        _git(original, "config", "core.hooksPath", str(hooks))
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "hooks path points outside"):
            sl.prepare_sources(run, {"demo": original})

    def test_resume_revalidates_private_git_metadata(self) -> None:
        original = self._repo()
        run = self.root / "run"
        run.mkdir()
        source = sl.prepare_sources(run, {"demo": original})["demo"].source
        _git(source, "config", "core.hooksPath", str(original / "hooks"))

        with self.assertRaisesRegex(sl.SnapshotError, "hooks path points outside"):
            sl.load_sources(run)

    def test_source_map_records_and_revalidates_git_kind(self) -> None:
        git_source = self._repo("git-source")
        plain_source = self._plain_source()
        run = self.root / "run"
        run.mkdir()

        snapshots = sl.prepare_sources(run, {"git": git_source, "plain": plain_source})
        document = json.loads((run / sl.SOURCE_MAP).read_text())

        self.assertEqual(document["version"], 2)
        self.assertTrue(snapshots["git"].is_git)
        self.assertFalse(snapshots["plain"].is_git)
        self.assertTrue(document["targets"]["git"]["is_git"])
        self.assertFalse(document["targets"]["plain"]["is_git"])

        shutil.rmtree(snapshots["git"].source / ".git")
        with self.assertRaisesRegex(sl.SnapshotError, "Git type"):
            sl.load_sources(run)

    def test_resume_rejects_git_created_inside_plain_private_source(self) -> None:
        plain_source = self._plain_source()
        run = self.root / "run"
        run.mkdir()
        snapshot = sl.prepare_sources(run, {"plain": plain_source})["plain"]

        _git(snapshot.source, "init", "--quiet")

        with self.assertRaisesRegex(sl.SnapshotError, "Git type"):
            sl.load_sources(run)

    def test_dormant_conditional_git_includes_are_rejected(self) -> None:
        conditions = (
            "onbranch:never-active",
            "hasconfig:remote.*.url:https://example.invalid/**",
        )
        for index, condition in enumerate(conditions):
            with self.subTest(condition=condition):
                original = self._repo(f"conditional-{index}")
                included = self.root / f"conditional-{index}.inc"
                included.write_text(f"[core]\n\thooksPath = {original / 'hooks'}\n")
                with (original / ".git" / "config").open("a") as config:
                    config.write(f'\n[includeIf "{condition}"]\n\tpath = {included}\n')
                run = self.root / f"run-conditional-{index}"
                run.mkdir()

                with self.assertRaisesRegex(sl.SnapshotError, "include"):
                    sl.prepare_sources(run, {"demo": original})

    def test_path_valued_fsmonitor_is_rejected(self) -> None:
        original = self._repo()
        monitor = original / "fsmonitor.sh"
        monitor.write_text("#!/bin/sh\nexit 0\n")
        monitor.chmod(0o755)
        _git(original, "config", "core.fsmonitor", str(monitor))
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "fsmonitor"):
            sl.prepare_sources(run, {"demo": original})

    def test_boolean_fsmonitor_values_are_supported(self) -> None:
        for value in ("true", "false"):
            with self.subTest(value=value):
                original = self._repo(f"fsmonitor-{value}")
                _git(original, "config", "core.fsmonitor", value)
                run = self.root / f"run-fsmonitor-{value}"
                run.mkdir()

                snapshot = sl.prepare_sources(run, {"demo": original})["demo"]

                self.assertTrue(snapshot.is_git)

    def test_repo_local_git_hooks_path_is_supported(self) -> None:
        original = self._repo()
        (original / ".githooks").mkdir()
        _git(original, "config", "core.hooksPath", ".githooks")
        run = self.root / "run"
        run.mkdir()

        source = sl.prepare_sources(run, {"demo": original})["demo"].source

        self.assertEqual(_git(source, "rev-parse", "--git-path", "hooks").strip(), ".githooks")

    def test_registered_linked_worktree_is_rejected(self) -> None:
        original = self._repo()
        linked = self.root / "linked"
        _git(original, "worktree", "add", "--quiet", "-b", "linked-test", str(linked))
        run = self.root / "run"
        run.mkdir()

        with self.assertRaisesRegex(sl.SnapshotError, "registered linked worktrees"):
            sl.prepare_sources(run, {"demo": original})

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

    def test_non_confirmation_worktree_registration_is_rejected_on_resume(self) -> None:
        for location in ("wrong-run-path", "external"):
            with self.subTest(location=location):
                original = self._repo(f"repo-{location}")
                run = self.root / f"run-{location}"
                run.mkdir()
                source = sl.prepare_sources(run, {"demo": original})["demo"].source
                if location == "wrong-run-path":
                    worktree = run / "demo" / ".specula-output" / "confirmation" / "MC-1" / "other"
                else:
                    worktree = self.root / "external-worktree"
                worktree.parent.mkdir(parents=True, exist_ok=True)
                _git(source, "worktree", "add", "--quiet", "--detach", str(worktree))

                with self.assertRaisesRegex(sl.SnapshotError, "registered linked worktrees"):
                    sl.load_sources(run)

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
                    _git(original, "init", "--quiet")
                    _git(original, "config", "core.worktree", str(original))
                    expected = "points outside"
                else:
                    os.mkfifo(original / "pipe")
                    expected = "special source files"
                run = self.root / f"run-{kind}"
                run.mkdir()
                with self.assertRaisesRegex(sl.SnapshotError, expected):
                    sl.prepare_sources(run, {"demo": original})


if __name__ == "__main__":
    unittest.main()
