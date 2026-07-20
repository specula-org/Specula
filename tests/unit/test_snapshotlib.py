from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

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

    def _repo(self) -> Path:
        repo = self.root / "original"
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
