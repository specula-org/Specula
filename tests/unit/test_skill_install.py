"""Tests for composable Specula skill installation."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from specula import skill_install

REPO_ROOT = Path(__file__).resolve().parents[2]


class SkillInstallCase(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        self.source = self.root / "source"
        self.target = self.root / "target"
        self.source.mkdir()

    def skill(self, folder: str, name: str, *, root: Path | None = None) -> Path:
        parent = root or self.source
        path = parent / folder
        path.mkdir(parents=True)
        (path / "SKILL.md").write_text(f"---\nname: {name}\ndescription: test\n---\n\nInstructions.\n")
        return path


class TestInstallSkills(SkillInstallCase):
    def test_repository_skills_have_unique_canonical_names(self) -> None:
        skills = skill_install.discover_skills(REPO_ROOT / "skills")
        names = [skill.name for skill in skills]
        self.assertEqual(
            names,
            [
                "bug-classification",
                "bug-confirmation",
                "bug-recording",
                "code-analysis",
                "harness-generation",
                "spec-generation",
                "tla-checking-workflow",
                "tla-trace-workflow",
                "validation-workflow",
                "writing-prompt-extra",
            ],
        )
        result = skill_install.install_skills(REPO_ROOT / "skills", self.target)
        self.assertTrue(result.complete)
        for skill in skills:
            self.assertEqual((self.target / skill.name).resolve(), skill.path.resolve())

    def test_first_install_uses_registered_names(self) -> None:
        code = self.skill("code_analysis", "code-analysis")
        validation = self.skill("validation-workflow", "validation-workflow")
        (self.source / "workflow-overview.md").write_text("not a skill\n")

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertEqual(result.linked, ("code-analysis", "validation-workflow"))
        self.assertEqual((self.target / "code-analysis").resolve(), code.resolve())
        self.assertEqual((self.target / "validation-workflow").resolve(), validation.resolve())
        self.assertFalse((self.target / "workflow-overview.md").exists())

    def test_existing_third_party_skill_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        third_party = self.skill("third-party", "third-party", root=self.target)
        marker = third_party / "keep.txt"
        marker.write_text("mine\n")

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertEqual(marker.read_text(), "mine\n")
        self.assertTrue((self.target / "code-analysis").is_symlink())

    def test_rerun_is_idempotent(self) -> None:
        self.skill("code_analysis", "code-analysis")
        first = skill_install.install_skills(self.source, self.target)
        second = skill_install.install_skills(self.source, self.target)

        self.assertEqual(first.linked, ("code-analysis",))
        self.assertEqual(second.linked, ())
        self.assertEqual(second.existing, ("code-analysis",))
        self.assertTrue(second.complete)

    def test_owned_noncanonical_link_is_migrated_to_registered_name(self) -> None:
        source = self.skill("code_analysis", "code-analysis")
        self.target.mkdir()
        old = self.target / "code_analysis"
        old.symlink_to(source, target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        canonical = self.target / "code-analysis"
        self.assertTrue(result.complete)
        self.assertEqual(result.migrated_links, ((old, canonical),))
        self.assertFalse(old.exists() or old.is_symlink())
        self.assertEqual(canonical.resolve(), source.resolve())

    def test_owned_noncanonical_link_reports_canonical_blocker(self) -> None:
        source = self.skill("code_analysis", "code-analysis")
        self.target.mkdir()
        old = self.target / "code_analysis"
        old.symlink_to(source, target_is_directory=True)
        canonical = self.target / "code-analysis"
        canonical.write_text("keep\n")

        result = skill_install.install_skills(self.source, self.target)

        self.assertEqual(result.conflicts, (canonical,))
        self.assertEqual(canonical.read_text(), "keep\n")
        self.assertEqual(old.resolve(), source.resolve())

    def test_same_name_directory_conflict_does_not_block_other_skills(self) -> None:
        self.skill("code_analysis", "code-analysis")
        self.skill("spec_generation", "spec-generation")
        existing = self.skill("code-analysis", "code-analysis", root=self.target)
        marker = existing / "keep.txt"
        marker.write_text("third party\n")

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertEqual(result.conflicts, (existing,))
        self.assertEqual(marker.read_text(), "third party\n")
        self.assertTrue((self.target / "spec-generation").is_symlink())

    def test_same_registered_name_under_another_directory_conflicts(self) -> None:
        self.skill("code_analysis", "code-analysis")
        existing = self.skill("custom-folder", "code-analysis", root=self.target)

        result = skill_install.install_skills(self.source, self.target)

        self.assertEqual(result.conflicts, (existing,))
        self.assertFalse((self.target / "code-analysis").exists())

    def test_unrelated_skill_symlink_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        elsewhere = self.root / "elsewhere"
        self.skill("foreign", "code-analysis", root=elsewhere)
        self.target.mkdir()
        destination = self.target / "code-analysis"
        destination.symlink_to(elsewhere / "foreign", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertEqual(result.conflicts, (destination,))
        self.assertEqual(destination.resolve(), (elsewhere / "foreign").resolve())

    def test_legacy_whole_directory_link_is_migrated(self) -> None:
        skill = self.skill("code_analysis", "code-analysis")
        self.target.symlink_to(self.source, target_is_directory=True)

        first = skill_install.install_skills(self.source, self.target)
        second = skill_install.install_skills(self.source, self.target)

        self.assertTrue(first.migrated_legacy_root)
        self.assertTrue(self.target.is_dir() and not self.target.is_symlink())
        self.assertEqual((self.target / "code-analysis").resolve(), skill.resolve())
        self.assertEqual(second.existing, ("code-analysis",))

    def test_user_managed_root_symlink_is_preserved_and_merged(self) -> None:
        source = self.skill("code_analysis", "code-analysis")
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        self.target.symlink_to(elsewhere, target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertTrue(self.target.is_symlink())
        self.assertEqual(self.target.resolve(), elsewhere.resolve())
        self.assertEqual((elsewhere / "code-analysis").resolve(), source.resolve())

    def test_broken_root_symlink_is_preserved_as_conflict(self) -> None:
        self.skill("code_analysis", "code-analysis")
        missing = self.root / "missing"
        self.target.symlink_to(missing, target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertEqual(result.conflicts, (self.target,))
        self.assertTrue(self.target.is_symlink())
        self.assertFalse(missing.exists())

    def test_root_symlink_to_file_is_preserved_as_conflict(self) -> None:
        self.skill("code_analysis", "code-analysis")
        file_target = self.root / "skills.txt"
        file_target.write_text("keep\n")
        self.target.symlink_to(file_target)

        result = skill_install.install_skills(self.source, self.target)

        self.assertEqual(result.conflicts, (self.target,))
        self.assertTrue(self.target.is_symlink())
        self.assertEqual(file_target.read_text(), "keep\n")

    def test_duplicate_source_names_fail_before_writing(self) -> None:
        self.skill("first", "duplicate")
        self.skill("second", "duplicate")

        with self.assertRaisesRegex(ValueError, "duplicate registered skill name"):
            skill_install.install_skills(self.source, self.target)

        self.assertFalse(self.target.exists())


class TestCli(SkillInstallCase):
    def test_conflict_returns_nonzero_and_reports_incomplete(self) -> None:
        self.skill("code_analysis", "code-analysis")
        self.skill("code-analysis", "code-analysis", root=self.target)
        out, err = io.StringIO(), io.StringIO()

        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = skill_install.main(["--source", str(self.source), "--target", str(self.target)])

        self.assertEqual(rc, 1)
        self.assertIn("CONFLICT", err.getvalue())
        self.assertIn("installation incomplete", err.getvalue())

    def test_success_removes_owned_relocated_legacy_root(self) -> None:
        self.skill("code_analysis", "code-analysis")
        legacy = self.root / "legacy"
        legacy.symlink_to(self.source, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--legacy-root",
                str(legacy),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertFalse(legacy.exists() or legacy.is_symlink())

    def test_success_preserves_unrelated_relocated_legacy_path(self) -> None:
        self.skill("code_analysis", "code-analysis")
        unrelated = self.root / "unrelated"
        unrelated.mkdir()
        legacy = self.root / "legacy"
        legacy.symlink_to(unrelated, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--legacy-root",
                str(legacy),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue(legacy.is_symlink())
        self.assertEqual(legacy.resolve(), unrelated.resolve())


if __name__ == "__main__":
    unittest.main()
