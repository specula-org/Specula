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

    def skill(
        self,
        folder: str,
        name: str,
        *,
        root: Path | None = None,
        name_line: str | None = None,
    ) -> Path:
        parent = root or self.source
        path = parent / folder
        path.mkdir(parents=True)
        name_line = name_line or f"name: {name}"
        (path / "SKILL.md").write_text(f"---\n{name_line}\ndescription: test\n---\n\nInstructions.\n")
        return path

    def checkout(self, folder: str) -> Path:
        checkout = self.root / folder
        (checkout / "scripts" / "infra").mkdir(parents=True)
        (checkout / "src" / "specula").mkdir(parents=True)
        (checkout / "skills").mkdir()
        (checkout / "pyproject.toml").write_text('[project]\nname = "specula"\n')
        (checkout / "README.md").write_text("# Specula: test checkout\n")
        (checkout / "scripts" / "infra" / "setup.sh").write_text('SKILLS_SOURCE="$PROJECT_ROOT/skills"\n')
        (checkout / "src" / "specula" / "__init__.py").write_text("")
        return checkout

    def legacy_checkout(self, folder: str) -> Path:
        checkout = self.root / folder
        (checkout / "scripts" / "infra").mkdir(parents=True)
        (checkout / "skills").mkdir()
        (checkout / "README.md").write_text("# Specula: legacy checkout\n")
        (checkout / "scripts" / "infra" / "setup.sh").write_text(
            'SKILLS_SOURCE="$PROJECT_ROOT/skills"\n'
            "setup_skills_symlink() {\n"
            '  ln -s "$skills_source" "$target_link"\n'
            "}\n"
        )
        return checkout

    def legacy_src_checkout(self, folder: str) -> Path:
        checkout = self.root / folder
        (checkout / "scripts" / "infra").mkdir(parents=True)
        (checkout / "src" / "skills").mkdir(parents=True)
        (checkout / "README.md").write_text("# Specula: legacy checkout\n")
        (checkout / "scripts" / "infra" / "setup.sh").write_text(
            'SKILLS_SOURCE="$PROJECT_ROOT/src/skills"\n'
            "setup_skills_root_symlink() {\n"
            '  ln -s "$skills_source" "$target_link"\n'
            "}\n"
        )
        return checkout


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

    def test_registered_names_accept_yaml_comments_and_quotes(self) -> None:
        self.skill("bare", "bare-name", name_line="name: bare-name # explanation")
        self.skill("single", "single-name", name_line="name: 'single-name' # explanation")
        self.skill("double", "double-name", name_line='name: "double-name" # explanation')

        self.assertEqual(
            [skill.name for skill in skill_install.discover_skills(self.source)],
            ["bare-name", "double-name", "single-name"],
        )

    def test_registered_name_ignores_nested_name_before_top_level_name(self) -> None:
        skill = self.skill("code_analysis", "code-analysis")
        (skill / "SKILL.md").write_text("---\nmetadata:\n  name: unrelated\nname: code-analysis\n---\n")

        self.assertEqual(skill_install.discover_skills(self.source)[0].name, "code-analysis")

    def test_existing_unclosed_frontmatter_fails_closed(self) -> None:
        self.skill("code_analysis", "code-analysis")
        invalid = self.skill("custom", "ignored", root=self.target)
        (invalid / "SKILL.md").write_text("---\nname: code-analysis\n")

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertEqual(result.conflicts, (invalid,))
        self.assertFalse((self.target / "code-analysis").exists())

    def test_existing_duplicate_top_level_name_fails_closed(self) -> None:
        self.skill("code_analysis", "code-analysis")
        invalid = self.skill("custom", "ignored", root=self.target)
        (invalid / "SKILL.md").write_text("---\nname: unrelated\nname: code-analysis\n---\n")

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertEqual(result.conflicts, (invalid,))
        self.assertFalse((self.target / "code-analysis").exists())

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

    def test_same_name_directory_conflict_still_installs_other_skills(self) -> None:
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

    def test_commented_registered_name_under_another_directory_conflicts(self) -> None:
        self.skill("code_analysis", "code-analysis")
        existing = self.skill(
            "custom-folder",
            "code-analysis",
            root=self.target,
            name_line="name: code-analysis # third-party skill",
        )

        result = skill_install.install_skills(self.source, self.target)

        self.assertEqual(result.conflicts, (existing,))
        self.assertFalse((self.target / "code-analysis").exists())

    def test_invalid_existing_skill_fails_closed_before_writing(self) -> None:
        self.skill("code_analysis", "code-analysis")
        self.skill("spec_generation", "spec-generation")
        invalid = self.skill("custom-folder", "ignored", root=self.target, name_line="name: [code-analysis]")

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertEqual(result.conflicts, (invalid,))
        self.assertEqual(result.linked, ())
        self.assertFalse((self.target / "code-analysis").exists())
        self.assertFalse((self.target / "spec-generation").exists())

    def test_duplicate_unrelated_registered_names_are_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        self.skill("spec_generation", "spec-generation")
        first = self.skill("first", "third-party", root=self.target)
        second = self.skill("second", "third-party", root=self.target)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertEqual(result.conflicts, ())
        self.assertTrue(first.is_dir())
        self.assertTrue(second.is_dir())
        self.assertTrue((self.target / "code-analysis").is_symlink())
        self.assertTrue((self.target / "spec-generation").is_symlink())

    def test_duplicate_relevant_registered_names_fail_before_writing(self) -> None:
        self.skill("code_analysis", "code-analysis")
        self.skill("spec_generation", "spec-generation")
        first = self.skill("first", "code-analysis", root=self.target)
        second = self.skill("second", "code-analysis", root=self.target)

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertEqual(result.conflicts, (first, second))
        self.assertFalse((self.target / "code-analysis").exists())
        self.assertFalse((self.target / "spec-generation").exists())

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

    def test_live_old_checkout_whole_directory_link_is_migrated(self) -> None:
        current = self.skill("code_analysis", "code-analysis")
        current_canonical = self.skill("bug-confirmation", "bug-confirmation")
        old_checkout = self.checkout("checkout-a")
        old_skill = self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        old_canonical = self.skill("bug-confirmation", "bug-confirmation", root=old_checkout / "skills")
        self.target.symlink_to(old_checkout / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertTrue(result.migrated_legacy_root)
        self.assertTrue(self.target.is_dir() and not self.target.is_symlink())
        self.assertEqual((self.target / "code-analysis").resolve(), current.resolve())
        self.assertEqual((self.target / "bug-confirmation").resolve(), current_canonical.resolve())
        self.assertTrue(old_skill.exists())
        self.assertTrue(old_canonical.exists())

    def test_modern_checkout_named_src_is_recognized(self) -> None:
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
        ):
            self.skill(folder, name)
        old_checkout = self.checkout("src")
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
        ):
            self.skill(folder, name, root=old_checkout / "skills")
        self.target.symlink_to(old_checkout / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertTrue(result.migrated_legacy_root)
        self.assertTrue((self.target / "code-analysis").is_symlink())

    def test_unrelated_project_named_specula_is_not_treated_as_owned(self) -> None:
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
        ):
            self.skill(folder, name)
        lookalike = self.root / "lookalike"
        (lookalike / "scripts" / "infra").mkdir(parents=True)
        (lookalike / "src" / "specula").mkdir(parents=True)
        (lookalike / "skills").mkdir()
        (lookalike / "pyproject.toml").write_text('[project]\nname = "specula"\n')
        (lookalike / "README.md").write_text("# A different project\n")
        (lookalike / "scripts" / "infra" / "setup.sh").write_text("#!/bin/sh\n")
        (lookalike / "src" / "specula" / "__init__.py").write_text("")
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
        ):
            self.skill(folder, name, root=lookalike / "skills")
        self.target.symlink_to(lookalike / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertFalse(result.migrated_legacy_root)
        self.assertTrue(self.target.is_symlink())

    def test_live_old_checkout_with_third_party_skill_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        third_party = self.skill("mine", "third-party", root=old_checkout / "skills")
        self.target.symlink_to(old_checkout / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertTrue(self.target.is_symlink())
        self.assertEqual((self.target / "mine").resolve(), third_party.resolve())
        self.assertIn((self.target / "mine").resolve(), {path.resolve() for path in result.conflicts})

    def test_live_old_checkout_with_duplicate_registered_name_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        first = self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        second = self.skill("duplicate", "code-analysis", root=old_checkout / "skills")
        self.target.symlink_to(old_checkout / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertTrue(self.target.is_symlink())
        self.assertEqual(
            {path.resolve() for path in result.conflicts},
            {first.resolve(), second.resolve()},
        )

    def test_725d9303_layout_whole_directory_link_is_migrated(self) -> None:
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
            ("validation-workflow", "validation-workflow"),
        ):
            self.skill(folder, name)
        old_checkout = self.legacy_checkout("checkout-725d9303")
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
            ("validation-workflow", "tla-verification-workflow"),
        ):
            self.skill(folder, name, root=old_checkout / "skills")
        self.target.symlink_to(old_checkout / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertTrue(result.migrated_legacy_root)
        self.assertFalse((old_checkout / "pyproject.toml").exists())
        self.assertTrue((self.target / "validation-workflow").is_symlink())

    def test_d3ec93db_src_layout_whole_directory_link_is_migrated(self) -> None:
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
            ("validation-workflow", "validation-workflow"),
        ):
            self.skill(folder, name)
        old_checkout = self.legacy_src_checkout("checkout-d3ec93db")
        for folder, name in (
            ("code_analysis", "code-analysis"),
            ("spec_generation", "spec-generation"),
            ("harness-generation", "harness-generation"),
            ("validation-workflow", "tla-verification-workflow"),
        ):
            self.skill(folder, name, root=old_checkout / "src" / "skills")
        self.target.symlink_to(old_checkout / "src" / "skills", target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertTrue(result.migrated_legacy_root)
        self.assertTrue((self.target / "validation-workflow").is_symlink())

    def test_broken_same_checkout_src_layout_link_is_migrated(self) -> None:
        checkout = self.root / "current-checkout"
        current_source = checkout / "skills"
        current_skill = self.skill("code_analysis", "code-analysis", root=current_source)
        target = checkout / ".claude" / "skills"
        target.parent.mkdir(parents=True)
        target.symlink_to(checkout / "src" / "skills", target_is_directory=True)

        result = skill_install.install_skills(current_source, target)

        self.assertTrue(result.complete)
        self.assertTrue(result.migrated_legacy_root)
        self.assertEqual((target / "code-analysis").resolve(), current_skill.resolve())

    def test_rerun_across_checkouts_updates_owned_skill_link(self) -> None:
        current = self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        old_skill = self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        self.target.mkdir()
        installed = self.target / "code-analysis"
        installed.symlink_to(old_skill, target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertTrue(result.complete)
        self.assertEqual(result.updated_links, (installed,))
        self.assertEqual(installed.resolve(), current.resolve())
        self.assertTrue(old_skill.exists())

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

    def test_user_managed_root_conflict_prevents_partial_install(self) -> None:
        self.skill("code_analysis", "code-analysis")
        self.skill("spec_generation", "spec-generation")
        elsewhere = self.root / "elsewhere"
        existing = self.skill("custom", "code-analysis", root=elsewhere)
        self.target.symlink_to(elsewhere, target_is_directory=True)

        result = skill_install.install_skills(self.source, self.target)

        self.assertFalse(result.complete)
        self.assertEqual(len(result.conflicts), 1)
        self.assertEqual(result.conflicts[0].resolve(), existing.resolve())
        self.assertTrue(self.target.is_symlink())
        self.assertFalse((elsewhere / "spec-generation").exists())

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

    def test_shadow_root_removes_live_old_checkout_link(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        shadow = self.root / "personal-skills"
        shadow.symlink_to(old_checkout / "skills", target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertFalse(shadow.exists() or shadow.is_symlink())
        self.assertTrue((self.target / "code-analysis").is_symlink())

    def test_shadow_whole_root_with_third_party_skill_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        third_party = self.skill("mine", "third-party", root=old_checkout / "skills")
        shadow = self.root / "personal-skills"
        shadow.symlink_to(old_checkout / "skills", target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 1)
        self.assertTrue(shadow.is_symlink())
        self.assertEqual((shadow / "mine").resolve(), third_party.resolve())
        self.assertFalse(self.target.exists())

    def test_shadow_whole_root_with_invalid_skill_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        invalid = self.skill("mine", "ignored", root=old_checkout / "skills")
        (invalid / "SKILL.md").write_text("---\nname: third-party\n")
        shadow = self.root / "personal-skills"
        shadow.symlink_to(old_checkout / "skills", target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 1)
        self.assertTrue(shadow.is_symlink())
        self.assertEqual((shadow / "mine").resolve(), invalid.resolve())
        self.assertFalse(self.target.exists())

    def test_legacy_whole_root_with_invalid_skill_is_preserved_and_fails(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        invalid = self.skill("mine", "ignored", root=old_checkout / "skills")
        (invalid / "SKILL.md").write_text("---\nname: third-party\n")
        legacy = self.root / "legacy-skills"
        legacy.symlink_to(old_checkout / "skills", target_is_directory=True)

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

        self.assertEqual(rc, 1)
        self.assertTrue(legacy.is_symlink())
        self.assertEqual((legacy / "mine").resolve(), invalid.resolve())
        self.assertFalse(self.target.exists())

    def test_legacy_whole_root_with_top_level_skill_creator_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        third_party = self.skill("skill-creator", "skill-creator", root=old_checkout / "skills")
        legacy = self.root / "legacy-skills"
        legacy.symlink_to(old_checkout / "skills", target_is_directory=True)

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

        self.assertEqual(rc, 1)
        self.assertTrue(legacy.is_symlink())
        self.assertEqual((legacy / "skill-creator").resolve(), third_party.resolve())
        self.assertFalse(self.target.exists())

    def test_shadow_root_removes_owned_old_checkout_skill_link(self) -> None:
        self.skill("code_analysis", "code-analysis")
        old_checkout = self.checkout("checkout-a")
        old_skill = self.skill("code_analysis", "code-analysis", root=old_checkout / "skills")
        shadow = self.root / "personal-skills"
        shadow.mkdir()
        old_link = shadow / "code-analysis"
        old_link.symlink_to(old_skill, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue(shadow.is_dir())
        self.assertFalse(old_link.exists() or old_link.is_symlink())

    def test_shadow_root_preserves_unrelated_duplicate_skills(self) -> None:
        self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        first = self.skill("first", "third-party", root=shadow)
        second = self.skill("second", "third-party", root=shadow)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue(first.is_dir())
        self.assertTrue(second.is_dir())
        self.assertTrue((self.target / "code-analysis").is_symlink())

    def test_target_aliasing_shadow_root_is_a_noop(self) -> None:
        source = self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        shadow.mkdir()
        installed = shadow / "code-analysis"
        installed.symlink_to(source, target_is_directory=True)
        self.target.symlink_to(shadow, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue(self.target.is_symlink())
        self.assertEqual(installed.resolve(), source.resolve())

    def test_broken_shadow_alias_to_target_becomes_valid_after_install(self) -> None:
        source = self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        shadow.symlink_to(self.target, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue(shadow.is_symlink())
        self.assertTrue(self.target.is_dir())
        self.assertEqual((shadow / "code-analysis").resolve(), source.resolve())

    def test_shadow_alias_third_party_collision_is_preserved(self) -> None:
        self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        third_party = self.skill("custom", "code-analysis", root=shadow)
        self.target.symlink_to(shadow, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 1)
        self.assertTrue(self.target.is_symlink())
        self.assertEqual((shadow / "custom").resolve(), third_party.resolve())

    def test_distinct_owned_root_links_to_same_source_are_migrated(self) -> None:
        source = self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        self.target.symlink_to(self.source, target_is_directory=True)
        shadow.symlink_to(self.source, target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 0)
        self.assertTrue(self.target.is_dir() and not self.target.is_symlink())
        self.assertEqual((self.target / "code-analysis").resolve(), source.resolve())
        self.assertFalse(shadow.exists() or shadow.is_symlink())

    def test_ambiguous_shadow_root_fails_before_installing(self) -> None:
        self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        self.skill("custom-folder", "code-analysis", root=shadow)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 1)
        self.assertFalse(self.target.exists())

    def test_broken_shadow_root_fails_before_installing(self) -> None:
        self.skill("code_analysis", "code-analysis")
        shadow = self.root / "personal-skills"
        shadow.symlink_to(self.root / "missing", target_is_directory=True)

        rc = skill_install.main(
            [
                "--source",
                str(self.source),
                "--target",
                str(self.target),
                "--shadow-root",
                str(shadow),
            ]
        )

        self.assertEqual(rc, 1)
        self.assertTrue(shadow.is_symlink())
        self.assertFalse(self.target.exists())


if __name__ == "__main__":
    unittest.main()
