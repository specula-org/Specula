"""Install Specula skills alongside an agent's existing skills."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class SkillSource:
    """A skill's registered name and source directory."""

    name: str
    path: Path


@dataclass(frozen=True)
class InstallResult:
    """Summary of one skills-directory installation."""

    linked: tuple[str, ...]
    existing: tuple[str, ...]
    conflicts: tuple[Path, ...]
    migrated_legacy_root: bool = False
    migrated_links: tuple[tuple[Path, Path], ...] = ()
    updated_links: tuple[Path, ...] = ()

    @property
    def complete(self) -> bool:
        return not self.conflicts


@dataclass(frozen=True)
class ShadowCleanupPlan:
    """Safe removals needed to keep a local install from being shadowed."""

    root: Path
    removals: tuple[Path, ...]
    conflicts: tuple[Path, ...]

    @property
    def complete(self) -> bool:
        return not self.conflicts


def _same_path(path: Path, expected: Path) -> bool:
    """Whether *path* resolves to *expected*, without requiring either path."""

    try:
        return path.resolve(strict=False) == expected.resolve(strict=False)
    except (OSError, RuntimeError):
        return False


def _same_directory_entry(path: Path, expected: Path) -> bool:
    """Whether two paths name the same entry without following the final symlink."""

    try:
        return path.parent.resolve(strict=False) / path.name == expected.parent.resolve(strict=False) / expected.name
    except (OSError, RuntimeError):
        return False


_SKILL_NAME = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
_KNOWN_LEGACY_SKILL_NAMES = {"tla-verification-workflow"}
_HISTORICAL_CORE_SKILL_NAMES = {
    "bug-confirmation",
    "bug-recording",
    "code-analysis",
    "harness-generation",
    "spec-generation",
    "tla-checking-workflow",
    "tla-trace-workflow",
    "tla-verification-workflow",
    "validation-workflow",
}


def _yaml_name_scalar(value: str, skill_file: Path) -> str:
    """Parse the small YAML scalar subset allowed by skill names."""

    value = value.lstrip()
    if not value:
        raise ValueError(f"empty skill name in: {skill_file}")

    if value.startswith('"'):
        try:
            name, end = json.JSONDecoder().raw_decode(value)
        except (json.JSONDecodeError, TypeError) as exc:
            raise ValueError(f"invalid quoted skill name in: {skill_file}") from exc
        if not isinstance(name, str):
            raise ValueError(f"invalid skill name {name!r} in: {skill_file}")
        remainder = value[end:]
    elif value.startswith("'"):
        characters: list[str] = []
        position = 1
        while position < len(value):
            if value[position] != "'":
                characters.append(value[position])
                position += 1
                continue
            if position + 1 < len(value) and value[position + 1] == "'":
                characters.append("'")
                position += 2
                continue
            position += 1
            break
        else:
            raise ValueError(f"invalid quoted skill name in: {skill_file}")
        name = "".join(characters)
        remainder = value[position:]
    else:
        comment = re.search(r"\s+#", value)
        if comment:
            name = value[: comment.start()].rstrip()
            remainder = value[comment.start() :]
        else:
            name = value.rstrip()
            remainder = ""

    if remainder.strip() and re.fullmatch(r"\s+#.*", remainder) is None:
        raise ValueError(f"invalid trailing content in skill name in: {skill_file}")
    if not _SKILL_NAME.fullmatch(name):
        raise ValueError(f"invalid skill name {name!r} in: {skill_file}")
    return name


def _registered_name(skill_file: Path) -> str:
    lines = skill_file.read_text().splitlines()
    if not lines or lines[0].strip() != "---":
        raise ValueError(f"SKILL.md is missing YAML frontmatter: {skill_file}")
    names: list[str] = []
    closed = False
    for line in lines[1:]:
        if line.strip() == "---":
            closed = True
            break
        if not line or line[0].isspace():
            continue
        key, separator, value = line.partition(":")
        if separator and key.strip() == "name":
            names.append(_yaml_name_scalar(value, skill_file))
    if not closed:
        raise ValueError(f"SKILL.md has unclosed YAML frontmatter: {skill_file}")
    if not names:
        raise ValueError(f"SKILL.md frontmatter has no top-level name: {skill_file}")
    if len(names) != 1:
        raise ValueError(f"SKILL.md frontmatter has duplicate top-level name keys: {skill_file}")
    return names[0]


def discover_skills(source: Path) -> list[SkillSource]:
    """Return installable skill directories in deterministic order."""

    source = source.resolve()
    if not source.is_dir():
        raise ValueError(f"skills source is not a directory: {source}")
    skills = [
        SkillSource(_registered_name(entry / "SKILL.md"), entry)
        for entry in source.iterdir()
        if entry.is_dir() and (entry / "SKILL.md").is_file()
    ]
    skills.sort(key=lambda skill: skill.name)
    if not skills:
        raise ValueError(f"no skill directories containing SKILL.md found under: {source}")
    names = [skill.name for skill in skills]
    duplicates = sorted(name for name in set(names) if names.count(name) > 1)
    if duplicates:
        raise ValueError(f"duplicate registered skill name(s): {', '.join(duplicates)}")
    return skills


def _installed_skills(target: Path) -> tuple[dict[str, list[Path]], list[Path]]:
    installed: dict[str, list[Path]] = {}
    invalid: list[Path] = []
    for entry in sorted(target.iterdir(), key=lambda path: path.name):
        skill_file = entry / "SKILL.md"
        if not entry.is_dir() or not skill_file.is_file():
            continue
        try:
            name = _registered_name(skill_file)
        except (OSError, ValueError):
            invalid.append(entry)
            continue
        installed.setdefault(name, []).append(entry)
    return installed, invalid


def _duplicate_skill_paths(
    installed: dict[str, list[Path]],
    relevant_names: set[str] | None = None,
) -> list[Path]:
    return [
        entry
        for name, entries in installed.items()
        if len(entries) > 1 and (relevant_names is None or name in relevant_names)
        for entry in entries
    ]


def _is_specula_skills_root(path: Path) -> bool:
    """Conservatively identify a live ``skills`` directory in a Specula checkout."""

    try:
        resolved = path.resolve(strict=True)
    except (OSError, RuntimeError):
        return False
    if resolved.name != "skills":
        return False

    modern_root = resolved.parent
    try:
        project = (modern_root / "pyproject.toml").read_text()
        modern_readme = (modern_root / "README.md").read_text().splitlines()
        modern_setup = (modern_root / "scripts" / "infra" / "setup.sh").read_text()
    except OSError:
        project = ""
        modern_readme = []
        modern_setup = ""
    project_section = re.search(r"(?ms)^\[project\]\s*$\n(.*?)(?=^\[|\Z)", project)
    modern_layout = (
        project_section is not None
        and re.search(r"""(?m)^\s*name\s*=\s*["']specula["']\s*$""", project_section.group(1)) is not None
        and bool(modern_readme)
        and modern_readme[0].startswith("# Specula:")
        and 'SKILLS_SOURCE="$PROJECT_ROOT/skills"' in modern_setup
        and (modern_root / "src" / "specula" / "__init__.py").is_file()
    )
    if modern_layout:
        return True

    try:
        installed, _invalid = _installed_skills(resolved)
    except OSError:
        return False
    core_names = set(installed) & _HISTORICAL_CORE_SKILL_NAMES
    if len(core_names) < 3:
        return False

    legacy_candidates = [(resolved.parent, "skills")]
    if resolved.parent.name == "src":
        legacy_candidates.append((resolved.parent.parent, "src/skills"))
    for project_root, source_suffix in legacy_candidates:
        try:
            readme_lines = (project_root / "README.md").read_text().splitlines()
            setup = (project_root / "scripts" / "infra" / "setup.sh").read_text()
        except OSError:
            continue
        has_legacy_identity = bool(readme_lines) and readme_lines[0].startswith("# Specula:")
        has_legacy_installer = f'SKILLS_SOURCE="$PROJECT_ROOT/{source_suffix}"' in setup and (
            "setup_skills_symlink" in setup
            or "setup_skills_root_symlink" in setup
            or re.search(r"(?m)^\s*ln\s+-s\b", setup) is not None
        )
        if has_legacy_identity and has_legacy_installer:
            return True
    return False


def _owned_legacy_root(source: Path, root: Path) -> bool:
    resolved_source = source.resolve(strict=False)
    historical_source = resolved_source.parent / "src" / "skills" if resolved_source.name == "skills" else None
    return root.is_symlink() and (
        _same_path(root, resolved_source)
        or (historical_source is not None and _same_path(root, historical_source))
        or _is_specula_skills_root(root)
    )


def _legacy_inventory_conflicts(source: Path, root: Path) -> tuple[Path, ...]:
    """Return entries that make removal of an owned whole-root link unsafe."""

    if not root.exists():
        return ()
    skills = discover_skills(source)
    installed, invalid = _installed_skills(root)
    conflicts = [*invalid, *_duplicate_skill_paths(installed)]
    allowed_names = {skill.name for skill in skills} | _KNOWN_LEGACY_SKILL_NAMES
    for name, entries in installed.items():
        if name not in allowed_names:
            conflicts.extend(entries)
    return tuple(dict.fromkeys(conflicts))


def remove_legacy_root(source: Path, legacy_root: Path) -> bool:
    """Remove an old whole-directory link only when Specula owns it."""

    if _owned_legacy_root(source, legacy_root) and not _legacy_inventory_conflicts(source, legacy_root):
        legacy_root.unlink()
        return True
    return False


def _owned_skill_link(path: Path, skill: SkillSource) -> bool:
    if not path.is_symlink():
        return False
    if _same_path(path, skill.path):
        return True
    try:
        resolved = path.resolve(strict=True)
        return _is_specula_skills_root(resolved.parent) and _registered_name(resolved / "SKILL.md") == skill.name
    except (OSError, RuntimeError, ValueError):
        return False


def plan_shadow_cleanup(source: Path, root: Path) -> ShadowCleanupPlan:
    """Plan removal of Specula skills that would shadow a local install.

    User-managed skills are never removed. An unreadable or ambiguous entry
    that could share a Specula name is reported as a conflict instead.
    """

    source = source.resolve()
    skills = {skill.name: skill for skill in discover_skills(source)}
    if not root.exists() and not root.is_symlink():
        return ShadowCleanupPlan(root, (), ())
    if _owned_legacy_root(source, root):
        conflicts = _legacy_inventory_conflicts(source, root)
        if conflicts:
            return ShadowCleanupPlan(root, (), conflicts)
        return ShadowCleanupPlan(root, (root,), ())
    if root.is_symlink() and not root.is_dir():
        return ShadowCleanupPlan(root, (), (root,))
    if not root.is_dir():
        return ShadowCleanupPlan(root, (), ())

    installed, invalid = _installed_skills(root)
    removals: list[Path] = []
    conflicts_list = [*invalid, *_duplicate_skill_paths(installed, set(skills))]
    for name, skill in skills.items():
        for entry in installed.get(name, []):
            if _owned_skill_link(entry, skill):
                removals.append(entry)
            else:
                conflicts_list.append(entry)
    if conflicts_list:
        removals = []
    return ShadowCleanupPlan(root, tuple(removals), tuple(dict.fromkeys(conflicts_list)))


def plan_legacy_cleanup(source: Path, root: Path) -> ShadowCleanupPlan:
    """Plan safe cleanup of an obsolete whole-root installation location."""

    if not root.exists() and not root.is_symlink():
        return ShadowCleanupPlan(root, (), ())
    if _owned_legacy_root(source, root):
        conflicts = _legacy_inventory_conflicts(source, root)
        if conflicts:
            return ShadowCleanupPlan(root, (), conflicts)
        return ShadowCleanupPlan(root, (root,), ())
    if root.is_symlink() and not root.exists():
        return ShadowCleanupPlan(root, (), (root,))
    return ShadowCleanupPlan(root, (), ())


def apply_shadow_cleanup(plan: ShadowCleanupPlan) -> None:
    """Apply a conflict-free shadow cleanup plan."""

    if not plan.complete:
        raise ValueError(f"shadow cleanup has unresolved conflicts under: {plan.root}")
    for path in plan.removals:
        path.unlink()


def install_skills(source: Path, target: Path) -> InstallResult:
    """Merge per-skill links into *target* without replacing user content.

    A legacy whole-directory link created by earlier Specula setup versions is
    migrated when it points at any identifiable live Specula checkout. A
    user-managed root symlink to a directory is merged through without replacing
    the link. Broken roots and per-skill collisions are preserved and reported
    as incomplete. Installation is preflighted before writing any skill link.
    """

    source = source.resolve()
    skills = discover_skills(source)
    migrated = False
    external_root = False

    if target.is_symlink():
        if _owned_legacy_root(source, target):
            unsafe_entries = _legacy_inventory_conflicts(source, target)
            if unsafe_entries:
                return InstallResult((), (), unsafe_entries)
            migrated = True
        elif not target.is_dir():
            return InstallResult((), (), (target,))
        else:
            external_root = True
    elif target.exists():
        if not target.is_dir():
            return InstallResult((), (), (target,))
    else:
        target.mkdir(parents=True)

    linked: list[str] = []
    existing: list[str] = []
    migrating_names: list[str] = []
    conflicts: list[Path] = []
    migrated_links: list[tuple[Path, Path]] = []
    migration_plans: list[tuple[SkillSource, Path, Path]] = []
    update_plans: list[tuple[SkillSource, Path]] = []
    root_exists = target.exists() and not migrated
    installed: dict[str, list[Path]] = {}
    if root_exists:
        installed, invalid = _installed_skills(target)
        ambiguous = [*invalid, *_duplicate_skill_paths(installed, {skill.name for skill in skills})]
        if ambiguous:
            return InstallResult((), (), tuple(dict.fromkeys(ambiguous)))
    for skill in skills:
        if not root_exists:
            linked.append(skill.name)
            continue
        destination = target / skill.name
        registered = installed.get(skill.name, [])
        if registered:
            current = registered[0]
            if not _owned_skill_link(current, skill):
                conflicts.append(current)
                continue
            if current == destination:
                if _same_path(current, skill.path):
                    existing.append(skill.name)
                else:
                    migrating_names.append(skill.name)
                    update_plans.append((skill, current))
                continue
            if current.is_symlink() and not destination.exists() and not destination.is_symlink():
                migrating_names.append(skill.name)
                migrated_links.append((current, destination))
                migration_plans.append((skill, current, destination))
            elif current.is_symlink() and (destination.exists() or destination.is_symlink()):
                conflicts.append(destination)
            else:
                conflicts.append(current)
            continue
        if destination.is_symlink():
            if _same_path(destination, skill.path):
                existing.append(skill.name)
            else:
                conflicts.append(destination)
            continue
        if destination.exists():
            conflicts.append(destination)
            continue
        linked.append(skill.name)

    if conflicts and external_root:
        return InstallResult((), tuple(existing), tuple(dict.fromkeys(conflicts)))

    if migrated:
        target.unlink()
        target.mkdir(parents=True)
    elif not target.exists():
        target.mkdir(parents=True)
    for skill, current, destination in migration_plans:
        destination.symlink_to(skill.path, target_is_directory=True)
        current.unlink()
    for skill, current in update_plans:
        current.unlink()
        current.symlink_to(skill.path, target_is_directory=True)
    for name in linked:
        skill = next(skill for skill in skills if skill.name == name)
        (target / name).symlink_to(skill.path, target_is_directory=True)
    existing = sorted([*existing, *migrating_names])

    return InstallResult(
        tuple(linked),
        tuple(existing),
        tuple(conflicts),
        migrated_legacy_root=migrated,
        migrated_links=tuple(migrated_links),
        updated_links=tuple(path for _skill, path in update_plans),
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--target", required=True, type=Path)
    parser.add_argument("--legacy-root", action="append", default=[], type=Path)
    parser.add_argument("--shadow-root", action="append", default=[], type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        shadow_plans = [plan_shadow_cleanup(args.source, root) for root in args.shadow_root]
        legacy_plans = [plan_legacy_cleanup(args.source, root) for root in args.legacy_root]
        target_is_owned_root = _owned_legacy_root(args.source, args.target)
        alias_conflicts = [
            plan.root
            for plan in shadow_plans
            if _same_directory_entry(args.target, plan.root)
            or (_same_path(args.target, plan.root) and not target_is_owned_root)
        ]
        cleanup_conflicts = list(
            dict.fromkeys(
                [
                    *alias_conflicts,
                    *(path for plan in [*shadow_plans, *legacy_plans] for path in plan.conflicts),
                ]
            )
        )
        if cleanup_conflicts:
            for path in cleanup_conflicts:
                print(f"CONFLICT: preserving unsafe skill path: {path}", file=sys.stderr)
            print(
                "ERROR: Specula skill installation incomplete; "
                f"resolve {len(cleanup_conflicts)} cleanup conflict(s) and rerun setup.",
                file=sys.stderr,
            )
            return 1
        result = install_skills(args.source, args.target)
    except (OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if result.migrated_legacy_root:
        print(f"Migrated legacy Specula skills symlink: {args.target}")
    for previous, current in result.migrated_links:
        print(f"Migrated Specula skill link: {previous} -> {current}")
    for path in result.updated_links:
        print(f"Updated Specula skill link: {path}")
    for name in result.linked:
        print(f"Linked Specula skill: {args.target / name}")
    for name in result.existing:
        print(f"Specula skill already configured: {args.target / name}")
    for path in result.conflicts:
        print(f"CONFLICT: preserving existing path: {path}", file=sys.stderr)

    if not result.complete:
        print(
            f"ERROR: Specula skill installation incomplete; resolve {len(result.conflicts)} conflict(s) and rerun setup.",
            file=sys.stderr,
        )
        return 1
    try:
        for plan in shadow_plans:
            apply_shadow_cleanup(plan)
            for path in plan.removals:
                print(f"Removed shadowing Specula skill path: {path}")
        for plan in legacy_plans:
            apply_shadow_cleanup(plan)
            for path in plan.removals:
                print(f"Removed legacy Specula skills symlink: {path}")
    except (OSError, ValueError) as exc:
        print(f"ERROR: could not remove shadowing Specula skill: {exc}", file=sys.stderr)
        return 1
    for legacy_root, plan in zip(args.legacy_root, legacy_plans, strict=True):
        if not plan.removals and (legacy_root.exists() or legacy_root.is_symlink()):
            print(f"Preserving unrelated legacy path: {legacy_root}")
    print(f"Specula skills installed: {len(result.linked) + len(result.existing)} in {args.target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
