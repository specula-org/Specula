"""Install Specula skills alongside an agent's existing skills."""

from __future__ import annotations

import argparse
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

    @property
    def complete(self) -> bool:
        return not self.conflicts


def _same_path(path: Path, expected: Path) -> bool:
    """Whether *path* resolves to *expected*, without requiring either path."""

    try:
        return path.resolve(strict=False) == expected.resolve(strict=False)
    except (OSError, RuntimeError):
        return False


_SKILL_NAME = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")


def _registered_name(skill_file: Path) -> str:
    lines = skill_file.read_text().splitlines()
    if not lines or lines[0].strip() != "---":
        raise ValueError(f"SKILL.md is missing YAML frontmatter: {skill_file}")
    for line in lines[1:]:
        if line.strip() == "---":
            break
        key, separator, value = line.partition(":")
        if separator and key.strip() == "name":
            name = value.strip().strip("\"'")
            if not _SKILL_NAME.fullmatch(name):
                raise ValueError(f"invalid skill name {name!r} in: {skill_file}")
            return name
    raise ValueError(f"SKILL.md frontmatter has no name: {skill_file}")


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


def _installed_skills(target: Path) -> dict[str, list[Path]]:
    installed: dict[str, list[Path]] = {}
    for entry in target.iterdir():
        skill_file = entry / "SKILL.md"
        if not entry.is_dir() or not skill_file.is_file():
            continue
        try:
            name = _registered_name(skill_file)
        except (OSError, ValueError):
            continue
        installed.setdefault(name, []).append(entry)
    return installed


def remove_legacy_root(source: Path, legacy_root: Path) -> bool:
    """Remove an old whole-directory link only when Specula owns it."""

    if legacy_root.is_symlink() and _same_path(legacy_root, source):
        legacy_root.unlink()
        return True
    return False


def install_skills(source: Path, target: Path) -> InstallResult:
    """Merge per-skill links into *target* without replacing user content.

    A legacy whole-directory link created by earlier Specula setup versions is
    migrated when it points at the current source. A user-managed root symlink
    to a directory is merged through without replacing the link. Broken roots
    and per-skill collisions are preserved and reported as incomplete.
    """

    source = source.resolve()
    skills = discover_skills(source)
    migrated = False

    if target.is_symlink():
        if _same_path(target, source):
            target.unlink()
            target.mkdir(parents=True)
            migrated = True
        elif not target.is_dir():
            return InstallResult((), (), (target,))
    elif target.exists():
        if not target.is_dir():
            return InstallResult((), (), (target,))
    else:
        target.mkdir(parents=True)

    linked: list[str] = []
    existing: list[str] = []
    conflicts: list[Path] = []
    migrated_links: list[tuple[Path, Path]] = []
    installed = _installed_skills(target)
    for skill in skills:
        destination = target / skill.name
        registered = installed.get(skill.name, [])
        if registered:
            if len(registered) != 1 or not _same_path(registered[0], skill.path):
                conflicts.extend(registered)
                continue
            current = registered[0]
            if current == destination:
                existing.append(skill.name)
                continue
            if current.is_symlink() and not destination.exists() and not destination.is_symlink():
                destination.symlink_to(skill.path, target_is_directory=True)
                current.unlink()
                existing.append(skill.name)
                migrated_links.append((current, destination))
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
        destination.symlink_to(skill.path, target_is_directory=True)
        linked.append(skill.name)

    return InstallResult(
        tuple(linked),
        tuple(existing),
        tuple(conflicts),
        migrated_legacy_root=migrated,
        migrated_links=tuple(migrated_links),
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--target", required=True, type=Path)
    parser.add_argument("--legacy-root", action="append", default=[], type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        result = install_skills(args.source, args.target)
    except (OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if result.migrated_legacy_root:
        print(f"Migrated legacy Specula skills symlink: {args.target}")
    for previous, current in result.migrated_links:
        print(f"Migrated Specula skill link: {previous} -> {current}")
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
    for legacy_root in args.legacy_root:
        if remove_legacy_root(args.source, legacy_root):
            print(f"Removed legacy Specula skills symlink: {legacy_root}")
        elif legacy_root.exists() or legacy_root.is_symlink():
            print(f"Preserving unrelated legacy path: {legacy_root}")
    print(f"Specula skills installed: {len(result.linked) + len(result.existing)} in {args.target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
