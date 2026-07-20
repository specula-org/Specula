"""Full-tree source snapshots for ``specula run --keep-original``.

The implementation is deliberately small: copy the source once, record every
non-``.git`` byte in a private Git object database, then diff that baseline
against the final copied tree.  Git ignore and index state do not decide what
is included.
"""

from __future__ import annotations

import contextlib
import json
import os
import shutil
import stat
import subprocess
import tempfile
from collections.abc import Mapping, MutableMapping, Sequence
from dataclasses import dataclass
from pathlib import Path

SOURCE_MAP = "source-map.json"
SNAPSHOT_MODE_ENV = "SPECULA_SOURCE_SNAPSHOT"
_BASELINE_REF = "refs/specula/baseline"
_PATHSPEC = (
    ".",
    ":(exclude).git",
    ":(exclude,glob).git/**",
    ":(exclude,glob)**/.git",
    ":(exclude,glob)**/.git/**",
)
_RAW_ATTRIBUTES = "* !diff -filter -ident -text !eol !working-tree-encoding\n"

# Repository-local variables reported by ``git rev-parse --local-env-vars``,
# plus the discovery/config selectors that can make a child Git process ignore
# its private cwd.  Keep authentication, identity, editor, and tracing variables
# intact for agents; those do not select another repository.
_GIT_REPOSITORY_ENV = frozenset(
    {
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CEILING_DIRECTORIES",
        "GIT_COMMON_DIR",
        "GIT_DIR",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM",
        "GIT_EXTERNAL_DIFF",
        "GIT_GRAFT_FILE",
        "GIT_IMPLICIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_NAMESPACE",
        "GIT_NO_REPLACE_OBJECTS",
        "GIT_OBJECT_DIRECTORY",
        "GIT_PREFIX",
        "GIT_QUARANTINE_PATH",
        "GIT_REPLACE_REF_BASE",
        "GIT_SHALLOW_FILE",
        "GIT_WORK_TREE",
    }
)


class SnapshotError(RuntimeError):
    """A private source snapshot could not be created or compared."""


@dataclass(frozen=True)
class SourceSnapshot:
    original: Path
    source: Path
    baseline_git: Path
    baseline: str
    patch: Path
    is_git: bool


def sanitize_snapshot_git_environment(env: MutableMapping[str, str], *, ceiling: str | None = None) -> None:
    """Remove ambient selectors that can rebind Git outside a private source."""
    for key in tuple(env):
        if key in _GIT_REPOSITORY_ENV or key == "GIT_CONFIG" or key.startswith("GIT_CONFIG_"):
            env.pop(key, None)
    if ceiling is not None:
        env["GIT_CEILING_DIRECTORIES"] = ceiling


def clean_git_environment(extra: Mapping[str, str] | None = None) -> dict[str, str]:
    """Return a deterministic environment for Specula-owned local Git calls."""
    env = os.environ.copy()
    for key in list(env):
        if key.startswith("GIT_"):
            env.pop(key)
    env.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_ATTR_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_AUTHOR_NAME": "Specula",
            "GIT_AUTHOR_EMAIL": "specula@localhost",
            "GIT_COMMITTER_NAME": "Specula",
            "GIT_COMMITTER_EMAIL": "specula@localhost",
        }
    )
    if extra:
        env.update(extra)
    return env


def _git_env(extra: Mapping[str, str] | None = None) -> dict[str, str]:
    return clean_git_environment(extra)


def _git(args: Sequence[str], *, cwd: Path | None = None, env: Mapping[str, str] | None = None) -> str:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=cwd,
            env=_git_env(env),
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise SnapshotError("Git is required for --keep-original") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "Git command failed").strip()
        raise SnapshotError(f"git {' '.join(args[:3])} failed: {detail[:500]}") from exc
    return result.stdout.strip()


def _controller_env(control: Path, source: Path, index: Path) -> dict[str, str]:
    return {
        "GIT_DIR": str(control),
        "GIT_WORK_TREE": str(source),
        "GIT_INDEX_FILE": str(index),
    }


def _validate_source_tree(source: Path) -> None:
    """Reject entries that copytree cannot isolate safely or predictably."""
    root = source.resolve()
    pending = [root]
    while pending:
        directory = pending.pop()
        try:
            entries = list(os.scandir(directory))
        except OSError as exc:
            raise SnapshotError(f"cannot read source directory {directory}: {exc}") from exc
        for entry in entries:
            path = Path(entry.path)
            try:
                mode = entry.stat(follow_symlinks=False).st_mode
            except OSError as exc:
                raise SnapshotError(f"cannot inspect source path {path}: {exc}") from exc
            if entry.name == ".git" and (path.parent != root or not stat.S_ISDIR(mode)):
                raise SnapshotError(
                    f"--keep-original does not support linked worktrees, submodules, or nested repositories: {path}"
                )
            if path.parent == root and entry.name == ".gitmodules":
                raise SnapshotError(f"--keep-original does not support submodules: {path}")
            if stat.S_ISLNK(mode):
                try:
                    raw_target = os.readlink(path)
                    target = path.resolve(strict=False)
                except (OSError, RuntimeError) as exc:
                    raise SnapshotError(f"cannot resolve source symlink {path}: {exc}") from exc
                if os.path.isabs(raw_target) or not target.is_relative_to(root):
                    raise SnapshotError(f"--keep-original does not copy symlinks outside the source tree: {path}")
            elif stat.S_ISDIR(mode):
                pending.append(path)
            elif not stat.S_ISREG(mode):
                raise SnapshotError(f"--keep-original does not support special source files: {path}")


def _create_baseline(control: Path, source: Path, index: Path) -> str:
    _git(["init", "--quiet", "--bare", "--template=", str(control)])
    (control / "info").mkdir(exist_ok=True)
    (control / "info" / "attributes").write_text(_RAW_ATTRIBUTES)
    env = _controller_env(control, source, index)
    try:
        _git(["read-tree", "--empty"], cwd=source, env=env)
        _git(["add", "--all", "--force", "--", *_PATHSPEC], cwd=source, env=env)
        tree = _git(["write-tree"], cwd=source, env=env)
        baseline = _git(["commit-tree", tree, "-m", "Specula source baseline"], cwd=source, env=env)
        _git(["update-ref", _BASELINE_REF, baseline], cwd=source, env=env)
        return baseline
    finally:
        index.unlink(missing_ok=True)
        index.with_name(index.name + ".lock").unlink(missing_ok=True)


def _git_config_entries(config: Path) -> list[tuple[str, str]]:
    output = _git(["config", "--file", str(config), "--no-includes", "--null", "--list"])
    entries: list[tuple[str, str]] = []
    for record in output.split("\0"):
        if record:
            key, _, value = record.partition("\n")
            entries.append((key.casefold(), value))
    return entries


def _validate_private_path(root: Path, raw: str, label: str, source: Path) -> None:
    path = Path(raw)
    resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
    if not resolved.is_relative_to(root):
        raise SnapshotError(f"copied Git {label} points outside the private source: {source}")


def _is_automatic_command_config(key: str) -> bool:
    """Whether a local Git operation can automatically launch this command."""
    if key == "diff.external":
        return True
    fields = key.split(".")
    if len(fields) < 3:
        return False
    section, variable = fields[0], fields[-1]
    return (
        (section == "filter" and variable in {"clean", "smudge", "process"})
        or (section == "diff" and variable in {"command", "textconv"})
        or (section == "merge" and variable == "driver")
    )


def _validate_private_git(source: Path, expected_git: bool) -> None:
    has_git = (source / ".git").is_dir()
    if has_git != expected_git:
        raise SnapshotError(f"private source Git type changed: {source}")
    if not has_git:
        return
    root = source.resolve()
    expected_git_dir = (root / ".git").resolve()
    repo_env = {"GIT_CEILING_DIRECTORIES": str(root.parent)}
    git_dir = Path(_git(["-C", str(root), "rev-parse", "--absolute-git-dir"], env=repo_env)).resolve()
    if git_dir != expected_git_dir:
        raise SnapshotError(f"copied Git directory points outside the private source: {source}")

    common_raw = Path(_git(["-C", str(root), "rev-parse", "--git-common-dir"], env=repo_env))
    common_dir = (root / common_raw).resolve() if not common_raw.is_absolute() else common_raw.resolve()
    if common_dir != expected_git_dir:
        raise SnapshotError(f"copied Git common directory points outside the private source: {source}")

    top = Path(_git(["-C", str(root), "rev-parse", "--show-toplevel"], env=repo_env)).resolve()
    if top != root:
        raise SnapshotError(f"copied Git work tree points outside the private source: {source}")

    worktree_output = _git(["-C", str(root), "worktree", "list", "--porcelain", "-z"], env=repo_env)
    worktrees = [
        Path(field.removeprefix("worktree ")).resolve()
        for field in worktree_output.split("\0")
        if field.startswith("worktree ")
    ]
    confirmation_root = root.parent / ".specula-output" / "confirmation"

    def run_local_confirmation_worktree(path: Path) -> bool:
        try:
            relative = path.relative_to(confirmation_root)
        except ValueError:
            return False
        return len(relative.parts) == 2 and relative.parts[1] == "worktree"

    if (
        worktrees.count(root) != 1
        or len(worktrees) != len(set(worktrees))
        or any(path != root and not run_local_confirmation_worktree(path) for path in worktrees)
    ):
        raise SnapshotError(f"--keep-original does not support registered linked worktrees: {source}")

    for config in (git_dir / "config", git_dir / "config.worktree"):
        if not config.is_file():
            continue
        entries = _git_config_entries(config)
        if any(key == "include.path" or (key.startswith("includeif.") and key.endswith(".path")) for key, _ in entries):
            raise SnapshotError(f"copied Git config includes are not supported: {source}")
        command_keys = [key for key, _ in entries if _is_automatic_command_config(key)]
        if command_keys:
            raise SnapshotError(f"copied Git automatic command config is not supported ({command_keys[0]}): {source}")
        hook_values = [value for key, value in entries if key == "core.hookspath"]
        if any("\n" in value for value in hook_values):
            raise SnapshotError(f"copied Git hooks path is invalid: {source}")
        if hook_values:
            hooks_output = _git(
                ["config", "--file", str(config), "--no-includes", "--path", "--get-all", "core.hooksPath"]
            )
            for hooks_value in hooks_output.splitlines():
                _validate_private_path(root, hooks_value, "hooks path", source)
        if any(key == "core.fsmonitor" for key, _ in entries):
            try:
                _git(
                    [
                        "config",
                        "--file",
                        str(config),
                        "--no-includes",
                        "--type=bool",
                        "--get-all",
                        "core.fsmonitor",
                    ]
                )
            except SnapshotError as exc:
                raise SnapshotError(f"copied Git fsmonitor must be boolean: {source}") from exc

    hooks_raw = Path(_git(["-C", str(root), "rev-parse", "--git-path", "hooks"], env=repo_env))
    hooks = (root / hooks_raw).resolve() if not hooks_raw.is_absolute() else hooks_raw.resolve()
    if not hooks.is_relative_to(root):
        raise SnapshotError(f"copied Git hooks path points outside the private source: {source}")


def _target_paths(run_dir: Path, name: str) -> tuple[Path, Path, Path]:
    if not name or Path(name).name != name or name in {".", ".."}:
        raise SnapshotError(f"invalid snapshot target name: {name!r}")
    target = run_dir / name
    if os.pathsep in os.fspath(target):
        raise SnapshotError(
            f"private source path contains the environment path-list separator {os.pathsep!r}: {target}"
        )
    return target / "source", target / "baseline.git", target / "changes.patch"


def validate_snapshot_destinations(run_dir: Path, names: Sequence[str]) -> None:
    """Validate private snapshot destinations without creating any files."""
    run_root = run_dir.resolve()
    for name in names:
        _target_paths(run_root, name)


def _snapshot_document(snapshots: Mapping[str, SourceSnapshot]) -> dict[str, object]:
    return {
        "version": 2,
        "targets": {
            name: {"original": str(item.original), "baseline": item.baseline, "is_git": item.is_git}
            for name, item in snapshots.items()
        },
    }


def _write_map(path: Path, document: Mapping[str, object]) -> None:
    fd, temporary = tempfile.mkstemp(prefix=".source-map.", suffix=".tmp", dir=path.parent)
    tmp = Path(temporary)
    try:
        with os.fdopen(fd, "w") as handle:
            json.dump(document, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        tmp.replace(path)
    finally:
        tmp.unlink(missing_ok=True)


def load_sources(run_dir: Path) -> dict[str, SourceSnapshot]:
    run_root = run_dir.resolve()
    map_path = run_root / SOURCE_MAP
    if map_path.is_symlink() or not map_path.is_file():
        raise SnapshotError(f"private source map is missing or unsafe: {map_path}")
    try:
        document = json.loads(map_path.read_text())
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise SnapshotError(f"cannot read private source map {map_path}: {exc}") from exc
    targets = document.get("targets") if isinstance(document, dict) and document.get("version") == 2 else None
    if not isinstance(targets, dict):
        raise SnapshotError(f"invalid private source map: {map_path}")
    snapshots: dict[str, SourceSnapshot] = {}
    for name, raw in targets.items():
        if not isinstance(name, str) or not isinstance(raw, dict):
            raise SnapshotError(f"invalid private source map: {map_path}")
        original_raw = raw.get("original")
        baseline = raw.get("baseline")
        is_git = raw.get("is_git")
        if (
            not isinstance(original_raw, str)
            or not Path(original_raw).is_absolute()
            or not isinstance(baseline, str)
            or not isinstance(is_git, bool)
        ):
            raise SnapshotError(f"invalid private source map entry: {name!r}")
        source, control, patch = _target_paths(run_root, name)
        if (
            source.is_symlink()
            or not source.is_dir()
            or source.resolve() != source
            or control.is_symlink()
            or not control.is_dir()
            or control.resolve() != control
        ):
            raise SnapshotError(f"private source for {name!r} is incomplete")
        resolved_baseline = _git(["--git-dir", str(control), "rev-parse", "--verify", f"{_BASELINE_REF}^{{commit}}"])
        if resolved_baseline != baseline:
            raise SnapshotError(f"private source baseline for {name!r} does not match its map")
        _validate_source_tree(source)
        _validate_private_git(source, is_git)
        snapshots[name] = SourceSnapshot(
            original=Path(original_raw).resolve(),
            source=source,
            baseline_git=control,
            baseline=baseline,
            patch=patch,
            is_git=is_git,
        )
    return snapshots


def _remove_snapshot_path(path: Path) -> None:
    if path.is_symlink() or (path.exists() and not path.is_dir()):
        path.unlink(missing_ok=True)
    elif path.is_dir():
        shutil.rmtree(path)


def prepare_sources(run_dir: Path, sources: Mapping[str, Path]) -> dict[str, SourceSnapshot]:
    """Copy each full source tree and record a raw-byte baseline."""
    run_root = run_dir.resolve()
    map_path = run_root / SOURCE_MAP
    if map_path.exists() or map_path.is_symlink():
        snapshots = load_sources(run_root)
        expected = {name: source.resolve() for name, source in sources.items()}
        actual = {name: item.original for name, item in snapshots.items()}
        if actual != expected:
            raise SnapshotError("snapshot sources do not match this run")
        return snapshots

    # Validate every destination before copying the first source.  In addition
    # to making failure transactional, this protects both the sandbox write
    # allowlist and Git's ceiling list, neither of which has a path escaping
    # mechanism for ``os.pathsep``.
    target_paths = {name: _target_paths(run_root, name) for name in sources}
    prepared: dict[str, SourceSnapshot] = {}
    attempted: list[tuple[Path, Path, Path, Path]] = []
    created_targets: list[Path] = []
    map_attempted = False
    try:
        for name, raw_source in sources.items():
            original = raw_source.resolve()
            source, control, patch = target_paths[name]
            target = source.parent
            if not original.is_dir():
                raise SnapshotError(f"source is not a directory: {original}")
            if run_root == original or run_root.is_relative_to(original) or original.is_relative_to(run_root):
                raise SnapshotError(f"run directory and source must not overlap: {original}")
            _validate_source_tree(original)
            is_git = (original / ".git").is_dir()
            target_existed = target.exists() or target.is_symlink()
            target.mkdir(parents=True, exist_ok=True)
            if not target_existed:
                created_targets.append(target)
            if target.is_symlink() or target.resolve() != target:
                raise SnapshotError(f"unsafe snapshot target directory: {target}")

            if source.exists() or source.is_symlink() or control.exists() or control.is_symlink():
                raise SnapshotError(f"private source exists without {SOURCE_MAP}; refusing to reuse it")
            source_stage = target / ".source.incomplete"
            control_stage = target / ".baseline.git.incomplete"
            _remove_snapshot_path(source_stage)
            _remove_snapshot_path(control_stage)
            attempted.append((source, control, source_stage, control_stage))
            try:
                shutil.copytree(original, source_stage, symlinks=True, copy_function=shutil.copy2)
                source_stage.replace(source)
                _validate_source_tree(source)
                _validate_private_git(source, is_git)
                index = target / ".baseline-index"
                baseline = _create_baseline(control_stage, source, index)
                control_stage.replace(control)
            finally:
                _remove_snapshot_path(source_stage)
                _remove_snapshot_path(control_stage)
            prepared[name] = SourceSnapshot(original, source, control, baseline, patch, is_git)

        map_attempted = True
        _write_map(map_path, _snapshot_document(prepared))
        return load_sources(run_root)
    except BaseException:
        if map_attempted:
            map_path.unlink(missing_ok=True)
        for paths in reversed(attempted):
            for path in paths:
                _remove_snapshot_path(path)
        for target in reversed(created_targets):
            with contextlib.suppress(OSError):
                target.rmdir()
        raise


def capture_changes(run_dir: Path) -> dict[str, bool]:
    """Write a complete binary Git-format filesystem diff for every source."""
    changed: dict[str, bool] = {}
    for name, item in load_sources(run_dir).items():
        index = item.patch.parent / ".changes-index"
        env = _controller_env(item.baseline_git, item.source, index)
        fd, temporary = tempfile.mkstemp(prefix=".changes.", suffix=".patch", dir=item.patch.parent)
        tmp = Path(temporary)
        try:
            with os.fdopen(fd, "wb") as output:
                _git(["read-tree", item.baseline], cwd=item.source, env=env)
                _git(["add", "--all", "--force", "--", *_PATHSPEC], cwd=item.source, env=env)
                subprocess.run(
                    [
                        "git",
                        "diff",
                        "--cached",
                        "--binary",
                        "--full-index",
                        "--no-ext-diff",
                        "--no-textconv",
                        item.baseline,
                        "--",
                    ],
                    cwd=item.source,
                    env=_git_env(env),
                    check=True,
                    stdout=output,
                    stderr=subprocess.PIPE,
                )
                output.flush()
                os.fsync(output.fileno())
            tmp.replace(item.patch)
            changed[name] = item.patch.stat().st_size > 0
        except (OSError, subprocess.CalledProcessError) as exc:
            raise SnapshotError(f"cannot capture source changes for {name!r}: {exc}") from exc
        finally:
            tmp.unlink(missing_ok=True)
            index.unlink(missing_ok=True)
            index.with_name(index.name + ".lock").unlink(missing_ok=True)
    return changed
