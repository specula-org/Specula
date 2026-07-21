"""Full-tree source snapshots for ``specula run --keep-original``.

Copy the working tree once, rebuild private Git metadata without repository
hooks or config, then record every non-``.git`` byte in a separate baseline.
Git ignore and index state do not decide what is included in the final diff.
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
_SOURCE_MAP_VERSION = 3
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
        "GIT_OBJECT_DIRECTORY",
        "GIT_PREFIX",
        "GIT_QUARANTINE_PATH",
        "GIT_SHALLOW_FILE",
        "GIT_WORK_TREE",
    }
)
_GIT_CONFIG_INJECTION_ENV = frozenset({"GIT_CONFIG", "GIT_CONFIG_COUNT", "GIT_CONFIG_PARAMETERS"})


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
        if (
            key in _GIT_REPOSITORY_ENV
            or key in _GIT_CONFIG_INJECTION_ENV
            or key.startswith("GIT_CONFIG_KEY_")
            or key.startswith("GIT_CONFIG_VALUE_")
        ):
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
            if entry.name == ".git":
                if path.parent != root or not stat.S_ISDIR(mode):
                    raise SnapshotError(
                        f"--keep-original does not support linked worktrees, submodules, or nested repositories: {path}"
                    )
                # Root Git metadata is rebuilt rather than copied.  Do not
                # inspect repository-owned hooks, config, or object links.
                continue
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


def _copy_working_tree(original: Path, destination: Path, *, is_git: bool) -> None:
    """Copy source bytes while leaving root Git metadata to the clean clone."""

    def ignore(directory: str, _names: list[str]) -> set[str]:
        return {".git"} if is_git and Path(directory) == original else set()

    shutil.copytree(
        original,
        destination,
        symlinks=True,
        copy_function=shutil.copy2,
        ignore=ignore,
        dirs_exist_ok=destination.exists(),
    )
    _make_tree_owner_accessible(destination, skip_root_git=is_git)


def _make_tree_owner_accessible(root: Path, *, skip_root_git: bool = False) -> None:
    """Make a copied tree usable by its new owner without following symlinks."""
    pending = [root]
    while pending:
        path = pending.pop()
        mode = path.stat(follow_symlinks=False).st_mode
        if stat.S_ISDIR(mode):
            required = stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR
        elif stat.S_ISREG(mode):
            required = stat.S_IRUSR | stat.S_IWUSR
            if stat.S_IMODE(mode) & 0o111:
                required |= stat.S_IXUSR
        else:
            continue
        os.chmod(path, stat.S_IMODE(mode) | required, follow_symlinks=False)
        if stat.S_ISDIR(mode):
            with os.scandir(path) as entries:
                pending.extend(
                    Path(entry.path)
                    for entry in entries
                    if not entry.is_symlink() and not (skip_root_git and path == root and entry.name == ".git")
                )


def _git_bool(repo: Path, key: str) -> bool:
    value = _git(["-C", str(repo), "config", "--type=bool", "--default=false", "--get", key])
    return value == "true"


def _git_refs(repo: Path, namespace: str) -> list[tuple[str, str, str | None]]:
    output = _git(["-C", str(repo), "for-each-ref", "--format=%(objectname) %(refname) %(symref)", namespace])
    refs: list[tuple[str, str, str | None]] = []
    for line in output.splitlines():
        fields = line.split()
        if len(fields) not in (2, 3):
            raise SnapshotError(f"cannot parse Git ref in {repo}: {line!r}")
        refs.append((fields[1], fields[0], fields[2] if len(fields) == 3 else None))
    return refs


def _restore_refs(original: Path, destination: Path, namespace: str, *, clear: bool = False) -> None:
    if clear:
        for ref_name, _object_name, _symbolic_target in _git_refs(destination, namespace):
            _git(["-C", str(destination), "update-ref", "--no-deref", "-d", ref_name])
    refs = _git_refs(original, namespace)
    for ref_name, object_name, symbolic_target in refs:
        if symbolic_target is None:
            _git(["-C", str(destination), "update-ref", "--no-deref", ref_name, object_name])
    for ref_name, _object_name, symbolic_target in refs:
        if symbolic_target is not None:
            _git(["-C", str(destination), "symbolic-ref", ref_name, symbolic_target])


def _restore_sparse_checkout(original: Path, destination: Path) -> None:
    if not _git_bool(original, "core.sparseCheckout"):
        return
    patterns = original / ".git" / "info" / "sparse-checkout"
    if patterns.is_symlink() or not patterns.is_file():
        raise SnapshotError(f"Git sparse-checkout patterns are unsafe: {original}")
    private_patterns = destination / ".git" / "info" / "sparse-checkout"
    private_patterns.parent.mkdir(exist_ok=True)
    shutil.copyfile(patterns, private_patterns)
    _git(["-C", str(destination), "config", "--local", "extensions.worktreeConfig", "true"])
    for key in ("core.sparseCheckout", "core.sparseCheckoutCone", "index.sparse"):
        value = "true" if _git_bool(original, key) else "false"
        _git(["-C", str(destination), "config", "--worktree", key, value])


def _create_private_git(original: Path, destination: Path) -> None:
    """Clone history without copying executable or externally linked metadata."""
    _git(
        [
            "clone",
            "--quiet",
            "--local",
            "--no-hardlinks",
            "--no-checkout",
            "--template=",
            "--",
            str(original),
            str(destination),
        ]
    )
    _restore_refs(original, destination, "refs/heads/")
    _restore_refs(original, destination, "refs/remotes/", clear=True)
    # A local clone records the source path as origin.  The private checkout
    # must not retain an active path back to the original repository.
    _git(["-C", str(destination), "config", "--local", "--remove-section", "remote.origin"])
    original_index = original / ".git" / "index"
    if original_index.exists() or original_index.is_symlink():
        if original_index.is_symlink() or not original_index.is_file():
            raise SnapshotError(f"Git index is unsafe: {original}")
        shutil.copyfile(original_index, destination / ".git" / "index")
        for shared_index in (original / ".git").glob("sharedindex.*"):
            if shared_index.is_symlink() or not shared_index.is_file():
                raise SnapshotError(f"Git shared index is unsafe: {original}")
            shutil.copyfile(shared_index, destination / ".git" / shared_index.name)
    else:
        # --no-checkout has no index.  Resetting avoids staged deletions and
        # also succeeds for an unborn repository.
        _git(["-C", str(destination), "reset", "--mixed", "--quiet"])
    _restore_sparse_checkout(original, destination)


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
        raise SnapshotError(f"private Git directory points outside the source: {source}")

    common_raw = Path(_git(["-C", str(root), "rev-parse", "--git-common-dir"], env=repo_env))
    common_dir = (root / common_raw).resolve() if not common_raw.is_absolute() else common_raw.resolve()
    if common_dir != expected_git_dir:
        raise SnapshotError(f"private Git common directory points outside the source: {source}")

    top = Path(_git(["-C", str(root), "rev-parse", "--show-toplevel"], env=repo_env)).resolve()
    if top != root:
        raise SnapshotError(f"private Git work tree points outside the source: {source}")

    for alternates_name in ("alternates", "http-alternates"):
        alternates = git_dir / "objects" / "info" / alternates_name
        if alternates.exists() or alternates.is_symlink():
            raise SnapshotError(f"--keep-original does not support Git object alternates: {source}")
    if any((git_dir / "objects" / "pack").glob("*.promisor")):
        raise SnapshotError(f"--keep-original does not support partial Git clones: {source}")


def _target_paths(run_dir: Path, name: str) -> tuple[Path, Path, Path]:
    if not name or Path(name).name != name or name in {".", "..", SOURCE_MAP}:
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
        "version": _SOURCE_MAP_VERSION,
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
    targets = (
        document.get("targets")
        if isinstance(document, dict) and document.get("version") == _SOURCE_MAP_VERSION
        else None
    )
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
        _make_tree_owner_accessible(path, skip_root_git=True)
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
            if is_git:
                top = Path(_git(["-C", str(original), "rev-parse", "--show-toplevel"])).resolve()
                if top != original:
                    raise SnapshotError(f"Git work tree does not match snapshot source: {original}")
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
                if is_git:
                    _create_private_git(original, source_stage)
                _copy_working_tree(original, source_stage, is_git=is_git)
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
