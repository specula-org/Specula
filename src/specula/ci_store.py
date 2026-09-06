"""Persistent project state and immutable inputs for incremental CI runs."""

from __future__ import annotations

import difflib
import fcntl
import hashlib
import json
import os
import secrets
import stat
import subprocess
from pathlib import Path
from typing import Any

from specula import ci_init
from specula.adapters.utils.run_lock import CI_LOCK_FD_ENV
from specula.snapshotlib import SourceSnapshot, clean_git_environment


class CIError(RuntimeError):
    """A CI run cannot safely prepare or publish its inputs."""


def read_json(path: Path) -> dict[str, Any]:
    if not stat.S_ISREG(path.lstat().st_mode):
        raise CIError(f"not a regular CI record: {path}")
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CIError(f"not a CI record: {path}")
    return value


def write_json(path: Path, value: object) -> None:
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(8)}")
    with temporary.open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
    temporary.replace(path)


def git(repo: Path, *args: str, output: Path | None = None) -> str:
    command = ["git", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false", "-C", str(repo), *args]
    if output is not None:
        with output.open("xb") as stream:
            result = subprocess.run(command, env=clean_git_environment(), stdout=stream, stderr=subprocess.PIPE)
        text = ""
        error = result.stderr.decode(errors="replace")
    else:
        completed = subprocess.run(command, env=clean_git_environment(), capture_output=True, text=True)
        result = completed  # type: ignore[assignment]
        text, error = completed.stdout, completed.stderr
    if result.returncode:
        raise CIError(f"git {args[0]} failed: {error.strip()[:500]}")
    return text.strip()


def freeze_source(snapshot: SourceSnapshot, destination: Path) -> None:
    """Keep history and the exact pre-instrumentation tree, including dirty source."""
    if not snapshot.is_git:
        raise CIError("persistent CI requires a Git source repository")
    git(
        destination.parent,
        "clone",
        "--quiet",
        "--no-local",
        "--no-checkout",
        "--template=",
        str(snapshot.source),
        str(destination),
    )
    git(destination, "fetch", "--quiet", str(snapshot.baseline_git), snapshot.baseline)
    # The baseline contains raw bytes; do not apply checkout text conversions.
    (destination / ".git/info").mkdir(exist_ok=True)
    (destination / ".git/info/attributes").write_text("* -filter -ident -text !eol !working-tree-encoding\n")
    git(destination, "checkout", "--quiet", "--detach", snapshot.baseline)


def asset_hashes(root: Path) -> dict[str, str]:
    if not stat.S_ISDIR(root.lstat().st_mode):
        raise CIError(f"model assets are not a real directory: {root}")
    result: dict[str, str] = {}
    for path in root.rglob("*"):
        mode = path.lstat().st_mode
        if stat.S_ISDIR(mode):
            continue
        if not stat.S_ISREG(mode):
            raise CIError(f"unsupported persistent model asset: {path}")
        result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


class CIStore:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.fd: int | None = None

    def acquire(self, *, allow_inherited: bool = False) -> None:
        self.root.mkdir(parents=True, exist_ok=True)
        if self.root.is_symlink() or not self.root.is_dir():
            raise CIError(f"CI directory is not a real directory: {self.root}")
        inherited = os.environ.get(CI_LOCK_FD_ENV) if allow_inherited else None
        if inherited is not None:
            try:
                descriptor = int(inherited)
                info = os.fstat(descriptor)
                expected = (self.root / ".lock").lstat()
            except (ValueError, OSError) as exc:
                raise CIError("inherited CI lease is unavailable") from exc
            if (
                not stat.S_ISREG(info.st_mode)
                or not stat.S_ISREG(expected.st_mode)
                or (info.st_dev, info.st_ino) != (expected.st_dev, expected.st_ino)
            ):
                raise CIError("inherited CI lease belongs to another directory")
            self.fd = os.dup(descriptor)
            os.environ[CI_LOCK_FD_ENV] = str(self.fd)
            return
        fd = os.open(self.root / ".lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        try:
            if not stat.S_ISREG(os.fstat(fd).st_mode):
                raise CIError("CI lock is not a regular file")
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BaseException:
            os.close(fd)
            raise
        self.fd = fd
        os.environ[CI_LOCK_FD_ENV] = str(fd)
        ci_init._directory(self.root, "runs")

    def close(self) -> None:
        if self.fd is not None:
            if os.environ.get(CI_LOCK_FD_ENV) == str(self.fd):
                os.environ.pop(CI_LOCK_FD_ENV, None)
            # Native Agent descendants inherit this lease, as with the run lock.
            os.close(self.fd)
            self.fd = None

    def current_token(self) -> str | None:
        path = self.root / "current"
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError:
            return None
        if not stat.S_ISLNK(mode):
            raise CIError(f"refusing to replace a non-CI current path: {path}")
        token = os.readlink(path)
        self.path(token)
        return token

    def path(self, relative: str) -> Path:
        path = Path(relative)
        if path.is_absolute() or not path.parts or ".." in path.parts:
            raise CIError(f"unsafe CI path: {relative}")
        result = self.root
        for part in path.parts:
            result /= part
            if result.is_symlink():
                raise CIError(f"unexpected symlink in CI state: {result}")
        return result

    def current(self) -> dict[str, Any]:
        token = self.current_token()
        if token is None:
            raise CIError("CI directory has no current model; run --ci-init --ci-dir=PATH first")
        return self.snapshot(token)

    def snapshot(self, token: str) -> dict[str, Any]:
        """Load a completed model publication without assuming it is current."""
        directory = self.path(token)
        state = read_json(directory / "state.json")
        if state.get("version") != 1:
            raise CIError("unsupported CI state version")
        if asset_hashes(directory / "model") != state.get("files_sha256"):
            raise CIError(
                "current model assets changed outside CI; preserve them and reinitialize in a new CI directory"
            )
        source = self.path(state["source"])
        if git(source, "rev-parse", "HEAD") != state["snapshot_commit"] or git(source, "status", "--porcelain"):
            raise CIError("current model's saved source was modified outside CI")
        state["token"] = token
        state["model_path"] = str(directory / "model")
        return state

    def publish(self, run_dir: Path, work: Path, inputs: dict[str, Any], *, advance: bool = True) -> Path:
        if self.current_token() != inputs["previous"]:
            raise CIError("current model advanced since this run started; start a new incremental run")
        for required in ("spec/base.tla", "harness/run.sh"):
            if not ci_init._regular_file(work, required) or not (work / required).read_bytes().strip():
                raise CIError(f"cannot publish without {required}")
        # Verify the old input was not edited by the run.
        previous = self.current() if inputs["previous"] is not None else None
        destination = ci_init._directory(run_dir, f"ci-published/{secrets.token_hex(16)}")
        assets = destination / "model"
        assets.mkdir()
        files, omitted = ci_init._copy_assets(work, assets)
        for filename in ("summary.md", ".summary-findings.md", "index.md"):
            if filename in files:
                (assets / filename).unlink()
                del files[filename]
        unsafe = [p for p in omitted if Path(p).name not in ci_init._SCRATCH_DIRS]
        if unsafe:
            raise CIError(f"model contains unsupported assets: {unsafe[:5]}")
        if previous is not None:
            # Diff only model/configuration text, never TLC states or run logs.
            prior = Path(previous["model_path"])
            names = set(files) | set(previous["files_sha256"])
            with (run_dir / "model.diff").open("w") as stream:
                for name in sorted(names):
                    if Path(name).suffix not in {".tla", ".cfg"}:
                        continue
                    before = (
                        (prior / name).read_text().splitlines(keepends=True) if name in previous["files_sha256"] else []
                    )
                    after = (assets / name).read_text().splitlines(keepends=True) if name in files else []
                    stream.writelines(difflib.unified_diff(before, after, fromfile=f"a/{name}", tofile=f"b/{name}"))
        state = {
            "version": 1,
            "target": inputs["target"],
            "artifact": inputs["artifact"],
            "source": inputs["source"],
            "source_commit": inputs["source_commit"],
            "snapshot_commit": inputs["snapshot_commit"],
            "dirty": inputs["dirty"],
            "guidance": inputs["guidance"],
            "run_id": run_dir.name,
            "files_sha256": files,
            "verification": "Agent-reported workflow completion; inspect retained evidence, not a proof of safety.",
            "previous": inputs["previous"],
            "check_key": inputs.get("check_key"),
            "source_tree": inputs.get("source_tree")
            or git(self.path(inputs["source"]), "rev-parse", f"{inputs['source_commit']}^{{tree}}"),
            "checked_source_commit": inputs.get("checked_source_commit", inputs["source_commit"]),
            "evidence_run_id": inputs.get("evidence_run_id", run_dir.name),
        }
        write_json(destination / "state.json", state)
        token = destination.relative_to(self.root).as_posix()
        if not advance:
            return destination
        return self.advance(token)

    def advance(self, token: str) -> Path:
        self.path(token)
        temporary = self.root / f".current-{secrets.token_hex(8)}"
        temporary.symlink_to(token)
        temporary.replace(self.root / "current")
        return self.root / "current"
