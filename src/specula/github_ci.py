"""GitHub event adapter for the existing incremental CI workflow."""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import html
import json
import os
import re
import secrets
import shutil
import stat
import sys
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from specula import ci_init
from specula.adapters.utils.run_lock import CI_EVENT_LOCK_FD_ENV
from specula.ci_identity import check_key
from specula.ci_inheritance import candidate_for, inherit, matches_source, result_key
from specula.ci_store import CIError, CIStore, git, read_json, write_json
from specula.ci_workflow import CIPipeline
from specula.pipelinelib import Pipeline, _valid_run_id


def sha(value: object) -> str:
    if not isinstance(value, str) or re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", value) is None:
        raise CIError("event does not identify an exact Git commit")
    return value


def mapping(value: object) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


@dataclass(frozen=True)
class Event:
    repository: str
    branch: str
    kind: str
    target: str
    pr_number: int | None = None

    @classmethod
    def parse(cls, name: str, payload: dict[str, Any], environment: dict[str, str]) -> Event | None:
        repository = mapping(payload.get("repository")).get("full_name")
        if not isinstance(repository, str) or repository != environment.get("GITHUB_REPOSITORY"):
            raise CIError("event repository does not match GITHUB_REPOSITORY")
        if name in {"pull_request", "pull_request_target"}:
            pr = mapping(payload.get("pull_request"))
            head = mapping(pr.get("head"))
            if mapping(head.get("repo")).get("full_name") != repository:
                return None  # Never acquire a runner-side CI lease for an external fork.
            if payload.get("action") not in {"opened", "reopened", "synchronize", "ready_for_review"}:
                return None
            branch = mapping(pr.get("base")).get("ref")
            if not isinstance(branch, str):
                raise CIError("PR event has no target branch")
            number = payload.get("number")
            if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
                raise CIError("invalid PR number")
            return cls(repository, branch, "pr", sha(head.get("sha")), pr_number=number)
        if name == "merge_group":
            group = mapping(payload.get("merge_group"))
            ref = group.get("base_ref", "")
            if (
                payload.get("action") != "checks_requested"
                or not isinstance(ref, str)
                or not ref.startswith("refs/heads/")
            ):
                raise CIError("unsupported merge-group event")
            return cls(repository, ref[len("refs/heads/") :], "candidate", sha(group.get("head_sha")))
        if name not in {"push", "schedule", "workflow_dispatch"}:
            raise CIError(f"unsupported CI event: {name}")
        ref = payload.get("ref") if name == "push" else environment.get("GITHUB_REF")
        if not isinstance(ref, str) or not ref.startswith("refs/heads/"):
            raise CIError("CI events must select a branch, not a tag or an arbitrary ref")
        if name == "push" and payload.get("deleted"):
            return None
        target = sha(payload.get("after") if name == "push" else environment.get("GITHUB_SHA"))
        return cls(repository, ref[len("refs/heads/") :], name, target)


class GitHubCI:
    def __init__(self, ci_dir: Path, artifact: Path, reports: Path, options: list[str]) -> None:
        self.store = CIStore(ci_dir.resolve())
        self.artifact = artifact.resolve()
        self.reports = reports.resolve()
        self.options = options
        self.directory = self.store.root / ".github-ci"
        self.source = self.directory / "source"
        self.fd: int | None = None
        self.rows: list[dict[str, Any]] = []

    def validate_reports(self) -> None:
        if self.reports == self.reports.parent or self.reports.exists():
            raise CIError("--reports-dir must name a new report directory")
        for root in (self.store.root, self.artifact):
            if self.reports.is_relative_to(root) or root.is_relative_to(self.reports):
                raise CIError("report exports must be outside CI storage and source checkouts")

    @contextlib.contextmanager
    def serialized(self) -> Iterator[None]:
        # Jobs queue on the dedicated runner. This lease also protects shared
        # storage when more than one runner is configured, without canceling jobs.
        self.store.current()
        ci_init._directory(self.store.root, ".github-ci")
        fd = os.open(self.directory / "lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            os.close(fd)
            raise CIError("automation lease is not a regular file")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX)
            self.fd = fd
            os.environ[CI_EVENT_LOCK_FD_ENV] = str(fd)
            self.store.acquire()
            yield
        finally:
            self.store.close()
            self.fd = None
            os.environ.pop(CI_EVENT_LOCK_FD_ENV, None)
            os.close(fd)

    def prepare(self, event: Event) -> None:
        git(self.artifact, "check-ref-format", f"refs/heads/{event.branch}")
        state_path = self.directory / "branch.json"
        identity = {"repository": event.repository, "branch": event.branch}
        if state_path.exists():
            if read_json(state_path) != identity:
                raise CIError("this CI directory tracks another repository/branch; configure a separate directory")
        else:
            write_json(state_path, identity)
        if not self.source.exists():
            git(
                self.directory,
                "clone",
                "--quiet",
                "--no-local",
                "--template=",
                str(self.artifact),
                str(self.source),
            )
        elif self.source.is_symlink():
            raise CIError("managed source must not be a symlink")
        if git(self.source, "status", "--porcelain"):
            raise CIError("managed CI checkout was modified outside the workflow")
        git(self.source, "fetch", "--quiet", str(self.artifact), event.target)
        git(
            self.source,
            "fetch",
            "--quiet",
            str(self.artifact),
            "+refs/heads/*:refs/remotes/input/heads/*",
            "+refs/remotes/origin/*:refs/remotes/input/origin/*",
        )
        git(self.source, "checkout", "--quiet", "--detach", event.target)
        ci_init._directory(self.store.root, ".github-ci/attempts")

    @contextlib.contextmanager
    def prepared(self, event: Event) -> Iterator[None]:
        with self.serialized():
            self.prepare(event)
            try:
                yield
            finally:
                # A PR candidate must not become the default source checkout
                # used by a later manual branch update.
                with contextlib.suppress(CIError):
                    target = self._branch_tip(event.branch, self.store.current()["source_commit"])
                    git(self.source, "checkout", "--quiet", "--detach", target)

    def configuration(self, current: dict[str, Any]) -> str:
        pipeline = CIPipeline()
        if pipeline.parse_args(["--incremental", f"--ci-dir={self.store.root}", *self.options]) is not None:
            raise CIError("invalid incremental execution options")
        guidance = pipeline.guidance_text
        if guidance is None and pipeline.guidance_path is not None:
            guidance = pipeline.guidance_path.read_text(errors="replace")
        key = check_key(pipeline, current["guidance"] if guidance is None else guidance)
        if key is None:
            raise CIError("automatic CI needs an explicit model (--model or a configured model environment variable)")
        return key

    def _attempt_path(self, event: Event, commit: str, configuration: str | None) -> Path:
        # Do not automatically retry a failed task. Native resume can supply a
        # completed result; newer targets include its changes cumulatively.
        candidate = event.kind in {"pr", "candidate"}
        source_id = git(self.source, "rev-parse", f"{commit}^{{tree}}") if candidate else commit
        identity = json.dumps(
            [
                event.repository,
                event.branch,
                candidate,
                event.pr_number,
                source_id,
                self.store.current_token() if candidate else None,
                configuration,
            ]
        )
        return self.directory / "attempts" / f"{result_key(identity, '', '')}.json"

    def _invoke(self, *, candidate: bool) -> tuple[int, dict[str, Any]]:
        request = secrets.token_hex(16)
        previous = os.environ.get("SPECULA_CI_RECEIPT")
        prior_borrow = os.environ.get("SPECULA_CI_BORROW_LEASE")
        os.environ["SPECULA_CI_RECEIPT"] = request
        os.environ["SPECULA_CI_BORROW_LEASE"] = "1"
        code = 0
        try:
            Pipeline()._run_launcher(
                "launch_pipeline.sh",
                [
                    "--incremental",
                    f"--ci-dir={self.store.root}",
                    f"--artifact={self.source}",
                    *(["--ci-candidate"] if candidate else []),
                    *self.options,
                ],
            )
        except SystemExit as exc:
            code = exc.code if isinstance(exc.code, int) else 1
        finally:
            if prior_borrow is None:
                os.environ.pop("SPECULA_CI_BORROW_LEASE", None)
            else:
                os.environ["SPECULA_CI_BORROW_LEASE"] = prior_borrow
            if previous is None:
                os.environ.pop("SPECULA_CI_RECEIPT", None)
            else:
                os.environ["SPECULA_CI_RECEIPT"] = previous
        receipt = self.directory / "receipts" / f"{request}.json"
        return code, read_json(receipt) if receipt.is_file() else {}

    def check(self, event: Event, commit: str, *, candidate: bool, force: bool = False) -> int:
        current = self.store.current()
        configuration = self.configuration(current)
        attempt_path = self._attempt_path(event, commit, configuration)
        git(self.source, "checkout", "--quiet", "--detach", commit)
        # A native resume can publish a result after this event recorded a
        # failure. Reconcile validated publications before consulting attempts.
        if candidate and not force and configuration is not None:
            tree = git(self.source, "rev-parse", f"{commit}^{{tree}}")
            reused_candidate = candidate_for(self.store, current, tree, configuration)
            from_current = matches_source(self.store, current, tree, configuration)
            if from_current or reused_candidate is not None:
                evidence = current if from_current else reused_candidate
                assert evidence is not None
                result = {
                    "commit": commit,
                    "status": "reused current result" if from_current else "reused candidate result",
                    "complete": True,
                    "run_id": evidence.get("evidence_run_id", evidence["run_id"]),
                }
                write_json(attempt_path, result)
                self.rows.append(result)
                return 0
        if not candidate and not force:
            reused = inherit(self.store, self.source, commit, configuration)
            if reused is not None:
                result = {
                    "commit": commit,
                    "status": "inherited PR result" if reused["reuse_kind"] == "candidate" else "reused current result",
                    "complete": True,
                    "run_id": reused["evidence_run_id"],
                }
                write_json(attempt_path, result)
                self.rows.append(result)
                return 0
        if attempt_path.exists() and not force:
            previous = read_json(attempt_path)
            self.rows.append({**previous, "status": f"already attempted ({previous['status']})"})
            return 0 if previous.get("complete") is True else 1
        result = {"commit": commit, "status": "incomplete", "complete": False}
        write_json(attempt_path, result)
        code, receipt = self._invoke(candidate=candidate)
        result.update({"run_id": receipt.get("run_id"), "exit_code": code})
        if code == 0:
            if receipt.get("complete") is not True or receipt.get("candidate") is not candidate:
                raise CIError("incremental command did not return a completed result receipt")
            snapshot = self.store.snapshot(receipt["snapshot"])
            if snapshot["source_commit"] != commit or snapshot["check_key"] != configuration:
                raise CIError("completed result does not match this task's source/configuration")
            result.update({"status": "candidate checked" if candidate else "checked", "complete": True})
        else:
            result["status"] = "failed"
        write_json(attempt_path, result)
        self.rows.append(result)
        if code in {129, 130, 143}:
            raise CIError("CI execution was interrupted; remaining updates were not started")
        return code

    def _branch_tip(self, branch: str, fallback: str) -> str:
        for ref in (f"refs/remotes/input/origin/{branch}", f"refs/remotes/input/heads/{branch}"):
            try:
                return git(self.source, "rev-parse", "--verify", f"{ref}^{{commit}}")
            except CIError:
                continue
        return fallback

    def process(self, event: Event, *, force: bool = False, revision: str | None = None) -> int:
        with self.prepared(event):
            current = self.store.current()
            if event.kind in {"pr", "candidate"}:
                if event.kind == "pr":
                    base = self._branch_tip(event.branch, current["source_commit"])
                    git(self.source, "checkout", "--quiet", "--detach", base)
                    try:
                        git(
                            self.source,
                            "merge",
                            "--no-ff",
                            "--no-edit",
                            "-m",
                            "Specula CI merge candidate",
                            event.target,
                        )
                    except CIError:
                        with contextlib.suppress(CIError):
                            git(self.source, "merge", "--abort")
                        raise
                    target = git(self.source, "rev-parse", "HEAD")
                else:
                    target = event.target
                return self.check(event, target, candidate=True, force=force)
            target = event.target
            if event.kind in {"schedule", "workflow_dispatch"}:
                target = self._branch_tip(event.branch, event.target)
                if revision:
                    requested = git(self.source, "rev-parse", "--verify", f"{revision}^{{commit}}")
                    git(self.source, "merge-base", "--is-ancestor", requested, target)
                    target = requested
            if target != current["source_commit"]:
                try:
                    git(self.source, "merge-base", "--is-ancestor", current["source_commit"], target)
                except CIError:
                    git(self.source, "merge-base", "--is-ancestor", target, current["source_commit"])
                    if revision or force:
                        raise CIError(
                            "requested revision is older than the current model; cannot move it backward"
                        ) from None
                    self.rows.append(
                        {
                            "commit": target,
                            "status": f"included in cumulative update to {current['source_commit']}; no separate check for this event",
                            "complete": False,
                            "run_id": current["evidence_run_id"],
                        }
                    )
                    return 0
            # The incremental runner diffs from the last successful snapshot to
            # this target, including all intervening net changes in one run.
            return self.check(event, target, candidate=False, force=force)

    def report(self, error: str | None = None) -> None:
        self.reports.mkdir(parents=True, exist_ok=False)
        lines = ["# Specula CI", "", "| Source commit | Result | Specula run |", "|---|---|---|"]
        for row in self.rows:
            lines.append(
                f"| {html.escape(str(row['commit']))} | {html.escape(str(row['status']))} | {html.escape(str(row.get('run_id') or '-'))} |"
            )
            run_id = row.get("run_id")
            if not isinstance(run_id, str) or not _valid_run_id(run_id):
                continue
            run = self.store.path(f"runs/{run_id}")
            try:
                target = read_json(run / "ci-input.json")["target"].split("|", 1)[0].strip()
            except (OSError, ValueError, CIError):
                continue
            work = run / target / ".specula-output"
            destination = self.reports / run_id
            destination.mkdir(exist_ok=True)
            for relative in (
                "ci-report.md",
                "summary.md",
                "confirmed-bugs.md",
                "spec/changelog.md",
                "spec/bug-report.md",
            ):
                if ci_init._regular_file(work, relative):
                    path = destination / relative
                    path.parent.mkdir(exist_ok=True)
                    shutil.copy2(work / relative, path)
            for filename in ("source.diff", "model.diff"):
                if ci_init._regular_file(run, filename):
                    shutil.copy2(run / filename, destination / filename)
        if error:
            lines += ["", f"Error: {html.escape(error)}"]
        lines += [
            "",
            "Each update checks the cumulative diff to its target, not every intermediate version separately.",
            "Reused/inherited rows launch no additional Agent; their usage summaries belong to the original run.",
            "Reports describe actual coverage; completion is not a proof of safety.",
            "",
        ]
        content = "\n".join(lines)
        (self.reports / "summary.md").write_text(content)
        summary = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary:
            with Path(summary).open("a") as stream:
                stream.write(content)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="specula ci", description="Handle a GitHub event using the incremental CI workflow"
    )
    parser.add_argument("--ci-dir", required=True, type=Path)
    parser.add_argument("--artifact", required=True, type=Path)
    parser.add_argument("--reports-dir", required=True, type=Path)
    parser.add_argument("--event-name", default=os.environ.get("GITHUB_EVENT_NAME"))
    parser.add_argument("--event-path", type=Path, default=os.environ.get("GITHUB_EVENT_PATH"))
    parser.add_argument("--force", action="store_true", help="Explicitly rerun a manual task")
    parser.add_argument("--branch", help="Target branch for scheduled or manual checks")
    parser.add_argument("--revision", help="Specific revision on the branch for a manual dispatch")
    args, options = parser.parse_known_args(argv)
    runner = GitHubCI(args.ci_dir, args.artifact, args.reports_dir, options)
    error: str | None = None
    code = 1
    report_safe = False
    try:
        runner.validate_reports()
        report_safe = True
        if not args.event_name or args.event_path is None:
            raise CIError("GITHUB_EVENT_NAME and GITHUB_EVENT_PATH are required")
        payload = read_json(args.event_path)
        event = Event.parse(args.event_name, payload, dict(os.environ))
        if args.branch and event is not None:
            if args.event_name not in {"schedule", "workflow_dispatch"} and args.branch != event.branch:
                raise CIError("configured branch does not match the source event")
            event = Event(event.repository, args.branch, event.kind, event.target, pr_number=event.pr_number)
        if args.force and args.event_name != "workflow_dispatch":
            raise CIError("--force is only available for an explicit manual dispatch")
        if args.revision and (args.event_name != "workflow_dispatch" or args.revision.startswith("-")):
            raise CIError("--revision requires a manual dispatch and a valid Git revision")
        if event is None:
            print("Event skipped: no authorized source update to execute")
            runner.rows.append(
                {"commit": "-", "status": "skipped (external fork or irrelevant event)", "complete": False}
            )
            code = 0
        else:
            code = runner.process(event, force=args.force, revision=args.revision)
    except (OSError, ValueError, CIError, ci_init.CIInitError) as exc:
        error = str(exc)
        print(f"ERROR: {error}", file=sys.stderr)
    finally:
        try:
            if report_safe:
                runner.report(error)
        except (OSError, ValueError, CIError) as exc:
            print(f"ERROR: could not publish CI report: {exc}", file=sys.stderr)
            code = 1
    return code


if __name__ == "__main__":
    raise SystemExit(main())
