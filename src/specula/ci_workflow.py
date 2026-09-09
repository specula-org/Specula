"""CI CLI scaffolding; the incremental skill owns the verification workflow."""

from __future__ import annotations

import contextlib
import os
import re
import shlex
import stat
import sys
from pathlib import Path
from typing import Any

from specula import ci_init, ci_verdict, resumelib
from specula.ci_identity import check_key
from specula.ci_inheritance import register_candidate
from specula.ci_store import CIError, CIStore, freeze_source, git, read_json, write_json
from specula.output_index import BYOM_REPORT_FILENAME
from specula.pipelinelib import Pipeline, _valid_run_id
from specula.snapshotlib import load_sources


class CIPipeline(Pipeline):
    def __init__(self) -> None:
        super().__init__()
        self.incremental = False
        self.ci_dir: Path | None = None
        self.revision: str | None = None
        self.store: CIStore | None = None
        self.inputs: dict[str, Any] | None = None
        self.candidate = False
        self._candidate_given = False
        self.receipt: Path | None = None

    def parse_args(self, argv: list[str]) -> int | None:
        ordinary: list[str] = []
        for arg in argv:
            if arg == "--incremental":
                self.incremental = True
            elif arg == "--ci-candidate":
                self.candidate = self._candidate_given = True
            elif arg.startswith("--ci-dir="):
                raw = arg.split("=", 1)[1]
                if not raw or self.ci_dir is not None:
                    print("ERROR: specify --ci-dir=PATH exactly once", file=sys.stderr)
                    return 1
                self.ci_dir = Path(raw).expanduser().absolute()
                if self.ci_dir.is_symlink():
                    print("ERROR: --ci-dir must not be a symlink", file=sys.stderr)
                    return 1
                self.ci_dir = self.ci_dir.resolve()
            elif arg.startswith("--revision="):
                self.revision = arg.split("=", 1)[1]
                if not self.revision or self.revision.startswith("-"):
                    print("ERROR: --revision requires a Git revision", file=sys.stderr)
                    return 1
            else:
                ordinary.append(arg)
        rc = super().parse_args(ordinary)
        if rc is not None:
            return rc
        self.argv = list(argv)
        if self.ci_dir is None:
            print("ERROR: --incremental requires --ci-dir=PATH", file=sys.stderr)
            return 1
        if self.candidate and (self.ci_init or not (self.incremental or self._run_id_given)):
            print("ERROR: --ci-candidate requires an incremental run", file=sys.stderr)
            return 1
        if (self.ci_init and self.incremental) or not (self.ci_init or self.incremental or self._run_id_given):
            print("ERROR: choose --ci-init, --incremental, or --run-id with --ci-dir", file=sys.stderr)
            return 1
        if not self.isolate or len(self.targets) != 1:
            print("ERROR: persistent CI requires one target and isolated output", file=sys.stderr)
            return 1
        if any(arg.startswith("--skip-") for arg in argv) or self._enable_reviews_given:
            print("ERROR: CI runs the complete workflow; skip and review flags are not supported", file=sys.stderr)
            return 1
        if self.fresh_context:
            print("ERROR: resume the original conversation, or omit --run-id to start a new CI run", file=sys.stderr)
            return 1
        if self.incremental:
            if (self._policy_retries_given and self.policy_retries) or (
                self._transient_resumes_given and self.transient_resumes
            ):
                print("ERROR: incremental CI does not retry failed Agent calls automatically", file=sys.stderr)
                return 1
            self.policy_retries = self.transient_resumes = 0
            self.skip_classification = True  # Findings live in the single Agent's ci-report.md.
        self.keep_original = True
        self._isolate_explicit = True
        self.store = CIStore(self.ci_dir)
        return None

    def _byom_option_error(self) -> str | None:
        error = super()._byom_option_error()
        if error is None and self.byom_path is not None and self.incremental:
            return "--byom cannot be used with --incremental; initialize a new CI directory with --ci-init"
        return error

    def run_storage_root(self) -> Path:
        assert self.ci_dir is not None
        return self.ci_dir / "runs"

    def should_confirm_without_guidance_before_resolve(self) -> bool:
        return False  # CI reuses its persisted user guidance when none is supplied.

    def _resume_configuration_document(self) -> dict[str, Any]:
        return {
            **super()._resume_configuration_document(),
            "ci_directory": str(self.ci_dir),
            "incremental": self.incremental,
            "revision": self.revision,
            "candidate": self.candidate,
        }

    def _restore_resume_configuration(self, raw: dict[str, Any], *, allow_overrides: bool = False) -> None:
        if raw.get("ci_directory") != str(self.ci_dir):
            raise resumelib.ResumeError("CI directory differs from the original conversation")
        mode = raw.get("incremental")
        if not isinstance(mode, bool) or (self.incremental and not mode):
            raise resumelib.ResumeError("CI run mode differs from the original conversation")
        if self.revision is not None and self.revision != raw.get("revision"):
            raise resumelib.ResumeError("target revision cannot change on resume; start a new run")
        self.incremental = mode
        candidate = raw.get("candidate", False)
        if not isinstance(candidate, bool) or (self._candidate_given and not candidate):
            raise resumelib.ResumeError("candidate publication mode cannot change on resume")
        self.candidate = candidate
        self.revision = raw.get("revision")
        super()._restore_resume_configuration(raw, allow_overrides=allow_overrides)
        if self.ci_init == self.incremental:
            raise resumelib.ResumeError("invalid stored CI run mode; expected initialization or incremental checking")
        if self.incremental:
            self.skip_classification = True

    def _position_at_manual_resume_phase(self, active: list[dict[str, Any]] | None = None) -> None:
        if self.incremental:
            if self._manual_resume_phase != "incremental":
                raise resumelib.ResumeError("expected the original incremental Agent conversation")
            return
        super()._position_at_manual_resume_phase(active)

    def _require_resume_run(self) -> None:
        if not self._run_id_given:
            return
        assert self.store is not None
        if not _valid_run_id(self.run_id):
            raise CIError(f"invalid --run-id '{self.run_id}' (allowed: [A-Za-z0-9._-]+)")
        run_dir = self.store.path(f"runs/{self.run_id}")
        try:
            mode = run_dir.lstat().st_mode
        except FileNotFoundError as exc:
            raise CIError(
                f"CI run '{self.run_id}' does not exist; cannot resume. Omit --run-id to start a new run."
            ) from exc
        if not stat.S_ISDIR(mode):
            raise CIError(f"CI run '{self.run_id}' is not a real run directory; cannot resume")

    def resolve_run_dir(self, *, acquire_lock: bool = False) -> int | None:
        assert self.store is not None
        try:
            # A CI --run-id only resumes: reject typos before creating storage.
            self._require_resume_run()
            self.store.acquire(allow_inherited=os.environ.get("SPECULA_CI_BORROW_LEASE") == "1")
            # Recheck under the project lease before the ordinary resolver,
            # whose non-CI semantics also allow naming a new run.
            self._require_resume_run()
            attaching = self._run_id_given
            if self.incremental and not attaching:
                current = self.store.current()
                if self._targets_given and self.targets != [current["target"]]:
                    raise CIError("CI directory belongs to another target")
                self.targets = [current["target"]]
                if not self._artifact_given:
                    self.artifact = current["artifact"]
                if not self._guidance_given:
                    self.guidance_text = current["guidance"]
            elif self.ci_init and not attaching and self.store.current_token() is not None:
                raise CIError("CI directory is already initialized; use --incremental or choose a new directory")
            rc = super().resolve_run_dir(acquire_lock=acquire_lock)
            if rc is not None:
                self.store.close()
            elif not self.dry_run:
                request = os.environ.get("SPECULA_CI_RECEIPT")
                if request:
                    if re.fullmatch(r"[0-9a-f]{32}", request) is None:
                        raise CIError("invalid CI receipt identity")
                    directory = ci_init._directory(self.store.root, ".github-ci/receipts")
                    self.receipt = directory / f"{request}.json"
                    write_json(self.receipt, {"run_id": self.run_id, "complete": False})
            return rc
        except BlockingIOError:
            print("ERROR: another run is using this CI directory; retry after it finishes", file=sys.stderr)
        except (OSError, ValueError, CIError, ci_init.CIInitError) as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
        self._release_run_lock()
        return 1

    def _release_run_lock(self) -> None:
        super()._release_run_lock()
        if self.store is not None:
            self.store.close()

    def prepare_source_snapshots(self, names: list[str]) -> None:
        super().prepare_source_snapshots(names)
        if self.dry_run:
            return
        assert self.run_dir is not None and self.store is not None and self.ci_dir is not None
        record = self.run_dir / "ci-input.json"
        if record.exists():
            self.inputs = read_json(record)
            if self.store.current_token() != self.inputs["previous"]:
                raise CIError("current model advanced since this run started; start a new incremental run")
            return
        name = names[0]
        snapshot = load_sources(self.run_dir)[name]
        source_commit = git(snapshot.source, "rev-parse", "HEAD")
        if (
            self.revision is not None
            and git(snapshot.source, "rev-parse", f"{self.revision}^{{commit}}") != source_commit
        ):
            raise CIError("--artifact is not checked out at --revision; check out the intended commit first")
        dirty = bool(git(snapshot.source, "status", "--porcelain", "--untracked-files=normal"))
        source = self.run_dir / "ci-source"
        freeze_source(snapshot, source)
        previous = self.store.current_token()
        inputs: dict[str, Any] = {
            "version": 1,
            "target": self.targets[0],
            "artifact": str(snapshot.original),
            "source": source.relative_to(self.ci_dir).as_posix(),
            "source_commit": source_commit,
            "snapshot_commit": snapshot.baseline,
            "dirty": dirty,
            "guidance": self.guidance_text or "",
            "previous": previous,
        }
        if self.ci_init:
            assert self._ci_init_inputs is not None
            inputs["guidance"] = (self._ci_init_inputs / "user-guidance.md").read_text()
        else:
            current = self.store.current()
            old_source = self.store.path(current["source"])
            git(source, "merge-base", "--is-ancestor", current["source_commit"], source_commit)
            git(source, "fetch", "--quiet", str(old_source), current["snapshot_commit"])
            git(
                source,
                "diff",
                "--binary",
                "--no-ext-diff",
                "--no-textconv",
                current["snapshot_commit"],
                snapshot.baseline,
                "--",
                output=self.run_dir / "source.diff",
            )
            inputs["old_source"] = str(old_source)
            inputs["old_model"] = current["model_path"]
            work = ci_init.prepare_output_directory(self.run_dir, name)
            ci_init._copy_assets(Path(current["model_path"]), work)
            # Prior run summaries remain available in old_model; they are not
            # this run's findings, completion evidence, or resource history.
            for filename in (
                "summary.md",
                ".summary-findings.md",
                "ci-report.md",
                ci_verdict.FILENAME,
                BYOM_REPORT_FILENAME,
            ):
                (work / filename).unlink(missing_ok=True)
        write_json(record, inputs)
        self.inputs = inputs

    def _max_parallel_summary(self) -> str:
        return "1 workflow Agent" if self.incremental else super()._max_parallel_summary()

    def _summary_validation_limits(self) -> tuple[str, ...]:
        if self.incremental:
            return ()
        return super()._summary_validation_limits()

    def main(self) -> int:
        if not self.incremental:
            return super().main()
        self.validate_agent_adapter()
        names = self.extract_names()
        self.prepare_source_snapshots(names)
        if self._attached_existing_run and self.guidance_path is None and self.inputs is not None:
            self.guidance_text = self.inputs["guidance"]
        self.stage_guidance(names)
        self.initialize_resource_summaries(names)
        print(f"CI directory: {self.ci_dir}\nRun: {self.run_id}\nSource update: {self.run_dir}/source.diff")
        with self.resource_phase("incremental", names):
            self._phase("INCREMENTAL WORKFLOW", "launch_incremental.sh", self._phase_args(names))
        return 0

    def finalize_ci_run(self, exit_code: int) -> tuple[str | None, int]:
        if self.dry_run:
            return None, exit_code
        resume = f"specula run --ci-dir={shlex.quote(str(self.ci_dir))} --run-id={self.run_id}"
        if exit_code:
            if self.run_dir is not None and resumelib.active_entries(self.run_dir):
                return f"Current CI model unchanged. To resume the conversation: {resume}", exit_code
            return (
                "Current CI model unchanged. No unfinished conversation is available; fix the error and start a new run.",
                exit_code,
            )
        if self.inputs is None or self.store is None or self.run_dir is None:
            raise CIError("no frozen CI inputs; current model unchanged")
        source = self.store.path(self.inputs["source"])
        if git(source, "rev-parse", "HEAD") != self.inputs["snapshot_commit"] or git(source, "status", "--porcelain"):
            raise CIError("pre-instrumentation source was modified during the run")
        name = self.extract_names()[0]
        work = Path(self.get_work_dir(name))
        verdict = (
            ci_verdict.read(work, self.run_id, previous=Path(self.inputs["old_model"]))
            if self.incremental
            else ci_verdict.from_confirmation(work, self.run_id)
        )
        publication = dict(self.inputs)
        publication["verdict"] = verdict
        if self.incremental and self.guidance_text is not None:
            publication["guidance"] = self.guidance_text
        publication["check_key"] = check_key(self, publication["guidance"])
        current = self.store.publish(self.run_dir, work, publication, advance=False)
        token = current.relative_to(self.store.root).as_posix()
        result = {
            "run_id": self.run_id,
            "complete": True,
            "verdict": verdict,
            "candidate": self.candidate,
            "snapshot": token,
        }
        write_json(self.run_dir / "ci-result.json", result)
        if self.receipt is not None:
            write_json(self.receipt, result)
        if not self.candidate:
            current = self.store.advance(token)
        else:
            register_candidate(self.store, token)
        if self.resource_summary is not None:
            with contextlib.suppress(OSError, ValueError):
                self.resource_summary.complete_run([name])
        label = "CI candidate saved; current model unchanged" if self.candidate else "Current CI model updated"
        return (
            f"CI verdict: {verdict}\n{label}: {current}/model\nResults and usage: {work}/summary.md",
            ci_verdict.exit_code(verdict),
        )
