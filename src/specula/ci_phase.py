"""One native Agent conversation for the entire incremental skill."""

from __future__ import annotations

import shlex
from pathlib import Path

from specula import ci_init, ci_result, ci_verdict, stop_gate
from specula.ci_store import CIError, read_json
from specula.phaselib import AgentFiles, Phase, Workspace, _last_message_path
from specula.prompts import render
from specula.skill_refs import prompt_skill_ids


class IncrementalPhase(Phase):
    key = "incremental"
    title = "Specula — Incremental CI"

    @staticmethod
    def _rate_limit_retries() -> int:
        return 0

    def check(self, ws: Workspace, names: list[str]) -> bool:
        return ws.run_dir is not None and (ws.run_dir / "ci-input.json").is_file()

    def agent_files(self, ws: Workspace, name: str) -> AgentFiles:
        work = ws.work_dir(name)
        return {
            "log": work / "incremental.log",
            "pid": work / "incremental.pid",
            "prompt": work / ".incremental-prompt.md",
            "mkdirs": [work],
        }

    def build_prompt(self, ws: Workspace, target: str) -> str:
        assert ws.run_dir is not None
        inputs = read_json(ws.run_dir / "ci-input.json")
        if ci_result.enabled(inputs):
            final_reporting = (
                f"Write only `{ws.work_dir(target) / ci_result.FILENAME}` using the final-result reference in the skill. "
                f"Use run ID `{ws.run_dir.name}`. Run `specula ci-result --work={shlex.quote(str(ws.work_dir(target)))}` "
                "before finishing; fix reported errors in that file. This generates the reports, verdict, and persistent "
                "records. Do not maintain those generated outputs separately. Missing reuse metadata only disables "
                "automatic reuse; missing core confirmation evidence prevents completion."
            )
        else:
            final_reporting = (
                f"This retained run uses the legacy output contract: write `{ws.work_dir(target) / 'ci-report.md'}` "
                f"and `ci-verdict.json` with version 1, run_id `{ws.run_dir.name}`, and findings containing "
                "id, status, and evidence. Include all prior unresolved findings. Update persistent findings through "
                "the existing record/reuse commands. Do not switch this run to final-result.json."
            )
        prompt = render(
            "incremental",
            skill=prompt_skill_ids("incremental-modeling"),
            target=target,
            old_source=inputs["old_source"],
            new_source=str(ws.find_repo_dir(target)),
            source_diff=str(ws.run_dir / "source.diff"),
            old_model=inputs["old_model"],
            work_dir=str(ws.work_dir(target)),
            run_id=ws.run_dir.name,
            final_reporting=final_reporting,
        )
        return self._with_extra(ws, target, prompt)

    def finalize_outputs(
        self, ws: Workspace, names: list[str], *, adapter: Path, dry_run: bool
    ) -> list[tuple[str, int]]:
        if dry_run:
            return []
        assert ws.run_dir is not None
        failures: list[tuple[str, int]] = []
        for name in names:
            work = ws.work_dir(name)
            log = self.agent_files(ws, name)["log"]
            response = _last_message_path(log) if adapter.stem == "codex" else log
            try:
                if not ci_init._regular_file(work, response.name):
                    raise CIError("missing current Agent final response")
                expected = f"SPECULA_INCREMENTAL_COMPLETE {ws.run_dir.name}"
                if response.read_text(errors="replace").strip().splitlines()[-1:] != [expected]:
                    raise CIError("Agent did not report completion of the incremental workflow")
                inputs = read_json(ws.run_dir / "ci-input.json")
                if ci_result.enabled(inputs):
                    ci_result.generate(work, ws.run_dir / "ci-source", ws.run_dir.name, Path(inputs["old_model"]))
                for required in ("ci-report.md", "spec/base.tla", "harness/run.sh"):
                    if not ci_init._regular_file(work, required) or not (work / required).read_bytes().strip():
                        raise CIError(f"missing required result: {required}")
                if stop_gate._accept_main(self.key, str(work)) != 0:
                    raise CIError("incremental run left blocked or unfinished work")
                ci_verdict.finalize(work, ws.run_dir / "ci-source", ws.run_dir.name, previous=Path(inputs["old_model"]))
            except (OSError, ValueError, CIError) as exc:
                print(f"ERROR: {exc}; current model will not be updated")
                failures.append((name, 1))
        return failures

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        for name in names:
            print(f"Incremental report: {ws.work_dir(name) / 'ci-report.md'}")
