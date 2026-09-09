"""One native Agent conversation for the entire incremental skill."""

from __future__ import annotations

from pathlib import Path

from specula import ci_init, ci_verdict, stop_gate
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
                for required in ("ci-report.md", "spec/base.tla", "harness/run.sh"):
                    if not ci_init._regular_file(work, required) or not (work / required).read_bytes().strip():
                        raise CIError(f"missing required result: {required}")
                if stop_gate._accept_main(self.key, str(work)) != 0:
                    raise CIError("incremental run left blocked or unfinished work")
                inputs = read_json(ws.run_dir / "ci-input.json")
                ci_verdict.read(work, ws.run_dir.name, previous=Path(inputs["old_model"]))
            except (OSError, ValueError, CIError) as exc:
                print(f"ERROR: {exc}; current model will not be updated")
                failures.append((name, 1))
        return failures

    def summarize(self, ws: Workspace, names: list[str]) -> None:
        for name in names:
            print(f"Incremental report: {ws.work_dir(name) / 'ci-report.md'}")
