"""--confirm-first: confirm the Phase 1 Scenarios before modeling.

Pins the sealed Scenario record (``specula.confirm_first``), the Scenario-only
and after-Scenario consolidation modes, carried verdicts and covered
model-checking findings in the dispatcher (including repair rounds), the
confirmation phase options, and the pipeline's phase order and resume rules.

    uv run pytest tests/unit/test_confirm_first.py -q
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path
from typing import Any
from unittest import mock

from specula import confirm_first as CF
from specula import confirmlib as C
from specula import phaselib as PhaseLib
from specula import pipelinelib as PL
from specula import resumelib
from specula.phaselib import Workspace

EVIDENCE = "The investigation inspected the real call path and captured concrete observed behavior."
TOKEN = "0123456789abcdef0123456789abcdef"
BRIEF = "# Modeling Brief\n\n### Scenario 1: Stale reply\n\nx\n\n### Scenario 2: Lease read\n\ny\n"


def quiet(fn: Any, *args: Any, **kwargs: Any) -> tuple[Any, str]:
    out = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        result = fn(*args, **kwargs)
    return result, out.getvalue()


def scenario(fid: str, number: int) -> dict[str, Any]:
    return {
        "id": fid,
        "title": f"Scenario {number} defect",
        "source": "code-review",
        "scenario": f"Scenario {number}",
        "severity": "High",
        "invariant": None,
        "config": None,
        "counterexample": None,
        "affected_code": [f"src/a.go:{number}"],
        "summary": f"Scenario {number} hypothesis.",
    }


class Case(unittest.TestCase):
    name = "T"

    def setUp(self) -> None:
        self.tmp = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tmp, True)
        patcher = mock.patch.dict(os.environ, {"SPECULA_RUN_DIR": self.tmp})
        patcher.start()
        self.addCleanup(patcher.stop)
        self.ws = Workspace([self.name])
        self.work = self.ws.work_dir(self.name)
        (self.work / "spec").mkdir(parents=True)
        (self.work / "modeling-brief.md").write_text(BRIEF)

    def cfg(self, **kw: Any) -> C.ConfirmConfig:
        return C.ConfirmConfig(
            name=self.name, ws=self.ws, adapter=Path("/x"), worktree=False, repo_dir="", max_parallel=1, **kw
        )

    def save(self, data: dict[str, Any], status: str, body: str = EVIDENCE) -> None:
        finding = C.Finding(data, self.work / "confirmation" / data["id"])
        if status == "REPRODUCED":
            repro = self.work / "repro" / f"test_bug{data['id']}_case.py"
            repro.parent.mkdir(parents=True, exist_ok=True)
            repro.write_text("assert True\n")
        C._save_verdict(C.Outcome(finding, status, True, 0, body), self.cfg(scenarios_only=True))

    def scenario_pass(self, statuses: dict[str, str] | None = None) -> list[dict[str, Any]]:
        """The on-disk result of a finished Scenario-only confirmation."""
        statuses = statuses or {"CR-1": "REPRODUCED", "CR-2": "FALSE POSITIVE"}
        candidates = [scenario(fid, index) for index, fid in enumerate(statuses, 1)]
        (self.work / "spec" / "candidates.json").write_text(json.dumps({"findings": candidates}))
        (self.work / "spec" / ".candidates-cache.json").write_text("{}")
        for candidate in candidates:
            self.save(candidate, statuses[candidate["id"]], f"{EVIDENCE} ({candidate['id']} evidence)")
        (self.work / "confirmed-bugs.md").write_text("# Scenario report\n")
        return candidates

    def incomplete_pass(self) -> None:
        """A Scenario-only pass whose CR-2 confirmation could not finish."""
        self.scenario_pass()
        (self.work / "confirmation" / "CR-2" / "verdict.json").unlink()
        (self.work / "confirmed-bugs.md").write_text(
            "| 1 | CR-1 | REPRODUCED | yes |\n| 2 | CR-2 | INCOMPLETE | no |\n"
        )

    def mc(self, fid: str, **extra: Any) -> dict[str, Any]:
        counterexample = self.work / "spec" / "output" / f"{fid}.out"
        counterexample.parent.mkdir(parents=True, exist_ok=True)
        counterexample.write_text(f"counterexample for {fid}\n")
        return {
            "id": fid,
            "source": "model-checking",
            "title": f"{fid} violation",
            "scenario": "Scenario 1",
            "summary": f"{fid} analysis",
            "invariant": "Inv",
            "config": "MC.cfg",
            "counterexample": f"spec/output/{fid}.out",
            **extra,
        }

    def model_outputs(self, findings: list[dict[str, Any]]) -> None:
        (self.work / "spec" / "findings.json").write_text(json.dumps({"findings": findings}))
        (self.work / "spec" / "bug-report.md").write_text("# Bug report\n")


class TestSeal(Case):
    def test_seal_moves_scenario_outputs_and_binds_verdicts(self) -> None:
        self.scenario_pass()
        sealed = CF.seal(self.work)
        self.assertEqual(sealed.ids, ["CR-1", "CR-2"])
        self.assertEqual(sealed.statuses, {"CR-1": "REPRODUCED", "CR-2": "FALSE POSITIVE"})
        for gone in ("spec/candidates.json", "spec/.candidates-cache.json", "confirmed-bugs.md"):
            self.assertFalse((self.work / gone).exists(), gone)
        self.assertTrue((self.work / CF.REPORT).is_file())
        self.assertTrue((self.work / "confirmation" / "CR-1" / "verdict.json").is_file())
        self.assertTrue(CF.is_current(self.work))
        self.assertEqual(CF.seal(self.work).ids, sealed.ids)

    def test_target_index_links_the_scenario_report(self) -> None:
        from specula.output_index import render_target_index

        self.assertNotIn("Scenario confirmation report", render_target_index(self.name, self.work))
        self.scenario_pass()
        CF.seal(self.work)
        self.assertIn(
            "[Scenario confirmation report](confirm-first/confirmed-bugs.md)",
            render_target_index(self.name, self.work),
        )

    def test_failed_seal_moves_nothing(self) -> None:
        self.scenario_pass()
        (self.work / "confirmation" / "CR-2" / "verdict.json").unlink()
        with self.assertRaisesRegex(CF.SealError, "CR-2 has no final verdict"):
            CF.seal(self.work)
        self.assertTrue((self.work / "spec" / "candidates.json").is_file())
        self.assertTrue((self.work / "confirmed-bugs.md").is_file())
        self.assertFalse(CF.sealed_exists(self.work))

    def test_incomplete_candidates_are_sealed_without_a_verdict(self) -> None:
        self.incomplete_pass()
        sealed = CF.seal(self.work)
        self.assertEqual(sealed.statuses, {"CR-1": "REPRODUCED", "CR-2": "INCOMPLETE"})
        self.assertEqual(sealed.incomplete, ["CR-2"])
        self.assertIn("1 incomplete and confirmed again after modeling", CF.summary(self.work) or "")
        self.save(scenario("CR-2", 2), "FALSE POSITIVE")  # the late pass may confirm it
        self.assertEqual(CF.load(self.work).statuses["CR-2"], "INCOMPLETE")

    def test_interrupted_seal_is_completed(self) -> None:
        self.scenario_pass()
        staging = self.work / ".confirm-first.tmp"
        staging.mkdir()
        os.replace(self.work / "spec" / "candidates.json", staging / "candidates.json")
        self.assertFalse(CF.has_current_seal(self.work))
        self.assertTrue(CF.is_current(self.work))
        self.assertFalse(staging.exists())
        self.assertEqual(CF.load(self.work).ids, ["CR-1", "CR-2"])

    def test_changed_verdict_or_report_invalidates_the_seal(self) -> None:
        self.scenario_pass()
        CF.seal(self.work)
        verdict = self.work / "confirmation" / "CR-1" / "verdict.json"
        original = verdict.read_text()
        verdict.write_text(original.replace("REPRODUCED", "MASKED"))
        with self.assertRaisesRegex(CF.SealError, "CR-1: verdict changed"):
            CF.load(self.work)
        verdict.write_text(original)
        (self.work / CF.REPORT).write_text("edited\n")
        with self.assertRaisesRegex(CF.SealError, "changed after"):
            CF.load(self.work)

    def test_brief_change_makes_the_seal_stale(self) -> None:
        self.scenario_pass()
        CF.seal(self.work)
        (self.work / "modeling-brief.md").write_text(BRIEF + "\n### Scenario 3: New\n")
        self.assertFalse(CF.is_current(self.work))
        CF.discard(self.work)
        self.assertFalse(CF.sealed_exists(self.work))


class TestMerge(Case):
    def sealed(self) -> CF.Sealed:
        candidates = [scenario("CR-1", 1), scenario("CR-2", 2)]
        return CF.Sealed(candidates, {"CR-1": "REPRODUCED", "CR-2": "FALSE POSITIVE"}, "")

    def test_reused_verdicts_cover_repeats_and_others_are_confirmed(self) -> None:
        model = [
            {"id": "MC-1", "source": "model-checking", "title": "repeat", CF.MATCH_KEY: ["CR-1"]},
            {"id": "MC-2", "source": "model-checking", "title": "rematch", CF.MATCH_KEY: ["CR-2", "CR-9"]},
            {"id": "MC-3", "source": "model-checking", "title": "new"},
            {"id": "CR-7", "source": "code-review", "title": "not model checking"},
        ]
        doc, warnings = CF.merge(model, self.sealed())
        self.assertEqual([f["id"] for f in doc["findings"]], ["MC-2", "MC-3", "CR-1", "CR-2"])
        self.assertEqual(CF.covered_ids(doc), {"MC-1"})
        self.assertEqual(doc["findings"][0][CF.MATCH_KEY], ["CR-2"])
        self.assertEqual(doc["findings"][1][CF.MATCH_KEY], [])
        self.assertEqual(len(warnings), 2)
        self.assertIn("CR-9", warnings[0])
        notes = CF.report_notes(doc)
        self.assertIn("MC-1: repeat. Same defect; this earlier verdict is reused.", notes["CR-1"])
        self.assertIn("MC-2: rematch. Confirmed separately", notes["CR-2"])

    def test_summary_counts_model_checking_against_the_seal(self) -> None:
        self.scenario_pass()
        sealed = CF.seal(self.work)
        self.assertIn("2 Scenario candidate(s) confirmed before modeling (1 reproduced", CF.summary(self.work) or "")
        model = [
            {"id": "MC-1", "source": "model-checking", CF.MATCH_KEY: ["CR-1"]},
            {"id": "MC-2", "source": "model-checking", CF.MATCH_KEY: ["CR-2"]},
            {"id": "MC-3", "source": "model-checking"},
        ]
        doc, _ = CF.merge(model, sealed)
        (self.work / "spec" / "candidates.json").write_text(json.dumps(doc))
        self.assertIn(
            "model checking: 3 finding(s) — 1 repeated an earlier confirmed defect, "
            "1 matched an unconfirmed Scenario candidate, 1 new",
            CF.summary(self.work) or "",
        )


class TestScenarioOnlyConsolidation(Case):
    def test_prompt_ignores_model_outputs(self) -> None:
        (self.work / "spec" / "findings.json").write_text("not json")
        prompts: list[str] = []

        def run(_adapter: Path, prompt: str, *_args: object, **_kwargs: object) -> tuple[int, str]:
            prompts.append(prompt)
            (self.work / "spec" / "candidates.json").write_text(json.dumps({"findings": [scenario("CR-1", 1)]}))
            return (0, "")

        with mock.patch.object(C, "run_agent_blocking", run):
            C.consolidate(self.cfg(scenarios_only=True))
        self.assertEqual(len(prompts), 1)
        self.assertIn("none. This pass confirms the Scenarios before any model exists", prompts[0])
        self.assertNotIn("findings.json", prompts[0])

    def test_candidate_cache_is_bound_to_the_mode(self) -> None:
        default = C._candidate_fingerprint(self.cfg())
        self.assertNotEqual(default, C._candidate_fingerprint(self.cfg(scenarios_only=True)))
        self.assertNotEqual(default, C._candidate_fingerprint(self.cfg(after_scenarios=True)))


class TestAfterScenarios(Case):
    def setUp(self) -> None:
        super().setUp()
        self.scenario_pass()
        CF.seal(self.work)
        self.model_outputs([self.mc("MC-1"), self.mc("MC-2"), self.mc("MC-3")])
        self.confirmed: list[str] = []

    def agent(self, matches: dict[str, list[str]]) -> Any:
        def run(_adapter: Path, prompt: str, prompt_file: Path, *_args: object, **_kwargs: object) -> tuple[int, str]:
            if Path(prompt_file).name == ".consolidate-after-scenarios.prompt.md":
                self.assertIn(str(self.work / CF.REPORT), prompt)
                findings = [{**self.mc(fid), CF.MATCH_KEY: ids} for fid, ids in matches.items()]
                (self.work / CF.MODEL_CANDIDATES).write_text(json.dumps({"findings": findings}))
                return (0, "")
            fid = prompt.split("Confirm finding **", 1)[1].split("**", 1)[0]
            self.confirmed.append(fid)
            return (0, f"{EVIDENCE}\nVERDICT: NEEDS MORE INFO")

        return run

    def report(self) -> str:
        return (self.work / "confirmed-bugs.md").read_text()

    def test_repeats_reuse_verdicts_and_others_are_confirmed(self) -> None:
        verdict = (self.work / "confirmation" / "CR-1" / "verdict.json").read_bytes()
        agent = self.agent({"MC-1": ["CR-1"], "MC-2": ["CR-2"], "MC-3": []})
        with mock.patch.object(C, "run_agent_blocking", agent):
            rc, _ = quiet(C.run_parallel_confirmation, self.cfg(after_scenarios=True))
        self.assertEqual(rc, 0)
        self.assertEqual(sorted(self.confirmed), ["MC-2", "MC-3"])
        report = self.report()
        self.assertIn("| 1 | MC-2 | NEEDS MORE INFO |", report)
        self.assertIn("| 2 | MC-3 | NEEDS MORE INFO |", report)
        self.assertIn("| 3 | CR-1 | REPRODUCED |", report)
        self.assertIn("| 4 | CR-2 | FALSE POSITIVE |", report)
        self.assertNotIn("| MC-1 |", report)
        self.assertIn("(CR-1 evidence)", report)
        self.assertIn("- MC-1: MC-1 violation. Same defect; this earlier verdict is reused.", report)
        self.assertIn("- MC-2: MC-2 violation. Confirmed separately", report)
        self.assertEqual((self.work / "confirmation" / "CR-1" / "verdict.json").read_bytes(), verdict)
        CF.load(self.work)  # the seal still verifies

        self.confirmed.clear()
        with mock.patch.object(C, "run_agent_blocking", self.agent({})):
            rc, _ = quiet(C.run_parallel_confirmation, self.cfg(after_scenarios=True))
        self.assertEqual(rc, 0)
        self.assertEqual(self.confirmed, [])  # cached candidates and verdicts

    def test_without_model_outputs_only_carried_verdicts_are_reported(self) -> None:
        for name in ("findings.json", "bug-report.md"):
            (self.work / "spec" / name).unlink()
        with mock.patch.object(C, "run_agent_blocking", self.agent({})):
            rc, _ = quiet(C.run_parallel_confirmation, self.cfg(after_scenarios=True))
        self.assertEqual(rc, 0)
        self.assertEqual(self.confirmed, [])
        self.assertIn("| 1 | CR-1 | REPRODUCED |", self.report())
        self.assertFalse((self.work / CF.MODEL_CANDIDATES).exists())

    def test_changed_sealed_verdict_withholds(self) -> None:
        verdict = self.work / "confirmation" / "CR-2" / "verdict.json"
        verdict.write_text(verdict.read_text().replace("FALSE POSITIVE", "DROPPED"))
        with mock.patch.object(C, "run_agent_blocking", self.agent({"MC-1": []})):
            rc, out = quiet(C.run_parallel_confirmation, self.cfg(after_scenarios=True))
        self.assertEqual(rc, 1)
        self.assertEqual(self.confirmed, [])
        self.assertIn("verdict changed after the Scenario confirmation was sealed", out)

    def test_repair_round_keeps_covered_violations_covered(self) -> None:
        agent = self.agent({"MC-1": ["CR-1"], "MC-2": [], "MC-3": []})
        with mock.patch.object(C, "run_agent_blocking", agent):
            quiet(C.run_parallel_confirmation, self.cfg(after_scenarios=True))
        findings = [self.mc("MC-1"), self.mc("MC-2")]
        findings_json = json.dumps({"findings": findings})
        (self.work / "spec" / "findings.json").write_text(findings_json)
        (self.work / "spec" / ".repair-phase3-commit.json").write_text(
            json.dumps(
                {
                    "version": 2,
                    "repair_round": 1,
                    "commit_token": TOKEN,
                    "request_ids": [],
                    "violation_ids": ["MC-1", "MC-2"],
                    "findings_json": findings_json,
                }
            )
        )
        self.confirmed.clear()
        cfg = self.cfg(after_scenarios=True, repair_round=1, repair_token=TOKEN)
        with mock.patch.object(C, "run_agent_blocking", self.agent({})):
            rc, _ = quiet(C.run_parallel_confirmation, cfg)
        self.assertEqual(rc, 0)
        self.assertEqual(self.confirmed, ["MC-2"])
        report = self.report()
        self.assertNotIn("| MC-1 |", report)
        self.assertIn("| CR-1 | REPRODUCED |", report)
        self.assertIn("Same defect; this earlier verdict is reused.", report)
        candidates = json.loads((self.work / "spec" / "candidates.json").read_text())
        self.assertNotIn("MC-1", [f["id"] for f in candidates["findings"]])
        self.assertEqual(CF.covered_ids(candidates), {"MC-1"})


class TestIncompleteScenario(Case):
    def test_incomplete_candidate_is_confirmed_with_the_model_findings(self) -> None:
        self.incomplete_pass()
        CF.seal(self.work)
        self.model_outputs([self.mc("MC-1"), self.mc("MC-2")])
        confirmed: list[str] = []

        def run(_adapter: Path, prompt: str, prompt_file: Path, *_args: object, **_kwargs: object) -> tuple[int, str]:
            if Path(prompt_file).name == ".consolidate-after-scenarios.prompt.md":
                findings = [{**self.mc("MC-1"), CF.MATCH_KEY: ["CR-2"]}, {**self.mc("MC-2"), CF.MATCH_KEY: ["CR-1"]}]
                (self.work / CF.MODEL_CANDIDATES).write_text(json.dumps({"findings": findings}))
                return (0, "")
            confirmed.append(prompt.split("Confirm finding **", 1)[1].split("**", 1)[0])
            return (0, f"{EVIDENCE}\nVERDICT: NEEDS MORE INFO")

        with mock.patch.object(C, "run_agent_blocking", run):
            rc, _ = quiet(C.run_parallel_confirmation, self.cfg(after_scenarios=True))
        self.assertEqual(rc, 0)
        self.assertEqual(sorted(confirmed), ["CR-2", "MC-1"])
        report = (self.work / "confirmed-bugs.md").read_text()
        self.assertIn("| CR-1 | REPRODUCED |", report)
        self.assertIn("| CR-2 | NEEDS MORE INFO |", report)
        self.assertNotIn("| MC-2 |", report)
        self.assertIn("- MC-1: MC-1 violation. Confirmed separately", report)
        CF.load(self.work)


class TestConfirmationPhase(Case):
    def test_option_rules(self) -> None:
        phase = PhaseLib.BugConfirmationPhase()
        cases: list[tuple[dict[str, str | bool], str]] = [
            ({"scenarios_only": True, "after_scenarios": True}, "cannot be used together"),
            ({"legacy": True, "scenarios_only": True}, "--legacy-confirm"),
            ({"scenarios_only": True, "repair_round": "1", "repair_token": TOKEN}, "--repair-round"),
        ]
        for extra, message in cases:
            with self.subTest(extra=extra):
                self.assertIn(message, phase.validate_options(dict(extra)) or "")
        self.assertIsNone(phase.validate_options({"after_scenarios": True, "repair_round": "1", "repair_token": TOKEN}))

    def test_check_prerequisites(self) -> None:
        phase = PhaseLib.BugConfirmationPhase()
        with mock.patch.object(Workspace, "find_repo_dir", return_value="/repo"):
            ok, out = quiet(phase.check, Workspace([self.name], opts={"scenarios_only": True}), [self.name])
            self.assertTrue(ok, out)
            ok, out = quiet(phase.check, Workspace([self.name]), [self.name])
            self.assertFalse(ok)
            self.assertIn("bug-report MISSING", out)
            self.model_outputs([])
            ok, out = quiet(phase.check, Workspace([self.name], opts={"after_scenarios": True}), [self.name])
            self.assertFalse(ok)
            self.assertIn("Scenario results INVALID", out)


class TestPipeline(unittest.TestCase):
    def setUp(self) -> None:
        self._old = os.getcwd()
        self.tmp = tempfile.mkdtemp()
        os.chdir(self.tmp)
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.addCleanup(os.chdir, self._old)

    def run_main(self, argv: list[str], *, repair: bool = False) -> list[tuple[str, list[str]]]:
        p = PL.Pipeline()
        self.assertIsNone(quiet(p.parse_args, argv)[0])
        calls: list[tuple[str, list[str]]] = []
        p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        p.generate_summary = lambda: None  # type: ignore[method-assign]

        def repair_loop(*_args: object, **_kwargs: object) -> set[str]:
            if not repair:
                self.fail("repair loop ran")
            calls.append(("repair-loop", []))
            return set()

        p.run_repair_loop = repair_loop  # type: ignore[method-assign]
        p._phase = lambda banner, script, args: calls.append((script, args))  # type: ignore[method-assign]
        with mock.patch.object(CF, "seal") as seal:
            quiet(p.main)
        self.sealed = seal.call_count
        return calls

    def test_only_confirms_scenarios_then_classifies(self) -> None:
        calls = self.run_main(["--no-isolate", "--confirm-first=only", "a|g|l|r"])
        self.assertEqual(
            [script for script, _ in calls],
            ["launch_code_analysis.sh", "launch_bug_confirmation.sh", "launch_bug_classification.sh"],
        )
        self.assertIn("--scenarios-only", dict(calls)["launch_bug_confirmation.sh"])
        self.assertEqual(self.sealed, 0)

    def test_continue_confirms_scenarios_before_the_model_phases(self) -> None:
        calls = self.run_main(["--confirm-first=continue", "a|g|l|r"], repair=True)
        self.assertEqual(
            [script for script, _ in calls],
            [
                "launch_code_analysis.sh",
                "launch_bug_confirmation.sh",
                "launch_spec_generation.sh",
                "launch_harness_generation.sh",
                "launch_spec_validation.sh",
                "launch_bug_confirmation.sh",
                "repair-loop",
                "launch_bug_classification.sh",
            ],
        )
        confirmations = [args for script, args in calls if script == "launch_bug_confirmation.sh"]
        self.assertIn("--scenarios-only", confirmations[0])
        self.assertIn("--after-scenarios", confirmations[1])
        self.assertNotIn("--scenarios-only", confirmations[1])
        self.assertEqual(self.sealed, 1)

    def run_after_scenario_failure(self, code: int) -> tuple[list[str], str, object]:
        """Run continue mode with the Scenario confirmation exiting with ``code``."""
        p = PL.Pipeline()
        self.assertIsNone(quiet(p.parse_args, ["--confirm-first=continue", "a|g|l|r"])[0])
        scripts: list[str] = []

        def phase(banner: str, script: str, args: list[str]) -> None:
            scripts.append(script)
            if "--scenarios-only" in args:
                raise SystemExit(code)

        def repair_loop(*_args: object, **_kwargs: object) -> set[str]:
            return set()

        p.validate_agent_adapter = lambda: None  # type: ignore[method-assign]
        p.wait_for_quota = lambda **kwargs: None  # type: ignore[method-assign]
        p.generate_summary = lambda: None  # type: ignore[method-assign]
        p.run_repair_loop = repair_loop  # type: ignore[method-assign]
        p._phase = phase  # type: ignore[method-assign]
        sealed = CF.Sealed([scenario("CR-1", 1)], {"CR-1": "INCOMPLETE"}, "")
        out = io.StringIO()
        exit_code: object = None
        with (
            mock.patch.object(CF, "seal", return_value=sealed),
            contextlib.redirect_stdout(out),
            contextlib.redirect_stderr(out),
        ):
            try:
                p.main()
            except SystemExit as exc:
                exit_code = exc.code
        return scripts, out.getvalue(), exit_code

    def test_incomplete_scenario_candidates_do_not_hold_modeling_back(self) -> None:
        scripts, out, _ = self.run_after_scenario_failure(1)
        self.assertIn("launch_spec_generation.sh", scripts)
        self.assertIn("CR-1 INCOMPLETE; confirmed again with the model-checking findings", out)
        for code in (75, 130):
            with self.subTest(code=code):
                scripts, _, exit_code = self.run_after_scenario_failure(code)
                self.assertEqual(exit_code, code)
                self.assertNotIn("launch_spec_generation.sh", scripts)

    def test_ordinary_run_is_unchanged(self) -> None:
        calls = self.run_main(["--no-isolate", "--skip-repair-loop", "a|g|l|r"])
        confirmations = [args for script, args in calls if script == "launch_bug_confirmation.sh"]
        self.assertEqual(len(confirmations), 1)
        self.assertFalse({"--scenarios-only", "--after-scenarios"} & set(confirmations[0]))

    def test_option_errors(self) -> None:
        model = Path(self.tmp) / "Model.tla"
        model.write_text("---- MODULE Model ----\n====\n")
        prior = Path(self.tmp) / "prior"
        prior.mkdir()
        for argv, message in (
            (["--confirm-first", "a|g|l|r"], "requires one value"),
            (["--confirm-first=later", "a|g|l|r"], "requires one value"),
            (["--confirm-first=only", "--confirm-first=only", "a|g|l|r"], "requires one value"),
            (["--confirm-first=only", "--legacy-confirm", "a|g|l|r"], "--legacy-confirm"),
            (["--confirm-first=only", "--skip-confirmation", "a|g|l|r"], "--skip-confirmation"),
            (["--confirm-first=continue", f"--byom={model}", "a|g|l|r"], "--byom"),
            (["--confirm-first=continue", f"--findings-from={prior}", "a|g|l|r"], "--findings-from"),
            (["--confirm-first=continue", "--no-isolate", "a|g|l|r"], "requires isolated output"),
        ):
            with self.subTest(argv=argv):
                rc, out = quiet(PL.Pipeline().parse_args, argv)
                self.assertEqual(rc, 1)
                self.assertIn(message, out)
        self.assertIsNone(quiet(PL.Pipeline().parse_args, ["--confirm-first=only", f"--findings-from={prior}", "a"])[0])

    def test_resume_restores_the_mode(self) -> None:
        initial = PL.Pipeline()
        self.assertIsNone(initial.parse_args(["--confirm-first=only", "a|g|l|r"]))
        stored = initial._resume_configuration_document()
        self.assertEqual(stored["confirm_first"], "only")
        resumed = PL.Pipeline()
        self.assertIsNone(resumed.parse_args([]))
        resumed._restore_resume_configuration(stored)
        self.assertEqual(resumed.confirm_first, "only")
        self.assertTrue(resumed.skip_specgen and resumed.skip_validation and resumed.skip_repair_loop)
        changing = PL.Pipeline()
        self.assertIsNone(changing.parse_args(["--confirm-first=continue"]))
        with self.assertRaisesRegex(resumelib.ResumeError, "--confirm-first differs"):
            changing._restore_resume_configuration(stored)
        ordinary = PL.Pipeline()
        self.assertIsNone(ordinary.parse_args(["a|g|l|r"]))
        self.assertNotIn("confirm_first", ordinary._resume_configuration_document())

    def position(self, run_dir: Path) -> PL.Pipeline:
        p = PL.Pipeline()
        self.assertIsNone(p.parse_args(["--confirm-first=continue", "a|g|l|r"]))
        p.run_dir = run_dir
        p._manual_resume_phase = "bug_confirmation"
        p._position_at_manual_resume_phase()
        return p

    def test_interrupted_scenario_pass_still_runs_the_model_phases(self) -> None:
        run_dir = Path(self.tmp) / "run"
        p = self.position(run_dir)
        self.assertTrue(p.skip_analysis)
        self.assertFalse(p.skip_specgen or p.skip_harness or p.skip_validation)

        work = run_dir / "a" / ".specula-output"
        (work / "spec").mkdir(parents=True)
        (work / "modeling-brief.md").write_text(BRIEF)
        (work / "spec" / "candidates.json").write_text('{"findings": []}')
        (work / "confirmed-bugs.md").write_text("# report\n")
        CF.seal(work)
        p = self.position(run_dir)
        self.assertTrue(p.skip_specgen and p.skip_harness and p.skip_validation)

    def test_only_summary_states_that_modeling_was_not_run(self) -> None:
        p = PL.Pipeline()
        self.assertIsNone(p.parse_args(["--no-isolate", "--confirm-first=only", "a|g|l|r"]))
        limits = p._summary_validation_limits()
        self.assertIn("--confirm-first=only", limits[0])
        self.assertFalse(any("model generation was skipped" in limit for limit in limits))


if __name__ == "__main__":
    unittest.main()
