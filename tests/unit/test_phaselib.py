"""Behavior tests for the phase launchers (src/specula/phaselib.py).

With the characterization goldens retired there is no bash to diff against, so
these tests ARE the pin for each `launch_<phase>.sh`'s observable contract — the
part no other test crosses (the e2e dry-run stops at the pipeline layer, which
only *prints* the launcher command lines and never enters phaselib):

  - the precondition gate: missing inputs -> the phase's own fail message and
    exit 1 (the deleted gate_* goldens);
  - the --dry-run adapter command line + the prompt file each phase assembles:
    the adapter invocation, the per-phase log/prompt filenames, the --prompt vs
    --prompt-file quirk, the skill guide each defers to, and the output paths
    (the deleted dryrun_* / check_ok_* goldens);
  - the review agent's prompt contract (the deleted review_* goldens).

Each phase runs in-process under an isolated SPECULA_RUN_DIR, so every output
lands in a tmp run dir; --dry-run means no adapter is spawned and no network is
touched. SPECULA_ROOT is patched to a tmp tree so skill/case-dir paths resolve
hermetically (LAUNCH_DIR — the real adapter the gate checks exists — is a
module global and stays pointed at the repo).

stdlib unittest, collected natively by pytest:

    uv run python -m unittest tests.unit.test_phaselib -v
"""

from __future__ import annotations

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, TypedDict

SRC = Path(__file__).resolve().parents[2] / "src"
if str(SRC) not in sys.path:  # test the tree this file lives in, installed or not
    sys.path.insert(0, str(SRC))

from specula import phaselib  # noqa: E402

NAME = "footest"


class PhaseSpec(TypedDict):
    key: str
    artifact: bool  # whether the phase accepts --artifact (bug_classification does not)
    inputs: list[str]  # files, relative to the work dir, check() needs to pass
    fail: str  # gate message when a prerequisite is missing
    ok: str  # --check success message
    log: str  # agent log filename
    prompt: str  # written prompt filename
    flag: str  # dry-run prompt flag: --prompt or --prompt-file
    skill: str  # skill guide the prompt defers to
    out: str  # a key output/input path the prompt must carry


# Per-phase contract table. `fail`/`ok`/`skill`/`out` are spelled out here rather
# than read back off the phase object, so a reworded gate, a typo'd skill path,
# or a dropped output path is caught rather than mirrored.
PHASES: list[PhaseSpec] = [
    {
        "key": "code_analysis",
        "artifact": True,
        "inputs": [],
        "fail": "Some repositories are missing",
        "ok": "All repos OK.",
        "log": "agent.log",
        "prompt": ".prompt.md",
        "flag": "--prompt",
        "skill": ".claude/skills/code_analysis/guide.md",
        "out": "modeling-brief.md",
    },
    {
        "key": "spec_generation",
        "artifact": True,
        "inputs": ["modeling-brief.md"],
        "fail": "Run code analysis first.",
        "ok": "All prerequisites OK.",
        "log": "spec-gen.log",
        "prompt": ".spec-gen-prompt.md",
        "flag": "--prompt",
        "skill": ".claude/skills/spec_generation/guide.md",
        "out": "spec/base.tla",
    },
    {
        "key": "harness_generation",
        "artifact": True,
        "inputs": ["spec/base.tla", "spec/Trace.tla", "spec/instrumentation-spec.md"],
        "fail": "Run spec generation (Phase 2) first.",
        "ok": "All prerequisites OK.",
        "log": "harness-gen.log",
        "prompt": ".harness-gen-prompt.md",
        "flag": "--prompt",
        "skill": ".claude/skills/harness-generation/guide.md",
        "out": "harness",
    },
    {
        "key": "spec_validation",
        "artifact": True,
        "inputs": ["spec/base.tla", "spec/MC.tla", "spec/Trace.tla", "spec/instrumentation-spec.md"],
        "fail": "Run spec generation first.",
        "ok": "All prerequisites OK.",
        "log": "spec-validation.log",
        "prompt": ".spec-validation-prompt.md",
        "flag": "--prompt",
        "skill": ".claude/skills/validation-workflow/guide.md",
        "out": "modeling-brief.md",
    },
    {
        "key": "bug_confirmation",
        "artifact": True,
        "inputs": ["spec/bug-report.md", "modeling-brief.md"],
        "fail": "Run full pipeline first.",
        "ok": "All prerequisites OK.",
        "log": "bug-confirmation.log",
        "prompt": ".bug-confirmation-prompt.md",
        "flag": "--prompt",
        "skill": ".claude/skills/bug-confirmation/guide.md",
        "out": "spec/confirmed-bugs.md",
    },
    {
        # the outlier: no --artifact (accepts_artifact=False) and its dry-run
        # line shows --prompt-file, not --prompt.
        "key": "bug_classification",
        "artifact": False,
        "inputs": ["spec/confirmed-bugs.md"],
        "fail": "Run Phase 4a (launch_bug_confirmation.sh) first.",
        "ok": "All prerequisites OK.",
        "log": "bug-classification.log",
        "prompt": ".bug-classification-prompt.md",
        "flag": "--prompt-file",
        "skill": ".claude/skills/bug-classification/guide.md",
        "out": "spec/bug-severity.md",
    },
]
BY_KEY = {p["key"]: p for p in PHASES}


class PhaseCase(unittest.TestCase):
    """A phase run in-process under an isolated, hermetic tmp SPECULA_ROOT +
    SPECULA_RUN_DIR."""

    def setUp(self) -> None:
        self.root = self.tmp()  # patched SPECULA_ROOT: skills/case dirs resolve here
        self.run_dir = self.tmp()  # SPECULA_RUN_DIR: every output lands here
        self.patch_attr(phaselib, "SPECULA_ROOT", self.root)
        # Env the driver reads; restore so one test can't leak into the next.
        for var in ("SPECULA_RUN_DIR", "SPECULA_PHASE", "SPECULA_WORK_DIR", "CLAUDE_ALIAS"):
            self.set_env(var, str(self.run_dir) if var == "SPECULA_RUN_DIR" else None)

    def tmp(self) -> Path:
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return Path(d.name).resolve()

    def patch_attr(self, module: Any, attr: str, value: Any) -> None:
        old = getattr(module, attr)

        def restore() -> None:
            setattr(module, attr, old)

        self.addCleanup(restore)
        setattr(module, attr, value)

    def set_env(self, var: str, value: str | None) -> None:
        old = os.environ.get(var)

        def restore() -> None:
            if old is None:
                os.environ.pop(var, None)
            else:
                os.environ[var] = old

        self.addCleanup(restore)
        if value is None:
            os.environ.pop(var, None)
        else:
            os.environ[var] = value

    def work_dir(self, name: str = NAME) -> Path:
        return self.run_dir / name / ".specula-output"

    def seed(self, inputs: list[str], name: str = NAME) -> None:
        for rel in inputs:
            p = self.work_dir(name) / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("seeded\n")  # non-empty: some gates check st_size > 0

    def artifact_flag(self) -> str:
        # A path find_repo_dir returns verbatim (need not exist), so the repo
        # prerequisite is satisfied without a real checkout or a git call.
        return f"--artifact={self.tmp() / 'repo'}"

    def run_phase(self, key: str, args: list[str]) -> tuple[int, str]:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = phaselib.PHASES[key].run(args)
        return rc, buf.getvalue()

    def dry_run(self, spec: PhaseSpec, extra: list[str] | None = None, name: str = NAME) -> tuple[int, str]:
        self.seed(spec["inputs"], name)
        args = ["--dry-run", *(extra or [])]
        if spec["artifact"]:
            args.append(self.artifact_flag())
        args.append(name)
        return self.run_phase(spec["key"], args)


class TestPreconditionGate(PhaseCase):
    """Missing inputs -> the phase's fail message on stdout + exit 1, before any
    agent is launched."""

    def test_each_phase_gate_fails_without_inputs(self) -> None:
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                rc, out = self.run_phase(spec["key"], [NAME])  # no inputs, no --artifact
                self.assertEqual(rc, 1, out)
                self.assertIn(spec["fail"], out)  # the phase's own, distinct fail message
                self.assertNotIn("[DRY RUN]", out)  # gate stops before the launch loop


class TestCheckOnly(PhaseCase):
    """--check with prerequisites satisfied -> the ok message + exit 0, no launch."""

    def test_each_phase_check_ok(self) -> None:
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                self.seed(spec["inputs"])
                args = ["--check"]
                if spec["artifact"]:
                    args.append(self.artifact_flag())
                args.append(NAME)
                rc, out = self.run_phase(spec["key"], args)
                self.assertEqual(rc, 0, out)
                self.assertIn(spec["ok"], out)
                self.assertNotIn("[DRY RUN]", out)


class TestDryRunCommand(PhaseCase):
    """The dry-run adapter command line + the assembled prompt file."""

    def test_each_phase_command_and_prompt(self) -> None:
        adapter = phaselib.LAUNCH_DIR / "adapters" / "claude-code.sh"
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                # bug_confirmation now defaults to parallel per-finding; the
                # single-agent adapter command this test pins is the
                # --legacy-confirm path (parallel default has its own test below).
                extra = ["--legacy-confirm"] if spec["key"] == "bug_confirmation" else None
                rc, out = self.dry_run(spec, extra=extra)
                self.assertEqual(rc, 0, out)

                wd = self.work_dir()
                log = wd / spec["log"]
                prompt = wd / spec["prompt"]

                # the [DRY RUN] adapter line, piece by piece
                self.assertIn("[DRY RUN]", out)
                self.assertIn(str(adapter), out)
                self.assertIn(f"{spec['flag']}=<prompt>", out)  # --prompt vs --prompt-file quirk
                self.assertIn("--max-turns=0", out)
                self.assertIn(f"--log={log}", out)
                self.assertIn("--background", out)
                self.assertIn(f"Prompt saved: {prompt}", out)

                # the prompt file the agent would receive
                self.assertTrue(prompt.is_file(), "prompt file not written")
                body = prompt.read_text()
                self.assertIn(spec["skill"], body)  # the skill guide it defers to
                self.assertIn(str(wd / spec["out"]), body)  # a key output/inputs path

    def test_bug_confirmation_defaults_to_parallel(self) -> None:
        # No --legacy-confirm: Phase 4a runs parallel per-finding confirmation
        # (confirmlib), NOT the single-agent adapter launch.
        rc, out = self.dry_run(BY_KEY["bug_confirmation"])
        self.assertEqual(rc, 0, out)
        self.assertIn("Parallel confirmation", out)
        self.assertNotIn("--background", out)  # not the single-agent _launch command

    def test_bug_confirmation_recheck_stays_single_agent(self) -> None:
        # --recheck always uses the single-agent path, even without --legacy-confirm.
        rc, out = self.dry_run(BY_KEY["bug_confirmation"], extra=["--recheck"])
        self.assertEqual(rc, 0, out)
        self.assertIn("[DRY RUN]", out)  # single-agent adapter launch
        self.assertNotIn("Parallel confirmation", out)

    def test_max_turns_forwarded_verbatim(self) -> None:
        rc, out = self.dry_run(BY_KEY["code_analysis"], extra=["--max-turns=7"])
        self.assertEqual(rc, 0, out)
        self.assertIn("--max-turns=7", out)

    def test_bug_classification_rejects_artifact(self) -> None:
        # accepts_artifact=False: --artifact is not a known option here.
        rc, out = self.run_phase("bug_classification", ["--artifact=/x", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown option", out)


class TestRepairAndRecheckModes(PhaseCase):
    """The two back-edge modes swap the prompt template and the log/prompt
    filenames (but keep the canonical .pid)."""

    def test_spec_validation_repair(self) -> None:
        rc, out = self.dry_run(BY_KEY["spec_validation"], extra=["--repair"])
        self.assertEqual(rc, 0, out)
        wd = self.work_dir()
        self.assertIn(f"--log={wd / 'spec-repair.log'}", out)
        body = (wd / ".spec-repair-prompt.md").read_text()
        self.assertIn("REPAIR MODE", body)
        self.assertIn("repair-request-format.md", body)

    def test_bug_confirmation_recheck(self) -> None:
        rc, out = self.dry_run(BY_KEY["bug_confirmation"], extra=["--recheck"])
        self.assertEqual(rc, 0, out)
        wd = self.work_dir()
        self.assertIn(f"--log={wd / 'bug-recheck.log'}", out)
        body = (wd / ".bug-recheck-prompt.md").read_text()
        self.assertIn("RE-CHECK", body)
        self.assertIn("03-recheck.md", body)


class TestArgErrors(PhaseCase):
    def test_unknown_agent(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--agent=bogus", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown agent 'bogus'", out)

    def test_unknown_option(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--bogus", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown option", out)

    def test_bad_max_parallel(self) -> None:
        rc, out = self.run_phase("code_analysis", ["--max-parallel=abc", self.artifact_flag(), NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Invalid --max-parallel", out)

    def test_help_prints_usage(self) -> None:
        for spec in PHASES:
            with self.subTest(phase=spec["key"]):
                rc, out = self.run_phase(spec["key"], ["--help"])
                self.assertEqual(rc, 0)
                self.assertIn("Usage:", out)
                self.assertIn(f"launch_{spec['key']}.sh", out)


class TestSummarize(PhaseCase):
    """The post-launch Results block each phase prints. Dry-run/--check return
    before the launch loop, so nothing else reaches summarize(); these seed the
    output files and call it directly (no agent). Replaces the retired summary_*
    goldens, incl. the non-UTF-8 _wc_l byte-count case."""

    class Case(TypedDict):
        name: str
        phase: str
        files: dict[str, str | bytes]
        want: list[str]

    CASES: list[Case] = [
        {
            "name": "code_analysis/brief",
            "phase": "code_analysis",
            "files": {"modeling-brief.md": "a\nb\nc\n"},
            "want": [f"OK  {NAME} -> modeling-brief.md (3 lines)"],
        },
        {
            "name": "code_analysis/report-only",
            "phase": "code_analysis",
            "files": {"analysis-report.md": "x\ny\n"},
            "want": [f"~~  {NAME} -> analysis-report.md only (2 lines, no modeling brief)"],
        },
        {
            "name": "code_analysis/none",
            "phase": "code_analysis",
            "files": {},
            "want": [f"--  {NAME} (no output)"],
        },
        {
            # _wc_l counts \n by bytes (wc -l): a \xff line with no trailing newline
            # must count, not crash. Replaces summary_code_analysis_nonutf8.
            "name": "code_analysis/nonutf8-bytes",
            "phase": "code_analysis",
            "files": {"modeling-brief.md": b"line1\n\xff\xfe line2 no newline"},
            "want": [f"OK  {NAME} -> modeling-brief.md (1 lines)"],
        },
        {
            "name": "spec_generation/complete",
            "phase": "spec_generation",
            "files": {f"spec/{f}": "l1\nl2\n" for f in ("base.tla", "MC.tla", "Trace.tla", "instrumentation-spec.md")},
            "want": [f"OK  {NAME} -> 4/4 files (base.tla: 2 lines)"],
        },
        {
            "name": "spec_generation/incomplete",
            "phase": "spec_generation",
            "files": {"spec/MC.tla": "x\n"},
            "want": [f"~~  {NAME} -> 1/4 files (incomplete)", "missing: base.tla"],
        },
        {
            "name": "harness_generation/run+traces",
            "phase": "harness_generation",
            "files": {"harness/run.sh": "#!/bin/sh\n", "traces/t1.ndjson": "{}\n"},
            "want": [f"OK  {NAME} -> run.sh: yes, traces: 1", "warning: missing INSTRUMENTATION.md"],
        },
        {
            "name": "harness_generation/none",
            "phase": "harness_generation",
            "files": {},
            "want": [f"--  {NAME} (no harness output)"],
        },
        {
            "name": "spec_validation/changelog",
            "phase": "spec_validation",
            "files": {"spec/changelog.md": "c1\nc2\nc3\n"},
            "want": [f"{NAME}: changelog written (3 lines)"],
        },
        {
            "name": "spec_validation/empty-changelog",
            "phase": "spec_validation",
            "files": {"spec/changelog.md": ""},
            "want": [f"{NAME}: changelog empty (check log)"],
        },
        {
            "name": "bug_confirmation/repro-count",
            "phase": "bug_confirmation",
            "files": {
                "spec/confirmed-bugs.md": "b1\nb2\n",
                "repro/test_bug1.py": "assert True\n",
                "repro/nested/test_bug2.py": "assert True\n",
            },
            "want": [f"{NAME}: confirmed-bugs.md written (2 lines, repro/ tests: 2)"],
        },
        {
            "name": "bug_classification/severity",
            "phase": "bug_classification",
            "files": {
                "spec/bug-severity.md": (
                    "- Total bugs: 7\n- Critical: 1\n- High: 2\n- Medium: 3\n- Low: 1\n- FALSE POSITIVE: 0\n"
                )
            },
            "want": [f"{NAME}: total=7  C=1 H=2 M=3 L=1 FP=0"],
        },
        {
            "name": "bug_classification/no-report",
            "phase": "bug_classification",
            "files": {},
            "want": [f"{NAME}: (no report — check log)"],
        },
    ]

    def test_results_block(self) -> None:
        for i, tc in enumerate(self.CASES):
            with self.subTest(tc["name"]):
                name = f"t{i}"  # fresh work dir per case so seeds don't leak
                for rel, content in tc["files"].items():
                    p = self.work_dir(name) / rel
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_bytes(content) if isinstance(content, bytes) else p.write_text(content)
                buf = io.StringIO()
                with contextlib.redirect_stdout(buf):
                    phaselib.PHASES[tc["phase"]].summarize(phaselib.Workspace([name]), [name])
                got = buf.getvalue()
                for want in tc["want"]:
                    self.assertIn(want.replace(NAME, name), got)


class TestReviewPhase(PhaseCase):
    """The review agent overrides run() wholesale; its contract is the prompt it
    assembles (no --dry-run, so drive the pure builders directly to stay off the
    network) plus its arg validation."""

    def review(self) -> phaselib.ReviewPhase:
        return phaselib.ReviewPhase()

    def test_analysis_prompt_contract(self) -> None:
        wd = self.work_dir()
        body = self.review()._analysis_prompt(wd, NAME)
        self.assertIn(f"Write your review to: {wd}/review-analysis.md", body)
        self.assertIn(str(wd / "modeling-brief.md"), body)
        self.assertIn("## Overall: X/35", body)

    def test_specgen_prompt_contract(self) -> None:
        wd = self.work_dir()
        body = self.review()._specgen_prompt(wd, NAME)
        self.assertIn(str(wd / "spec" / "review-specgen.md"), body)
        self.assertIn(str(wd / "spec" / "base.tla"), body)
        self.assertIn("## Overall: X/40", body)

    def test_validation_prompt_contract(self) -> None:
        wd = self.work_dir()
        body = self.review()._validation_prompt(wd, NAME)
        self.assertIn(str(wd / "spec" / "review-validation.md"), body)
        self.assertIn("Ready for trace validation", body)

    def test_requires_phase_and_targets(self) -> None:
        for argv in ([], ["analysis"]):  # no phase / no targets
            with self.subTest(argv=argv):
                rc, out = self.run_phase("review", argv)
                self.assertEqual(rc, 1)
                self.assertIn("review <analysis|specgen|validation>", out)

    def test_unknown_agent(self) -> None:
        rc, out = self.run_phase("review", ["analysis", "--agent=bogus", NAME])
        self.assertEqual(rc, 1)
        self.assertIn("Unknown agent 'bogus'", out)

    def test_help(self) -> None:
        rc, out = self.run_phase("review", ["analysis", "--help"])
        self.assertEqual(rc, 0)
        self.assertIn("Run a Claude Code review agent", out)


if __name__ == "__main__":
    unittest.main()
