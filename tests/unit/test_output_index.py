"""Unit tests for the deterministic, human-facing output indexes."""

from __future__ import annotations

import os
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

from specula import output_index as oi


class OutputIndexCase(unittest.TestCase):
    def setUp(self) -> None:
        self._temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self._temporary.cleanup)
        self.root = Path(self._temporary.name).resolve()

    @staticmethod
    def write(base: Path, relative: str, content: str = "content\n") -> Path:
        path = base / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path


class TestRunIndex(OutputIndexCase):
    def test_minimal_deterministic_status_and_noop_refresh(self) -> None:
        run_root = self.root / "run"
        beta = run_root / "beta" / ".specula-output"
        alpha = run_root / "alpha" / ".specula-output"
        for work_dir in (beta, alpha):
            self.write(work_dir, "confirmed-bugs.md")
            self.write(work_dir, "bug-severity.md")
        self.assertTrue(oi.write_target_index("beta", beta, output_root=run_root))
        self.assertTrue(oi.write_target_index("alpha", alpha, output_root=run_root))
        pipeline_log = self.write(run_root, "pipeline.log")
        self.write(run_root, "run.json")
        self.write(run_root, "tlc-resources.json")
        summary = run_root / "pipeline-summary.md"
        targets = [
            oi.TargetOutput("beta", beta, run_root),
            oi.TargetOutput("alpha", alpha, run_root),
        ]

        expected_pending = textwrap.dedent(
            """\
            # Specula Run

            Select a target to browse its results or open its final reports directly.

            ## Targets

            | Target | Results | Confirmation | Severity |
            |---|---|---|---|
            | beta | [Open results](beta/.specula-output/index.md) | [Open report](beta/.specula-output/confirmed-bugs.md) | [Open report](beta/.specula-output/bug-severity.md) |
            | alpha | [Open results](alpha/.specula-output/index.md) | [Open report](alpha/.specula-output/confirmed-bugs.md) | [Open report](alpha/.specula-output/bug-severity.md) |

            ## Run Status

            - Final summary: Not available
            - Full pipeline log: [pipeline.log](pipeline.log)
            """
        )
        self.assertEqual(
            oi.render_run_index(run_root, targets, summary=summary, pipeline_log=pipeline_log),
            expected_pending,
        )

        self.assertTrue(oi.write_run_index(run_root, targets, summary=summary, pipeline_log=pipeline_log))
        index = run_root / "index.md"
        self.assertEqual(index.read_text(), expected_pending)
        self.assertFalse(oi.write_run_index(run_root, targets, summary=summary, pipeline_log=pipeline_log))
        self.assertEqual(index.read_text(), expected_pending)

        summary.write_text("# Complete\n")
        self.assertTrue(oi.write_run_index(run_root, targets, summary=summary, pipeline_log=pipeline_log))
        completed = index.read_text()
        self.assertIn("- Final summary: [pipeline-summary.md](pipeline-summary.md)", completed)
        self.assertLess(completed.index("| beta |"), completed.index("| alpha |"))
        for machine_detail in ("run.json", "tlc-resources.json", "model", "SHA", "## Reviews"):
            self.assertNotIn(machine_detail, completed)
        self.assertFalse(oi.write_run_index(run_root, targets, summary=summary, pipeline_log=pipeline_log))


class TestTargetIndex(OutputIndexCase):
    def test_final_reports_lead_supporting_analysis_without_reviews_or_machine_files(self) -> None:
        work_dir = self.root / ".specula-output"
        for relative in (
            "summary.md",
            "modeling-brief.md",
            "analysis-report.md",
            "spec/brief-coverage.md",
            "spec/instrumentation-spec.md",
            "spec/changelog.md",
            "spec/bug-report.md",
            "confirmed-bugs.md",
            "bug-severity.md",
        ):
            self.write(work_dir, relative)
        for hidden_from_humans in (
            "review-analysis.md",
            "spec/review-specgen.md",
            "spec/review-validation.md",
            "spec/findings.json",
            "spec/candidates.json",
            "agent.pid",
            "agent.usage.json",
            "agent.resume.json",
        ):
            self.write(work_dir, hidden_from_humans)

        expected = textwrap.dedent(
            """\
            # demo Results

            ## Final Reports

            - [Resource summary](summary.md) — Runtime, token, and cost usage
            - [Confirmation report](confirmed-bugs.md) — Confirmation results and supporting evidence
            - [Severity report](bug-severity.md) — Impact assessment

            > Availability means that a document exists. It does not imply review approval
            > or confirmation of every finding.

            ## Supporting Analysis

            | Step | Document | What it contains |
            |---:|---|---|
            | 1 | [Modeling brief](modeling-brief.md) | System model, Scenarios, and proposed invariants |
            | 2 | [Analysis report](analysis-report.md) | Detailed source-code investigation |
            | 3 | [Spec coverage](spec/brief-coverage.md) · [Instrumentation map](spec/instrumentation-spec.md) | How the analysis was translated into the model |
            | 4 | [Validation changelog](spec/changelog.md) | Model corrections and validation history |
            | 5 | [Model-checking report](spec/bug-report.md) | Candidate findings from model checking |
            """
        )
        rendered = oi.render_target_index("demo", work_dir)
        self.assertEqual(rendered, expected)
        self.assertLess(rendered.index("[Resource summary]"), rendered.index("[Confirmation report]"))
        for hidden_from_humans in (
            "review-analysis.md",
            "review-specgen.md",
            "review-validation.md",
            "findings.json",
            "candidates.json",
            "agent.pid",
            "agent.usage.json",
            "agent.resume.json",
            "## Reviews",
            "Machine-Readable",
        ):
            self.assertNotIn(hidden_from_humans, rendered)

    def test_optional_sections_only_show_available_human_documents(self) -> None:
        work_dir = self.root / "run" / "demo" / ".specula-output"
        self.write(work_dir, "spec/findings.json")
        self.write(work_dir, "spec/candidates.json")
        self.write(work_dir, "confirmation/MC-1/verdict.json")
        pipeline_log = work_dir.parents[1] / "pipeline.log"

        minimal = oi.render_target_index("demo", work_dir, pipeline_log=pipeline_log)
        for section in ("## Confirmation Details", "## Technical Details", "## Troubleshooting"):
            self.assertNotIn(section, minimal)

        self.write(work_dir, "spec/base.tla")
        self.write(work_dir, "spec/MC.tla")
        self.write(work_dir, "harness/INSTRUMENTATION.md")
        self.write(work_dir, "spec/repair-ledger.md")
        pipeline_log.write_text("pipeline\n")
        rendered = oi.render_target_index("demo", work_dir, pipeline_log=pipeline_log)

        self.assertIn("## Technical Details", rendered)
        self.assertIn("- TLA+ models: [base.tla](spec/base.tla) · [MC.tla](spec/MC.tla)", rendered)
        self.assertNotIn("Trace.tla", rendered)
        self.assertIn("- Harness guide: [INSTRUMENTATION.md](harness/INSTRUMENTATION.md)", rendered)
        self.assertIn("- Repair history: [repair-ledger.md](spec/repair-ledger.md)", rendered)
        self.assertIn("## Troubleshooting", rendered)
        self.assertIn("- Full pipeline log: [pipeline.log](../../pipeline.log)", rendered)
        self.assertNotIn("## Confirmation Details", rendered)
        for machine_file in ("findings.json", "candidates.json", "verdict.json"):
            self.assertNotIn(machine_file, rendered)

    def test_confirmation_rows_are_sorted_partial_and_match_reproductions_by_finding(self) -> None:
        work_dir = self.root / ".specula-output"
        self.write(work_dir, "confirmation/MC-2/investigation.md")
        self.write(work_dir, "confirmation/MC-1/debate.md")
        self.write(work_dir, "confirmation/MC-3/verdict.json")
        self.write(work_dir, "repro/test_bugMC-1_z.py")
        self.write(work_dir, "repro/test_bugMC-1_a.py")
        self.write(work_dir, "repro/test_bugMC-2_case.py")
        self.write(work_dir, "repro/test_bugMC-10_other.py")
        self.write(work_dir, "repro/unrelated.py")

        rendered = oi.render_target_index("demo", work_dir)
        self.assertIn("## Confirmation Details", rendered)
        mc1 = (
            "| MC-1 | Not available | [Read](confirmation/MC-1/debate.md) | "
            "[test_bugMC-1_a.py](repro/test_bugMC-1_a.py) · "
            "[test_bugMC-1_z.py](repro/test_bugMC-1_z.py) |"
        )
        mc2 = (
            "| MC-2 | [Read](confirmation/MC-2/investigation.md) | Not available | "
            "[test_bugMC-2_case.py](repro/test_bugMC-2_case.py) |"
        )
        self.assertIn(mc1, rendered)
        self.assertIn(mc2, rendered)
        self.assertLess(rendered.index(mc1), rendered.index(mc2))
        for excluded in ("MC-3 |", "test_bugMC-10_other.py", "unrelated.py", "verdict.json"):
            self.assertNotIn(excluded, rendered)


class TestIndexSafety(OutputIndexCase):
    def test_symlinked_inputs_and_unlisted_trees_are_never_followed(self) -> None:
        work_dir = self.root / ".specula-output"
        work_dir.mkdir()
        outside = self.root / "outside"
        self.write(outside, "document.md")
        self.write(outside, "confirmation/MC-9/investigation.md")
        (work_dir / "summary.md").symlink_to(outside / "document.md")
        (work_dir / "modeling-brief.md").symlink_to(outside / "document.md")
        (work_dir / "spec").mkdir()
        (work_dir / "spec" / "base.tla").symlink_to(outside / "document.md")
        (work_dir / "confirmation").symlink_to(outside / "confirmation", target_is_directory=True)
        self.write(work_dir, "spec/output/deep/unlisted.md")

        with mock.patch.object(Path, "rglob", side_effect=AssertionError("recursive scan attempted")):
            rendered = oi.render_target_index("demo", work_dir)

        self.assertIn("Resource summary: Not available", rendered)
        self.assertIn("| 1 | Modeling brief: Not available |", rendered)
        self.assertNotIn("## Confirmation Details", rendered)
        self.assertNotIn("## Technical Details", rendered)
        self.assertNotIn("unlisted.md", rendered)

        parent_symlink = self.root / "parent-symlink" / ".specula-output"
        parent_symlink.mkdir(parents=True)
        self.write(outside, "base.tla")
        (parent_symlink / "spec").symlink_to(outside, target_is_directory=True)
        parent_rendered = oi.render_target_index("parent-symlink", parent_symlink)
        self.assertNotIn("[base.tla]", parent_rendered)
        self.assertNotIn("## Technical Details", parent_rendered)

        safe_confirmation = self.root / "safe" / ".specula-output"
        self.write(safe_confirmation, "confirmation/MC-1/debate.md")
        repro_dir = safe_confirmation / "repro"
        repro_dir.mkdir()
        (repro_dir / "test_bugMC-1_escape.py").symlink_to(outside / "document.md")
        safe_rendered = oi.render_target_index("safe", safe_confirmation)
        self.assertIn(
            "| MC-1 | Not available | [Read](confirmation/MC-1/debate.md) | Not available |",
            safe_rendered,
        )
        self.assertNotIn("test_bugMC-1_escape.py", safe_rendered)

    def test_markdown_text_and_relative_urls_are_safe(self) -> None:
        run_root = self.root / "run"
        work_dir = run_root / "two words [x] #1 (v1)" / ".specula-output"
        oi.write_target_index("target", work_dir, output_root=run_root)
        target_name = "bad|<script>[x]\nnext"

        rendered = oi.render_run_index(
            run_root,
            [oi.TargetOutput(target_name, work_dir, run_root)],
            summary=run_root / "pipeline-summary.md",
            pipeline_log=run_root / "pipeline.log",
        )

        self.assertIn("| bad\\|&lt;script&gt;\\[x\\] next |", rendered)
        self.assertIn(
            "[Open results](two%20words%20%5Bx%5D%20%231%20%28v1%29/.specula-output/index.md)",
            rendered,
        )
        self.assertNotIn("<script>", rendered)
        target_rendered = oi.render_target_index(target_name, work_dir)
        self.assertTrue(target_rendered.startswith("# bad\\|&lt;script&gt;\\[x\\] next Results\n"))

    def test_writing_replaces_an_index_symlink_without_touching_its_target(self) -> None:
        work_dir = self.root / ".specula-output"
        work_dir.mkdir()
        outside = self.root / "outside-index.md"
        outside.write_text("outside stays unchanged\n")
        index = work_dir / "index.md"
        index.symlink_to(outside)

        self.assertTrue(oi.write_target_index("demo", work_dir, output_root=self.root))

        self.assertFalse(index.is_symlink())
        self.assertTrue(index.is_file())
        self.assertEqual(outside.read_text(), "outside stays unchanged\n")
        self.assertTrue(index.read_text().startswith("# demo Results\n"))

    def test_writing_rejects_symlinked_target_ancestor(self) -> None:
        run_root = self.root / "run"
        outside = self.root / "outside-target"
        run_root.mkdir()
        outside.mkdir()
        (run_root / "target").symlink_to(outside, target_is_directory=True)
        work_dir = run_root / "target" / ".specula-output"

        with self.assertRaisesRegex(OSError, "crosses a symlink"):
            oi.write_target_index("target", work_dir, output_root=run_root)

        self.assertFalse((outside / ".specula-output").exists())

        self.write(outside, ".specula-output/index.md")
        rendered = oi.render_run_index(
            run_root,
            [oi.TargetOutput("target", work_dir, run_root)],
            summary=run_root / "pipeline-summary.md",
            pipeline_log=run_root / "pipeline.log",
        )
        self.assertIn("| target | Not available |", rendered)
        self.assertNotIn("[Open results]", rendered)

    def test_target_name_must_be_one_safe_path_component(self) -> None:
        for valid in ("alpha", "two words", ".hidden", "name[1]"):
            with self.subTest(valid=valid):
                self.assertTrue(oi.is_safe_target_name(valid))
        for invalid in (
            "",
            "   ",
            ".",
            "..",
            "../escape",
            "a/b",
            "/absolute",
            "line\nbreak",
            "tab\tname",
            "\ud800",
        ):
            with self.subTest(invalid=invalid):
                self.assertFalse(oi.is_safe_target_name(invalid))

    @unittest.skipUnless(os.name == "posix", "invalid-byte filenames are a POSIX behavior")
    def test_invalid_utf8_filename_does_not_block_index(self) -> None:
        work_dir = self.root / ".specula-output"
        self.write(work_dir, "confirmation/MC-1/investigation.md")
        repro = work_dir / "repro"
        repro.mkdir()
        raw_path = os.fsencode(repro) + b"/test_bugMC-1_" + bytes([0xFF]) + b".py"
        descriptor = os.open(raw_path, os.O_WRONLY | os.O_CREAT, 0o600)
        os.close(descriptor)

        rendered = oi.render_target_index("demo", work_dir)

        self.assertIn("test_bugMC-1_?.py", rendered)
        self.assertIn("repro/test_bugMC-1_%FF.py", rendered)


class TestAtomicIndexWrite(OutputIndexCase):
    def test_publish_is_atomic_and_failure_preserves_the_previous_index(self) -> None:
        index = self.root / "index.md"
        index.write_text("old complete index\n")
        real_replace = os.replace
        observed: list[tuple[Path, Path]] = []

        def observe_replace(source: Path, destination: Path) -> None:
            self.assertEqual(index.read_text(), "old complete index\n")
            self.assertEqual(source.read_text(), "new complete index\n")
            observed.append((source, destination))
            real_replace(source, destination)

        with mock.patch("specula.output_index.os.replace", side_effect=observe_replace):
            self.assertTrue(oi._atomic_write_if_changed(index, "new complete index\n"))

        self.assertEqual(len(observed), 1)
        self.assertEqual(observed[0][1], index)
        self.assertEqual(index.read_text(), "new complete index\n")
        self.assertEqual(list(self.root.glob(".index.md.*.tmp")), [])

        with (
            mock.patch("specula.output_index.os.replace", side_effect=OSError("injected replace failure")),
            self.assertRaisesRegex(OSError, "injected replace failure"),
        ):
            oi._atomic_write_if_changed(index, "unpublished index\n")

        self.assertEqual(index.read_text(), "new complete index\n")
        self.assertEqual(list(self.root.glob(".index.md.*.tmp")), [])

    def test_identical_content_is_a_true_noop(self) -> None:
        index = self.root / "index.md"
        index.write_text("same bytes\n")
        modified_before = index.stat().st_mtime_ns

        with mock.patch("specula.output_index.os.replace") as replace:
            self.assertFalse(oi._atomic_write_if_changed(index, "same bytes\n"))

        replace.assert_not_called()
        self.assertEqual(index.stat().st_mtime_ns, modified_before)
        self.assertEqual(index.read_text(), "same bytes\n")
        self.assertEqual(list(self.root.glob(".index.md.*.tmp")), [])


if __name__ == "__main__":
    unittest.main()
