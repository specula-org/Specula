"""Ordinary pipeline persistence/reuse with fixture findings, no live verification."""

from __future__ import annotations

import json
import shlex
import textwrap
import unittest
from pathlib import Path

import test_incremental_ci as fixtures

from specula import persistent_findings as findings


class OneShotFindings(unittest.TestCase):
    def test_plain_runs_persist_reuse_and_reanalyze_without_ci(self) -> None:
        fixture = fixtures.IncrementalCLI()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        adapter = fixture.helper._ci_init_adapter(fixture.root)
        helper = adapter.with_suffix(".persistent.py")
        helper.write_text(
            "import json, subprocess, sys\nfrom pathlib import Path\n"
            f"sys.path.insert(0, {str(fixture.root / 'src')!r})\n"
            "from specula import persistent_findings as pf\n"
            + textwrap.dedent("""\
                mode, location, log, adapter = sys.argv[1:]
                location, adapter = Path(location), Path(adapter)
                candidate = {'id':'MC-1', 'source':'model-checking', 'title':'Fixture reply defect',
                             'invariant':'ReplySafety', 'config':'spec/MC.cfg', 'counterexample':'spec/ce.txt'}
                if mode == 'validate':
                    work = location
                    (work/'spec/ce.txt').write_text('Fixture counterexample, no semantic check.\\n')
                    current = [candidate]
                    if (adapter.with_suffix('.reuse')).exists():
                        source, run_id, previous = pf.context(work)
                        if not pf.check(work, source, 'MC-1'):
                            pf.reuse_issue(work, source, run_id, 'MC-1', 'Same fixture mechanism, consequence and premises.')
                            current = []
                    (work/'spec/findings.json').write_text(json.dumps({'findings':current}))
                elif location.name == '.consolidate.prompt.md':
                    work = location.parent.parent
                    (work/'spec/candidates.json').write_text((work/'spec/findings.json').read_text())
                    Path(log).write_text('Fixture consolidation completed.\\n')
                else:
                    fdir, work = location.parent, location.parent.parent.parent
                    count = adapter.with_suffix('.confirmation-count')
                    count.write_text(count.read_text() + 'x' if count.exists() else 'x')
                    (work/'repro').mkdir(exist_ok=True)
                    (work/'repro/test_bugMC-1_fixture.sh').write_text('#!/bin/sh\\n# Fixture only\\nexit 0\\n')
                    proposal = {
                        'id':'MC-1','status':'REPRODUCED','title':'Fixture reply defect',
                        'cause':'Fixture ordering defect','trigger':'Delayed reply','consequence':'Wrong fixture output',
                        'sites':['logic.txt'],'actions':['Reply'],'invariants':['ReplySafety'],
                        'premises':['Fixture evidence only; no live verification.'],
                        'dependencies':[{'root':'source','path':'logic.txt','start':'BUG','end':'END'},
                                        {'root':'work','path':'spec/base.tla'}],
                        'evidence':['repro/test_bugMC-1_fixture.sh']}
                    if 'MC-1' in pf.index(work):
                        proposal['revises'] = pf.record_digest(work, 'MC-1')
                    (fdir/'issue.json').write_text(json.dumps(proposal))
                    Path(log).write_text('- **Source**: MC\\n- **Novelty**: NEW\\n\\n'
                                         '## Description\\nFixture result; no real verification performed.\\n'
                                         'VERDICT: REPRODUCED\\n')
                """)
        )
        script = adapter.read_text()
        old = '    printf \'{"generated_by":"consolidate","findings":[]}\\n\' > "$SPECULA_WORK_DIR/spec/candidates.json"\n'
        self.assertIn(old, script)
        script = script.replace(
            old, f'    python3 {shlex.quote(str(helper))} confirm "$prompt" "$log" "$0"\n    exit 0\n'
        )
        script = script.replace(
            "esac\n",
            'esac\nif [ "$SPECULA_PHASE" = spec_validation ]; then\n'
            f'    python3 {shlex.quote(str(helper))} validate "$SPECULA_WORK_DIR" "$log" "$0"\nfi\n',
        )
        adapter.write_text(script)
        guidance = fixture.work / "guidance.md"
        guidance.write_text("Fixture reply scope.\n")
        args = [
            "run",
            "--orchestration=phased",
            "--agent=fake",
            f"--artifact={fixture.source}",
            f"--guidance={guidance}",
            "--skip-classification",
            "--skip-repair-loop",
            "footest",
        ]
        fixture.change_source("BUG\naccept reply\nEND\nlogging v1\n")
        result = fixture.helper.run_cli(fixture.root, args, cwd=fixture.work)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        first_run = (fixture.root / "runs/latest").resolve()
        first = first_run / "footest/.specula-output"
        original = findings.load(first, "MC-1")
        self.assertTrue(original["reusable"])
        self.assertFalse((first_run / "ci-input.json").exists())
        self.assertFalse((first / "ci-verdict.json").exists())

        adapter.with_suffix(".reuse").touch()
        fixture.change_source("BUG\naccept reply\nEND\nlogging v2\n")
        result = fixture.helper.run_cli(fixture.root, [*args, f"--findings-from={first}"], cwd=fixture.work)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        second_run = (fixture.root / "runs/latest").resolve()
        second = second_run / "footest/.specula-output"
        self.assertEqual(findings.load(second, "MC-1"), original)
        self.assertIn("historical conclusion reused", (second / "confirmed-bugs.md").read_text())
        self.assertEqual(adapter.with_suffix(".confirmation-count").read_text(), "x")
        self.assertFalse((second_run / "ci-input.json").exists())
        self.assertFalse((second / "ci-verdict.json").exists())
        configuration = json.loads((second_run / "run.json").read_text())["resume_configuration"]
        self.assertEqual(configuration["findings_from"], str(first))

        fixture.change_source("BUG\nchanged reply logic\nEND\nlogging v2\n")
        result = fixture.helper.run_cli(fixture.root, [*args, f"--findings-from={second}"], cwd=fixture.work)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        third_run = (fixture.root / "runs/latest").resolve()
        third = third_run / "footest/.specula-output"
        self.assertEqual(adapter.with_suffix(".confirmation-count").read_text(), "xx")
        self.assertEqual(findings.load(third, "MC-1")["origin_run"], third_run.name)
        self.assertNotIn("historical conclusion reused", (third / "confirmed-bugs.md").read_text())

        # A fresh invocation of this same run must also handle in-place source edits.
        previous_record = findings.record_digest(third, "MC-1")
        fixture.change_source("BUG\nchanged reply logic again\nEND\nlogging v2\n")
        result = fixture.helper.run_cli(
            fixture.root,
            [*args, f"--findings-from={second}", f"--run-id={third_run.name}", "--fresh-context"],
            cwd=fixture.work,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((fixture.root / "runs/latest").resolve(), third_run)
        self.assertEqual(adapter.with_suffix(".confirmation-count").read_text(), "xxx")
        self.assertNotEqual(findings.record_digest(third, "MC-1"), previous_record)
        self.assertEqual(findings.check(third, fixture.source, "MC-1"), [])
        self.assertNotIn("historical conclusion reused", (third / "confirmed-bugs.md").read_text())

    def _invalid_issue_run(self, *, interrupt_mc2: bool) -> tuple[fixtures.IncrementalCLI, Path, Path, int]:
        """MC-1 keeps an over-long title after its one correction; MC-2 is valid."""
        fixture = fixtures.IncrementalCLI()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        adapter = fixture.helper._ci_init_adapter(fixture.root)
        self.assertEqual(adapter, fixture.adapter)
        helper = adapter.with_suffix(".issue.py")
        helper.write_text(
            "import json, sys\nfrom pathlib import Path\n"
            + textwrap.dedent("""\
                mode, location, log, adapter = sys.argv[1:5]
                location, adapter = Path(location), Path(adapter)
                def bump(name):
                    count = adapter.with_suffix('.' + name)
                    count.write_text(count.read_text() + 'x' if count.exists() else 'x')
                    return len(count.read_text())
                if mode == 'validate':
                    work = location
                    (work/'spec/ce.txt').write_text('Fixture counterexample, no semantic check.\\n')
                    candidates = [{'id': fid, 'source': 'model-checking', 'title': 'Fixture ' + fid,
                                   'invariant': 'ReplySafety', 'config': 'spec/MC.cfg',
                                   'counterexample': 'spec/ce.txt'} for fid in ('MC-1', 'MC-2')]
                    (work/'spec/findings.json').write_text(json.dumps({'findings': candidates}))
                    raise SystemExit(0)
                if location.name == '.consolidate.prompt.md':
                    work = location.parent.parent
                    (work/'spec/candidates.json').write_text((work/'spec/findings.json').read_text())
                    Path(log).write_text('Fixture consolidation completed.\\n')
                    raise SystemExit(0)
                resume = Path(sys.argv[5])
                fdir, work, stem = location.parent, location.parent.parent.parent, location.name
                fid = fdir.name
                if stem == 'turn01_A-issue.prompt.md':
                    bump(fid + '-issue')
                    with adapter.with_suffix('.issue-sessions').open('a') as sessions:
                        sessions.write(resume.read_text())
                    Path(log).write_text('Could not shorten the fixture title.\\n')
                    raise SystemExit(0)
                if bump(fid + '-confirm') == 1:
                    resume.write_text('fixture-session-' + fid + '\\n')
                    if adapter.with_suffix('.interrupt-' + fid).exists():
                        Path(log).write_text('interrupted\\n')
                        raise SystemExit(9)
                (work/'repro').mkdir(exist_ok=True)
                repro = 'repro/test_bug' + fid + '_fixture.sh'
                (work/repro).write_text('#!/bin/sh\\n# Fixture only\\nexit 0\\n')
                proposal = {
                    'id': fid, 'status': 'REPRODUCED', 'title': 'Fixture reply defect ' * (10 if fid == 'MC-1' else 1),
                    'cause': 'Fixture ordering defect', 'trigger': 'Delayed reply', 'consequence': 'Wrong output',
                    'sites': ['logic.txt'], 'actions': ['Reply'], 'invariants': ['ReplySafety'],
                    'premises': ['Fixture evidence only; no live verification.'],
                    'dependencies': [{'root': 'source', 'path': 'logic.txt', 'start': 'BUG', 'end': 'END'},
                                     {'root': 'work', 'path': 'spec/base.tla'}],
                    'evidence': [repro]}
                (fdir/'issue.json').write_text(json.dumps(proposal))
                Path(log).write_text('- **Source**: MC\\n- **Novelty**: NEW\\n\\n'
                                     '## Description\\nFixture result; no real verification performed.\\n'
                                     'VERDICT: REPRODUCED\\n')
                """)
        )
        script = adapter.read_text()
        old = '    printf \'{"generated_by":"consolidate","findings":[]}\\n\' > "$SPECULA_WORK_DIR/spec/candidates.json"\n'
        self.assertIn(old, script)
        script = script.replace(
            old, f'    python3 {shlex.quote(str(helper))} confirm "$prompt" "$log" "$0" "$resume"\n    exit $?\n'
        )
        script = script.replace(
            "esac\n",
            'esac\nif [ "$SPECULA_PHASE" = spec_validation ]; then\n'
            f'    python3 {shlex.quote(str(helper))} validate "$SPECULA_WORK_DIR" "$log" "$0"\nfi\n',
        )
        adapter.write_text(script)
        guidance = fixture.work / "guidance.md"
        guidance.write_text("Fixture reply scope.\n")
        fixture.change_source("BUG\naccept reply\nEND\nlogging v1\n")
        if interrupt_mc2:
            adapter.with_suffix(".interrupt-MC-2").touch()
        args = [
            "run",
            "--orchestration=phased",
            "--agent=fake",
            f"--artifact={fixture.source}",
            f"--guidance={guidance}",
            "--skip-repair-loop",
        ]
        first = fixture.helper.run_cli(fixture.root, [*args, "footest"], cwd=fixture.work)
        run = (fixture.root / "runs/latest").resolve()
        work = run / "footest/.specula-output"
        mc1 = work / "confirmation/MC-1"
        self.assertIn("| 1 | MC-1 | REPRODUCED | yes |", (work / "confirmed-bugs.md").read_text())
        self.assertFalse((mc1 / "issue.json").exists())
        self.assertTrue((mc1 / findings.SET_ASIDE_PROPOSAL).is_file())
        self.assertIn("issue title must be at most 160 characters", (mc1 / "error.txt").read_text())
        self.assertEqual(adapter.with_suffix(".issue-sessions").read_text(), "fixture-session-MC-1\n")
        return fixture, run, work, first.returncode

    def _assert_final(self, adapter: Path, work: Path, mc2_calls: str) -> None:
        """MC-1 ran once plus one correction; only MC-2 was ever retried."""
        self.assertEqual(adapter.with_suffix(".MC-1-confirm").read_text(), "x")
        self.assertEqual(adapter.with_suffix(".MC-1-issue").read_text(), "x")
        self.assertEqual(adapter.with_suffix(".MC-2-confirm").read_text(), mc2_calls)
        self.assertFalse(adapter.with_suffix(".MC-2-issue").exists())
        report = (work / "confirmed-bugs.md").read_text()
        self.assertIn("| 1 | MC-1 | REPRODUCED | yes |", report)
        self.assertIn("| 2 | MC-2 | REPRODUCED | yes |", report)
        self.assertIn("**Persistence**: Not automatically reusable", report)
        self.assertFalse(findings.load(work, "MC-1")["reusable"])
        self.assertTrue(findings.load(work, "MC-2")["reusable"])
        self.assertIn("bug_classification", adapter.with_name(adapter.name + ".phases").read_text().splitlines())
        self.assertTrue((work / "bug-severity.md").is_file())

    def test_invalid_issue_proposal_keeps_verdict_and_reaches_classification(self) -> None:
        fixture, _, work, code = self._invalid_issue_run(interrupt_mc2=False)
        self.assertEqual(code, 0)
        self._assert_final(fixture.adapter, work, "x")

    def test_attach_after_set_aside_does_not_retry_the_proposal(self) -> None:
        fixture, run, work, code = self._invalid_issue_run(interrupt_mc2=True)
        self.assertNotEqual(code, 0)
        self.assertIn("| 2 | MC-2 | INCOMPLETE |", (work / "confirmed-bugs.md").read_text())
        resumed = fixture.helper.run_cli(fixture.root, ["run", f"--run-id={run.name}"], cwd=fixture.work)
        self.assertEqual(resumed.returncode, 0, resumed.stdout + resumed.stderr)
        self._assert_final(fixture.adapter, work, "xx")
