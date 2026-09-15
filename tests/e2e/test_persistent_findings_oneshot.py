"""Ordinary pipeline persistence/reuse with fixture findings, no live verification."""

from __future__ import annotations

import json
import shlex
import textwrap
import unittest

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
