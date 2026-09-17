"""Real CLI publication with fixture confirmation; no LLM or target verification."""

from __future__ import annotations

import json
import shlex
import unittest
from pathlib import Path

import test_incremental_ci as fixtures

from specula import persistent_findings
from specula.ci_store import CIStore


class IssueReuseCLI(unittest.TestCase):
    def test_record_unrelated_update_reuse_invalidation_and_fix(self) -> None:
        fixture = fixtures.IncrementalCLI()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.initialize()
        Path(f"{fixture.adapter}.nochange").touch()
        helper = fixture.adapter.with_suffix(".issues.py")
        helper.write_text(
            "import json, subprocess, sys\nfrom pathlib import Path\n"
            f"sys.path.insert(0, {str(fixture.root / 'src')!r})\n"
            "from specula import persistent_findings\n"
            "work, adapter = map(Path, sys.argv[1:])\n"
            "mode = Path(str(adapter) + '.issue-mode').read_text()\n"
            "path = work / 'spec/final-result.json'\n"
            "document = json.loads(path.read_text())\n"
            "if mode == 'record':\n"
            "    counter = Path(str(adapter) + '.analysis-count')\n"
            "    counter.write_text(counter.read_text() + 'x' if counter.exists() else 'x')\n"
            "    proposal = {\n"
            "      'id': 'MC-1', 'status': 'REPRODUCED', 'source': 'model-checking', 'title': 'Fixture unresolved reply',\n"
            "      'cause': 'Fixture ordering defect', 'trigger': 'Delayed fixture reply',\n"
            "      'consequence': 'Wrong fixture result', 'sites': ['logic.txt'],\n"
            "      'actions': ['Reply'], 'invariants': ['ReplySafety'],\n"
            "      'premises': ['Fixture only; no real verification performed.'],\n"
            "      'dependencies': [{'root':'source','path':'logic.txt','start':'BUG','end':'END'},\n"
            "                       {'root':'work','path':'spec/base.tla'}],\n"
            "      'evidence': ['spec/confirmation-fixture.md']}\n"
            "    document['findings'][0].update({k: proposal[k] for k in ('title','source','cause','trigger','consequence')})\n"
            "    document['findings'][0]['persistence'] = {k: proposal[k] for k in ('sites','actions','invariants','premises','dependencies')}\n"
            "elif mode == 'reuse':\n"
            "    document['findings'] = [{'id':'MC-1', 'reuse':'Same fixture mechanism, consequence and premises.'}]\n"
            "path.write_text(json.dumps(document))\n"
        )
        fixture.adapter.write_text(
            fixture.adapter.read_text().replace(
                '    if [ -f "$0.omit-verdict" ];',
                f'    python3 {shlex.quote(str(helper))} "$SPECULA_WORK_DIR" "$0"\n    if [ -f "$0.omit-verdict" ];',
            )
        )
        mode = Path(f"{fixture.adapter}.issue-mode")
        mode.write_text("record")
        fixture.finding_status("REPRODUCED")
        fixture.change_source("BUG\naccept old reply\nEND\nlogging v1\n")
        first = fixture.run_ci("--incremental", "--agent=fake")
        self.assertEqual(first.returncode, 2, first.stdout + first.stderr)
        baseline = (fixture.ci / "current/model").resolve()
        original = persistent_findings.load(baseline, "MC-1")
        self.assertTrue(original["reusable"])
        self.assertEqual(persistent_findings.lookup(baseline, ["ReplySafety"])[0]["id"], "MC-1")

        mode.write_text("reuse")
        Path(f"{fixture.adapter}.findings").unlink()
        fixture.change_source("BUG\naccept old reply\nEND\nlogging v2\n")
        reused = fixture.run_ci("--incremental", "--agent=fake")
        self.assertEqual(reused.returncode, 2, reused.stdout + reused.stderr)
        current = (fixture.ci / "current/model").resolve()
        self.assertNotEqual(current, baseline)
        self.assertEqual(persistent_findings.load(current, "MC-1"), original)
        self.assertEqual(Path(f"{fixture.adapter}.analysis-count").read_text(), "x")
        report = (current / "ci-report.md").read_text()
        self.assertIn("historical conclusion reused", report)
        self.assertEqual(CIStore(fixture.ci).current()["verdict"], "FAIL")
        entry = json.loads((current / "ci-verdict.json").read_text())["findings"][0]
        self.assertEqual(entry["reuse"]["run_id"], fixture.latest().name)
        bundled = current / original["evidence"][0]["path"]
        self.assertIn(original["origin_run"], bundled.read_text())

        # The explicit reuse decision remains valid across another unrelated update.
        Path(f"{fixture.adapter}.findings").write_text(
            json.dumps([{"id": "MC-1", "status": "REPRODUCED", "evidence": "spec/finding-reuse/MC-1.md"}])
        )
        fixture.change_source("BUG\naccept old reply\nEND\nlogging v3\n")
        listed = fixture.run_ci("--incremental", "--agent=fake")
        self.assertEqual(listed.returncode, 2, listed.stdout + listed.stderr)
        current = (fixture.ci / "current/model").resolve()
        self.assertTrue(json.loads((fixture.latest() / "ci-result.json").read_text())["complete"])
        entry = json.loads((current / "ci-verdict.json").read_text())["findings"][0]
        self.assertEqual(entry["reuse"]["run_id"], fixture.latest().name)
        self.assertEqual(CIStore(fixture.ci).current()["verdict"], "FAIL")

        # A relevant change invalidates the old conclusion before any costly
        # fixture confirmation. A failed run cannot advance the baseline.
        fixture.change_source("BUG\nvalidate then accept\nEND\nlogging v2\n")
        rejected = fixture.run_ci("--incremental", "--agent=fake", "--transient-resumes=0")
        self.assertNotEqual(rejected.returncode, 0)
        self.assertEqual((fixture.ci / "current/model").resolve(), current)
        self.assertFalse((fixture.latest() / "ci-result.json").exists())
        work = fixture.latest() / "footest/.specula-output"
        self.assertFalse((work / persistent_findings.RECEIPTS / "MC-1.json").exists())
        self.assertFalse((work / "spec/issue-input/MC-1.json").exists())

        mode.write_text("fixed")
        fixture.finding_status("FIXED")
        fixed = fixture.run_ci("--incremental", "--agent=fake")
        self.assertEqual(fixed.returncode, 0, fixed.stdout + fixed.stderr)
        current = (fixture.ci / "current/model").resolve()
        self.assertEqual(CIStore(fixture.ci).current()["verdict"], "PASS")
        self.assertEqual(persistent_findings.lookup(current, ["ReplySafety"]), [])
        self.assertFalse((current / persistent_findings._record_path("MC-1")).exists())
        self.assertFalse((current / persistent_findings.DIRECTORY / "evidence/MC-1").exists())
