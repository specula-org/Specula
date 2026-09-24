"""Standalone Lite installation, runtime preparation, and process evidence."""

from __future__ import annotations

import hashlib
import importlib.util
import io
import json
import os
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
import zipfile
from pathlib import Path
from types import ModuleType
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SKILL = ROOT / "skills/specula-lite"


def load_module(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location("lite_test_helper", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class LiteSkillTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.installed = self.root / "installed skill"
        shutil.copytree(SKILL, self.installed, ignore=shutil.ignore_patterns("__pycache__"))
        self.cache = self.root / "cache"
        self.environment = {**os.environ, "SPECULA_LITE_CACHE": str(self.cache)}
        self.prepare = load_module(self.installed / "scripts/prepare.py")

    def test_bundle_matches_shared_sources(self) -> None:
        bundler = load_module(ROOT / "scripts/infra/bundle_lite.py")
        self.assertEqual((self.installed / "assets/shared.zip").read_bytes(), bundler.bundle())

    def test_copied_skill_reads_counterexample_without_repo_or_site_packages(self) -> None:
        trace = self.root / "counterexample.json"
        shutil.copyfile(ROOT / "tools/inv_checking_tool/tests/test_data/trace.json", trace)
        log = self.root / "check.log"
        log.write_text("Error: Invariant Safety is violated.\nCounterExample written: counterexample.json\n")
        result = subprocess.run(
            [sys.executable, "-S", str(self.installed / "scripts/read_tlc.py"), str(log), "--summary", "--json"],
            cwd=self.root,
            env=self.environment,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        summary = json.loads(result.stdout)
        self.assertGreater(summary["trace_length"], 0)
        self.assertTrue(summary["actions"])
        guides = next(self.cache.glob("shared-*")) / "skills"
        for path in (
            "code_analysis/guide.md",
            "spec_generation/references/base-spec-methodology.md",
            "tla-checking-workflow/references/spec-fidelity-checklist.md",
            "bug-confirmation/phases/02-reproduction.md",
            "bug-classification/guide.md",
        ):
            self.assertEqual((guides / path).read_bytes(), (ROOT / "skills" / path).read_bytes())
        self.assertFalse(list(self.cache.glob("*.jar")))

    def test_preparation_reuses_valid_runtime_offline(self) -> None:
        self.cache.mkdir()
        jar = self.cache / "test.jar"
        jar.write_bytes(b"pinned jar")
        checksum = hashlib.sha256(jar.read_bytes()).hexdigest()
        with (
            mock.patch.dict(os.environ, self.environment),
            mock.patch.object(self.prepare, "ensure_java", return_value="/existing/java"),
            mock.patch.object(self.prepare, "JARS", [(jar.name, "https://unused.invalid/jar", checksum)]),
            mock.patch.object(self.prepare.urllib.request, "urlopen", side_effect=AssertionError("network used")),
        ):
            first = self.prepare.prepare()
            second = self.prepare.prepare()
        self.assertEqual(first, second)
        self.assertEqual(first["jars"], [str(jar)])
        self.assertTrue((Path(first["guides"]) / "code_analysis/guide.md").is_file())

    def test_download_rejects_checksum_mismatch_without_overwriting(self) -> None:
        destination = self.root / "tool.jar"
        destination.write_bytes(b"previous")
        with (
            mock.patch.object(self.prepare.urllib.request, "urlopen", return_value=io.BytesIO(b"corrupt")),
            self.assertRaisesRegex(RuntimeError, "Checksum mismatch"),
        ):
            self.prepare.download("https://example.invalid/tool", destination, "0" * 64)
        self.assertEqual(destination.read_bytes(), b"previous")
        self.assertEqual(sorted(path.name for path in self.root.iterdir()), ["installed skill", "tool.jar"])

    @unittest.skipUnless(os.name == "posix", "fixture uses a POSIX executable")
    def test_missing_java_is_prepared_without_system_install(self) -> None:
        archive = self.root / "jre.tar.gz"
        executable = b"#!/bin/sh\necho 'openjdk version \"21.0.12\"' >&2\n"
        with tarfile.open(archive, "w:gz") as bundle:
            entry = tarfile.TarInfo("jre/bin/java")
            entry.size = len(executable)
            entry.mode = 0o755
            bundle.addfile(entry, io.BytesIO(executable))
        checksum = hashlib.sha256(archive.read_bytes()).hexdigest()
        with (
            mock.patch.dict(os.environ, {"SPECULA_LITE_CACHE": str(self.cache), "PATH": ""}, clear=True),
            mock.patch.object(self.prepare.platform, "system", return_value="Linux"),
            mock.patch.object(self.prepare.platform, "machine", return_value="x86_64"),
            mock.patch.object(self.prepare, "JAVA_HASHES", {("linux", "x64"): checksum}),
            mock.patch.object(self.prepare.urllib.request, "urlopen", return_value=io.BytesIO(archive.read_bytes())),
        ):
            java = Path(self.prepare.ensure_java())
        self.assertTrue(java.is_relative_to(self.cache))
        self.assertTrue(self.prepare.java_works(str(java)))

    def test_archives_cannot_write_outside_cache(self) -> None:
        archive = self.root / "bad.zip"
        with zipfile.ZipFile(archive, "w") as bundle:
            bundle.writestr("../escaped", "bad")
        with self.assertRaises(ValueError):
            self.prepare.unpack(archive, self.cache / "shared")
        self.assertFalse((self.cache / "shared").exists())
        self.assertFalse((self.cache / "escaped").exists())

    @unittest.skipUnless(os.name == "posix", "symbolic-link fixture")
    def test_jre_symlink_cannot_escape(self) -> None:
        archive = self.root / "bad.tar.gz"
        with tarfile.open(archive, "w:gz") as bundle:
            link = tarfile.TarInfo("jre/escape")
            link.type = tarfile.SYMTYPE
            link.linkname = "../../outside"
            bundle.addfile(link)
        with self.assertRaises(ValueError):
            self.prepare.unpack(archive, self.cache / "java")
        self.assertFalse((self.cache / "java").exists())


@unittest.skipUnless(os.name == "posix", "process fixtures use POSIX executables and signals")
class LiteRunnerTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.runner = self.root / "tlc.py"
        shutil.copyfile(SKILL / "scripts/tlc.py", self.runner)
        self.java = self.root / "fake java"
        (self.root / "prepare.py").write_text(
            f"def prepare():\n    return {{'java': {str(self.java)!r}, 'jars': ['test.jar']}}\n"
        )
        self.spec = self.root / "model directory" / "Test.tla"
        self.spec.parent.mkdir()
        self.spec.write_text("fixture\n")
        (self.spec.parent / "Test.cfg").write_text("fixture\n")
        self.log = self.root / "check.log"

    def fake_java(self, body: str) -> None:
        self.java.write_text(f"#!{sys.executable}\n{body}\n")
        self.java.chmod(0o755)

    def command(self) -> list[str]:
        return [
            sys.executable,
            str(self.runner),
            "check",
            str(self.spec),
            "--config",
            "Test.cfg",
            "--log",
            str(self.log),
        ]

    def test_runner_preserves_failure_output_exit_and_command(self) -> None:
        self.fake_java("import sys\nprint('counterexample output')\nprint('diagnostic', file=sys.stderr)\nsys.exit(12)")
        result = subprocess.run(
            self.command() + ["--", "-simulate", "num=10"], cwd=self.root, capture_output=True, text=True
        )
        self.assertEqual(result.returncode, 12, result.stderr)
        self.assertIn("counterexample output", self.log.read_text())
        self.assertIn("diagnostic", self.log.read_text())
        record = json.loads(self.log.with_name("check.log.run.json").read_text())
        self.assertEqual(record["exit_code"], 12)
        self.assertEqual(record["cwd"], str(self.spec.parent))
        self.assertEqual(record["command"][-3:], ["-simulate", "num=10", "Test.tla"])
        before = self.log.read_bytes()
        repeated = subprocess.run(self.command(), cwd=self.root, capture_output=True, text=True)
        self.assertNotEqual(repeated.returncode, 0)
        self.assertEqual(self.log.read_bytes(), before)

    def test_termination_stops_child_and_records_incomplete_execution(self) -> None:
        self.fake_java("import time\nprint('started', flush=True)\ntime.sleep(120)")
        with subprocess.Popen(self.command(), cwd=self.root, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
            try:
                deadline = time.monotonic() + 10
                while time.monotonic() < deadline:
                    if self.log.exists() and "started" in self.log.read_text():
                        break
                    time.sleep(0.02)
                else:
                    self.fail("fixture child did not start")
                record = json.loads(self.log.with_name("check.log.run.json").read_text())
                process.send_signal(signal.SIGTERM)
                process.communicate(timeout=10)
                self.assertEqual(process.returncode, 143)
                with self.assertRaises(ProcessLookupError):
                    os.kill(record["pid"], 0)
                result = json.loads(self.log.with_name("check.log.run.json").read_text())
                self.assertTrue(result["interrupted"])
                self.assertEqual(result["exit_code"], 143)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()


if __name__ == "__main__":
    unittest.main()
