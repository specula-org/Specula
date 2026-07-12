"""Contract tests for the generated Codex plugin's skill namespace."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import cast
from unittest import mock

from specula import confirmlib as confirmation
from specula import phaselib, skill_install
from specula.skill_refs import CODEX_PLUGIN_NAME

REPO_ROOT = Path(__file__).resolve().parents[2]
SETUP_SCRIPT = REPO_ROOT / "scripts" / "infra" / "setup_codex_plugin.py"


class TestCodexPluginSkillContract(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)

    def generate_plugin(self) -> tuple[Path, dict[str, object]]:
        plugin_root = self.root / "plugin-root"
        subprocess.run(
            [
                sys.executable,
                str(SETUP_SCRIPT),
                "--project-root",
                str(REPO_ROOT),
                "--plugin-root",
                str(plugin_root),
                "--no-install",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        plugin_dir = plugin_root / "plugins" / CODEX_PLUGIN_NAME
        manifest = cast(
            dict[str, object],
            json.loads((plugin_dir / ".codex-plugin" / "plugin.json").read_text()),
        )
        return plugin_dir, manifest

    def production_prompts(self) -> dict[str, tuple[str, tuple[str, ...]]]:
        with mock.patch.dict(os.environ, {"SPECULA_RUN_DIR": ""}):
            ws = phaselib.Workspace(["T"], artifact="/repo", cwd=self.root)
            repair_ws = phaselib.Workspace(["T"], artifact="/repo", cwd=self.root, opts={"repair": True})
            recheck_ws = phaselib.Workspace(
                ["T"],
                artifact="/repo",
                cwd=self.root,
                opts={"recheck": True, "max_repair_rounds": "2"},
            )
            prompts: dict[str, tuple[str, tuple[str, ...]]] = {
                "code analysis": (
                    phaselib.PHASES["code_analysis"].build_prompt(ws, "T|owner/repo|Go|reference"),
                    ("code-analysis",),
                ),
                "spec generation": (
                    phaselib.PHASES["spec_generation"].build_prompt(ws, "T"),
                    ("spec-generation",),
                ),
                "harness generation": (
                    phaselib.PHASES["harness_generation"].build_prompt(ws, "T"),
                    ("harness-generation",),
                ),
                "validation": (
                    phaselib.PHASES["spec_validation"].build_prompt(ws, "T"),
                    ("validation-workflow", "tla-trace-workflow", "tla-checking-workflow"),
                ),
                "validation repair": (
                    phaselib.PHASES["spec_validation"].build_prompt(repair_ws, "T"),
                    (
                        "bug-confirmation",
                        "validation-workflow",
                        "tla-trace-workflow",
                        "tla-checking-workflow",
                    ),
                ),
                "legacy confirmation": (
                    phaselib.PHASES["bug_confirmation"].build_prompt(ws, "T"),
                    ("bug-confirmation",),
                ),
                "confirmation recheck": (
                    phaselib.PHASES["bug_confirmation"].build_prompt(recheck_ws, "T"),
                    ("bug-confirmation",),
                ),
                "classification": (
                    phaselib.PHASES["bug_classification"].build_prompt(ws, "T"),
                    ("bug-classification",),
                ),
            }

            cfg = confirmation.ConfirmConfig(
                name="T",
                ws=ws,
                adapter=Path("/adapter"),
                repo_dir="/repo",
            )
            finding = confirmation.Finding(
                {"id": "MC-1", "title": "finding", "summary": "summary"},
                ws.work_dir("T") / "confirmation" / "MC-1",
            )
            prompts["per-finding confirmation"] = (
                confirmation.prompt_reproduce(cfg, finding, "/repo"),
                ("bug-confirmation",),
            )

            captured: list[str] = []
            spec_dir = ws.work_dir("T") / "spec"
            spec_dir.mkdir(parents=True, exist_ok=True)

            def run(
                _adapter: Path,
                prompt: str,
                *_args: object,
                **_kwargs: object,
            ) -> tuple[int, str]:
                captured.append(prompt)
                (spec_dir / "candidates.json").write_text('{"generated_by":"consolidate","findings":[]}')
                return (0, "")

            with mock.patch.object(confirmation, "run_agent_blocking", run):
                confirmation.consolidate(cfg)
            prompts["confirmation consolidate"] = (captured[0], ("validation-workflow",))
            return prompts

    def test_plugin_only_ids_cover_every_production_prompt(self) -> None:
        plugin_dir, manifest = self.generate_plugin()
        plugin_name = str(manifest["name"])
        self.assertEqual(plugin_name, CODEX_PLUGIN_NAME)

        skills_path = cast(str, manifest["skills"])
        plugin_skill_ids = {
            f"{plugin_name}:{skill.name}" for skill in skill_install.discover_skills(plugin_dir / skills_path)
        }
        prompts = self.production_prompts()

        for label, (prompt, skills) in prompts.items():
            with self.subTest(prompt=label):
                self.assertNotIn("/skills/", prompt)
                self.assertNotIn(".claude/skills", prompt)
                for skill in skills:
                    namespaced = f"{plugin_name}:{skill}"
                    self.assertIn(namespaced, plugin_skill_ids)
                    self.assertIn(f"**{skill}**", prompt)
                    self.assertIn(f"**{namespaced}**", prompt)


if __name__ == "__main__":
    unittest.main()
