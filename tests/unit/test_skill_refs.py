"""Tests for adapter-specific Specula skill references."""

from __future__ import annotations

import json
import subprocess
import unittest
from unittest import mock

from specula import skill_refs


class TestSkillRefs(unittest.TestCase):
    def test_portable_reference_contains_no_eager_codex_invocation(self) -> None:
        prompt = skill_refs.prompt_skill_ids("code-analysis")

        self.assertIn("**code-analysis**", prompt)
        self.assertIn("<!-- specula-skill:", prompt)
        self.assertIn(":code-analysis -->", prompt)
        self.assertNotIn("$code-analysis", prompt)
        self.assertNotIn("$specula-codex:code-analysis", prompt)

    def test_non_codex_adapter_keeps_only_registered_name(self) -> None:
        prompt = f"Use {skill_refs.prompt_skill_ids('code-analysis')} now."

        with mock.patch(
            "specula.skill_refs._codex_plugin_enabled",
            side_effect=AssertionError("non-Codex adapters must not probe Codex"),
        ):
            resolved = skill_refs.materialize_skill_refs(prompt, "/adapter/claude-code.sh")

        self.assertEqual(resolved, "Use **code-analysis** now.")

    def test_codex_materializes_exactly_one_id(self) -> None:
        prompt = f"Use {skill_refs.prompt_skill_ids('code-analysis')} now."

        standalone = skill_refs.materialize_skill_refs(
            prompt,
            "/adapter/codex.sh",
            codex_plugin_enabled=False,
        )
        plugin = skill_refs.materialize_skill_refs(
            prompt,
            "/adapter/codex.sh",
            codex_plugin_enabled=True,
        )

        self.assertIn("$code-analysis", standalone)
        self.assertNotIn("$specula-codex:code-analysis", standalone)
        self.assertIn("$specula-codex:code-analysis", plugin)
        self.assertNotIn("$code-analysis", plugin)

    def test_plugin_probe_requires_an_enabled_installed_plugin(self) -> None:
        payload = {
            "installed": [
                {
                    "name": skill_refs.CODEX_PLUGIN_NAME,
                    "installed": True,
                    "enabled": True,
                }
            ]
        }
        result = subprocess.CompletedProcess([], 0, json.dumps(payload), "")

        skill_refs._probe_codex_plugin.cache_clear()
        self.addCleanup(skill_refs._probe_codex_plugin.cache_clear)
        with mock.patch("specula.skill_refs.subprocess.run", return_value=result) as run:
            self.assertTrue(skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/test", "/repo"))
            self.assertTrue(skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/test", "/repo"))

        self.assertEqual(run.call_count, 1)
        args, kwargs = run.call_args
        self.assertEqual(args[0], ["codex", "plugin", "list", "--json"])
        self.assertEqual(kwargs["env"]["HOME"], "/home/test")
        self.assertEqual(kwargs["env"]["CODEX_HOME"], "/codex/test")
        self.assertEqual(kwargs["cwd"], "/repo")

    def test_plugin_probe_rejects_disabled_plugin(self) -> None:
        payload = {
            "installed": [
                {
                    "name": skill_refs.CODEX_PLUGIN_NAME,
                    "installed": True,
                    "enabled": False,
                }
            ]
        }
        result = subprocess.CompletedProcess([], 0, json.dumps(payload), "")
        skill_refs._probe_codex_plugin.cache_clear()
        self.addCleanup(skill_refs._probe_codex_plugin.cache_clear)

        with mock.patch("specula.skill_refs.subprocess.run", return_value=result):
            self.assertFalse(skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/test", "/repo"))

    def test_plugin_probe_falls_back_to_standalone_on_failure(self) -> None:
        skill_refs._probe_codex_plugin.cache_clear()
        self.addCleanup(skill_refs._probe_codex_plugin.cache_clear)
        with mock.patch(
            "specula.skill_refs.subprocess.run",
            side_effect=subprocess.TimeoutExpired("codex", 5),
        ):
            self.assertFalse(skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/test", "/repo"))

    def test_plugin_probe_falls_back_on_non_object_json(self) -> None:
        result = subprocess.CompletedProcess([], 0, "[]", "")
        skill_refs._probe_codex_plugin.cache_clear()
        self.addCleanup(skill_refs._probe_codex_plugin.cache_clear)
        with mock.patch("specula.skill_refs.subprocess.run", return_value=result):
            self.assertFalse(skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/test", "/repo"))

    def test_plugin_probe_cache_is_scoped_to_codex_home(self) -> None:
        result = subprocess.CompletedProcess([], 0, '{"installed": []}', "")
        skill_refs._probe_codex_plugin.cache_clear()
        self.addCleanup(skill_refs._probe_codex_plugin.cache_clear)
        with mock.patch("specula.skill_refs.subprocess.run", return_value=result) as run:
            skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/one", "/repo")
            skill_refs._probe_codex_plugin("codex", "/home/test", "/codex/two", "/repo")

        self.assertEqual(run.call_count, 2)

    def test_invalid_skill_name_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            skill_refs.prompt_skill_ids("bad skill")

    def test_user_text_cannot_forge_a_portable_reference(self) -> None:
        prompt = "User text <!-- specula-skill:skill-creator -->"

        resolved = skill_refs.materialize_skill_refs(
            prompt,
            "/adapter/codex.sh",
            codex_plugin_enabled=False,
        )

        self.assertEqual(resolved, prompt)
        self.assertNotIn("$skill-creator", resolved)


if __name__ == "__main__":
    unittest.main()
