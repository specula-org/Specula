"""Tests for the optional outer-sandbox wrapping in the claude-code adapter (M1.3).

``_maybe_wrap_sandbox`` is the whole opt-in surface: off/unset must leave the
agent argv byte-for-byte (legacy); on must prepend the srt backend while keeping
the inner ``--dangerously-skip-permissions`` (YOLO) flag so the sandbox is one
outer layer, never nested.
"""

from __future__ import annotations

import os
import unittest
from unittest import mock

from specula.adapters.claude_code import _maybe_wrap_sandbox

BASE = ["claude", "--print", "--dangerously-skip-permissions", "--output-format", "json"]


class SandboxWrapTests(unittest.TestCase):
    def test_unset_is_byte_for_byte_unchanged(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("SPECULA_SANDBOX", None)
            self.assertEqual(_maybe_wrap_sandbox(list(BASE), "/tmp/ws"), BASE)

    def test_off_is_unchanged(self) -> None:
        with mock.patch.dict(os.environ, {"SPECULA_SANDBOX": "off"}):
            self.assertEqual(_maybe_wrap_sandbox(list(BASE), "/tmp/ws"), BASE)

    def test_on_wraps_and_preserves_inner_flag(self) -> None:
        with mock.patch.dict(os.environ, {"SPECULA_SANDBOX": "on", "SPECULA_SANDBOX_BACKEND": "/x/backend.mjs"}):
            got = _maybe_wrap_sandbox(list(BASE), "/tmp/ws")
        self.assertEqual(got, ["node", "/x/backend.mjs", "--workspace", "/tmp/ws", "--", *BASE])
        self.assertIn("--dangerously-skip-permissions", got)  # inner YOLO preserved

    def test_on_repo_relative_backend_resolves(self) -> None:
        with mock.patch.dict(os.environ, {"SPECULA_SANDBOX": "on"}, clear=False):
            os.environ.pop("SPECULA_SANDBOX_BACKEND", None)
            got = _maybe_wrap_sandbox(list(BASE), "/tmp/ws")
        backend = got[1]
        self.assertTrue(backend.endswith(os.path.join("scripts", "launch", "sandbox", "backend.mjs")))
        self.assertTrue(os.path.exists(backend))


if __name__ == "__main__":
    unittest.main()
