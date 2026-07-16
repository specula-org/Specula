"""Behavior tests for the agent adapters (claude-code, codex, copilot-cli, opencode, pi).

These pin the *command-construction contract*: given the launcher-facing flags,
what does each adapter invoke the underlying CLI with, which flags map/skip, and
how does argument validation behave. This is the only coverage of that contract
now that the characterization goldens are gone — a wrong flag here silently
breaks every agent call.

Each case runs the real adapter as a subprocess with a fake `claude`/`codex`/
`copilot`/`opencode`/`pi` on PATH that records the argv (and, for Python adapters, stdin + the exported
CLAUDE_CONFIG_DIR + a session-env marker) it observed, then asserts on the
recording. All adapters are exercised through their shipped launch scripts.

stdlib unittest, collected natively by pytest:

    uv run python -m unittest tests.unit.test_adapters -v
"""

from __future__ import annotations

import contextlib
import json
import os
import signal
import sqlite3
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from fnmatch import fnmatchcase
from pathlib import Path
from typing import Any, TypedDict

REPO_ROOT = Path(__file__).resolve().parents[2]
CLAUDE_PY = REPO_ROOT / "src" / "specula" / "adapters" / "claude_code.py"
OPENCODE_SH = REPO_ROOT / "scripts" / "launch" / "adapters" / "opencode.sh"
PI_SH = REPO_ROOT / "scripts" / "launch" / "adapters" / "pi.sh"
CODEX_SH = REPO_ROOT / "scripts" / "launch" / "adapters" / "codex.sh"
COPILOT_SH = REPO_ROOT / "scripts" / "launch" / "adapters" / "copilot-cli.sh"
EVENT_STREAM_COMMAND = [
    sys.executable,
    "-I",
    "-c",
    (
        "import sys; sys.path.insert(0, sys.argv.pop(1)); "
        "from specula.adapters.utils.event_stream import main; "
        "raise SystemExit(main(sys.argv[1:]))"
    ),
    str(REPO_ROOT / "src"),
]

# A minimal well-formed claude result: the claude adapter parses this for
# .log/.usage.json. codex/copilot don't parse it, so any text is fine for them.
CLAUDE_JSON = {
    "result": "done",
    "total_cost_usd": 0.5,
    "num_turns": 3,
    "duration_ms": 1000,
    "stop_reason": "end_turn",
    "session_id": "",
    "usage": {},
    "modelUsage": {},
}

# env that would otherwise steer the adapters; popped so construction is
# deterministic regardless of the harness's ambient environment.
_VOLATILE = (
    "CLAUDE_CONFIG_DIR",
    "CLAUDE_ALIAS",
    "CLAUDE_EFFORT",
    "CLAUDE_MODEL",
    "COPILOT_MODEL",
    "CODEX_MODEL",
    "CODEX_EFFORT",
    "OPENCODE_MODEL",
    "OPENCODE_EFFORT",
    "OPENCODE_CONFIG",
    "OPENCODE_CONFIG_CONTENT",
    "OPENCODE_PERMISSION",
    "PI_MODEL",
    "PI_EFFORT",
    "CLAUDECODE",
    "CLAUDE_CODE_SSE_PORT",
    "CLAUDE_CODE_ENTRYPOINT",
    "SPECULA_PHASE",
    "SPECULA_WORK_DIR",
    "SPECULA_STOP_GATE",
    "SPECULA_STOP_GATE_WORK_DIR",
    "SPECULA_SANDBOX",
    "SPECULA_SANDBOX_BACKEND",
    "SPECULA_SANDBOX_CONFIG",
    "SPECULA_ACTIVITY_LOG",
    "CODEX_HOME",
    "ADAPTER_EXIT_CODE",
    "COPILOT_HELP_TEXT",
    "ADAPTER_PI_SESSION_FIXTURE",
    "ADAPTER_READY_FILE",
    "ADAPTER_WAIT_SECONDS",
)


class AdapterRun(TypedDict):
    returncode: int
    stdout: str
    stderr: str
    argv: list[str]
    configdir: str
    sessionenv: str
    modelenv: str
    effortenv: str
    vcsenv: str
    opencode_config: str
    opencode_permission: str
    stdin: str | None
    base: Path


class SessionCase(TypedDict):
    name: str
    transcript: str | None  # session JSONL to seed, or None to leave absent
    want: dict[str, int]
    absent: list[str]


class AdapterCase(unittest.TestCase):
    """A tmp sandbox with a fake underlying CLI on PATH that records what the
    adapter invoked it with."""

    def sandbox(self) -> Path:
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return Path(d.name).resolve()

    def _write_fake(self, bindir: Path, name: str, fixture: Path, record_extra: bool) -> None:
        """A stub CLI that records its argv (and, when record_extra, the exported
        CLAUDE_CONFIG_DIR + CLAUDECODE it sees + its stdin) into side channels,
        then prints the fixture so the adapter's post-processing runs."""
        bindir.mkdir(parents=True, exist_ok=True)
        lines = [
            "#!/usr/bin/env bash",
        ]
        if name == "copilot":
            lines += [
                'if [[ "${1:-}" == "--help" ]]; then',
                '  printf "%s\\n" "${COPILOT_HELP_TEXT:-}"',
                "  exit 0",
                "fi",
            ]
        lines.append('printf "%s\\n" "$@" > "${ADAPTER_ARGV_FILE:-/dev/null}"')
        model_var = {
            "claude": "CLAUDE_MODEL",
            "codex": "CODEX_MODEL",
            "copilot": "COPILOT_MODEL",
            "opencode": "OPENCODE_MODEL",
            "pi": "PI_MODEL",
        }.get(name)
        effort_var = {
            "claude": "CLAUDE_EFFORT",
            "codex": "CODEX_EFFORT",
            "opencode": "OPENCODE_EFFORT",
            "pi": "PI_EFFORT",
        }.get(name)
        if model_var:
            lines.append(f'printf "%s\\n" "${{{model_var}-<unset>}}" > "${{ADAPTER_MODEL_ENV_FILE:-/dev/null}}"')
        if effort_var:
            lines.append(f'printf "%s\\n" "${{{effort_var}-<unset>}}" > "${{ADAPTER_EFFORT_ENV_FILE:-/dev/null}}"')
        if name == "opencode":
            lines.append('printf "%s\\n" "${OPENCODE_FAKE_VCS-<unset>}" > "${ADAPTER_VCS_ENV_FILE:-/dev/null}"')
            lines.append('printf "%s\\n" "${OPENCODE_CONFIG-<unset>}" > "${ADAPTER_CONFIGDIR_FILE:-/dev/null}"')
            lines.append(
                'printf "%s\\n" "${OPENCODE_PERMISSION-<unset>}" > "${ADAPTER_OPENCODE_PERMISSION_FILE:-/dev/null}"'
            )
            lines.append(
                'if [[ -n "${OPENCODE_CONFIG:-}" && -f "$OPENCODE_CONFIG" ]]; then '
                'cat "$OPENCODE_CONFIG" > "${ADAPTER_OPENCODE_CONFIG_FILE:-/dev/null}"; fi'
            )
        if record_extra:
            if name != "opencode":
                lines.append('printf "%s\\n" "${CLAUDE_CONFIG_DIR:-<unset>}" > "${ADAPTER_CONFIGDIR_FILE:-/dev/null}"')
            lines += [
                'printf "%s\\n" "${CLAUDECODE:-<unset>}" > "${ADAPTER_SESSIONENV_FILE:-/dev/null}"',
                'cat > "${ADAPTER_STDIN_FILE:-/dev/null}"',
            ]
        if name == "pi":
            lines += [
                'if [[ -n "${ADAPTER_PI_SESSION_FIXTURE:-}" ]]; then',
                '  mkdir -p "$TMPDIR/pi-subagent-session-test/run-0"',
                '  cp "$ADAPTER_PI_SESSION_FIXTURE" "$TMPDIR/pi-subagent-session-test/run-0/session.jsonl"',
                "fi",
            ]
        lines += [
            'if [[ -n "${ADAPTER_READY_FILE:-}" ]]; then',
            '  printf "ready\\n" > "$ADAPTER_READY_FILE"',
            '  sleep "${ADAPTER_WAIT_SECONDS:-30}"',
            "fi",
        ]
        lines.append(f"cat {json.dumps(str(fixture))}")
        lines.append('exit "${ADAPTER_EXIT_CODE:-0}"')
        stub = bindir / name
        stub.write_text("\n".join(lines) + "\n")
        stub.chmod(stub.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)

    def run_adapter(
        self,
        cmd: list[str],
        flags: list[str],
        *,
        fake_name: str,
        fixture_text: str | bytes,
        env_extra: dict[str, str] | None = None,
        with_fake: bool = True,
        record_extra: bool = False,
        timeout: float | None = None,
    ) -> AdapterRun:
        base = self.sandbox()
        bindir = base / "bin"
        fixture = base / "fixture.txt"
        if isinstance(fixture_text, bytes):
            fixture.write_bytes(fixture_text)
        else:
            fixture.write_text(fixture_text)
        record = {
            "ADAPTER_ARGV_FILE": base / "argv.txt",
            "ADAPTER_CONFIGDIR_FILE": base / "configdir.txt",
            "ADAPTER_SESSIONENV_FILE": base / "sessionenv.txt",
            "ADAPTER_MODEL_ENV_FILE": base / "modelenv.txt",
            "ADAPTER_EFFORT_ENV_FILE": base / "effortenv.txt",
            "ADAPTER_VCS_ENV_FILE": base / "vcsenv.txt",
            "ADAPTER_OPENCODE_CONFIG_FILE": base / "opencode_config.json",
            "ADAPTER_OPENCODE_PERMISSION_FILE": base / "opencode_permission.json",
            "ADAPTER_STDIN_FILE": base / "stdin.txt",
        }
        env = {k: v for k, v in os.environ.items() if k not in _VOLATILE}
        env["HOME"] = str(base)
        if with_fake:
            self._write_fake(bindir, fake_name, fixture, record_extra)
            env["PATH"] = f"{bindir}:/usr/bin:/bin"
        else:
            env["PATH"] = "/usr/bin:/bin"
        env.update({k: str(v) for k, v in record.items()})
        env.update(env_extra or {})
        proc = subprocess.run(cmd + flags, cwd=str(base), env=env, capture_output=True, text=True, timeout=timeout)

        def read(p: Path) -> str | None:
            return p.read_text() if p.exists() else None

        return {
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "argv": (read(record["ADAPTER_ARGV_FILE"]) or "").splitlines(),
            "configdir": (read(record["ADAPTER_CONFIGDIR_FILE"]) or "").strip(),
            "sessionenv": (read(record["ADAPTER_SESSIONENV_FILE"]) or "").strip(),
            "modelenv": (read(record["ADAPTER_MODEL_ENV_FILE"]) or "").strip(),
            "effortenv": (read(record["ADAPTER_EFFORT_ENV_FILE"]) or "").strip(),
            "vcsenv": (read(record["ADAPTER_VCS_ENV_FILE"]) or "").strip(),
            "opencode_config": read(record["ADAPTER_OPENCODE_CONFIG_FILE"]) or "",
            "opencode_permission": (read(record["ADAPTER_OPENCODE_PERMISSION_FILE"]) or "").strip(),
            "stdin": read(record["ADAPTER_STDIN_FILE"]),
            "base": base,
        }

    def with_prompt_file(self, base: Path, text: str = "the prompt\n") -> str:
        p = base / "prompt.md"
        p.write_text(text)
        return f"--prompt-file={p}"


# ── claude-code (Python port) ────────────────────────────────────────────────
class ClaudeCodeAdapter(AdapterCase):
    CMD = [sys.executable, str(CLAUDE_PY)]
    FIXTURE = json.dumps(CLAUDE_JSON)

    def invoke(self, flags: list[str], *, env_extra: dict[str, str] | None = None) -> AdapterRun:
        return self.run_adapter(
            self.CMD, flags, fake_name="claude", fixture_text=self.FIXTURE, record_extra=True, env_extra=env_extra
        )

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log"]

    def test_base_command_and_default_effort(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base))
        self.assertEqual(r["returncode"], 0)
        # base argv, in order, then the default effort (CLAUDE_EFFORT unset -> max)
        self.assertEqual(
            r["argv"][:5],
            ["--print", "--dangerously-skip-permissions", "--output-format", "json", "--effort"],
        )
        self.assertIn("--effort", r["argv"])
        self.assertEqual(r["argv"][r["argv"].index("--effort") + 1], "max")

    def test_stop_gate_state_and_settings_use_worker_scope(self) -> None:
        base = self.sandbox()
        target = base / "target"
        gate_scope = base / "finding"
        for path in (target, gate_scope):
            state = path / ".stop-gate"
            state.mkdir(parents=True)
            (state / "blocks").write_text("3\n")

        r = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_PHASE": "bug_confirmation_turn",
                "SPECULA_WORK_DIR": str(target),
                "SPECULA_STOP_GATE_WORK_DIR": str(gate_scope),
            },
        )

        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertTrue((target / ".stop-gate" / "blocks").is_file())
        self.assertFalse((gate_scope / ".stop-gate" / "blocks").exists())
        settings = gate_scope / ".stop-gate" / "claude-settings.json"
        self.assertTrue(settings.is_file())
        self.assertEqual(r["argv"][r["argv"].index("--settings") + 1], str(settings))

    def test_effort_model_budget_assembled(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--effort=high", "--model=opus", "--max-budget=10"])
        argv = r["argv"]
        self.assertEqual(argv[argv.index("--effort") + 1], "high")
        self.assertEqual(argv[argv.index("--model") + 1], "opus")
        self.assertEqual(argv[argv.index("--max-budget-usd") + 1], "10")

    def test_effort_default_sentinel_skips_flag(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--effort=default"])
        self.assertNotIn("--effort", r["argv"])

    def test_budget_zero_skips_flag(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--max-budget=0"])
        self.assertNotIn("--max-budget-usd", r["argv"])

    def test_empty_effort_env_still_means_max(self) -> None:
        # bash ${VAR:-default}: an exported-but-empty CLAUDE_EFFORT is still "max".
        base = self.sandbox()
        r = self.invoke(self.base_flags(base), env_extra={"CLAUDE_EFFORT": ""})
        self.assertEqual(r["argv"][r["argv"].index("--effort") + 1], "max")

    def test_explicit_max_wins_over_low_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--effort=max"], env_extra={"CLAUDE_EFFORT": "low"})
        self.assertEqual(r["argv"][r["argv"].index("--effort") + 1], "max")

    def test_explicit_empty_model_effort_clear_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(
            self.base_flags(base) + ["--model=", "--effort="],
            env_extra={"CLAUDE_MODEL": "env-model", "CLAUDE_EFFORT": "low"},
        )
        self.assertNotIn("--model", r["argv"])
        self.assertNotIn("--effort", r["argv"])
        self.assertEqual(r["modelenv"], "<unset>")
        self.assertEqual(r["effortenv"], "<unset>")

    def test_alias_sets_config_dir(self) -> None:
        # HOME is run_adapter's own sandbox (returned as r["base"]); the config
        # dir is derived from it, $HOME/.<alias>.
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base), f"--log={base}/out.log", "--claude-alias=myprofile"])
        self.assertEqual(r["configdir"], f"{r['base']}/.myprofile")

    def test_default_alias_config_dir(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base))  # no --claude-alias
        self.assertEqual(r["configdir"], f"{r['base']}/.claude")

    def test_prompt_delivered_via_stdin(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base, "hello prompt\n"), f"--log={base}/out.log"])
        self.assertEqual(r["stdin"], "hello prompt\n")

    def test_session_env_stripped_before_spawn(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base), env_extra={"CLAUDECODE": "1"})
        self.assertEqual(r["sessionenv"], "<unset>")

    def test_log_and_usage_written(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        log = base / "out.log"
        usage = base / "out.usage.json"
        self.assertEqual(log.read_text(), "done\n")
        self.assertEqual(json.loads(usage.read_text())["total_cost_usd"], 0.5)

    def test_specula_activity_uses_stream_json(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = "\n".join(
            [
                json.dumps(
                    {
                        "type": "assistant",
                        "message": {
                            "content": [{"type": "tool_use", "name": "Read", "input": {"file_path": "kilo.c"}}]
                        },
                    }
                ),
                json.dumps({"type": "result", **CLAUDE_JSON}),
            ]
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=fixture,
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        argv = r["argv"]
        self.assertEqual(argv[argv.index("--output-format") + 1], "stream-json")
        self.assertIn("--verbose", argv)
        self.assertEqual(activity.read_text(), fixture)
        self.assertEqual((base / "out.log").read_text(), "reading kilo.c\ndone\n")
        self.assertEqual(json.loads((base / "out.raw.json").read_text())["type"], "result")

    def test_stream_json_drops_tool_result_echoes(self) -> None:
        # `user` records replay the full text of every file the agent opened. No
        # consumer reads them, and claude keeps its own session transcript.
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        assistant = json.dumps({"type": "assistant", "message": {"content": [{"type": "text", "text": "hi"}]}})
        echo = json.dumps({"type": "user", "message": {"content": [{"type": "tool_result", "content": "x" * 4096}]}})
        result = json.dumps({"type": "result", **CLAUDE_JSON})
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text="\n".join([assistant, echo, result]),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(activity.read_text(), f"{assistant}\n{result}")
        self.assertEqual((base / "out.log").read_text(), "hi\ndone\n")

    def test_stream_json_log_keeps_result_line_structure(self) -> None:
        # agent.log is the human-facing report; collapsing markdown to one line
        # (as `summary` does for the CLI ticker) destroys it.
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        report = "# Findings\n\n1. Bug A\n2. Bug B\n"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=json.dumps({"type": "result", **CLAUDE_JSON, "result": report}),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual((base / "out.log").read_text(), "# Findings\n\n1. Bug A\n2. Bug B\n")

    def test_rate_limit_exits_75(self) -> None:
        base = self.sandbox()
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text="you hit your limit for today",
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 75)

    def test_rate_limit_in_stream_result_exits_75(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=json.dumps(
                {"type": "result", **CLAUDE_JSON, "is_error": True, "result": "you hit your limit for today"}
            ),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 75)

    def test_structured_session_limit_exits_75(self) -> None:
        """Claude 2.1 reports quota exhaustion in a `success` envelope."""
        base = self.sandbox()
        record = {
            "type": "result",
            **CLAUDE_JSON,
            "subtype": "success",
            "is_error": True,
            "api_error_status": 429,
            "terminal_reason": "api_error",
            "result": "You've hit your session limit · resets 7:50am (UTC)",
        }
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=json.dumps(record),
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 75, r["stderr"])

    def test_structured_429_does_not_depend_on_message_wording(self) -> None:
        base = self.sandbox()
        record = {
            "type": "result",
            **CLAUDE_JSON,
            "subtype": "success",
            "is_error": True,
            "api_error_status": 429,
            "terminal_reason": "api_error",
            "result": "Quota temporarily unavailable",
        }
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=json.dumps(record),
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 75, r["stderr"])

    def test_api_error_terminal_reason_recognizes_session_limit(self) -> None:
        base = self.sandbox()
        record = {
            "type": "result",
            **CLAUDE_JSON,
            "subtype": "success",
            "is_error": False,
            "api_error_status": None,
            "terminal_reason": "api_error",
            "result": "You've hit your session limit · resets soon",
        }
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=json.dumps(record),
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 75, r["stderr"])

    def test_rate_limit_plain_text_banner_in_stream_exits_75(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text="Claude usage limit reached — you hit your limit for today\n",
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 75)

    def test_rate_limit_phrase_the_agent_merely_read_is_not_a_rate_limit(self) -> None:
        # The stream capture holds everything the agent said and every diagnostic
        # the CLI printed. Only claude's own verdict may trip EX_TEMPFAIL: 75
        # makes the pipeline stop and wait for a reset that never comes.
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        chatter = json.dumps(
            {
                "type": "assistant",
                "message": {"content": [{"type": "text", "text": "The old log says: you hit your limit for today"}]},
            }
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text="\n".join([chatter, json.dumps({"type": "result", **CLAUDE_JSON})]),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])

    def test_rate_limit_phrase_in_successful_result_is_not_a_rate_limit(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=json.dumps(
                {
                    "type": "result",
                    **CLAUDE_JSON,
                    "is_error": False,
                    "api_error_status": None,
                    "terminal_reason": "completed",
                    "result": "The old log says: You've hit your session limit · resets tomorrow",
                }
            ),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])

    def test_prefixed_diagnostic_does_not_make_successful_quote_a_rate_limit(self) -> None:
        base = self.sandbox()
        result = json.dumps(
            {
                "type": "result",
                **CLAUDE_JSON,
                "is_error": False,
                "api_error_status": None,
                "terminal_reason": "completed",
                "result": "The old log says: You've hit your session limit · resets tomorrow",
            }
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=f"benign CLI diagnostic\n{result}\n",
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])

    @unittest.skipUnless(Path("/dev/full").exists(), "requires /dev/full")
    def test_readable_log_failure_does_not_drop_stream_but_fails_adapter(self) -> None:
        base = self.sandbox()
        log = base / "out.log"
        log.symlink_to("/dev/full")
        activity = base / "out.activity.jsonl"
        assistant = json.dumps({"type": "assistant", "message": {"content": [{"type": "text", "text": "working"}]}})
        result = json.dumps({"type": "result", **CLAUDE_JSON})
        fixture = "\n".join([assistant, result])
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base), f"--log={log}"],
            fake_name="claude",
            fixture_text=fixture,
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 1, r["stderr"])
        self.assertIn("readable log", r["stderr"])
        self.assertEqual(activity.read_text(), fixture)
        self.assertEqual(json.loads((base / "out.raw.json").read_text())["result"], "done")

    def test_raw_activity_failure_drains_cli_without_failing_adapter(self) -> None:
        base = self.sandbox()
        activity = base / "bad-activity"
        activity.mkdir()
        log = base / "out.log"
        result = json.dumps({"type": "result", **CLAUDE_JSON})
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base), f"--log={log}"],
            fake_name="claude",
            fixture_text=result,
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertIn("activity log", r["stderr"])
        self.assertEqual(log.read_text(), "done\n")
        self.assertEqual(json.loads((base / "out.usage.json").read_text())["total_cost_usd"], 0.5)

    def test_raw_activity_failure_preserves_cli_status(self) -> None:
        base = self.sandbox()
        activity = base / "bad-activity"
        activity.mkdir()
        log = base / "out.log"
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base), f"--log={log}"],
            fake_name="claude",
            fixture_text=json.dumps({"type": "result", **CLAUDE_JSON}),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "ADAPTER_EXIT_CODE": "9"},
        )
        self.assertEqual(r["returncode"], 9, r["stderr"])
        self.assertEqual(log.read_text(), "done\n")

    def test_raw_activity_failure_preserves_rate_limit_detection(self) -> None:
        fixtures = [
            json.dumps({"type": "result", **CLAUDE_JSON, "is_error": True, "result": "you hit your limit for today"}),
            "Claude usage limit reached - you hit your limit for today\n",
        ]
        for fixture in fixtures:
            with self.subTest(structured=fixture.startswith("{")):
                base = self.sandbox()
                activity = base / "bad-activity"
                activity.mkdir()
                log = base / "out.log"
                r = self.run_adapter(
                    self.CMD,
                    [self.with_prompt_file(base), f"--log={log}"],
                    fake_name="claude",
                    fixture_text=fixture,
                    record_extra=True,
                    env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
                )
                self.assertEqual(r["returncode"], 75, r["stderr"])

    @unittest.skipUnless(Path("/dev/full").exists(), "requires /dev/full")
    def test_failed_raw_device_is_not_reopened(self) -> None:
        base = self.sandbox()
        log = base / "out.log"
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base), f"--log={log}"],
            fake_name="claude",
            fixture_text=json.dumps({"type": "result", **CLAUDE_JSON}),
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": "/dev/full"},
            timeout=3,
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(log.read_text(), "done\n")

    @unittest.skipUnless(Path("/proc").is_dir(), "requires procfs")
    def test_postprocess_failure_preserves_cli_status(self) -> None:
        for cli_rc, expected in (("0", 1), ("9", 9), ("75", 75)):
            with self.subTest(cli_rc=cli_rc):
                base = self.sandbox()
                activity = base / "out.activity.jsonl"
                fixture = json.dumps({"type": "result", **CLAUDE_JSON})
                r = self.run_adapter(
                    self.CMD,
                    [self.with_prompt_file(base), "--log=/proc/specula-adapter.log"],
                    fake_name="claude",
                    fixture_text=fixture,
                    record_extra=True,
                    env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "ADAPTER_EXIT_CODE": cli_rc},
                )
                self.assertEqual(r["returncode"], expected, r["stderr"])
                self.assertEqual(activity.read_text(), fixture)

    def test_cli_failure_is_propagated(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base), env_extra={"ADAPTER_EXIT_CODE": "9"})
        self.assertEqual(r["returncode"], 9)

    def test_nonutf8_output_degrades_gracefully(self) -> None:
        # deliberate deviation from the bash (which died on non-UTF-8 output):
        # decode with errors="replace" -> exit 0, .usage.json = parse_failed.
        base = self.sandbox()
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="claude",
            fixture_text=b"\xff\xfe not valid utf-8",
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 0)
        self.assertEqual(json.loads((base / "out.usage.json").read_text()), {"error": "parse_failed"})

    def test_missing_claude_exits_command_not_found(self) -> None:
        base = self.sandbox()
        r = self.run_adapter(
            self.CMD, self.base_flags(base), fake_name="claude", fixture_text="", with_fake=False, record_extra=True
        )
        self.assertEqual(r["returncode"], 127)
        self.assertEqual(json.loads((base / "out.usage.json").read_text()), {"error": "parse_failed"})

    def test_prompt_xor_prompt_file(self) -> None:
        base = self.sandbox()
        r = self.invoke(["--prompt=inline", self.with_prompt_file(base), f"--log={base}/out.log"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("mutually exclusive", r["stderr"])

    def test_neither_prompt_errors(self) -> None:
        base = self.sandbox()
        r = self.invoke([f"--log={base}/out.log"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("one of --prompt or --prompt-file is required", r["stderr"])

    def test_log_required(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base)])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("--log is required", r["stderr"])

    def test_prompt_file_not_found(self) -> None:
        base = self.sandbox()
        r = self.invoke([f"--prompt-file={base}/nope.md", f"--log={base}/out.log"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("prompt file not found", r["stderr"])

    def test_unknown_option(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--bogus"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("unknown option", r["stderr"])

    def test_help(self) -> None:
        r = self.invoke(["--help"])
        self.assertEqual(r["returncode"], 0)
        self.assertIn("claude-code", r["stdout"])
        self.assertIn("--prompt-file", r["stdout"])

    def test_session_usage(self) -> None:
        # non-empty session_id -> _extract_usage rewrites num_turns from the session
        # JSONL. Default fixture uses session_id="", so this is the only coverage.
        assistant = json.dumps({"type": "assistant", "message": {"content": [{"type": "tool_use"}, {"type": "text"}]}})
        assistant_tool = json.dumps({"type": "assistant", "message": {"content": [{"type": "tool_use"}]}})
        user = json.dumps({"type": "user", "message": {"content": []}})
        noise = '{"type": "tool_result", "huge": "payload with no assistant marker"}'

        cases: list[SessionCase] = [
            {
                # 2 assistant turns, 2 tool_use total; user/tool_result ignored
                "name": "recomputes-from-transcript",
                "transcript": "\n".join([assistant, user, noise, assistant_tool]) + "\n",
                "want": {"num_turns": 2, "num_turns_reported": 9, "num_tool_uses": 2},
                "absent": [],
            },
            {
                # no JSONL on disk -> block skipped, turns untouched
                "name": "missing-transcript-leaves-turns-alone",
                "transcript": None,
                "want": {"num_turns": 9},
                "absent": ["num_turns_reported", "num_tool_uses"],
            },
        ]
        for tc in cases:
            with self.subTest(tc["name"]):
                sid = "sess-123"
                fixture = dict(CLAUDE_JSON, session_id=sid, num_turns=9)
                usage = self._run_with_session(fixture, transcript=tc["transcript"], sid=sid)
                for key, val in tc["want"].items():
                    self.assertEqual(usage[key], val)
                for key in tc["absent"]:
                    self.assertNotIn(key, usage)

    def _run_with_session(self, fixture: dict[str, Any], *, transcript: str | None, sid: str = "") -> dict[str, Any]:
        """Run the claude adapter with HOME==cwd==base so a seeded transcript lands
        where the adapter looks ($HOME/.claude/projects/-<key>). Not via
        run_adapter, which mints its own HOME."""
        base = self.sandbox()
        bindir = base / "bin"
        fixture_file = base / "fixture.txt"
        fixture_file.write_text(json.dumps(fixture))
        self._write_fake(bindir, "claude", fixture_file, record_extra=False)
        (base / "prompt.md").write_text("the prompt\n")
        if transcript is not None:
            key = str(base).replace("/", "-").lstrip("-")
            jsonl = base / ".claude" / "projects" / f"-{key}" / f"{sid}.jsonl"
            jsonl.parent.mkdir(parents=True)
            jsonl.write_text(transcript)
        env = {k: v for k, v in os.environ.items() if k not in _VOLATILE}
        env["HOME"] = str(base)
        env["PATH"] = f"{bindir}:/usr/bin:/bin"
        proc = subprocess.run(
            self.CMD + [f"--prompt-file={base}/prompt.md", f"--log={base}/out.log"],
            cwd=str(base),
            env=env,
            capture_output=True,
            text=True,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        usage: dict[str, Any] = json.loads((base / "out.usage.json").read_text())
        return usage


# ── opencode (Python) ───────────────────────────────────────────
class OpenCodeAdapter(AdapterCase):
    CMD = [str(OPENCODE_SH)]
    RECORDS = [
        {
            "type": "text",
            "sessionID": "ses_first",
            "part": {"type": "text", "text": "finished"},
        },
        {
            "type": "step_finish",
            "sessionID": "ses_first",
            "part": {
                "tokens": {
                    "input": 10,
                    "output": 20,
                    "reasoning": 30,
                    "cache": {"read": 40, "write": 50},
                },
                "cost": 0.25,
                "reason": "tool-calls",
            },
        },
        {
            "type": "step_finish",
            "sessionID": "ses_later",
            "part": {
                "tokens": {
                    "input": 1,
                    "output": 2,
                    "reasoning": 3,
                    "cache": {"read": 4, "write": 5},
                },
                "cost": 0.75,
                "reason": "stop",
            },
        },
    ]
    FIXTURE = "\n".join(json.dumps(record) for record in RECORDS) + "\n"

    def invoke(
        self,
        flags: list[str],
        *,
        env_extra: dict[str, str] | None = None,
        with_fake: bool = True,
    ) -> AdapterRun:
        return self.run_adapter(
            self.CMD,
            flags,
            fake_name="opencode",
            fixture_text=self.FIXTURE,
            record_extra=True,
            env_extra=env_extra,
            with_fake=with_fake,
        )

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log"]

    def test_command_construction_from_environment(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base),
            env_extra={
                "OPENCODE_MODEL": "zai-coding-plan/glm-5.2",
                "OPENCODE_EFFORT": "high",
            },
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(
            result["argv"],
            [
                "run",
                "--format=json",
                "--thinking",
                "--dangerously-skip-permissions",
                "--model",
                "zai-coding-plan/glm-5.2",
                "--variant",
                "high",
            ],
        )
        self.assertEqual(result["stdin"], "the prompt\n")
        self.assertEqual(result["modelenv"], "<unset>")
        self.assertEqual(result["effortenv"], "<unset>")
        self.assertEqual(result["vcsenv"], "git")

    def test_external_specula_and_artifact_paths_are_allowed(self) -> None:
        base = self.sandbox()
        specula_root = base / "Specula"
        target_repo = base / "target"
        work_dir = base / "run" / "kilo" / ".specula-output"
        result = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_ROOT": str(specula_root),
                "SPECULA_TARGET_REPO_DIR": str(target_repo),
                "SPECULA_WORK_DIR": str(work_dir),
            },
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(result["configdir"], "<unset>")
        external = json.loads(result["opencode_permission"])["external_directory"]
        self.assertEqual(external[str(specula_root)], "allow")
        self.assertEqual(external[f"{specula_root}/**"], "allow")
        self.assertEqual(external[str(target_repo)], "allow")
        self.assertEqual(external[f"{target_repo}/**"], "allow")
        self.assertEqual(external[str(work_dir)], "allow")
        self.assertEqual(external[f"{work_dir}/**"], "allow")

    def test_native_config_is_not_copied_or_rebased(self) -> None:
        base = self.sandbox()
        config_path = base / "config" / "custom.jsonc"
        config_path.parent.mkdir()
        config_text = """{
  // OpenCode accepts JSONC and resolves these relative to this file.
  \"plugin\": [\"./plugin.js\"],
  \"instructions\": [\"{file:./instructions.md}\"],
}
"""
        config_path.write_text(config_text)

        result = self.invoke(
            self.base_flags(base),
            env_extra={"OPENCODE_CONFIG": str(config_path)},
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(result["configdir"], str(config_path))
        self.assertEqual(result["opencode_config"], config_text)
        self.assertIn("external_directory", json.loads(result["opencode_permission"]))

    def test_native_permission_override_is_preserved(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_ROOT": str(base / "Specula"),
                "OPENCODE_PERMISSION": json.dumps(
                    {
                        "bash": "deny",
                        "external_directory": {"*": "deny", "/keep-denied": "deny"},
                    }
                ),
            },
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        permission = json.loads(result["opencode_permission"])
        self.assertEqual(permission["bash"], "deny")
        self.assertEqual(permission["external_directory"]["*"], "deny")
        self.assertEqual(permission["external_directory"]["/keep-denied"], "deny")
        self.assertEqual(permission["external_directory"][str(base / "Specula")], "allow")

    def test_native_specific_rules_win_by_opencode_last_match_order(self) -> None:
        base = self.sandbox()
        specula_root = base / "Specula"
        private = specula_root / "private"
        exception = private / "allowed"
        result = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_ROOT": str(specula_root),
                "OPENCODE_PERMISSION": json.dumps(
                    {
                        "external_directory": {
                            "*": "deny",
                            f"{private}/**": "deny",
                            f"{exception}/**": "allow",
                        }
                    }
                ),
            },
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        rules = json.loads(result["opencode_permission"])["external_directory"]

        def last_match(path: Path) -> str | None:
            actions = [action for pattern, action in rules.items() if fnmatchcase(str(path), pattern)]
            return actions[-1] if actions else None

        self.assertEqual(last_match(specula_root / "public" / "file.txt"), "allow")
        self.assertEqual(last_match(private / "secret.txt"), "deny")
        self.assertEqual(last_match(exception / "kept.txt"), "allow")

    def test_native_rule_order_and_same_pattern_are_preserved(self) -> None:
        base = self.sandbox()
        specula_root = base / "Specula"
        unrelated = base / "unrelated"
        target_pattern = f"{specula_root}/**"
        native_rules = {
            f"{unrelated}/**": "allow",
            "*": "deny",
            target_pattern: "deny",
        }
        result = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_ROOT": str(specula_root),
                "OPENCODE_PERMISSION": json.dumps({"external_directory": native_rules}),
            },
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        rules = json.loads(result["opencode_permission"])["external_directory"]
        self.assertEqual([pattern for pattern in rules if pattern in native_rules], list(native_rules))
        self.assertEqual(rules[target_pattern], "deny")

        def last_match(path: Path) -> str | None:
            actions = [action for pattern, action in rules.items() if fnmatchcase(str(path), pattern)]
            return actions[-1] if actions else None

        # The catch-all originally followed this allow, so it must still win.
        self.assertEqual(last_match(unrelated / "file.txt"), "deny")
        # A native rule identical to a generated pattern keeps its deny value.
        self.assertEqual(last_match(specula_root / "private.txt"), "deny")

    def test_scalar_native_permission_becomes_catch_all(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_ROOT": str(base / "Specula"),
                "OPENCODE_PERMISSION": json.dumps("deny"),
            },
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        permission = json.loads(result["opencode_permission"])
        self.assertEqual(permission["*"], "deny")
        self.assertEqual(permission["external_directory"][str(base / "Specula")], "allow")

    def test_prompt_file_and_large_prompt_use_stdin(self) -> None:
        for prompt in ("prompt from file\n", "x" * 200_000):
            with self.subTest(size=len(prompt)):
                base = self.sandbox()
                result = self.invoke([self.with_prompt_file(base, prompt), f"--log={base}/out.log"])
                self.assertEqual(result["returncode"], 0, result["stderr"])
                self.assertEqual(result["stdin"], prompt)
                self.assertEqual(
                    result["argv"],
                    ["run", "--format=json", "--thinking", "--dangerously-skip-permissions"],
                )

    def test_direct_prompt_uses_stdin(self) -> None:
        base = self.sandbox()
        result = self.invoke(["--prompt=the prompt\n", f"--log={base}/out.log"])
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(result["stdin"], "the prompt\n")
        self.assertEqual(
            result["argv"],
            ["run", "--format=json", "--thinking", "--dangerously-skip-permissions"],
        )

    def test_compatibility_flags_are_accepted_but_not_forwarded(self) -> None:
        base = self.sandbox()
        result = self.invoke(self.base_flags(base) + ["--max-turns=8", "--background", "--claude-alias=profile"])
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(
            result["argv"],
            ["run", "--format=json", "--thinking", "--dangerously-skip-permissions"],
        )

    def test_flag_values_override_environment_defaults(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base) + ["--model=flag-model", "--effort=max"],
            env_extra={"OPENCODE_MODEL": "env-model", "OPENCODE_EFFORT": "low"},
        )
        self.assertEqual(
            result["argv"],
            [
                "run",
                "--format=json",
                "--thinking",
                "--dangerously-skip-permissions",
                "--model",
                "flag-model",
                "--variant",
                "max",
            ],
        )
        self.assertEqual(result["modelenv"], "<unset>")
        self.assertEqual(result["effortenv"], "<unset>")

    def test_explicit_empty_model_and_effort_clear_environment_defaults(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base) + ["--model=", "--effort="],
            env_extra={"OPENCODE_MODEL": "env-model", "OPENCODE_EFFORT": "low"},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(
            result["argv"],
            ["run", "--format=json", "--thinking", "--dangerously-skip-permissions"],
        )
        self.assertEqual(result["modelenv"], "<unset>")
        self.assertEqual(result["effortenv"], "<unset>")

    def test_stream_and_normalized_usage_reach_sidecars(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        result = self.invoke(
            self.base_flags(base),
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(activity.read_text(), self.FIXTURE)
        self.assertEqual((base / "out.log").read_text(), "finished\n")
        parent_usage = {
            "input_tokens": 11,
            "cached_input_tokens": 44,
            "cache_write_input_tokens": 55,
            "output_tokens": 22,
            "reasoning_output_tokens": 33,
            "total_tokens": 132,
        }
        self.assertEqual(
            json.loads((base / "out.usage.json").read_text()),
            {
                "agent": "opencode",
                "session_id": "ses_first",
                "session_file": None,
                "total_cost_usd": 1.0,
                "usage": parent_usage,
                "usage_scope": "partial",
                "usage_complete": False,
                "usage_warning": "OpenCode session database unavailable",
                "parent": {
                    "session_id": "ses_first",
                    "total_cost_usd": 1.0,
                    "usage": parent_usage,
                },
                "subagents": {
                    "complete": False,
                    "session_count": 0,
                    "total_cost_usd": None,
                    "usage": {
                        "input_tokens": 0,
                        "cached_input_tokens": 0,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 0,
                        "reasoning_output_tokens": 0,
                        "total_tokens": 0,
                    },
                    "sessions": [],
                },
                "combined": {"complete": False, "total_cost_usd": 1.0, "usage": parent_usage},
            },
        )

    def test_subagent_sessions_are_included_in_combined_usage(self) -> None:
        base = self.sandbox()
        data_home = base / "xdg-data"
        database_path = data_home / "opencode" / "opencode.db"
        database_path.parent.mkdir(parents=True)
        with sqlite3.connect(database_path) as database:
            database.executescript(
                """
                CREATE TABLE session (id TEXT PRIMARY KEY, parent_id TEXT);
                CREATE TABLE part (
                    id TEXT PRIMARY KEY,
                    session_id TEXT,
                    time_created INTEGER,
                    data TEXT
                );
                """
            )
            database.executemany(
                "INSERT INTO session (id, parent_id) VALUES (?, ?)",
                (
                    ("ses_first", None),
                    ("child_a", "ses_first"),
                    ("child_b", "child_a"),
                    ("unrelated", None),
                    ("unrelated_child", "unrelated"),
                ),
            )
            database.executemany(
                "INSERT INTO part (id, session_id, time_created, data) VALUES (?, ?, ?, ?)",
                (
                    (
                        "part_a",
                        "child_a",
                        1,
                        json.dumps(
                            {
                                "type": "step-finish",
                                "cost": 0.5,
                                "tokens": {
                                    "input": 5,
                                    "output": 6,
                                    "reasoning": 2,
                                    "cache": {"read": 7, "write": 8},
                                },
                            }
                        ),
                    ),
                    (
                        "part_b",
                        "child_b",
                        2,
                        json.dumps(
                            {
                                "type": "step-finish",
                                "cost": 0.25,
                                "tokens": {
                                    "input": 1,
                                    "output": 2,
                                    "reasoning": 1,
                                    "cache": {"read": 3, "write": 4},
                                },
                            }
                        ),
                    ),
                    (
                        "part_unrelated",
                        "unrelated_child",
                        3,
                        json.dumps(
                            {
                                "type": "step-finish",
                                "tokens": {"input": 1000, "output": 1000},
                            }
                        ),
                    ),
                ),
            )

        result = self.invoke(
            self.base_flags(base),
            env_extra={"XDG_DATA_HOME": str(data_home)},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        usage = json.loads((base / "out.usage.json").read_text())
        self.assertEqual(usage["parent"]["usage"]["total_tokens"], 132)
        self.assertEqual(usage["usage_scope"], "combined")
        self.assertTrue(usage["usage_complete"])
        self.assertTrue(usage["subagents"]["complete"])
        self.assertEqual(usage["subagents"]["session_count"], 2)
        self.assertEqual(usage["subagents"]["usage"]["total_tokens"], 36)
        self.assertEqual(
            [session["session_id"] for session in usage["subagents"]["sessions"]],
            ["child_a", "child_b"],
        )
        self.assertEqual(usage["combined"]["usage"]["total_tokens"], 168)
        self.assertEqual(usage["usage"]["total_tokens"], 168)
        self.assertEqual(usage["total_cost_usd"], 1.75)

    def test_unrelated_session_database_is_reported_as_partial_usage(self) -> None:
        base = self.sandbox()
        data_home = base / "xdg-data"
        database_path = data_home / "opencode" / "opencode.db"
        database_path.parent.mkdir(parents=True)
        with sqlite3.connect(database_path) as database:
            database.executescript(
                """
                CREATE TABLE session (id TEXT PRIMARY KEY, parent_id TEXT);
                CREATE TABLE part (
                    id TEXT PRIMARY KEY,
                    session_id TEXT,
                    time_created INTEGER,
                    data TEXT
                );
                INSERT INTO session (id, parent_id) VALUES ('another_session', NULL);
                """
            )

        result = self.invoke(
            self.base_flags(base),
            env_extra={"XDG_DATA_HOME": str(data_home)},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        usage = json.loads((base / "out.usage.json").read_text())
        self.assertEqual(usage["usage_scope"], "partial")
        self.assertFalse(usage["usage_complete"])
        self.assertEqual(
            usage["usage_warning"],
            "OpenCode parent session not found in session database",
        )

    def test_structured_rate_limit_maps_native_failure_to_retry_status(self) -> None:
        base = self.sandbox()
        records = [
            {
                "type": "error",
                "sessionID": "ses_limited",
                "error": {
                    "name": "APIError",
                    "data": {
                        "message": "quota exhausted",
                        "statusCode": 429,
                        "isRetryable": True,
                    },
                },
            },
            {
                "type": "step_finish",
                "sessionID": "ses_limited",
                "part": {"type": "step-finish", "reason": "stop", "tokens": {}},
            },
        ]
        result = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="opencode",
            fixture_text="\n".join(json.dumps(record) for record in records) + "\n",
            env_extra={"ADAPTER_EXIT_CODE": "1"},
            record_extra=True,
        )
        self.assertEqual(result["returncode"], 75, result["stderr"])
        self.assertIn("rate limit hit", result["stderr"])

    def test_rate_limit_phrase_in_agent_text_is_not_a_retry_signal(self) -> None:
        base = self.sandbox()
        records = [
            {
                "type": "text",
                "sessionID": "ses_success",
                "part": {"type": "text", "text": "The old log said HTTP 429 quota exhausted."},
            },
            {
                "type": "step_finish",
                "sessionID": "ses_success",
                "part": {"type": "step-finish", "reason": "stop", "tokens": {}},
            },
        ]
        result = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="opencode",
            fixture_text="\n".join(json.dumps(record) for record in records) + "\n",
            record_extra=True,
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])

    def test_native_failures_are_preserved(self) -> None:
        for native_status in (9, 75):
            with self.subTest(native_status=native_status):
                base = self.sandbox()
                result = self.invoke(
                    self.base_flags(base),
                    env_extra={"ADAPTER_EXIT_CODE": str(native_status)},
                )
                self.assertEqual(result["returncode"], native_status, result["stderr"])

    def test_incomplete_terminal_event_overrides_zero_native_exit(self) -> None:
        for name, fixture, diagnostic in (
            (
                "tool-calls",
                json.dumps(
                    {
                        "type": "step_finish",
                        "sessionID": "ses_incomplete",
                        "part": {"type": "step-finish", "reason": "tool-calls", "tokens": {}},
                    }
                ),
                "tool-calls",
            ),
            ("missing", json.dumps({"type": "text", "part": {"type": "text", "text": "partial"}}), "without"),
        ):
            with self.subTest(name=name):
                base = self.sandbox()
                result = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="opencode",
                    fixture_text=fixture,
                    record_extra=True,
                )
                self.assertEqual(result["returncode"], 1, result["stderr"])
                self.assertIn(diagnostic, result["stderr"])

    def test_tool_error_is_preserved_in_readable_log(self) -> None:
        base = self.sandbox()
        records = [
            {
                "type": "tool_use",
                "sessionID": "ses_recovered",
                "part": {
                    "type": "tool",
                    "tool": "write",
                    "state": {
                        "status": "error",
                        "input": {"path": "/blocked/file"},
                        "error": "Permission denied: write access rejected",
                    },
                },
            },
            {
                "type": "step_finish",
                "sessionID": "ses_recovered",
                "part": {"type": "step-finish", "reason": "stop", "tokens": {}},
            },
        ]
        result = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="opencode",
            fixture_text="\n".join(json.dumps(record) for record in records) + "\n",
            record_extra=True,
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(
            (base / "out.log").read_text(),
            "editing /blocked/file\nadapter tool error: write: Permission denied: write access rejected\n",
        )

    def test_raw_activity_failure_does_not_fail_adapter(self) -> None:
        base = self.sandbox()
        activity = base / "bad-activity"
        activity.mkdir()
        result = self.invoke(
            self.base_flags(base),
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertIn("activity log", result["stderr"])
        self.assertEqual((base / "out.log").read_text(), "finished\n")

    def test_missing_executable_returns_127_and_writes_diagnostic(self) -> None:
        base = self.sandbox()
        result = self.invoke(self.base_flags(base), with_fake=False)
        self.assertEqual(result["returncode"], 127, result["stderr"])
        self.assertIn("opencode adapter: failed to launch opencode", (base / "out.log").read_text())
        usage = json.loads((base / "out.usage.json").read_text())
        self.assertEqual(usage["agent"], "opencode")
        self.assertIsNone(usage["session_id"])
        self.assertEqual(usage["usage"]["total_tokens"], 0)

    def test_invalid_options_fail_before_launch(self) -> None:
        for name, flags, diagnostic in (
            (
                "both-prompts",
                ["--prompt=inline", self.with_prompt_file(self.sandbox()), f"--log={self.sandbox()}/out.log"],
                "mutually exclusive",
            ),
            ("neither-prompt", [f"--log={self.sandbox()}/out.log"], "one of --prompt or --prompt-file is required"),
            ("missing-log", [self.with_prompt_file(self.sandbox())], "--log is required"),
            (
                "missing-prompt-file",
                [f"--prompt-file={self.sandbox()}/missing.md", f"--log={self.sandbox()}/out.log"],
                "prompt file not found",
            ),
            ("unknown-option", [*self.base_flags(self.sandbox()), "--bogus"], "unknown option"),
        ):
            with self.subTest(name=name):
                result = self.invoke(flags)
                self.assertEqual(result["returncode"], 1)
                self.assertIn(diagnostic, result["stderr"])
                self.assertEqual(result["argv"], [])


# ── pi (Python) ──────────────────────────────────────────────────────────────
class PiAdapter(AdapterCase):
    CMD = [str(PI_SH)]
    RECORDS: list[dict[str, Any]] = [
        {
            "type": "session",
            "version": 3,
            "id": "pi_session",
            "timestamp": "2026-07-14T00:00:00.000Z",
            "cwd": "/workspace",
        },
        {
            "type": "message_update",
            "assistantMessageEvent": {"type": "text_delta", "delta": "working"},
        },
        {
            "type": "tool_execution_start",
            "toolName": "read",
            "args": {"path": "src/main.py"},
        },
        {
            "type": "message_end",
            "message": {
                "role": "user",
                "usage": {
                    "input": 100,
                    "output": 100,
                    "cacheRead": 100,
                    "cacheWrite": 100,
                    "cost": {"total": 100.0},
                },
            },
        },
        {
            "type": "message_end",
            "message": {
                "role": "assistant",
                "stopReason": "toolUse",
                "usage": {
                    "input": 10,
                    "output": 20,
                    "cacheRead": 30,
                    "cacheWrite": 40,
                    "cost": {"total": 0.25},
                },
            },
        },
        {
            "type": "message_end",
            "message": {
                "role": "assistant",
                "stopReason": "stop",
                "usage": {
                    "input": 1,
                    "output": 2,
                    "cacheRead": 3,
                    "cacheWrite": 4,
                    "cost": {"total": 0.75},
                },
            },
        },
    ]
    FIXTURE = "\n".join(json.dumps(record) for record in RECORDS) + "\n"

    @staticmethod
    def expected_activity(records: list[dict[str, Any]]) -> str:
        lines: list[str] = []
        for record in records:
            if record.get("type") != "message_update":
                lines.append(json.dumps(record))
                continue
            update = record.get("assistantMessageEvent")
            compact: dict[str, object] = {"type": "message_update"}
            if isinstance(update, dict):
                compact_update = {
                    key: value
                    for key in ("type", "contentIndex", "delta")
                    if (value := update.get(key)) is not None and isinstance(value, (str, int, float, bool))
                }
                if compact_update:
                    compact["assistantMessageEvent"] = compact_update
            lines.append(json.dumps(compact, separators=(",", ":")))
        return "\n".join(lines) + "\n"

    def invoke(
        self,
        flags: list[str],
        *,
        env_extra: dict[str, str] | None = None,
        with_fake: bool = True,
    ) -> AdapterRun:
        return self.run_adapter(
            self.CMD,
            flags,
            fake_name="pi",
            fixture_text=self.FIXTURE,
            record_extra=True,
            env_extra=env_extra,
            with_fake=with_fake,
        )

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log"]

    def test_baseline_command_uses_environment_defaults_and_stdin(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base),
            env_extra={"PI_MODEL": "openai/gpt-5.5", "PI_EFFORT": "high"},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(
            result["argv"],
            [
                "--print",
                "--mode",
                "json",
                "--no-session",
                "--approve",
                "--model",
                "openai/gpt-5.5",
                "--thinking",
                "high",
            ],
        )
        self.assertEqual(result["stdin"], "the prompt\n")
        self.assertEqual(result["modelenv"], "<unset>")
        self.assertEqual(result["effortenv"], "<unset>")

    def test_max_effort_forwards_unchanged(self) -> None:
        base = self.sandbox()
        result = self.invoke(self.base_flags(base) + ["--effort=max"])
        self.assertEqual(
            result["argv"],
            ["--print", "--mode", "json", "--no-session", "--approve", "--thinking", "max"],
        )

    def test_all_other_efforts_forward_unchanged(self) -> None:
        for effort in ("low", "medium", "high", "xhigh"):
            with self.subTest(effort=effort):
                base = self.sandbox()
                result = self.invoke(self.base_flags(base) + [f"--effort={effort}"])
                self.assertEqual(result["argv"][-2:], ["--thinking", effort])

    def test_flag_values_override_environment_defaults(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base) + ["--model=flag-model", "--effort=medium"],
            env_extra={"PI_MODEL": "env-model", "PI_EFFORT": "low"},
        )
        self.assertEqual(
            result["argv"],
            [
                "--print",
                "--mode",
                "json",
                "--no-session",
                "--approve",
                "--model",
                "flag-model",
                "--thinking",
                "medium",
            ],
        )
        self.assertEqual(result["modelenv"], "<unset>")
        self.assertEqual(result["effortenv"], "<unset>")

    def test_explicit_empty_model_and_effort_clear_environment_defaults(self) -> None:
        base = self.sandbox()
        result = self.invoke(
            self.base_flags(base) + ["--model=", "--effort="],
            env_extra={"PI_MODEL": "env-model", "PI_EFFORT": "low"},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(result["argv"], ["--print", "--mode", "json", "--no-session", "--approve"])
        self.assertEqual(result["modelenv"], "<unset>")
        self.assertEqual(result["effortenv"], "<unset>")

    def test_compatibility_flags_are_accepted_but_not_forwarded(self) -> None:
        base = self.sandbox()
        result = self.invoke(self.base_flags(base) + ["--max-turns=8", "--background", "--claude-alias=profile"])
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(result["argv"], ["--print", "--mode", "json", "--no-session", "--approve"])

    def test_large_prompt_file_uses_stdin(self) -> None:
        base = self.sandbox()
        prompt = "x" * 200_000
        result = self.invoke([self.with_prompt_file(base, prompt), f"--log={base}/out.log"])
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(result["stdin"], prompt)
        self.assertEqual(result["argv"], ["--print", "--mode", "json", "--no-session", "--approve"])

    def test_readable_deltas_and_tool_summaries_reach_log(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        records = [
            {
                "type": "message_update",
                "assistantMessageEvent": {
                    "type": "text_delta",
                    "contentIndex": 0,
                    "delta": "work",
                    "partial": {"type": "text", "text": "a large cumulative snapshot"},
                },
                "message": {"role": "assistant", "content": [{"type": "text", "text": "work"}]},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "ing"},
            },
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "working"}],
                    "stopReason": "toolUse",
                },
            },
            {
                "type": "tool_execution_start",
                "toolName": "read",
                "args": {"path": "src/main.py"},
            },
            {
                "type": "message_update",
                "assistantMessageEvent": {"type": "text_delta", "delta": "done"},
            },
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "done"}],
                    "stopReason": "stop",
                },
            },
        ]
        fixture = "\n".join(json.dumps(record) for record in records) + "\n"
        result = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="pi",
            fixture_text=fixture,
            record_extra=True,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual(activity.read_text(), self.expected_activity(records))
        self.assertNotIn("cumulative snapshot", activity.read_text())
        self.assertEqual((base / "out.log").read_text(), "working\nreading src/main.py\ndone\n")

    def test_message_end_without_deltas_writes_final_answer(self) -> None:
        base = self.sandbox()
        fixture = json.dumps(
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "final answer only"}],
                    "stopReason": "stop",
                    "usage": {},
                },
            }
        )
        result = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="pi",
            fixture_text=fixture,
            record_extra=True,
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual((base / "out.log").read_text(), "final answer only\n")

    def test_session_header_and_assistant_usage_reach_usage_sidecar(self) -> None:
        base = self.sandbox()
        result = self.invoke(self.base_flags(base))
        self.assertEqual(result["returncode"], 0, result["stderr"])
        usage = json.loads((base / "out.usage.json").read_text())
        parent_usage = {
            "input_tokens": 11,
            "cached_input_tokens": 33,
            "cache_write_input_tokens": 44,
            "output_tokens": 22,
            "reasoning_output_tokens": 0,
            "total_tokens": 110,
        }
        self.assertEqual(usage["usage_scope"], "combined")
        self.assertTrue(usage["usage_complete"])
        self.assertEqual(usage["usage"], parent_usage)
        self.assertEqual(usage["parent"], {"session_id": "pi_session", "total_cost_usd": 1.0, "usage": parent_usage})
        self.assertTrue(usage["subagents"]["complete"])
        self.assertEqual(usage["subagents"]["session_count"], 0)
        self.assertEqual(usage["subagents"]["usage"]["total_tokens"], 0)
        self.assertEqual(usage["combined"], {"complete": True, "total_cost_usd": 1.0, "usage": parent_usage})

    def test_structured_provider_failure_overrides_zero_native_exit(self) -> None:
        for reason in ("error", "aborted"):
            with self.subTest(reason=reason):
                base = self.sandbox()
                message = f"provider stopped with {reason}"
                fixture = json.dumps(
                    {
                        "type": "message_end",
                        "message": {
                            "role": "assistant",
                            "content": [],
                            "stopReason": reason,
                            "errorMessage": message,
                            "usage": {},
                        },
                    }
                )
                result = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="pi",
                    fixture_text=fixture,
                    record_extra=True,
                )
                self.assertEqual(result["returncode"], 1, result["stderr"])
                self.assertIn(message, result["stderr"])
                self.assertEqual((base / "out.log").read_text(), f"adapter error: {message}\n")

    def test_structured_rate_limit_maps_to_retry_status(self) -> None:
        for native_status in (0, 1):
            with self.subTest(native_status=native_status):
                base = self.sandbox()
                fixture = json.dumps(
                    {
                        "type": "message_end",
                        "message": {
                            "role": "assistant",
                            "content": [],
                            "stopReason": "error",
                            "errorMessage": "HTTP 429: quota exhausted",
                            "usage": {},
                        },
                    }
                )
                result = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="pi",
                    fixture_text=fixture,
                    env_extra={"ADAPTER_EXIT_CODE": str(native_status)},
                    record_extra=True,
                )
                self.assertEqual(result["returncode"], 75, result["stderr"])
                self.assertIn("rate limit hit", result["stderr"])

    def test_top_level_rate_limit_maps_to_retry_status(self) -> None:
        fixture = json.dumps(
            {
                "type": "error",
                "message": "HTTP 429: quota exhausted",
                "statusCode": 429,
            }
        )
        for native_status in (0, 1):
            with self.subTest(native_status=native_status):
                base = self.sandbox()
                result = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="pi",
                    fixture_text=fixture,
                    env_extra={"ADAPTER_EXIT_CODE": str(native_status)},
                    record_extra=True,
                )
                self.assertEqual(result["returncode"], 75, result["stderr"])
                self.assertIn("rate limit hit", result["stderr"])
                self.assertIn("HTTP 429: quota exhausted", result["stderr"])

    def test_incomplete_terminal_event_overrides_zero_native_exit(self) -> None:
        for name, fixture, diagnostic in (
            (
                "tool-use",
                json.dumps(
                    {
                        "type": "message_end",
                        "message": {"role": "assistant", "content": [], "stopReason": "toolUse", "usage": {}},
                    }
                ),
                "toolUse",
            ),
            ("missing", json.dumps({"type": "session", "id": "pi_incomplete"}), "without"),
        ):
            with self.subTest(name=name):
                base = self.sandbox()
                result = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="pi",
                    fixture_text=fixture,
                    record_extra=True,
                )
                self.assertEqual(result["returncode"], 1, result["stderr"])
                self.assertIn(diagnostic, result["stderr"])

    def test_terminating_tool_result_completes_without_follow_up_message(self) -> None:
        records = [
            {
                "type": "message_end",
                "message": {
                    "role": "assistant",
                    "content": [{"type": "toolCall", "id": "call_final", "name": "finalize"}],
                    "stopReason": "toolUse",
                    "usage": {},
                },
            },
            {
                "type": "tool_execution_end",
                "toolCallId": "call_final",
                "toolName": "finalize",
                "result": {
                    "content": [{"type": "text", "text": "structured result"}],
                    "details": {},
                    "terminate": True,
                },
                "isError": False,
            },
            {
                "type": "message_end",
                "message": {
                    "role": "toolResult",
                    "toolCallId": "call_final",
                    "toolName": "finalize",
                    "content": [{"type": "text", "text": "structured result"}],
                    "isError": False,
                },
            },
            {"type": "agent_end", "messages": []},
        ]
        base = self.sandbox()
        result = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="pi",
            fixture_text="\n".join(json.dumps(record) for record in records) + "\n",
            record_extra=True,
        )

        self.assertEqual(result["returncode"], 0, result["stderr"])
        self.assertEqual((base / "out.log").read_text(), "structured result\n")

    def test_terminating_tool_requires_successful_result_and_agent_end(self) -> None:
        assistant = {
            "type": "message_end",
            "message": {"role": "assistant", "content": [], "stopReason": "toolUse", "usage": {}},
        }
        for name, result_record, include_agent_end in (
            (
                "missing-terminate",
                {
                    "type": "tool_execution_end",
                    "result": {"content": [], "details": {}},
                    "isError": False,
                },
                True,
            ),
            (
                "tool-error",
                {
                    "type": "tool_execution_end",
                    "result": {"content": [], "details": {}, "terminate": True},
                    "isError": True,
                },
                True,
            ),
            (
                "missing-error-status",
                {
                    "type": "tool_execution_end",
                    "result": {"content": [], "details": {}, "terminate": True},
                },
                True,
            ),
            (
                "missing-agent-end",
                {
                    "type": "tool_execution_end",
                    "result": {"content": [], "details": {}, "terminate": True},
                    "isError": False,
                },
                False,
            ),
        ):
            with self.subTest(name=name):
                records: list[dict[str, Any]] = [assistant, result_record]
                if include_agent_end:
                    records.append({"type": "agent_end", "messages": []})
                base = self.sandbox()
                result = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="pi",
                    fixture_text="\n".join(json.dumps(record) for record in records) + "\n",
                    record_extra=True,
                )

                self.assertEqual(result["returncode"], 1, result["stderr"])
                self.assertIn("toolUse", result["stderr"])

    @unittest.skipUnless(hasattr(os, "killpg") and hasattr(signal, "SIGHUP"), "requires POSIX signals")
    def test_termination_signals_cleanup_temporary_files(self) -> None:
        for signum in (signal.SIGTERM, signal.SIGHUP):
            with self.subTest(signal=signal.Signals(signum).name):
                base = self.sandbox()
                bindir = base / "bin"
                fixture = base / "fixture.jsonl"
                fixture.write_text("")
                self._write_fake(bindir, "pi", fixture, record_extra=True)
                tmpdir = base / "tmp"
                tmpdir.mkdir()
                ready = base / "ready"
                child_session = base / "child-session.jsonl"
                child_session.write_text(json.dumps({"type": "session", "id": "child"}) + "\n")
                env = {key: value for key, value in os.environ.items() if key not in _VOLATILE}
                env.update(
                    {
                        "HOME": str(base),
                        "PATH": f"{bindir}:/usr/bin:/bin",
                        "TMPDIR": str(tmpdir),
                        "ADAPTER_READY_FILE": str(ready),
                        "ADAPTER_WAIT_SECONDS": "30",
                        "ADAPTER_PI_SESSION_FIXTURE": str(child_session),
                    }
                )
                proc = subprocess.Popen(
                    [*self.CMD, "--prompt=temporary prompt", f"--log={base}/out.log"],
                    cwd=base,
                    env=env,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    start_new_session=True,
                )

                def cleanup(process: subprocess.Popen[str] = proc) -> None:
                    if process.poll() is None:
                        with contextlib.suppress(ProcessLookupError):
                            os.killpg(process.pid, signal.SIGKILL)
                        process.wait()

                self.addCleanup(cleanup)
                deadline = time.monotonic() + 5
                while not ready.is_file() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(ready.is_file(), "fake Pi did not become ready")
                self.assertTrue(list(tmpdir.glob("specula-pi-sessions-*")))
                self.assertTrue(list(tmpdir.glob("specula-pi-activity-*.jsonl")))
                self.assertTrue(list(tmpdir.glob("specula-pi-prompt-*.txt")))

                os.killpg(proc.pid, signum)
                _stdout, stderr = proc.communicate(timeout=5)
                self.assertEqual(proc.returncode, 128 + signum, stderr)
                self.assertFalse(list(tmpdir.glob("specula-pi-sessions-*")))
                self.assertFalse(list(tmpdir.glob("specula-pi-activity-*.jsonl")))
                self.assertFalse(list(tmpdir.glob("specula-pi-prompt-*.txt")))

    def test_subagent_sessions_are_included_in_combined_usage(self) -> None:
        base = self.sandbox()
        child_session = base / "child-session.jsonl"
        child_records = [
            {"type": "session", "version": 3, "id": "child_session", "cwd": "/workspace"},
            {
                "type": "message",
                "message": {
                    "role": "assistant",
                    "usage": {
                        "input": 5,
                        "output": 6,
                        "cacheRead": 7,
                        "cacheWrite": 8,
                        "cost": {"total": 0.5},
                    },
                },
            },
            {
                "type": "message",
                "message": {
                    "role": "user",
                    "usage": {"input": 100, "output": 100, "cacheRead": 100, "cacheWrite": 100},
                },
            },
        ]
        child_session.write_text("\n".join(json.dumps(record) for record in child_records) + "\n")
        result = self.invoke(
            self.base_flags(base),
            env_extra={"ADAPTER_PI_SESSION_FIXTURE": str(child_session)},
        )
        self.assertEqual(result["returncode"], 0, result["stderr"])
        usage = json.loads((base / "out.usage.json").read_text())
        self.assertEqual(usage["parent"]["usage"]["total_tokens"], 110)
        self.assertEqual(usage["subagents"]["session_count"], 1)
        self.assertEqual(usage["subagents"]["usage"]["total_tokens"], 26)
        self.assertEqual(usage["subagents"]["sessions"][0]["session_id"], "child_session")
        self.assertEqual(usage["combined"]["usage"]["total_tokens"], 136)
        self.assertEqual(usage["usage"]["total_tokens"], 136)
        self.assertEqual(usage["total_cost_usd"], 1.5)

    @unittest.skipUnless(Path("/proc").is_dir(), "requires procfs")
    def test_postprocessing_failure_defers_to_native_status(self) -> None:
        for native_status, expected in ((0, 1), (9, 9), (75, 75)):
            with self.subTest(native_status=native_status):
                base = self.sandbox()
                activity = base / "out.activity.jsonl"
                result = self.invoke(
                    [self.with_prompt_file(base), "--log=/proc/specula-pi-adapter.log"],
                    env_extra={
                        "SPECULA_ACTIVITY_LOG": str(activity),
                        "ADAPTER_EXIT_CODE": str(native_status),
                    },
                )
                self.assertEqual(result["returncode"], expected, result["stderr"])
                self.assertEqual(activity.read_text(), self.expected_activity(self.RECORDS))

    def test_missing_executable_returns_127_and_writes_diagnostic(self) -> None:
        base = self.sandbox()
        result = self.invoke(self.base_flags(base), with_fake=False)
        self.assertEqual(result["returncode"], 127, result["stderr"])
        self.assertIn("pi adapter: failed to launch pi", (base / "out.log").read_text())
        usage = json.loads((base / "out.usage.json").read_text())
        self.assertEqual(usage["agent"], "pi")
        self.assertIsNone(usage["session_id"])
        self.assertEqual(usage["usage"]["total_tokens"], 0)

    def test_invalid_options_fail_before_launch(self) -> None:
        for name, flags, diagnostic in (
            (
                "both-prompts",
                ["--prompt=inline", self.with_prompt_file(self.sandbox()), f"--log={self.sandbox()}/out.log"],
                "mutually exclusive",
            ),
            ("neither-prompt", [f"--log={self.sandbox()}/out.log"], "one of --prompt or --prompt-file is required"),
            ("missing-log", [self.with_prompt_file(self.sandbox())], "--log is required"),
            (
                "missing-prompt-file",
                [f"--prompt-file={self.sandbox()}/missing.md", f"--log={self.sandbox()}/out.log"],
                "prompt file not found",
            ),
            ("unknown-option", [*self.base_flags(self.sandbox()), "--bogus"], "unknown option"),
        ):
            with self.subTest(name=name):
                result = self.invoke(flags)
                self.assertEqual(result["returncode"], 1)
                self.assertIn(diagnostic, result["stderr"])
                self.assertEqual(result["argv"], [])


# ── codex (bash) ────────────────────────────────────────────
class CodexAdapter(AdapterCase):
    CMD = ["bash", str(CODEX_SH)]

    def invoke(self, flags: list[str], *, env_extra: dict[str, str] | None = None) -> AdapterRun:
        # record_extra=True captures the fake codex's stdin: the adapter feeds the
        # prompt via stdin (not argv) to stay under MAX_ARG_STRLEN, so the prompt
        # must show up there, not in argv.
        return self.run_adapter(
            self.CMD, flags, fake_name="codex", fixture_text="codex ran\n", record_extra=True, env_extra=env_extra
        )

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log", "--max-turns=0"]

    def test_command_construction(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base))
        self.assertEqual(r["returncode"], 0)
        # The CLI transcript stays in out.log; Codex writes the final assistant
        # response to a distinct sidecar for blocking confirmation turns.
        self.assertEqual(
            r["argv"],
            [
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--output-last-message",
                str(base / "out.last-message.txt"),
                "-",
            ],
        )
        self.assertEqual(r["stdin"], "the prompt")

    def test_stop_gate_reset_uses_worker_scope(self) -> None:
        base = self.sandbox()
        target = base / "target"
        gate_scope = base / "finding"
        for path in (target, gate_scope):
            state = path / ".stop-gate"
            state.mkdir(parents=True)
            (state / "blocks").write_text("3\n")

        r = self.invoke(
            self.base_flags(base),
            env_extra={
                "SPECULA_PHASE": "bug_confirmation_turn",
                "SPECULA_WORK_DIR": str(target),
                "SPECULA_STOP_GATE_WORK_DIR": str(gate_scope),
            },
        )

        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertTrue((target / ".stop-gate" / "blocks").is_file())
        self.assertFalse((gate_scope / ".stop-gate" / "blocks").exists())

    def test_prompt_from_file_is_read(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base, "codex task\n"), f"--log={base}/out.log", "--max-turns=0"])
        # prompt is delivered via stdin, not argv (argv ends with the '-' sentinel)
        self.assertEqual(r["argv"][-1], "-")
        self.assertEqual(r["stdin"], "codex task")

    def test_output_redirected_to_log(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        self.assertEqual((base / "out.log").read_text(), "codex ran\n")

    def test_non_log_suffix_preserved_in_last_message_path(self) -> None:
        base = self.sandbox()
        log = base / "out.output"
        r = self.invoke([self.with_prompt_file(base), f"--log={log}", "--max-turns=0"])
        output_flag = r["argv"].index("--output-last-message")
        self.assertEqual(r["argv"][output_flag + 1], str(log) + ".last-message.txt")

    def test_specula_activity_uses_json_stream(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = "\n".join(
            [
                json.dumps(
                    {
                        "type": "item.started",
                        "item": {"type": "command_execution", "command": "/bin/bash -lc pwd"},
                    }
                ),
                json.dumps(
                    {
                        "type": "item.completed",
                        "item": {"type": "agent_message", "text": "done"},
                    }
                ),
            ]
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="codex",
            fixture_text=fixture,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(
            r["argv"],
            [
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--output-last-message",
                str(base / "out.last-message.txt"),
                "--json",
                "-",
            ],
        )
        self.assertEqual(r["stdin"], "the prompt")
        self.assertEqual(activity.read_text(), fixture)
        self.assertEqual((base / "out.log").read_text(), "running pwd\ndone\n")

    def test_large_prompt_uses_stdin_with_activity_stream(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        prompt = "x" * 200000
        fixture = json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "done"}})
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base, prompt), f"--log={base}/out.log", "--max-turns=0"],
            fake_name="codex",
            fixture_text=fixture,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
            record_extra=True,
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(r["argv"][-2:], ["--json", "-"])
        self.assertEqual(r["stdin"], prompt)

    def test_cli_failure_is_preserved_without_activity_stream(self) -> None:
        for cli_rc in ("9", "75"):
            with self.subTest(cli_rc=cli_rc):
                base = self.sandbox()
                r = self.invoke(self.base_flags(base), env_extra={"ADAPTER_EXIT_CODE": cli_rc})
                self.assertEqual(r["returncode"], int(cli_rc), r["stderr"])

    def test_structured_turn_failure_is_logged_but_cli_owns_status(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = "\n".join(
            [
                json.dumps({"type": "turn.failed", "error": {"message": "quota\u001b[2J exhausted"}}),
                json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "recovered"}}),
                json.dumps({"type": "turn.completed", "usage": {}}),
            ]
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="codex",
            fixture_text=fixture,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual((base / "out.log").read_text(), "adapter error: quota exhausted\nrecovered\n")

    def test_recoverable_structured_errors_are_logged_without_failing(self) -> None:
        cases = [
            (
                "top-level",
                {"type": "error", "message": "websocket reconnecting"},
                "adapter error: websocket reconnecting\n",
            ),
            (
                "item",
                {"type": "item.completed", "item": {"id": "item_1", "type": "error", "message": "lagged"}},
                "adapter warning: lagged\n",
            ),
        ]
        for name, record, expected_log in cases:
            with self.subTest(name):
                base = self.sandbox()
                activity = base / "out.activity.jsonl"
                r = self.run_adapter(
                    self.CMD,
                    self.base_flags(base),
                    fake_name="codex",
                    fixture_text=json.dumps(record),
                    env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
                )
                self.assertEqual(r["returncode"], 0, r["stderr"])
                self.assertEqual((base / "out.log").read_text(), expected_log)

    def test_cli_failure_is_preserved_with_structured_error(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="codex",
            fixture_text=json.dumps({"type": "turn.failed", "error": {"message": "fatal"}}),
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "ADAPTER_EXIT_CODE": "9"},
        )
        self.assertEqual(r["returncode"], 9, r["stderr"])

    @unittest.skipUnless(Path("/proc").is_dir(), "requires procfs")
    def test_usage_write_failure_preserves_cli_status(self) -> None:
        for cli_rc, expected in (("0", 1), ("9", 9), ("75", 75)):
            with self.subTest(cli_rc=cli_rc):
                base = self.sandbox()
                activity = base / "out.activity.jsonl"
                fixture = json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "done"}})
                r = self.run_adapter(
                    self.CMD,
                    [self.with_prompt_file(base), "--log=/proc/specula-adapter.log", "--max-turns=0"],
                    fake_name="codex",
                    fixture_text=fixture,
                    env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "ADAPTER_EXIT_CODE": cli_rc},
                )
                self.assertEqual(r["returncode"], expected, r["stderr"])
                self.assertEqual(activity.read_text(), fixture)

    @unittest.skipUnless(Path("/dev/full").exists(), "requires /dev/full")
    def test_readable_log_failure_keeps_raw_stream_and_fails_adapter(self) -> None:
        for cli_rc, expected in (("0", 1), ("9", 9)):
            with self.subTest(cli_rc=cli_rc):
                base = self.sandbox()
                log = base / "out.log"
                log.symlink_to("/dev/full")
                activity = base / "out.activity.jsonl"
                first = json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "first"}})
                final = json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "final"}})
                fixture = "\n".join([first, final])
                r = self.run_adapter(
                    self.CMD,
                    [self.with_prompt_file(base), f"--log={log}", "--max-turns=0"],
                    fake_name="codex",
                    fixture_text=fixture,
                    env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "ADAPTER_EXIT_CODE": cli_rc},
                )
                self.assertEqual(r["returncode"], expected, r["stderr"])
                self.assertIn("readable log", r["stderr"])
                self.assertEqual(activity.read_text(), fixture)

    def test_raw_activity_failure_drains_cli_without_failing_adapter(self) -> None:
        base = self.sandbox()
        activity = base / "bad-activity"
        activity.mkdir()
        log = base / "out.log"
        final = json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "final"}})
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base), f"--log={log}", "--max-turns=0"],
            fake_name="codex",
            fixture_text=final,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity)},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertIn("activity log", r["stderr"])
        self.assertEqual(log.read_text(), "final\n")

    def test_usage_json_tags_agent_codex(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        self.assertEqual(json.loads((base / "out.usage.json").read_text())["agent"], "codex")

    def test_model_and_effort_forwarded_alias_ignored(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--claude-alias=x", "--model=gpt-5.5", "--effort=high"])
        self.assertEqual(r["returncode"], 0)
        # --claude-alias is ignored; --model -> -m, --effort -> -c model_reasoning_effort
        self.assertEqual(
            r["argv"],
            [
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--output-last-message",
                str(base / "out.last-message.txt"),
                "-m",
                "gpt-5.5",
                "-c",
                "model_reasoning_effort=high",
                "-",
            ],
        )
        self.assertEqual(r["stdin"], "the prompt")

    def test_model_effort_from_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(
            self.base_flags(base),
            env_extra={"CODEX_MODEL": "gpt-5.6-sol", "CODEX_EFFORT": "ultra"},
        )
        self.assertEqual(r["returncode"], 0)
        argv = r["argv"]
        self.assertEqual(argv[argv.index("-m") + 1], "gpt-5.6-sol")
        self.assertEqual(argv[argv.index("-c") + 1], "model_reasoning_effort=ultra")
        self.assertEqual(r["modelenv"], "<unset>")
        self.assertEqual(r["effortenv"], "<unset>")

    def test_flag_wins_over_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(
            self.base_flags(base) + ["--model=flag-model"],
            env_extra={"CODEX_MODEL": "env-model"},
        )
        argv = r["argv"]
        self.assertEqual(argv[argv.index("-m") + 1], "flag-model")

    def test_explicit_empty_model_effort_clear_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(
            self.base_flags(base) + ["--model=", "--effort="],
            env_extra={"CODEX_MODEL": "env-model", "CODEX_EFFORT": "high"},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(
            r["argv"],
            [
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--output-last-message",
                str(base / "out.last-message.txt"),
                "-",
            ],
        )
        self.assertEqual(r["stdin"], "the prompt")
        self.assertEqual(r["modelenv"], "<unset>")
        self.assertEqual(r["effortenv"], "<unset>")

    def test_max_turns_required(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base), f"--log={base}/out.log"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("--max-turns is required", r["stderr"])

    def test_log_required(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base), "--max-turns=0"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("--log is required", r["stderr"])

    def test_prompt_xor_prompt_file(self) -> None:
        base = self.sandbox()
        r = self.invoke(["--prompt=x", self.with_prompt_file(base), f"--log={base}/out.log", "--max-turns=0"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("mutually exclusive", r["stderr"])

    def test_unknown_option(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--bogus"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("unknown option", r["stderr"])

    def test_help(self) -> None:
        r = self.invoke(["--help"])
        self.assertEqual(r["returncode"], 0)
        self.assertIn("Adapter: codex", r["stdout"])


# ── copilot-cli (bash) ───────────────────────────────────────────────────────
class CopilotAdapter(AdapterCase):
    CMD = ["bash", str(COPILOT_SH)]
    DEFAULT_HELP = "--autopilot"

    def invoke(self, flags: list[str], *, env_extra: dict[str, str] | None = None) -> AdapterRun:
        env = {"COPILOT_HELP_TEXT": self.DEFAULT_HELP}
        env.update(env_extra or {})
        return self.run_adapter(self.CMD, flags, fake_name="copilot", fixture_text="copilot ran\n", env_extra=env)

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log"]

    def test_command_construction(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base))
        self.assertEqual(r["returncode"], 0)
        # copilot -p "<prompt>" --allow-all --autopilot
        self.assertEqual(r["argv"], ["-p", "the prompt", "--allow-all", "--autopilot"])

    def test_autopilot_requires_supported_cli(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base), env_extra={"COPILOT_HELP_TEXT": "--allow-all"})
        self.assertEqual(r["returncode"], 1)
        self.assertIn("does not advertise it; upgrade Copilot CLI", r["stderr"])
        self.assertEqual(r["argv"], [])  # help probe only; task was never launched

    def test_model_flag_appended(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--model=gpt-5"])
        self.assertEqual(r["argv"], ["-p", "the prompt", "--allow-all", "--autopilot", "--model", "gpt-5"])

    def test_model_from_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base), env_extra={"COPILOT_MODEL": "envmodel"})
        self.assertEqual(r["argv"][-2:], ["--model", "envmodel"])
        self.assertEqual(r["modelenv"], "<unset>")

    def test_explicit_empty_model_clears_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--model="], env_extra={"COPILOT_MODEL": "envmodel"})
        self.assertNotIn("--model", r["argv"])
        self.assertEqual(r["modelenv"], "<unset>")

    def test_max_turns_maps_to_autopilot_continues(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--max-turns=4"])
        self.assertEqual(r["argv"][-2:], ["--max-autopilot-continues", "4"])

    def test_max_turns_zero_omits_flag(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--max-turns=0"])
        self.assertNotIn("--max-autopilot-continues", r["argv"])

    def test_alias_ignored_and_effort_forwarded(self) -> None:
        base = self.sandbox()
        r = self.invoke(
            self.base_flags(base) + ["--claude-alias=claude", "--effort=high"],
            env_extra={"COPILOT_HELP_TEXT": "  --autopilot\n  --reasoning-effort <level>"},
        )
        self.assertEqual(r["returncode"], 0)
        self.assertEqual(
            r["argv"],
            ["-p", "the prompt", "--allow-all", "--autopilot", "--reasoning-effort", "high"],
        )

    def test_effort_alias_fallback(self) -> None:
        base = self.sandbox()
        r = self.invoke(
            self.base_flags(base) + ["--effort=max"],
            env_extra={"COPILOT_HELP_TEXT": "  --autopilot\n  --effort <level>"},
        )
        self.assertEqual(r["returncode"], 0)
        self.assertEqual(r["argv"][-2:], ["--effort", "max"])

    def test_effort_requires_supported_cli(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--effort=high"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("requires Copilot CLI 1.0.4+", r["stderr"])
        self.assertEqual(r["argv"], [])  # help probe only; task was never launched

    def test_explicit_empty_effort_keeps_old_cli_compatible(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--effort="])
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(r["argv"], ["-p", "the prompt", "--allow-all", "--autopilot"])

    def test_output_redirected_to_log(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        self.assertEqual((base / "out.log").read_text(), "copilot ran\n")

    def test_specula_activity_uses_json_stream(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = "\n".join(
            [
                json.dumps(
                    {
                        "type": "assistant.message",
                        "data": {"content": "Inspecting input handling."},
                    }
                ),
                json.dumps(
                    {
                        "type": "tool.execution_start",
                        "data": {"toolName": "bash", "arguments": {"command": "pwd"}},
                    }
                ),
                json.dumps({"type": "assistant.message", "data": {"content": "done"}}),
                json.dumps({"type": "result", "exitCode": 0}),
            ]
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base) + ["--effort=high"],
            fake_name="copilot",
            fixture_text=fixture,
            env_extra={
                "SPECULA_ACTIVITY_LOG": str(activity),
                "COPILOT_HELP_TEXT": "--autopilot\n--reasoning-effort\n--output-format\n--stream",
            },
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertIn("--reasoning-effort", r["argv"])
        self.assertEqual(r["argv"][r["argv"].index("--reasoning-effort") + 1], "high")
        self.assertEqual(r["argv"][-4:], ["--output-format", "json", "--stream", "on"])
        self.assertEqual(activity.read_text(), fixture)
        self.assertEqual(
            (base / "out.log").read_text(),
            "Inspecting input handling.\nrunning pwd\ndone\n",
        )

    def test_old_cli_falls_back_to_plain_stream(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="copilot",
            fixture_text="old copilot completed\n",
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "COPILOT_HELP_TEXT": "--autopilot\n--stream"},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertNotIn("--output-format", r["argv"])
        self.assertEqual(r["argv"][-2:], ["--stream", "on"])
        self.assertEqual(activity.read_text(), "old copilot completed\n")
        self.assertEqual((base / "out.log").read_text(), "old copilot completed\n")

    def test_old_cli_plain_text_does_not_infer_error_prefixes(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = "Tests failed before the fix; they pass now.\nAPI Error: 529 overloaded_error\n"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="copilot",
            fixture_text=fixture,
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "COPILOT_HELP_TEXT": "--autopilot\n--stream"},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual((base / "out.log").read_text(), fixture)
        self.assertEqual(activity.read_text(), fixture)

    def test_cli_without_stream_support_falls_back_without_new_flags(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="copilot",
            fixture_text="legacy copilot completed\n",
            env_extra={"SPECULA_ACTIVITY_LOG": str(activity), "COPILOT_HELP_TEXT": "--autopilot"},
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertNotIn("--output-format", r["argv"])
        self.assertNotIn("--stream", r["argv"])
        self.assertEqual(activity.read_text(), "legacy copilot completed\n")
        self.assertEqual((base / "out.log").read_text(), "legacy copilot completed\n")

    def test_plain_stream_updates_raw_activity_before_a_newline(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        log = base / "out.log"
        proc = subprocess.Popen(
            [*EVENT_STREAM_COMMAND, "copilot", str(activity), str(log)],
            stdin=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            self.assertIsNotNone(proc.stdin)
            assert proc.stdin is not None
            proc.stdin.write(b"partial token")
            proc.stdin.flush()

            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                if activity.is_file() and activity.read_bytes() == b"partial token":
                    break
                time.sleep(0.01)
            self.assertEqual(activity.read_bytes(), b"partial token")

            proc.stdin.write(b" final\n")
            proc.stdin.close()
            self.assertEqual(proc.wait(timeout=2), 0)
            self.assertEqual(activity.read_bytes(), b"partial token final\n")
            self.assertEqual(log.read_text(), "partial token final\n")
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()

    def test_session_error_is_logged_but_cli_owns_status(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = "\n".join(
            [
                json.dumps(
                    {
                        "type": "session.error",
                        "data": {
                            "errorType": "rate_limit\u001b[2J",
                            "message": "quota\u001b]0;spoof\u0007 exhausted",
                            "statusCode": 429,
                        },
                    }
                ),
                json.dumps({"type": "assistant.message", "data": {"content": "recovered"}}),
                json.dumps({"type": "result", "exitCode": 0}),
            ]
        )
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="copilot",
            fixture_text=fixture,
            env_extra={
                "SPECULA_ACTIVITY_LOG": str(activity),
                "COPILOT_HELP_TEXT": "--autopilot\n--output-format\n--stream",
            },
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertEqual(
            (base / "out.log").read_text(),
            "adapter error: rate_limit / HTTP 429: quota exhausted\nrecovered\n",
        )

    def test_cli_failure_is_preserved_with_session_error(self) -> None:
        base = self.sandbox()
        activity = base / "out.activity.jsonl"
        fixture = json.dumps({"type": "session.error", "data": {"message": "fatal"}})
        r = self.run_adapter(
            self.CMD,
            self.base_flags(base),
            fake_name="copilot",
            fixture_text=fixture,
            env_extra={
                "SPECULA_ACTIVITY_LOG": str(activity),
                "COPILOT_HELP_TEXT": "--autopilot\n--output-format\n--stream",
                "ADAPTER_EXIT_CODE": "9",
            },
        )
        self.assertEqual(r["returncode"], 9, r["stderr"])

    @unittest.skipUnless(Path("/dev/full").exists(), "requires /dev/full")
    def test_readable_log_failure_keeps_raw_stream_and_fails_adapter(self) -> None:
        for cli_rc, expected in (("0", 1), ("9", 9)):
            with self.subTest(cli_rc=cli_rc):
                base = self.sandbox()
                log = base / "out.log"
                log.symlink_to("/dev/full")
                activity = base / "out.activity.jsonl"
                first = json.dumps({"type": "assistant.message", "data": {"content": "first"}})
                final = json.dumps({"type": "assistant.message", "data": {"content": "final"}})
                fixture = "\n".join([first, final])
                r = self.run_adapter(
                    self.CMD,
                    [self.with_prompt_file(base), f"--log={log}"],
                    fake_name="copilot",
                    fixture_text=fixture,
                    env_extra={
                        "SPECULA_ACTIVITY_LOG": str(activity),
                        "COPILOT_HELP_TEXT": "--autopilot\n--output-format\n--stream",
                        "ADAPTER_EXIT_CODE": cli_rc,
                    },
                )
                self.assertEqual(r["returncode"], expected, r["stderr"])
                self.assertIn("readable log", r["stderr"])
                self.assertEqual(activity.read_text(), fixture)

    def test_raw_activity_failure_drains_cli_without_failing_adapter(self) -> None:
        base = self.sandbox()
        activity = base / "bad-activity"
        activity.mkdir()
        log = base / "out.log"
        final = json.dumps({"type": "assistant.message", "data": {"content": "final"}})
        r = self.run_adapter(
            self.CMD,
            [self.with_prompt_file(base), f"--log={log}"],
            fake_name="copilot",
            fixture_text=final,
            env_extra={
                "SPECULA_ACTIVITY_LOG": str(activity),
                "COPILOT_HELP_TEXT": "--autopilot\n--output-format\n--stream",
            },
        )
        self.assertEqual(r["returncode"], 0, r["stderr"])
        self.assertIn("activity log", r["stderr"])
        self.assertEqual(log.read_text(), "final\n")

    def test_log_required(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base)])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("--log is required", r["stderr"])

    def test_prompt_xor_prompt_file(self) -> None:
        base = self.sandbox()
        r = self.invoke(["--prompt=x", self.with_prompt_file(base), f"--log={base}/out.log"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("mutually exclusive", r["stderr"])

    def test_unknown_option(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--bogus"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("unknown option", r["stderr"])

    def test_oversized_prompt_rejected(self) -> None:
        # copilot takes the prompt only as an argv argument (no stdin/prompt-file
        # input into the CLI), so a prompt over MAX_ARG_STRLEN is rejected up front
        # rather than sent to exec, where it would fail with E2BIG and no output.
        base = self.sandbox()
        log = base / "out.log"
        log.write_text("stale output\n")
        r = self.invoke([self.with_prompt_file(base, "x" * 130000), f"--log={base}/out.log"])
        self.assertEqual(r["returncode"], 1)
        self.assertIn("the copilot CLI accepts", r["stderr"])
        self.assertEqual(r["argv"], [])  # copilot was never invoked
        self.assertEqual(log.read_text(), r["stderr"])
        self.assertNotIn("stale output", log.read_text())

    def test_help(self) -> None:
        r = self.invoke(["--help"])
        self.assertEqual(r["returncode"], 0)
        self.assertIn("Adapter: copilot-cli", r["stdout"])


if __name__ == "__main__":
    unittest.main()
