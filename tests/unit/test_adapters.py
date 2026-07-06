"""Behavior tests for the agent adapters (claude-code, codex, copilot-cli).

These pin the *command-construction contract*: given the launcher-facing flags,
what does each adapter invoke the underlying CLI with, which flags map/skip, and
how does argument validation behave. This is the only coverage of that contract
now that the characterization goldens are gone — a wrong flag here silently
breaks every agent call.

Each case runs the real adapter as a subprocess with a fake `claude`/`codex`/
`copilot` on PATH that records the argv (and, for claude, stdin + the exported
CLAUDE_CONFIG_DIR + a session-env marker) it observed, then asserts on the
recording. `claude-code` is the Python port (adapters/claude_code.py); `codex`
and `copilot-cli` are still bash (scripts/launch/adapters/*.sh).

stdlib unittest, collected natively by pytest:

    uv run python -m unittest tests.unit.test_adapters -v
"""

from __future__ import annotations

import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, TypedDict

REPO_ROOT = Path(__file__).resolve().parents[2]
CLAUDE_PY = REPO_ROOT / "src" / "specula" / "adapters" / "claude_code.py"
CODEX_SH = REPO_ROOT / "scripts" / "launch" / "adapters" / "codex.sh"
COPILOT_SH = REPO_ROOT / "scripts" / "launch" / "adapters" / "copilot-cli.sh"

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
    "CLAUDECODE",
    "CLAUDE_CODE_SSE_PORT",
    "CLAUDE_CODE_ENTRYPOINT",
    "SPECULA_PHASE",
    "SPECULA_WORK_DIR",
    "SPECULA_STOP_GATE",
    "CODEX_HOME",
)


class AdapterRun(TypedDict):
    returncode: int
    stdout: str
    stderr: str
    argv: list[str]
    configdir: str
    sessionenv: str
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
            'printf "%s\\n" "$@" > "${ADAPTER_ARGV_FILE:-/dev/null}"',
        ]
        if record_extra:
            lines += [
                'printf "%s\\n" "${CLAUDE_CONFIG_DIR:-<unset>}" > "${ADAPTER_CONFIGDIR_FILE:-/dev/null}"',
                'printf "%s\\n" "${CLAUDECODE:-<unset>}" > "${ADAPTER_SESSIONENV_FILE:-/dev/null}"',
                'cat > "${ADAPTER_STDIN_FILE:-/dev/null}"',
            ]
        lines.append(f"cat {json.dumps(str(fixture))}")
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
        proc = subprocess.run(cmd + flags, cwd=str(base), env=env, capture_output=True, text=True)

        def read(p: Path) -> str | None:
            return p.read_text() if p.exists() else None

        return {
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "argv": (read(record["ADAPTER_ARGV_FILE"]) or "").splitlines(),
            "configdir": (read(record["ADAPTER_CONFIGDIR_FILE"]) or "").strip(),
            "sessionenv": (read(record["ADAPTER_SESSIONENV_FILE"]) or "").strip(),
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

    def test_missing_claude_still_exits_zero(self) -> None:
        # bash wrote the shell error into RAW_JSON and carried on; the port mirrors
        # that: spawn failure -> exit 0, .log holds the error, .usage.json=parse_failed.
        base = self.sandbox()
        r = self.run_adapter(
            self.CMD, self.base_flags(base), fake_name="claude", fixture_text="", with_fake=False, record_extra=True
        )
        self.assertEqual(r["returncode"], 0)
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
            cwd=str(base), env=env, capture_output=True, text=True,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        usage: dict[str, Any] = json.loads((base / "out.usage.json").read_text())
        return usage


# ── codex (bash) ─────────────────────────────────────────────────────────────
class CodexAdapter(AdapterCase):
    CMD = ["bash", str(CODEX_SH)]

    def invoke(self, flags: list[str], *, env_extra: dict[str, str] | None = None) -> AdapterRun:
        return self.run_adapter(self.CMD, flags, fake_name="codex", fixture_text="codex ran\n", env_extra=env_extra)

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log", "--max-turns=0"]

    def test_command_construction(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base))
        self.assertEqual(r["returncode"], 0)
        # codex exec --dangerously-bypass-approvals-and-sandbox "<prompt>"
        self.assertEqual(r["argv"], ["exec", "--dangerously-bypass-approvals-and-sandbox", "the prompt"])

    def test_prompt_from_file_is_read(self) -> None:
        base = self.sandbox()
        r = self.invoke([self.with_prompt_file(base, "codex task\n"), f"--log={base}/out.log", "--max-turns=0"])
        self.assertEqual(r["argv"][-1], "codex task")

    def test_output_redirected_to_log(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        self.assertEqual((base / "out.log").read_text(), "codex ran\n")

    def test_usage_json_tags_agent_codex(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        self.assertEqual(json.loads((base / "out.usage.json").read_text())["agent"], "codex")

    def test_alias_and_effort_accepted_but_ignored(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--claude-alias=x", "--effort=high"])
        self.assertEqual(r["returncode"], 0)
        self.assertEqual(r["argv"], ["exec", "--dangerously-bypass-approvals-and-sandbox", "the prompt"])

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

    def invoke(self, flags: list[str], *, env_extra: dict[str, str] | None = None) -> AdapterRun:
        return self.run_adapter(self.CMD, flags, fake_name="copilot", fixture_text="copilot ran\n", env_extra=env_extra)

    def base_flags(self, base: Path) -> list[str]:
        return [self.with_prompt_file(base), f"--log={base}/out.log"]

    def test_command_construction(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base))
        self.assertEqual(r["returncode"], 0)
        # copilot -p "<prompt>" --allow-all
        self.assertEqual(r["argv"], ["-p", "the prompt", "--allow-all"])

    def test_model_flag_appended(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--model=gpt-5"])
        self.assertEqual(r["argv"], ["-p", "the prompt", "--allow-all", "--model", "gpt-5"])

    def test_model_from_env(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base), env_extra={"COPILOT_MODEL": "envmodel"})
        self.assertEqual(r["argv"][-2:], ["--model", "envmodel"])

    def test_max_turns_maps_to_autopilot_continues(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--max-turns=4"])
        self.assertEqual(r["argv"][-2:], ["--max-autopilot-continues", "4"])

    def test_max_turns_zero_omits_flag(self) -> None:
        base = self.sandbox()
        r = self.invoke(self.base_flags(base) + ["--max-turns=0"])
        self.assertNotIn("--max-autopilot-continues", r["argv"])

    def test_output_redirected_to_log(self) -> None:
        base = self.sandbox()
        self.invoke(self.base_flags(base))
        self.assertEqual((base / "out.log").read_text(), "copilot ran\n")

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

    def test_help(self) -> None:
        r = self.invoke(["--help"])
        self.assertEqual(r["returncode"], 0)
        self.assertIn("Adapter: copilot-cli", r["stdout"])


if __name__ == "__main__":
    unittest.main()
