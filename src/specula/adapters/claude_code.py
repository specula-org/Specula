"""Adapter: claude-code (Python port of claude-code.sh).

Unified interface for invoking the Claude Code CLI. The command-construction
contract (argv assembly, config-dir from the alias, exit codes incl. the
rate-limit 75, the num_turns session fixup) is pinned by
tests/unit/test_adapters.py.

Options:
  --prompt=...          Task prompt (mutually exclusive with --prompt-file)
  --prompt-file=FILE    Read prompt from file (mutually exclusive with --prompt)
  --max-turns=N         (DEPRECATED, ignored — use --max-budget)
  --max-budget=N        Max dollar budget for API calls (optional)
  --claude-alias=NAME   Claude CLI alias/profile (default: claude). Selects
                        CLAUDE_CONFIG_DIR=$HOME/.<NAME>. Also via CLAUDE_ALIAS env.
  --effort=LEVEL        low|medium|high|xhigh|max (default: max; via CLAUDE_EFFORT)
  --model=NAME          Model alias/name (default: profile default; via CLAUDE_MODEL)
  --resume-state=FILE   Persist or resume the exact Claude session for this logical turn
  --log=FILE            Log file path (required)
  --background          Run in background (accepted; caller handles backgrounding)
  --help                Show this help
"""

import contextlib
import json
import os
import shlex
import subprocess
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path
from typing import IO, Any

if __package__:
    from .utils.event_stream import stream_events
    from .utils.policy import POLICY_BLOCKED_RC, final_diagnostic_has_policy_block, looks_policy_blocked
    from .utils.resume import ResumeStateError, capture_session_id, read_session_id
    from .utils.transient import TRANSIENT_FAILURE_RC, final_diagnostic_has_transient_failure, looks_transient
else:
    from utils.event_stream import stream_events  # type: ignore[import-not-found, no-redef]
    from utils.policy import (  # type: ignore[import-not-found, no-redef]
        POLICY_BLOCKED_RC,
        final_diagnostic_has_policy_block,
        looks_policy_blocked,
    )
    from utils.resume import (  # type: ignore[import-not-found, no-redef]
        ResumeStateError,
        capture_session_id,
        read_session_id,
    )
    from utils.transient import (  # type: ignore[import-not-found, no-redef]
        TRANSIENT_FAILURE_RC,
        final_diagnostic_has_transient_failure,
        looks_transient,
    )

HELP = __doc__

# Nested-session markers stripped before spawning claude, so the child CLI does
# not believe it is running inside another Claude Code session.
SESSION_ENV_VARS = ("CLAUDECODE", "CLAUDE_CODE_SSE_PORT", "CLAUDE_CODE_ENTRYPOINT")

_RATE_LIMIT_MARKERS = ("hit your limit", "hit your session limit")


def _derived_path(log_file: str, suffix: str) -> str:
    """Mirror bash `${LOG_FILE%.log}<suffix>`."""
    stem = log_file[:-4] if log_file.endswith(".log") else log_file
    return stem + suffix


def _maybe_wrap_sandbox(cmd: list[str], work_dir: str) -> list[str]:
    """Optionally wrap the agent command in the outer srt sandbox (M1.3).

    Opt-in via ``SPECULA_SANDBOX=on``; additive — when off/unset the command is
    returned byte-for-byte (legacy). One outer srt layer wraps claude and every
    descendant it spawns (TLC / MCP / build); the inner
    ``--dangerously-skip-permissions`` stays, so the agent runs YOLO with no
    nested second sandbox. Backend path is repo-relative but overridable via
    ``SPECULA_SANDBOX_BACKEND`` (e.g. an installed layout).
    """
    if os.environ.get("SPECULA_SANDBOX", "").lower() != "on":
        return cmd
    backend = os.environ.get("SPECULA_SANDBOX_BACKEND") or os.path.normpath(
        os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "..",
            "..",
            "..",
            "scripts",
            "launch",
            "sandbox",
            "backend.mjs",
        )
    )
    workspace = work_dir or os.getcwd()
    wrapped = ["node", backend, "--workspace", workspace]
    config = os.environ.get("SPECULA_SANDBOX_CONFIG", "")
    if config:
        wrapped += ["--config", config]
    return [*wrapped, "--", *cmd]


def _parse_result(raw_text: str) -> dict[str, Any] | None:
    """Find the Claude result in single-result JSON or a stream-json capture."""
    try:
        d = json.loads(raw_text)
    except Exception:
        d = None
    if isinstance(d, dict):
        return d
    for line in reversed(raw_text.splitlines()):
        try:
            candidate = json.loads(line)
        except Exception:
            continue
        if isinstance(candidate, dict) and (candidate.get("type") == "result" or "result" in candidate):
            return candidate
    return None


def _rate_limited(raw_text: str, streaming: bool) -> bool:
    """Did *claude* say it is rate limited?

    It announces that either as a plain-text banner (no JSON at all) or inside
    its final result record. A stream-json capture additionally holds every
    assistant message and CLI diagnostic, so scanning it whole would turn a log
    the agent merely *read* into a spurious EX_TEMPFAIL — and callers treat 75 as
    "stop everything and wait for the quota to reset". Keep the scan on claude's
    own verdict."""

    def error_result(record: object) -> bool:
        if not isinstance(record, dict):
            return False
        # Recent Claude CLI versions return a structurally successful `result`
        # envelope for API failures.  The payload is still unambiguous: HTTP
        # 429 plus terminal_reason=api_error.  Prefer that machine-readable
        # signal over wording, which changes between CLI releases.
        api_status = record.get("api_error_status")
        if api_status == 429 or api_status == "429":
            return True
        verdict = record.get("is_error")
        subtype = record.get("subtype")
        terminal_reason = record.get("terminal_reason")
        subtype_is_error = isinstance(subtype, str) and subtype.startswith("error")
        if verdict is not True and not subtype_is_error and terminal_reason != "api_error":
            return False
        result = record.get("result")
        return isinstance(result, str) and any(marker in result.casefold() for marker in _RATE_LIMIT_MARKERS)

    # Non-streaming output is one JSON result. A successful result can quote an
    # old rate-limit message in its report, so the phrase alone is not a verdict.
    try:
        record = json.loads(raw_text)
    except Exception:
        record = None
    if isinstance(record, dict):
        return error_result(record)
    if not streaming:
        # A CLI diagnostic may precede the otherwise valid final JSON record.
        # Prefer that structured verdict to scanning the entire capture: the
        # successful assistant response may legitimately quote an old limit.
        record = _parse_result(raw_text)
        if record is not None:
            return error_result(record)
        folded = raw_text.casefold()
        return any(marker in folded for marker in _RATE_LIMIT_MARKERS)

    for line in raw_text.splitlines():
        try:
            record = json.loads(line)
        except Exception:
            folded = line.casefold()
            # Claude's plain-text banner (as opposed to an assistant event).
            if any(marker in folded for marker in _RATE_LIMIT_MARKERS):
                return True
            continue
        if isinstance(record, dict) and record.get("type") == "result" and error_result(record):
            return True
    return False


def _result_policy_blocked(record: object) -> bool:
    """Whether Claude's terminal result is an unresolved provider policy block.

    Inspect the result text only after the terminal envelope declares an error.
    Successful agents may legitimately quote a policy-block diagnostic while
    explaining or repairing an earlier run.
    """
    if not isinstance(record, dict):
        return False
    verdict = record.get("is_error")
    subtype = record.get("subtype")
    terminal_reason = record.get("terminal_reason")
    api_status = record.get("api_error_status")
    subtype_is_error = isinstance(subtype, str) and subtype.startswith("error")
    if (
        verdict is not True
        and not subtype_is_error
        and terminal_reason != "api_error"
        and api_status in (None, "", 0, "0")
    ):
        return False
    return looks_policy_blocked(record) or looks_policy_blocked(record.get("result"))


def _result_transient_failure(record: object) -> bool:
    """Whether Claude's terminal result is a retryable provider failure.

    The failed-envelope gate is essential: a successful report may quote the
    same capacity or transport diagnostic while describing earlier work.
    """
    if not isinstance(record, dict):
        return False
    verdict = record.get("is_error")
    subtype = record.get("subtype")
    terminal_reason = record.get("terminal_reason")
    api_status = record.get("api_error_status")
    subtype_is_error = isinstance(subtype, str) and subtype.startswith("error")
    if (
        verdict is not True
        and not subtype_is_error
        and terminal_reason != "api_error"
        and api_status in (None, "", 0, "0")
    ):
        return False
    if api_status in (500, 502, 503, 504, 529, "500", "502", "503", "504", "529"):
        return True
    return looks_transient(record) or looks_transient(record.get("result"))


def _drain(stream: IO[bytes]) -> None:
    """Read a pipe to EOF and discard it, so the child never blocks writing."""
    with contextlib.suppress(OSError):
        while stream.read(1 << 16):
            pass


def _read_capture(path: str) -> str:
    """The captured claude output, or "" when it could not be written/read.

    errors="replace" is a deliberate deviation from the bash, which died on
    non-UTF-8 claude output (UnicodeDecodeError under set -e: non-zero exit,
    empty .log, no .usage.json — and a rate-limit hit lost its exit-75 retry
    signal). Degrade to U+FFFD + parse_failed on the normal exit-code path
    instead (test_adapters.py::test_nonutf8_output_degrades_gracefully)."""
    with contextlib.suppress(OSError), open(path, errors="replace") as fh:
        return fh.read()
    return ""


def _extract_log(d: dict[str, Any] | None, raw_text: str, log_file: str) -> None:
    """Result text -> .log; on JSON-parse failure, fall back to the raw output."""
    with open(log_file, "w") as fh:
        if d is not None:
            print(d.get("result", ""), file=fh)
        else:
            print(raw_text, file=fh)


def _extract_usage(d: dict[str, Any] | None, usage_path: str, fallback_session_id: str = "") -> None:
    """Usage stats -> .usage.json, fixing num_turns from the session JSONL when a
    session_id is present. Any failure reports ``parse_failed`` and retains a
    known session ID so a resumable failed turn stays attributable."""
    session_id = fallback_session_id
    if isinstance(d, dict):
        result_session_id = d.get("session_id")
        if isinstance(result_session_id, str) and result_session_id:
            session_id = result_session_id
    try:
        if d is None:
            raise ValueError("result JSON unparseable")
        usage = {
            "session_id": session_id,
            "total_cost_usd": d.get("total_cost_usd", 0),
            "num_turns": d.get("num_turns", 0),
            "duration_ms": d.get("duration_ms", 0),
            "stop_reason": d.get("stop_reason", ""),
            "usage": d.get("usage", {}),
            "model_usage": d.get("modelUsage", {}),
        }
        if session_id:
            cwd = os.getcwd()
            proj_key = cwd.replace("/", "-").lstrip("-")
            config_dir = os.environ.get("CLAUDE_CONFIG_DIR") or os.path.expanduser("~/.claude")
            proj_dir = os.path.join(config_dir, "projects", f"-{proj_key}")
            jsonl_path = os.path.join(proj_dir, f"{session_id}.jsonl")
            if os.path.exists(jsonl_path):
                assistant_count = 0
                tool_count = 0
                with open(jsonl_path) as f:
                    for line in f:
                        # Session transcripts are dominated by huge tool-result
                        # lines; skip the full JSON parse for anything that can't
                        # be an assistant turn (cheap superset substring test).
                        if '"assistant"' not in line:
                            continue
                        try:
                            msg = json.loads(line)
                            if msg.get("type") == "assistant":
                                assistant_count += 1
                                content = msg.get("message", {}).get("content", [])
                                if isinstance(content, list):
                                    tool_count += sum(
                                        1 for c in content if isinstance(c, dict) and c.get("type") == "tool_use"
                                    )
                        except Exception:
                            pass
                usage["num_turns_reported"] = usage["num_turns"]
                usage["num_turns"] = assistant_count
                usage["num_tool_uses"] = tool_count
        with open(usage_path, "w") as uf:
            json.dump(usage, uf, indent=2)
            uf.write("\n")
    except Exception:
        with open(usage_path, "w") as uf:
            failure: dict[str, Any] = {"error": "parse_failed"}
            if session_id:
                failure["session_id"] = session_id
            json.dump(failure, uf)
            uf.write("\n")


def _die(msg: str) -> int:
    print(msg, file=sys.stderr)
    return 1


def main(argv: list[str]) -> int:
    prompt = ""
    prompt_file = ""
    max_budget = ""
    resume_state = ""
    resume_state_set = False
    log_file = ""
    _background = False  # accepted; caller does the backgrounding, as in bash
    # `or`: bash ${VAR:-default} treats an exported-but-empty var as unset — an
    # empty CLAUDE_EFFORT must still mean "max", not "skip the --effort flag".
    claude_alias = os.environ.get("CLAUDE_ALIAS") or "claude"
    effort = os.environ.get("CLAUDE_EFFORT") or "max"
    model = os.environ.get("CLAUDE_MODEL", "")

    for arg in argv:
        if arg.startswith("--prompt="):
            prompt = arg[len("--prompt=") :]
        elif arg.startswith("--prompt-file="):
            prompt_file = arg[len("--prompt-file=") :]
        elif arg.startswith("--max-turns="):
            pass  # deprecated, ignored
        elif arg.startswith("--max-budget="):
            max_budget = arg[len("--max-budget=") :]
        elif arg.startswith("--claude-alias="):
            claude_alias = arg[len("--claude-alias=") :]
        elif arg.startswith("--effort="):
            effort = arg[len("--effort=") :]
        elif arg.startswith("--model="):
            model = arg[len("--model=") :]
        elif arg.startswith("--resume-state="):
            resume_state = arg[len("--resume-state=") :]
            resume_state_set = True
        elif arg.startswith("--log="):
            log_file = arg[len("--log=") :]
        elif arg == "--background":
            _background = True
        elif arg in ("--help", "-h"):
            print(HELP)
            return 0
        else:
            return _die(f"claude-code adapter: unknown option: {arg}")

    # Environment variables are wrapper fallbacks, not a second input channel
    # for the child process.  The resolved values are expressed through argv;
    # removing them here makes an explicit empty flag a real reset.
    os.environ.pop("CLAUDE_MODEL", None)
    os.environ.pop("CLAUDE_EFFORT", None)
    for name in ("SPECULA_RESUME_STATE", "SPECULA_RESUME_MODEL", "SPECULA_RESUME_EFFORT"):
        os.environ.pop(name, None)

    # ── Validate arguments ──
    if prompt and prompt_file:
        return _die("claude-code adapter: --prompt and --prompt-file are mutually exclusive")
    if not prompt and not prompt_file:
        return _die("claude-code adapter: one of --prompt or --prompt-file is required")
    if not log_file:
        return _die("claude-code adapter: --log is required")
    if resume_state_set and not resume_state:
        return _die("claude-code adapter: --resume-state requires a path")

    # A resume state belongs to one exact logical turn.  Refuse mismatched or
    # malformed state rather than silently starting a fresh session and
    # repeating work that Claude may already have completed.
    resume_session_id = ""
    if resume_state:
        resume_state = os.path.abspath(resume_state)
        try:
            resume_session_id = (
                read_session_id(
                    resume_state,
                    adapter="claude-code",
                    cwd=os.getcwd(),
                    model=model,
                    effort=effort,
                )
                or ""
            )
        except (OSError, ResumeStateError) as e:
            return _die(f"claude-code adapter: invalid resume state: {e}")

    # ── Resolve prompt ──
    # Feed prompt via stdin (not -p) to keep the process cmdline clean, so
    # `pkill -f` can't collateral-kill on strings like "tlc2.TLC".
    tmp_prompt = None
    hidden_activity_log: str | None = None
    if prompt_file:
        if not os.path.isfile(prompt_file):
            return _die(f"claude-code adapter: prompt file not found: {prompt_file}")
        prompt_input = prompt_file
    else:
        fd, tmp_prompt = tempfile.mkstemp()
        with os.fdopen(fd, "w") as f:
            f.write(prompt + "\n")
        prompt_input = tmp_prompt

    try:
        # ── Environment setup ──
        for var in SESSION_ENV_VARS:
            os.environ.pop(var, None)
        # Alias determines the config dir authoritatively (do NOT inherit an
        # ambient CLAUDE_CONFIG_DIR, which would redirect quota-sensitive runs).
        os.environ["CLAUDE_CONFIG_DIR"] = os.environ.get("HOME", "") + "/." + (claude_alias or "claude")
        # ── Stop gate (execution layer) ──
        # Generic gate interface: the phase launcher exports SPECULA_PHASE +
        # SPECULA_WORK_DIR (see src/specula/stop_gate.py). Parallel workers may
        # additionally narrow gate state/PID scanning with
        # SPECULA_STOP_GATE_WORK_DIR while retaining the target workspace for the
        # outer sandbox. When the required context is present, register a Stop
        # hook so the agent cannot end its turn while background jobs it started
        # run unobserved, or without the phase deliverable.
        # Without them (interactive use, tests, other callers) nothing is
        # injected and the claude argv is unchanged.
        settings_args: list[str] = []
        work_dir = os.environ.get("SPECULA_WORK_DIR", "")
        gate_work_dir = os.environ.get("SPECULA_STOP_GATE_WORK_DIR", "") or work_dir
        if (
            work_dir
            and gate_work_dir
            and os.environ.get("SPECULA_PHASE")
            and os.environ.get("SPECULA_STOP_GATE", "").lower() != "off"
            and os.path.isdir(work_dir)
            and os.path.isdir(gate_work_dir)
        ):
            try:
                gate = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "stop_gate.py"))
                state_dir = os.path.join(gate_work_dir, ".stop-gate")
                os.makedirs(state_dir, exist_ok=True)
                # Fresh fuse per agent run — via the gate's own CLI (like
                # codex.sh) so the state-file list has exactly one owner.
                subprocess.run([sys.executable, gate, "reset", gate_work_dir], check=False)
                hook = {"type": "command", "command": f"python3 {shlex.quote(gate)} claude", "timeout": 60}
                settings_path = os.path.join(state_dir, "claude-settings.json")
                with open(settings_path, "w") as sf:
                    json.dump({"hooks": {"Stop": [{"hooks": [hook]}]}}, sf, indent=2)
                    sf.write("\n")
                settings_args = ["--settings", settings_path]
            except OSError as e:  # fail-open: a broken gate must never wedge the run
                settings_args = []
                print(
                    f"claude-code adapter: stop-gate setup failed ({e}); continuing without the gate", file=sys.stderr
                )

        # ── Build command ──
        activity_log = os.environ.get("SPECULA_ACTIVITY_LOG", "")
        stream_activity_log = activity_log
        if resume_state and not stream_activity_log:
            # Exact resume state requires Claude's early system/init event even
            # when progress display is disabled. Keep the structured stream in
            # a private sidecar and remove it after post-processing.
            try:
                fd, hidden_activity_log = tempfile.mkstemp(prefix="specula-claude-activity-", suffix=".jsonl")
            except OSError as exc:
                return _die(f"claude-code adapter: unable to create session-capture stream: {exc}")
            os.close(fd)
            stream_activity_log = hidden_activity_log
        streaming = bool(stream_activity_log)
        output_format = "stream-json" if streaming else "json"
        cmd = ["claude", "--print", "--dangerously-skip-permissions", "--output-format", output_format]
        if resume_session_id:
            cmd += ["--resume", resume_session_id]
        if streaming:
            cmd += ["--verbose"]
        if effort and effort != "default":
            cmd += ["--effort", effort]
        if max_budget and max_budget != "0":
            cmd += ["--max-budget-usd", max_budget]
        if model:
            cmd += ["--model", model]
        cmd += settings_args
        cmd = _maybe_wrap_sandbox(cmd, work_dir)

        # ── Run ──
        raw_json = _derived_path(log_file, ".raw.json")
        capture_path = stream_activity_log or raw_json
        cli_rc = 127
        proc: subprocess.Popen[bytes] | None = None
        activity_failed = False
        stream_failed = False
        stream_resume_failed = False
        stream_terminal_record: object | None = None
        stream_policy_block_error: str | None = None
        stream_plain_policy_block_error: str | None = None
        stream_transient_error: str | None = None
        stream_plain_transient_error: str | None = None
        stream_plain_diagnostics: tuple[str, ...] = ()
        # This `try` covers the spawn ONLY. An OSError here means no agent work
        # has happened (claude missing / not executable / unreadable prompt), so
        # a conventional command-not-found status is the honest answer.
        try:
            if streaming:
                with open(prompt_input) as pin:
                    proc = subprocess.Popen(cmd, stdin=pin, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            else:
                with open(prompt_input) as pin, open(capture_path, "w") as out:
                    cli_rc = subprocess.run(cmd, stdin=pin, stdout=out, stderr=subprocess.STDOUT).returncode
        except OSError as e:
            error = f"claude-code adapter: failed to run claude: {e}\n"
            for path in (capture_path, log_file) if streaming else (capture_path,):
                with contextlib.suppress(OSError), open(path, "w") as out:
                    out.write(error)

        if proc is not None:
            if proc.stdout is not None:  # always, given stdout=PIPE
                try:
                    session_capture: Callable[[str], None] | None = None
                    if resume_state:

                        def explicit_capture(session_id: str) -> None:
                            capture_session_id(
                                resume_state,
                                adapter="claude-code",
                                session_id=session_id,
                                cwd=os.getcwd(),
                                model=model,
                                effort=effort,
                            )

                        session_capture = explicit_capture
                    stream_status = stream_events(
                        "claude-code",
                        Path(stream_activity_log),
                        Path(log_file),
                        proc.stdout,
                        session_capture=session_capture,
                    )
                    activity_failed = not stream_status.activity_ok
                    stream_failed = not stream_status.log_ok
                    stream_resume_failed = not stream_status.resume_ok
                    stream_terminal_record = stream_status.terminal_record
                    stream_policy_block_error = stream_status.policy_block_error
                    stream_plain_policy_block_error = stream_status.plain_policy_block_error
                    stream_transient_error = stream_status.transient_error
                    stream_plain_transient_error = stream_status.plain_transient_error
                    stream_plain_diagnostics = stream_status.plain_diagnostics
                except OSError as e:
                    # Sink failures are returned after a full drain. An exception
                    # here means the source pipe itself failed and neither output
                    # can be trusted as a complete capture.
                    activity_failed = True
                    stream_failed = True
                    print(f"claude-code adapter: event stream failed: {e}", file=sys.stderr)
                    _drain(proc.stdout)
            cli_rc = proc.wait()

        # A failed activity sink may still point at stale data (or a
        # non-terminating device such as /dev/full). Reconstruct the terminal
        # result/CLI diagnostics retained by stream_events instead of reopening
        # it; activity telemetry is never the only source of result semantics.
        if activity_failed:
            raw_text = (
                json.dumps(stream_terminal_record)
                if stream_terminal_record is not None
                else "".join(stream_plain_diagnostics)
            )
        else:
            raw_text = _read_capture(capture_path)

        # ── Detect rate limit → exit 75 (EX_TEMPFAIL) so callers can wait/retry ──
        rate_limited = cli_rc == 75 or _rate_limited(raw_text, streaming)
        if rate_limited:
            print("claude-code adapter: rate limit hit", file=sys.stderr)

        postprocess_failed = False
        resume_postprocess_failed = False
        result = _parse_result(raw_text)
        usage_session_id = resume_session_id
        if resume_state and result is not None:
            result_session_id = result.get("session_id")
            if isinstance(result_session_id, str) and result_session_id:
                usage_session_id = result_session_id
                try:
                    capture_session_id(
                        resume_state,
                        adapter="claude-code",
                        session_id=result_session_id,
                        cwd=os.getcwd(),
                        model=model,
                        effort=effort,
                    )
                except (OSError, ResumeStateError) as e:
                    postprocess_failed = True
                    resume_postprocess_failed = True
                    print(f"claude-code adapter: resume state write failed: {e}", file=sys.stderr)
        if resume_state and not usage_session_id:
            # In stream-json mode Claude exposes the session in `system/init`
            # before the terminal result. event_stream persists it immediately;
            # read it back so usage remains tied to the same exact session even
            # when a CLI version omits session_id from its result envelope.
            try:
                usage_session_id = (
                    read_session_id(
                        resume_state,
                        adapter="claude-code",
                        cwd=os.getcwd(),
                        model=model,
                        effort=effort,
                    )
                    or ""
                )
            except (OSError, ResumeStateError) as e:
                postprocess_failed = True
                resume_postprocess_failed = True
                print(f"claude-code adapter: resume state read failed: {e}", file=sys.stderr)
        policy_blocked = stream_policy_block_error is not None or _result_policy_blocked(result)
        if streaming and cli_rc != 0 and stream_plain_policy_block_error is not None:
            policy_blocked = True
        if not streaming and cli_rc != 0 and result is None:
            # A failed pre-stream CLI may emit only a plain provider diagnostic.
            # Never apply this scan to a successful run or to arbitrary streamed
            # assistant history, where quoting an old block is normal task text.
            policy_blocked = final_diagnostic_has_policy_block(raw_text)
        transient_failure = stream_transient_error is not None or _result_transient_failure(result)
        if streaming and cli_rc != 0 and stream_plain_transient_error is not None:
            transient_failure = True
        if not streaming and cli_rc != 0 and result is None:
            # As with policy diagnostics, the plain fallback is restricted to a
            # failed CLI with no structured terminal result. Agent-authored text
            # and successful reports are never retry signals.
            transient_failure = final_diagnostic_has_transient_failure(raw_text)
        if streaming:
            try:
                with open(raw_json, "w") as out:
                    if result is not None:
                        json.dump(result, out)
                        out.write("\n")
                    else:
                        out.write(raw_text)
            except OSError as e:
                postprocess_failed = True
                print(f"claude-code adapter: raw result write failed: {e}", file=sys.stderr)
        if not streaming:
            try:
                _extract_log(result, raw_text, log_file)
            except OSError as e:
                postprocess_failed = True
                print(f"claude-code adapter: readable log write failed: {e}", file=sys.stderr)
        try:
            _extract_usage(result, _derived_path(log_file, ".usage.json"), usage_session_id)
        except OSError as e:
            postprocess_failed = True
            print(f"claude-code adapter: usage write failed: {e}", file=sys.stderr)

        if stream_resume_failed or resume_postprocess_failed:
            return 1
        if rate_limited:
            return 75
        if policy_blocked or cli_rc == POLICY_BLOCKED_RC:
            print("claude-code adapter: provider policy block", file=sys.stderr)
            return POLICY_BLOCKED_RC
        if transient_failure:
            print("claude-code adapter: transient provider failure", file=sys.stderr)
            return TRANSIENT_FAILURE_RC
        if cli_rc != 0:
            return 1 if cli_rc == TRANSIENT_FAILURE_RC else cli_rc
        return 1 if stream_failed or postprocess_failed else 0
    finally:
        if hidden_activity_log is not None:
            with contextlib.suppress(OSError):
                os.remove(hidden_activity_log)
        if tmp_prompt is not None:
            with contextlib.suppress(OSError):
                os.remove(tmp_prompt)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
