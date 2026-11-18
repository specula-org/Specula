"""Run one agent session inside a bubblewrap sandbox and record behavior and cost.

Used by run.py (main incremental runs) and annotate.py (v2 annotation step).

Sandbox (same shape as the blind study's run_incremental.py):
  - bwrap --unshare-all --share-net --clearenv; /usr and /etc read-only; fresh /tmp;
  - the workspace is mounted at /work: listed paths read-only, listed paths writable;
  - HOME is a throwaway directory holding only the agent's credentials;
  - PATH starts with /work/tools/network-guard, which blocks curl/wget/gh/lynx and
    git fetch/clone/pull; the network itself stays up for the model API and builds.
  - Afterwards every shell command is scanned for research/history commands.

Backends:
  claude  `claude -p --output-format stream-json`; cost from the final result event.
  codex   `codex exec --json` (needs CODEX_AUTH=<auth.json>); usage from turn.completed events.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
import threading
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

from common import sha256, write_json

HOME = Path.home()
RUSTUP = HOME / ".rustup"
CARGO_BIN = HOME / ".cargo/bin"
CLAUDE_BIN = Path(os.path.realpath(shutil.which("claude") or HOME / ".local/bin/claude"))
CODEX_BIN = Path(os.path.realpath(shutil.which("codex") or HOME / ".local/bin/codex"))

DEFAULTS = {
    "claude": {"model": "claude-opus-5-5", "effort": "xhigh"},
    "codex": {"model": "gpt-5.6-sol", "effort": "xhigh"},
}

RESEARCH_PATTERNS = [
    re.compile(r"(?<![\w-])(?:curl|wget|gh)(?![\w-])"),
    re.compile(r"\bgit\s+(?:fetch|pull|clone|ls-remote|submodule)\b"),
    re.compile(r"\b(?:lynx|links|w3m)\b"),
    re.compile(r"\bpython(?:3)?\b.*\b(?:requests|urllib|httpx|aiohttp)\b.*https?://"),
]


AUTH_FAILURE = re.compile(r"Failed to authenticate|OAuth session expired|could not be refreshed|invalid_grant")


def _expires(path: Path) -> int:
    try:
        return int(json.loads(path.read_text()).get("claudeAiOauth", {}).get("expiresAt") or 0)
    except Exception:
        return 0


def _replace(src: Path, dest: Path) -> None:
    tmp = dest.with_name(dest.name + ".inv-e2e-tmp")
    shutil.copy2(src, tmp)
    os.replace(tmp, dest)


def _credential_sync(home: Path, activity: Path, proc, stop) -> None:
    """Keep the sandbox's and the host's claude OAuth credentials consistent during a run.

    Refresh tokens rotate: whichever side refreshes invalidates the other's copy. Every 30 s,
    the copy with the later expiresAt overwrites the other. Also stops the agent at once if it
    reports an authentication failure (otherwise it can hang until the timeout)."""
    host, box = HOME / ".claude/.credentials.json", home / ".claude/.credentials.json"
    seen = 0
    while not stop.wait(30):
        try:
            h, b = _expires(host), _expires(box)
            if b > h:
                _replace(box, host)
            elif h > b:
                _replace(host, box)
        except Exception:
            pass
        try:
            with activity.open("rb") as f:
                f.seek(seen)
                chunk = f.read()
                seen = f.tell()
            if b'"type":"result"' in chunk and AUTH_FAILURE.search(chunk.decode(errors="replace")):
                os.killpg(proc.pid, signal.SIGTERM)
                return
        except Exception:
            pass


def _tail(path: Path, n: int = 20000) -> str:
    try:
        with path.open("rb") as f:
            f.seek(max(0, path.stat().st_size - n))
            return f.read().decode(errors="replace")
    except OSError:
        return ""


def _home(backend: str) -> Path:
    home = Path(tempfile.mkdtemp(prefix="inv-e2e-home-", dir="/dev/shm"))
    if backend == "claude":
        (home / ".claude").mkdir()
        shutil.copy2(HOME / ".claude/.credentials.json", home / ".claude/.credentials.json")
        config = json.loads((HOME / ".claude.json").read_text()) if (HOME / ".claude.json").exists() else {}
        for key in ("projects", "githubRepoPaths", "history", "mcpServers"):
            config.pop(key, None)
        (home / ".claude.json").write_text(json.dumps(config))
    else:
        auth = Path(os.environ.get("CODEX_AUTH", HOME / ".codex/auth.json"))
        if not auth.is_file():
            raise RuntimeError(f"codex backend needs an auth.json (set CODEX_AUTH); not found: {auth}")
        (home / ".codex").mkdir()
        shutil.copy2(auth, home / ".codex/auth.json")
    return home


def bwrap_command(workspace: Path, ro: list[str], rw: list[str], extra_binds: list[tuple[str, str]],
                  home: Path, agent_argv: list[str]) -> list[str]:
    cmd = [
        "bwrap", "--die-with-parent", "--unshare-all", "--share-net", "--new-session", "--clearenv",
        "--proc", "/proc", "--dev", "/dev",
        "--ro-bind", "/usr", "/usr",
        "--symlink", "usr/bin", "/bin", "--symlink", "usr/lib", "/lib",
        "--symlink", "usr/lib64", "/lib64", "--symlink", "usr/sbin", "/sbin",
        "--ro-bind", "/etc", "/etc",
        "--dir", "/run",
    ]
    if Path("/run/systemd/resolve").exists():
        cmd += ["--ro-bind", "/run/systemd/resolve", "/run/systemd/resolve"]
    cmd += ["--tmpfs", "/tmp", "--dir", "/home", "--bind", str(home), "/home/agent", "--dir", "/work"]
    for rel in rw:
        cmd += ["--bind", str(workspace / rel), f"/work/{rel}"]
    for rel in ro:
        cmd += ["--ro-bind", str(workspace / rel), f"/work/{rel}"]
    for src, dst in extra_binds:
        cmd += ["--ro-bind", src, dst]
    if RUSTUP.exists():
        cmd += ["--ro-bind", str(RUSTUP), "/opt/rustup", "--ro-bind", str(CARGO_BIN), "/opt/cargo-bin"]
    env = {
        "HOME": "/home/agent",
        "PATH": "/work/tools/network-guard:/opt/agent:/opt/cargo-bin:/usr/local/go/bin:/usr/bin:/bin",
        "RUSTUP_HOME": "/opt/rustup",
        "CARGO_HOME": "/work/.cache/cargo",
        "CARGO_TARGET_DIR": "/work/.cache/cargo-target",
        "GOCACHE": "/work/.cache/go-build",
        "GOMODCACHE": "/work/.cache/go-mod",
        "GOPATH": "/work/.cache/gopath",
        "MAVEN_OPTS": "-Dmaven.repo.local=/work/.cache/m2",
        "REBAR_CACHE_DIR": "/work/.cache/rebar3",
        "TMPDIR": "/work/.cache/tmp",
        "SPECULA_ROOT": "/work",
        "LANG": "C.UTF-8",
        "USER": "agent",
        "SHELL": "/bin/bash",
        "TERM": "dumb",
    }
    for key, value in env.items():
        cmd += ["--setenv", key, value]
    cmd += ["--chdir", "/work", *agent_argv]
    return cmd


def agent_argv(backend: str, model: str, effort: str, budget_usd: float | None,
               schema: str | None, final_path: str) -> tuple[list[str], list[tuple[str, str]]]:
    if backend == "claude":
        argv = ["/opt/agent/claude", "-p", "--output-format", "stream-json", "--verbose",
                "--model", model, "--effort", effort,
                "--dangerously-skip-permissions", "--setting-sources", "project",
                "--no-session-persistence", "--disallowedTools", "WebFetch", "WebSearch"]
        if budget_usd:
            argv += ["--max-budget-usd", str(budget_usd)]
        return argv, [(str(CLAUDE_BIN), "/opt/agent/claude")]
    argv = ["/opt/agent/codex", "exec", "--ignore-user-config", "--strict-config", "--ephemeral",
            "--skip-git-repo-check", "--dangerously-bypass-approvals-and-sandbox",
            "--model", model, "--config", 'model_provider="openai"',
            "--config", f'model_reasoning_effort="{effort}"', "--json"]
    if schema:
        argv += ["--output-schema", schema, "--output-last-message", final_path]
    argv.append("-")
    return argv, [(str(CODEX_BIN), "/opt/agent/codex")]


def summarize_activity(backend: str, activity: Path) -> dict[str, Any]:
    """Behavior and cost from the agent's event stream."""
    tools: dict[str, int] = {}
    commands: list[str] = []
    files_read: list[str] = []
    web: list[int] = []
    usage: dict[str, int] = {}
    cost = None
    turns = None
    result_subtype = None
    streamed_usage: dict[str, dict[str, int]] = {}
    error: dict[str, Any] | None = None
    for n, line in enumerate(activity.read_text(errors="replace").splitlines(), 1):
        try:
            ev = json.loads(line)
        except json.JSONDecodeError:
            continue
        if backend == "claude":
            if ev.get("type") == "assistant":
                msg = ev.get("message", {}) or {}
                # Token usage per API message (deduplicated by message id); survives a killed run,
                # unlike the final result event.
                if msg.get("id") and isinstance(msg.get("usage"), dict):
                    streamed_usage[msg["id"]] = {k: v for k, v in msg["usage"].items() if isinstance(v, int)}
                for block in msg.get("content", []) or []:
                    if block.get("type") != "tool_use":
                        continue
                    name = block.get("name", "?")
                    tools[name] = tools.get(name, 0) + 1
                    inp = block.get("input") or {}
                    if name == "Bash" and isinstance(inp.get("command"), str):
                        commands.append(inp["command"])
                    if name == "Read" and isinstance(inp.get("file_path"), str):
                        files_read.append(inp["file_path"])
                    if name == "Skill" and isinstance(inp.get("skill"), str):
                        files_read.append(f"/skills/{inp['skill']}/SKILL.md (Skill tool)")
                    if name in ("WebFetch", "WebSearch"):
                        web.append(n)
            elif ev.get("type") == "result":
                cost = ev.get("total_cost_usd")
                turns = ev.get("num_turns")
                result_subtype = ev.get("subtype")
                if ev.get("is_error"):
                    error = {"text": str(ev.get("result") or "")[:500],
                             "api_error_status": ev.get("api_error_status")}
                for key, value in (ev.get("usage") or {}).items():
                    if isinstance(value, int):
                        usage[key] = value
        else:
            item = ev.get("item") if isinstance(ev.get("item"), dict) else None
            if item:
                kind = item.get("type", "?")
                if ev.get("type") == "item.completed":
                    tools[kind] = tools.get(kind, 0) + 1
                if kind == "command_execution" and isinstance(item.get("command"), str) and ev.get("type") == "item.completed":
                    commands.append(item["command"])
                if kind in ("web_search", "web_search_call"):
                    web.append(n)
            if ev.get("type") == "turn.completed" and isinstance(ev.get("usage"), dict):
                for key, value in ev["usage"].items():
                    if isinstance(value, int):
                        usage[key] = usage.get(key, 0) + value
    research = [{"command": c[:2000]} for c in commands if any(p.search(c) for p in RESEARCH_PATTERNS)]
    tlc_runs = sum(1 for c in commands if "tlc2.TLC" in c or re.search(r"\btlc\b", c))
    sany_runs = sum(1 for c in commands if "tla2sany" in c)
    build_test = sum(1 for c in commands if re.search(r"\b(go test|cargo (test|build)|mvn|gradle)\b", c))
    for c in commands:  # shell reads (cat/sed/rg) of skill files, the usual route for codex
        files_read.extend(re.findall(r"/work/\.(?:agents|claude)/skills/[\w./-]+\.md", c))
    skill_reads = sorted({f for f in files_read if "/skills/" in f})
    streamed: dict[str, int] = {}
    for u in streamed_usage.values():
        for key, value in u.items():
            streamed[key] = streamed.get(key, 0) + value
    return {
        "cost_usd": cost,
        "cost_source": "result_event" if cost is not None else "unavailable (run killed or no result event; see streamed_usage)",
        "num_turns": turns,
        "result_subtype": result_subtype,
        "error": error,
        "usage": usage,
        "streamed_usage": streamed,
        "api_messages": len(streamed_usage),
        "tool_calls": tools,
        "bash_commands": len(commands),
        "tlc_commands": tlc_runs,
        "sany_commands": sany_runs,
        "build_or_test_commands": build_test,
        "skill_files_read": skill_reads,
        "network_audit": {
            "prohibited_command_matches": research,
            "web_tool_events": web,
            "contaminated": bool(research or web),
        },
    }


LIMIT_TEXT = re.compile(r"hit your .*limit|usage limit|rate limit", re.I)


def is_usage_limit(behavior: dict[str, Any], stderr: Path | None = None) -> bool:
    """True when the session ended on an account usage limit (HTTP 429 / 'You've hit your ... limit')."""
    error = behavior.get("error") or {}
    if error.get("api_error_status") == 429 or LIMIT_TEXT.search(error.get("text", "")):
        return True
    if stderr is not None and stderr.exists():
        return bool(LIMIT_TEXT.search(stderr.read_text(errors="replace")[-4000:]))
    return False


def limit_wait_seconds(behavior: dict[str, Any], stderr: Path | None = None) -> int | None:
    """Seconds until the usage window resets, plus a margin; None when no reset time can be parsed.

    Parses 'resets 3pm (America/Chicago)' or 'resets 1:20am (...)'. A reset more than
    6 hours away cannot belong to a 5-hour window (for example a weekly limit), so it
    also returns None: the caller must stop and leave the decision to a person.
    """
    from zoneinfo import ZoneInfo

    text = (behavior.get("error") or {}).get("text", "")
    if stderr is not None and stderr.exists():
        text += "\n" + stderr.read_text(errors="replace")[-4000:]
    if not re.search(r"5-hour", text, re.I):
        return None
    m = re.search(r"resets (\d{1,2})(?::(\d{2}))?\s*(am|pm)\s*\(([^)]+)\)", text, re.I)
    if not m:
        return None
    hour = int(m.group(1)) % 12 + (12 if m.group(3).lower() == "pm" else 0)
    now = datetime.now(ZoneInfo(m.group(4)))
    reset = now.replace(hour=hour, minute=int(m.group(2) or 0), second=0, microsecond=0)
    if reset <= now:
        reset += timedelta(days=1)
    wait = (reset - now).total_seconds()
    if wait > 6 * 3600:
        return None
    return int(wait) + 180


def run_agent(*, backend: str, workspace: Path, ro: list[str], rw: list[str], prompt: str,
              log_dir: Path, timeout_s: int, model: str | None = None, effort: str | None = None,
              budget_usd: float | None = None, schema: str | None = None,
              final_path: str = "/work/current/final-response.json",
              extra_binds: list[tuple[str, str]] | None = None, meta: dict[str, Any] | None = None) -> dict[str, Any]:
    """Run one session; write log_dir/{activity.jsonl, stderr.log, run-manifest.json}; return the manifest."""
    model = model or DEFAULTS[backend]["model"]
    effort = effort or DEFAULTS[backend]["effort"]
    log_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = log_dir / "run-manifest.json"
    if manifest_path.exists():
        raise RuntimeError(f"refusing to overwrite {manifest_path}")
    argv, binds = agent_argv(backend, model, effort, budget_usd, schema, final_path)
    started = datetime.now(timezone.utc)
    manifest: dict[str, Any] = {
        "schema_version": 1,
        **(meta or {}),
        "backend": backend,
        "model": model,
        "effort": effort,
        "budget_usd": budget_usd,
        "timeout_seconds": timeout_s,
        "agent_binary_sha256": sha256(Path(binds[0][0])),
        "prompt_sha256": __import__("hashlib").sha256(prompt.encode()).hexdigest(),
        "status": "RUNNING",
        "started_at_utc": started.isoformat(),
        "isolation": "bwrap unshare-all + share-net; workspace at /work; throwaway HOME; network-guard on PATH",
    }
    write_json(manifest_path, manifest)
    activity = log_dir / "activity.jsonl"
    stderr = log_dir / "stderr.log"
    home = _home(backend)
    try:
        cmd = bwrap_command(workspace, ro, rw, binds + (extra_binds or []), home, argv)
        (log_dir / "command.json").write_text(json.dumps(cmd, indent=1))
        t0 = time.monotonic()
        with activity.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=out, stderr=err,
                                    env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}, start_new_session=True)
            assert proc.stdin is not None
            proc.stdin.write(prompt.encode())
            proc.stdin.close()
            stop_sync = threading.Event()
            if backend == "claude":
                threading.Thread(target=_credential_sync, args=(home, activity, proc, stop_sync), daemon=True).start()
            try:
                proc.wait(timeout=timeout_s)
                timed_out = False
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
            finally:
                stop_sync.set()
        wall = time.monotonic() - t0
    finally:
        if backend == "claude":
            try:  # a refresh in the last seconds of the run must not be lost with the throwaway HOME
                box, host = home / ".claude/.credentials.json", HOME / ".claude/.credentials.json"
                if _expires(box) > _expires(host):
                    _replace(box, host)
            except Exception:
                pass
        shutil.rmtree(home, ignore_errors=True)
    finished = datetime.now(timezone.utc)
    behavior = summarize_activity(backend, activity)
    status = "TIMEOUT" if timed_out else ("EXITED_0" if proc.returncode == 0 else "FAILED")
    if is_usage_limit(behavior, stderr):
        status = "USAGE_LIMIT"
    elif AUTH_FAILURE.search(json.dumps(behavior.get("error") or {}) + _tail(activity)):
        status = "AUTH_ERROR"
    manifest.update({
        "status": status,
        "exit_code": proc.returncode,
        "timed_out": timed_out,
        "finished_at_utc": finished.isoformat(),
        "wall_seconds": round(wall, 1),
        "activity_sha256": sha256(activity),
        "behavior": behavior,
    })
    write_json(manifest_path, manifest)
    return manifest
