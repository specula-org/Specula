"""Native compaction between CLI turns; never edit or replace session history."""

from __future__ import annotations

import asyncio
import base64
import contextlib
import importlib
import json
import os
import secrets
import shutil
import signal
import socket
import sys
import urllib.error
import urllib.request
from collections.abc import AsyncIterator
from pathlib import Path
from typing import Any

from specula.context_control import write_json


@contextlib.asynccontextmanager
async def process(argv: list[str], log: Path, env: dict[str, str] | None = None) -> AsyncIterator[Any]:
    with log.open("ab") as errors:
        child = await asyncio.create_subprocess_exec(
            *argv,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=errors,
            env=env,
            limit=64 * 1024 * 1024,
        )
        try:
            yield child
        finally:
            if child.stdin:
                child.stdin.close()
            if child.returncode is None:
                with contextlib.suppress(ProcessLookupError):
                    child.terminate()
                try:
                    await asyncio.wait_for(child.wait(), 5)
                except asyncio.TimeoutError:
                    with contextlib.suppress(ProcessLookupError):
                        child.kill()
                    await child.wait()


class Lines:
    def __init__(self, child: Any) -> None:
        self.child = child
        self.number = 0
        self.events: list[dict[str, Any]] = []

    async def send(self, value: dict[str, Any]) -> None:
        self.child.stdin.write((json.dumps(value) + "\n").encode())
        await self.child.stdin.drain()

    async def receive(self) -> dict[str, Any]:
        while line := await self.child.stdout.readline():
            try:
                event = json.loads(line)
            except ValueError:
                continue
            if isinstance(event, dict):
                return event
        raise RuntimeError("Native compaction process exited before a completion response")

    async def call(self, method: str, params: dict[str, Any], *, pi: bool = False) -> dict[str, Any]:
        self.number += 1
        key = str(self.number)
        await self.send(
            {"id": key, "type": method, **params} if pi else {"id": key, "method": method, "params": params}
        )
        while True:
            event = await self.receive()
            if event.get("id") == key and ("result" in event or "error" in event or pi):
                if event.get("error") or event.get("success") is False:
                    raise RuntimeError(str(event.get("error", "Native compaction request failed")))
                result = event.get("data", {}) if pi else event.get("result", {})
                if not isinstance(result, dict):
                    raise RuntimeError("Native control returned an invalid response")
                return result
            if "method" in event and "id" in event:
                # Compaction must not execute user tools or approve new work.
                await self.send({"id": event["id"], "error": {"code": -32601, "message": "No tools during compaction"}})
            else:
                self.events.append(event)


async def codex(state: dict[str, Any], log: Path) -> dict[str, Any]:
    argv = ["codex", "app-server"]
    if state.get("effort"):
        argv += ["-c", "model_reasoning_effort=" + json.dumps(state["effort"])]
    async with process(argv, log) as child:
        rpc = Lines(child)
        await rpc.call("initialize", {"clientInfo": {"name": "specula", "version": "1"}})
        await rpc.send({"method": "initialized", "params": {}})
        params = {"threadId": state["session_id"], "cwd": state["cwd"]}
        if state.get("model"):
            params["model"] = state["model"]
        resumed = await rpc.call("thread/resume", params)
        if resumed.get("thread", {}).get("id") != state["session_id"]:
            raise RuntimeError("Codex resumed a different conversation")
        rpc.events.clear()
        await rpc.call("thread/compact/start", {"threadId": state["session_id"]})
        compacted = False
        while True:
            event = rpc.events.pop(0) if rpc.events else await rpc.receive()
            p = event.get("params", {})
            if p.get("threadId") != state["session_id"]:
                continue
            if event.get("method") == "item/completed" and p.get("item", {}).get("type") == "contextCompaction":
                compacted = True
            if event.get("method") == "turn/completed":
                if not compacted or p.get("turn", {}).get("status") != "completed":
                    raise RuntimeError("Codex compaction did not complete")
                return {
                    "status": "completed",
                    "evidence": event,
                    "usage_warning": "Codex compaction reports context size, not billable compaction usage.",
                }


async def claude(state: dict[str, Any], log: Path, alias: str) -> dict[str, Any]:
    env = os.environ.copy()
    for key in ("CLAUDECODE", "CLAUDE_CODE_SSE_PORT", "CLAUDE_CODE_ENTRYPOINT"):
        env.pop(key, None)
    env["CLAUDE_CONFIG_DIR"] = str(Path.home() / f".{alias or 'claude'}")
    argv = ["claude", "--print", "--resume", state["session_id"], "--output-format", "stream-json", "--verbose"]
    if state.get("model"):
        argv += ["--model", state["model"]]
    if state.get("effort"):
        argv += ["--effort", state["effort"]]
    async with process(argv, log, env) as child:
        child.stdin.write(b"/compact\n")
        await child.stdin.drain()
        child.stdin.close()
        rpc = Lines(child)
        boundary = None
        while True:
            event = await rpc.receive()
            if event.get("session_id") not in (None, state["session_id"]):
                raise RuntimeError("Claude compaction changed session identity")
            if event.get("type") == "system" and event.get("subtype") == "compact_boundary":
                boundary = event
            if event.get("type") == "result":
                if event.get("is_error") or event.get("subtype") != "success":
                    raise RuntimeError("Claude compaction failed: " + str(event.get("result", event.get("errors", ""))))
                return {
                    "status": "completed" if boundary else "skipped",
                    "evidence": boundary or event,
                    "usage_payload": event,
                }


async def pi(state: dict[str, Any], log: Path) -> dict[str, Any]:
    argv = ["pi", "--mode", "rpc", "--session", state["session_id"]]
    if state.get("model"):
        argv += ["--model", state["model"]]
    if state.get("effort"):
        argv += ["--thinking", state["effort"]]
    async with process(argv, log) as child:
        rpc = Lines(child)
        current = await rpc.call("get_state", {}, pi=True)
        if current.get("sessionId") != state["session_id"]:
            raise RuntimeError("Pi resumed a different conversation")
        result = await rpc.call("compact", {}, pi=True)
        if not result.get("summary") or not result.get("firstKeptEntryId"):
            raise RuntimeError("Pi returned no compaction result")
        return {"status": "completed", "evidence": result, "pi_usage": result.get("usage")}


async def copilot(state: dict[str, Any], log: Path) -> dict[str, Any]:
    # Installed by tools/context_control/requirements.txt, not needed by other paths.
    sdk = importlib.import_module("copilot")
    client: Any = sdk.CopilotClient(
        connection=sdk.RuntimeConnection.for_stdio(path=shutil.which("copilot") or "copilot"),
        working_directory=state["cwd"],
        log_level="error",
    )
    events: list[dict[str, Any]] = []
    try:
        await client.start()
        session = await client.resume_session(
            state["session_id"],
            model=state.get("model") or None,
            reasoning_effort=state.get("effort") or None,
            working_directory=state["cwd"],
        )
        session.on(lambda event: events.append(event.to_dict()) if "compaction" in str(event.type).lower() else None)
        try:
            result = await session.rpc.history.compact()
            evidence = result.to_dict()
        except Exception as exc:
            return {"status": "failed", "error": f"{type(exc).__name__}: {exc}", "events": events}
        return {
            "status": "completed" if evidence.get("success") is True else "failed",
            "evidence": evidence,
            "events": events,
        }
    finally:
        await client.force_stop()


async def opencode(state: dict[str, Any], log: Path) -> dict[str, Any]:
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
    password = secrets.token_urlsafe(24)
    env = {
        **os.environ,
        "OPENCODE_SERVER_PASSWORD": password,
        "OPENCODE_SERVER_USERNAME": "opencode",
        "OPENCODE_FAKE_VCS": "git",
    }
    auth = base64.b64encode(f"opencode:{password}".encode()).decode()
    base = f"http://127.0.0.1:{port}"

    def request(path: str, body: Any = None) -> Any:
        req = urllib.request.Request(
            base + path,
            headers={
                "Authorization": "Basic " + auth,
                "Content-Type": "application/json",
                "x-opencode-directory": state["cwd"],
            },
            data=json.dumps(body).encode() if body is not None else None,
        )
        with log.open("a") as stream:
            stream.write(f"OpenCode control: {path}\n")
        with urllib.request.urlopen(req, timeout=180 if path.endswith("/summarize") else 10) as response:
            return json.loads(response.read() or b"null")

    async with process(["opencode", "serve", "--hostname", "127.0.0.1", "--port", str(port)], log, env) as child:
        # Drain the server banner so its stdout can never fill while serving HTTP.
        drain = asyncio.create_task(child.stdout.read())
        try:
            for _ in range(100):
                try:
                    await asyncio.to_thread(request, "/global/health")
                    break
                except (OSError, urllib.error.URLError):
                    if child.returncode is not None:
                        raise RuntimeError("OpenCode server exited") from None
                    await asyncio.sleep(0.1)
            else:
                raise RuntimeError("OpenCode server did not become ready")
            prefix = "/session/" + state["session_id"]
            current = await asyncio.to_thread(request, prefix)
            if current.get("id") != state["session_id"]:
                raise RuntimeError("OpenCode resumed a different conversation")
            before = await asyncio.to_thread(request, prefix + "/message")
            model = state.get("model", "")
            if not model or "/" not in model:
                assistants = [m["info"] for m in before if m.get("info", {}).get("role") == "assistant"]
                if not assistants:
                    raise RuntimeError("OpenCode has no previous model to compact with")
                provider, model_id = assistants[-1]["providerID"], assistants[-1]["modelID"]
            else:
                provider, model_id = model.split("/", 1)
            known = {m["info"]["id"] for m in before}
            await asyncio.to_thread(request, prefix + "/summarize", {"providerID": provider, "modelID": model_id})
            after = await asyncio.to_thread(request, prefix + "/message")
            added = [m["info"] for m in after if m["info"]["id"] not in known and m["info"].get("role") == "assistant"]
            completed = [
                m for m in added if m.get("summary") and not m.get("error") and m.get("time", {}).get("completed")
            ]
            if not completed:
                raise RuntimeError("OpenCode produced no completed compaction checkpoint")
            return {"status": "completed", "evidence": completed, "opencode_usage": added}
        finally:
            drain.cancel()


async def compact(state: dict[str, Any], log: Path, alias: str = "") -> dict[str, Any]:
    if not state.get("session_id") or not state.get("cwd"):
        raise ValueError("An existing native session is required")
    agent = state["adapter"]
    if agent == "claude-code":
        return await claude(state, log, alias)
    functions = {"codex": codex, "pi": pi, "opencode": opencode, "copilot-cli": copilot}
    if agent not in functions:
        raise ValueError(f"Native compaction is not available for {agent}")
    return await functions[agent](state, log)


async def managed_compact(state: dict[str, Any], log: Path, alias: str) -> dict[str, Any]:
    task = asyncio.current_task()
    assert task is not None
    loop = asyncio.get_running_loop()
    loop.add_signal_handler(signal.SIGTERM, task.cancel)
    try:
        return await asyncio.wait_for(compact(state, log, alias), 300)
    except asyncio.CancelledError:
        return {"status": "failed", "error": "Compaction interrupted"}
    finally:
        loop.remove_signal_handler(signal.SIGTERM)


def main() -> int:
    state_file, receipt_file, alias = sys.argv[1:4]
    receipt = Path(receipt_file)
    try:
        state = json.loads(Path(state_file).read_text())
        result = asyncio.run(managed_compact(state, receipt.with_suffix(".log"), alias))
    except Exception as exc:
        result = {"status": "failed", "error": f"{type(exc).__name__}: {exc}"}
    write_json(receipt, result)
    return 0  # The caller continues the existing conversation even on failure.


if __name__ == "__main__":
    raise SystemExit(main())
