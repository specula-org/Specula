"""CI context requests and native completion protocols; no paid model calls."""

from __future__ import annotations

import asyncio
import contextlib
import importlib
import json
import os
import sys
import urllib.request
from pathlib import Path
from types import SimpleNamespace
from typing import Any
from unittest.mock import AsyncMock

import pytest

from specula import context_control as control
from specula import context_runner as runner
from specula import native_compaction as native
from specula.adapters.utils import event_stream


def configure(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> Path:
    work = tmp_path / "work"
    work.mkdir()
    monkeypatch.setenv("SPECULA_PHASE", "incremental")
    monkeypatch.setenv("SPECULA_WORK_DIR", str(work))
    monkeypatch.setenv(control.REQUEST_ENV, str(tmp_path / "request.json"))
    monkeypatch.setenv(control.TOKEN_ENV, "this-invocation")
    return work


def test_request_requires_saved_handoff_but_not_a_semantic_schema(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    work = configure(monkeypatch, tmp_path)
    with pytest.raises(ValueError, match="handoff"):
        control.request_compaction("missing.md")
    (work / "handoff.md").write_text("Pending counterexample. Final regression has not run.\n")
    result = control.request_compaction("handoff.md")
    assert result["status"] == "requested"
    assert control.YIELD_PREFIX in result["instruction"]
    saved = json.loads((tmp_path / "request.json").read_text())
    assert saved == {"token": "this-invocation", "handoff_path": str(work / "handoff.md")}
    outside = tmp_path / "outside.md"
    outside.write_text("unrelated")
    with pytest.raises(ValueError):
        control.request_compaction(str(outside))
    monkeypatch.setenv("SPECULA_PHASE", "code_analysis")
    with pytest.raises(ValueError, match="incremental"):
        control.request_compaction("handoff.md")


def test_request_keeps_two_invocations_separate(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    work = configure(monkeypatch, tmp_path)
    (work / "handoff.md").write_text("important")
    for name in ("first", "second"):
        directory = tmp_path / name
        directory.mkdir()
        env = runner.tool_environment(directory, work, Path(sys.executable))
        with monkeypatch.context() as scoped:
            for key, value in env.items():
                scoped.setenv(key, value)
            control.request_compaction("handoff.md")
        assert json.loads((directory / "request.json").read_text())["token"] == env[control.TOKEN_ENV]
    assert (tmp_path / "first/request.json").read_text() != (tmp_path / "second/request.json").read_text()


@pytest.mark.asyncio
async def test_mcp_discovery_and_real_tool_call(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    work = configure(monkeypatch, tmp_path)
    (work / "handoff.md").write_text("Unresolved evidence stays unresolved.")
    server = Path(control.__file__).resolve().parents[2] / "tools/context_control/mcp_server.py"
    params = StdioServerParameters(command=sys.executable, args=[str(server)], env=dict(os.environ))
    async with stdio_client(params) as (reader, writer), ClientSession(reader, writer) as session:
        await session.initialize()
        listed = await session.list_tools()
        assert [tool.name for tool in listed.tools] == [control.TOOL_NAME]
        result = await session.call_tool(control.TOOL_NAME, {"handoff_path": "handoff.md"})
        assert not result.isError
    assert json.loads((tmp_path / "request.json").read_text())["handoff_path"] == str(work / "handoff.md")


@pytest.mark.parametrize("agent", ["codex", "claude-code", "pi", "opencode", "copilot-cli"])
@pytest.mark.parametrize("outcome", ["completed", "failed"])
@pytest.mark.parametrize("native_failure", [False, True])
def test_internal_yield_compacts_and_continues_original_session(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    agent: str,
    outcome: str,
    native_failure: bool,
) -> None:
    work = configure(monkeypatch, tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.delenv("SPECULA_RUN_DIR", raising=False)
    tool = tmp_path / "tools/context_control"
    (tool / ".venv/bin").mkdir(parents=True)
    (tool / ".venv/bin/python").symlink_to(sys.executable)
    (tool / "compact.py").write_text(
        "import json,sys\nfrom pathlib import Path\n"
        "state=json.loads(Path(sys.argv[1]).read_text())\n"
        "assert state['session_id']=='original-session'\n"
        f"Path(sys.argv[2]).write_text(json.dumps({{'status':{outcome!r}, 'usage_in_native_session': True}}))\n"
    )
    real_src = Path(control.__file__).resolve().parents[1]
    adapter = tmp_path / f"{agent}.sh"
    adapter.write_text(
        f"#!{sys.executable}\n"
        "import json,os,sys\nfrom pathlib import Path\n"
        f"sys.path.insert(0,{str(real_src)!r})\n"
        "from specula.context_control import request_compaction\n"
        "opts=dict(x[2:].split('=',1) for x in sys.argv[1:] if x.startswith('--') and '=' in x)\n"
        "work=Path(os.environ['SPECULA_WORK_DIR']); log=Path(opts['log']); resume=Path(opts['resume-state'])\n"
        "second=resume.exists()\n"
        "if second:\n"
        " assert json.loads(resume.read_text())['session_id']=='original-session'\n"
        " assert 'First read the saved handoff' in Path(opts['prompt-file']).read_text()\n"
        " assert (work/'ci-context.md').read_text()=='Unresolved cex: do not mark passed.'\n"
        " response='SPECULA_INCREMENTAL_COMPLETE test-run'\n"
        "else:\n"
        f" resume.write_text(json.dumps({{'adapter':{agent!r},'session_id':'original-session','cwd':{str(tmp_path)!r}}}))\n"
        " (work/'ci-context.md').write_text('Unresolved cex: do not mark passed.')\n"
        " request_compaction('ci-context.md')\n"
        " response='SPECULA_CONTEXT_YIELD '+os.environ['SPECULA_CONTEXT_TOKEN']\n"
        "log.write_text(response+'\\n'); log.with_suffix('.last-message.txt').write_text(response+'\\n')\n"
        f"log.with_suffix('.usage.json').write_text(json.dumps({{'agent':{agent!r},'session_id':'original-session','total_cost_usd':2.0 if second else 1.0,'usage':{{'total_tokens':200 if second else 100,'cached_input_tokens':20 if second else 10}}}}))\n"
        f"raise SystemExit(9 if second and {native_failure!r} else 0)\n"
    )
    adapter.chmod(0o755)
    prompt = work / "prompt.md"
    prompt.write_text("Original task")
    log = work / "incremental.log"
    args = [f"--log={log}", f"--resume-state={work / 'incremental.resume.json'}", f"--prompt-file={prompt}"]
    # A real execution failure still wins over a final-looking model response.
    assert runner.run(adapter, args) == (9 if native_failure else 0)
    assert log.read_text().strip() == "SPECULA_INCREMENTAL_COMPLETE test-run"
    receipts = list(work.glob(".context-control/invocation-*/1/compaction.json"))
    assert len(receipts) == 1
    assert json.loads(receipts[0].read_text())["status"] == outcome
    assert json.loads((work / "incremental.resume.json").read_text())["session_id"] == "original-session"
    usage = json.loads(log.with_suffix(".usage.json").read_text())
    if agent == "codex":
        assert usage["observed_cost_usd"] == 2.0  # Not 1 + 2: native cumulative accounting.
        assert usage["observed_usage"]["total_tokens"] == 200
        assert usage["usage_complete"] is False  # Native compaction's billable usage is unavailable.
    else:
        assert usage["usage_complete"] is False  # The fixture did not provide compaction usage.
        assert usage["total_cost_usd"] is None


def test_accounting_includes_compaction_and_does_not_invent_missing_cost(tmp_path: Path) -> None:
    receipt = {"pi_usage": {"input": 10, "output": 4, "cacheRead": 6, "cost": {"total": 0.2}}}
    row = runner.compaction_usage("pi", receipt)
    assert row is not None and row.total_tokens == 20 and row.cost_usd == 0.2
    target = tmp_path / "usage.json"
    runner.publish_usage(target, "pi", "id", [row, row])
    assert json.loads(target.read_text())["total_cost_usd"] == 0.4
    runner.publish_usage(target, "pi", "id", [row, None])
    assert json.loads(target.read_text())["total_cost_usd"] is None
    assert json.loads(target.read_text())["observed_cost_usd"] == 0.2
    assert json.loads(target.read_text())["usage_complete"] is False


def test_copilot_autopilot_yield_uses_successful_native_completion(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    work = configure(monkeypatch, tmp_path)
    monkeypatch.setenv("SPECULA_CONTEXT_AGENT", "copilot-cli")
    (work / "handoff.md").write_text("Pending")
    result = control.request_compaction("handoff.md")
    assert "task_complete" in result["instruction"]
    record = {"type": "session.task_complete", "data": {"success": True, "summary": "SPECULA_CONTEXT_YIELD token"}}
    assert event_stream._copilot_events(record, False)[0].text == "SPECULA_CONTEXT_YIELD token"
    record["data"] = {"success": False, "summary": "SPECULA_CONTEXT_YIELD token"}
    assert not event_stream._copilot_events(record, False)
    monkeypatch.setenv("SPECULA_PHASE", "code_analysis")
    record["data"] = {"success": True, "summary": "SPECULA_CONTEXT_YIELD token"}
    assert not event_stream._copilot_events(record, False)


class Input:
    def __init__(self, output: asyncio.StreamReader, handler: Any) -> None:
        self.output = output
        self.handler = handler
        self.messages: list[Any] = []

    def write(self, raw: bytes) -> None:
        message = json.loads(raw) if raw.lstrip().startswith(b"{") else raw.decode().strip()
        self.messages.append(message)
        for response in self.handler(message):
            self.output.feed_data((json.dumps(response) + "\n").encode())

    async def drain(self) -> None:
        pass

    def close(self) -> None:
        pass


def mock_process(monkeypatch: pytest.MonkeyPatch, handler: Any) -> tuple[list[list[str]], list[Input]]:
    commands: list[list[str]] = []
    inputs: list[Input] = []

    @contextlib.asynccontextmanager
    async def fake(argv: list[str], _log: Path, _env: Any = None) -> Any:
        commands.append(argv)
        output = asyncio.StreamReader()
        stdin = Input(output, handler)
        inputs.append(stdin)
        yield SimpleNamespace(stdin=stdin, stdout=output, returncode=None)

    monkeypatch.setattr(native, "process", fake)
    return commands, inputs


@pytest.mark.asyncio
@pytest.mark.parametrize("finished", [True, False])
async def test_codex_requires_actual_compaction_completion(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    finished: bool,
) -> None:
    def handler(m: dict[str, Any]) -> list[dict[str, Any]]:
        if m["method"] == "initialized":
            return []
        result = {"thread": {"id": "original"}} if m["method"] == "thread/resume" else {}
        messages = [{"id": m["id"], "result": result}]
        if m["method"] == "thread/compact/start":
            if finished:
                messages.append(
                    {
                        "method": "item/completed",
                        "params": {"threadId": "original", "item": {"type": "contextCompaction"}},
                    }
                )
            messages.append(
                {"method": "turn/completed", "params": {"threadId": "original", "turn": {"status": "completed"}}}
            )
        return messages

    _, inputs = mock_process(monkeypatch, handler)
    state = {"session_id": "original", "cwd": str(tmp_path), "model": "selected-model", "effort": "high"}
    if finished:
        result = await native.codex(state, tmp_path / "log")
        assert result["status"] == "completed"
    else:
        with pytest.raises(RuntimeError, match="did not complete"):
            await native.codex(state, tmp_path / "log")
    assert all(m.get("method") != "thread/start" for m in inputs[0].messages)
    resume = next(m for m in inputs[0].messages if m.get("method") == "thread/resume")
    assert resume["params"]["model"] == "selected-model"


@pytest.mark.asyncio
@pytest.mark.parametrize("boundary", [True, False])
async def test_claude_distinguishes_noop_from_completed_compaction(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    boundary: bool,
) -> None:
    def handler(_m: Any) -> list[dict[str, Any]]:
        records = [{"type": "system", "subtype": "compact_boundary", "session_id": "original"}] if boundary else []
        return records + [{"type": "result", "subtype": "success", "session_id": "original", "total_cost_usd": 0.1}]

    commands, inputs = mock_process(monkeypatch, handler)
    result = await native.claude({"session_id": "original"}, tmp_path / "log", "alias")
    assert result["status"] == ("completed" if boundary else "skipped")
    assert commands[0][commands[0].index("--resume") + 1] == "original"
    assert inputs[0].messages == ["/compact"]


@pytest.mark.asyncio
async def test_pi_native_rpc_preserves_session_and_returns_compaction_usage(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    def handler(m: dict[str, Any]) -> list[dict[str, Any]]:
        data = (
            {"sessionId": "original"}
            if m["type"] == "get_state"
            else {
                "summary": "Pending check remains pending",
                "firstKeptEntryId": "entry",
                "usage": {"input": 12},
            }
        )
        return [{"id": m["id"], "type": "response", "command": m["type"], "success": True, "data": data}]

    commands, inputs = mock_process(monkeypatch, handler)
    result = await native.pi({"session_id": "original", "effort": "high"}, tmp_path / "log")
    assert result["status"] == "completed" and result["pi_usage"] == {"input": 12}
    assert [m["type"] for m in inputs[0].messages] == ["get_state", "compact"]
    assert "original" in commands[0]


@pytest.mark.asyncio
@pytest.mark.parametrize("success", [True, False])
async def test_copilot_obeys_native_success_not_just_rpc_return(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    success: bool,
) -> None:
    session = SimpleNamespace(
        on=lambda callback: None,
        rpc=SimpleNamespace(
            history=SimpleNamespace(
                compact=AsyncMock(return_value=SimpleNamespace(to_dict=lambda: {"success": success}))
            )
        ),
    )
    client = SimpleNamespace(start=AsyncMock(), resume_session=AsyncMock(return_value=session), force_stop=AsyncMock())
    sdk = SimpleNamespace(
        CopilotClient=lambda **kwargs: client, RuntimeConnection=SimpleNamespace(for_stdio=lambda **kwargs: None)
    )
    monkeypatch.setattr(importlib, "import_module", lambda name: sdk)
    result = await native.copilot({"session_id": "original", "cwd": str(tmp_path)}, tmp_path / "log")
    assert result["status"] == ("completed" if success else "failed")
    client.resume_session.assert_awaited_once_with(
        "original", model=None, reasoning_effort=None, working_directory=str(tmp_path)
    )
    client.force_stop.assert_awaited_once()


@pytest.mark.asyncio
@pytest.mark.parametrize("checkpoint", [True, False])
async def test_opencode_checks_new_native_checkpoint(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    checkpoint: bool,
) -> None:
    mock_process(monkeypatch, lambda _: [])
    calls: list[Any] = []
    count = 0

    def urlopen(request: Any, timeout: int) -> Any:
        nonlocal count
        calls.append(request)
        url = request.full_url
        if url.endswith("/global/health"):
            value: Any = {"healthy": True}
        elif url.endswith("/session/original"):
            value = {"id": "original"}
        elif url.endswith("/summarize"):
            assert json.loads(request.data) == {"providerID": "provider", "modelID": "model"}
            value = True
        else:
            count += 1
            value = [{"info": {"id": "old", "role": "assistant"}}]
            if count > 1 and checkpoint:
                value.append(
                    {
                        "info": {
                            "id": "new",
                            "role": "assistant",
                            "summary": True,
                            "time": {"completed": 1},
                            "tokens": {},
                            "cost": 0.1,
                        }
                    }
                )
        return contextlib.nullcontext(SimpleNamespace(read=lambda: json.dumps(value).encode()))

    monkeypatch.setattr(urllib.request, "urlopen", urlopen)
    if checkpoint:
        result = await native.opencode(
            {"session_id": "original", "model": "provider/model", "cwd": str(tmp_path)}, tmp_path / "log"
        )
        assert result["status"] == "completed"
    else:
        with pytest.raises(RuntimeError, match="checkpoint"):
            await native.opencode(
                {"session_id": "original", "model": "provider/model", "cwd": str(tmp_path)}, tmp_path / "log"
            )
    assert all("127.0.0.1" in c.full_url for c in calls)
    assert all(c.get_header("Authorization") for c in calls)
