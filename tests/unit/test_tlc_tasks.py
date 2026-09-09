"""Real process/MCP waits, with a deterministic substitute for the TLC JVM."""

from __future__ import annotations

import asyncio
import json
import os
import subprocess
import sys
import time
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import test_adapters as adapters
import test_run_model_check as wrappers

from specula import context_runner, phaselib
from specula import tlc_tasks as tasks


@pytest.fixture
def runtime(monkeypatch: pytest.MonkeyPatch) -> Iterator[wrappers.RunModelCheckTests]:
    fixture = wrappers.RunModelCheckTests()
    fixture.setUp()
    for key in list(os.environ):
        if key.startswith("SPECULA_TLC_TOOL_"):
            monkeypatch.delenv(key)
    for key, value in fixture.env().items():
        monkeypatch.setenv(key, value)
    monkeypatch.setenv("SPECULA_WORK_DIR", str(fixture.work))
    monkeypatch.setenv("SPECULA_TLC_TOOL_OWNER", str(fixture.work / "agent.log"))
    java = fixture.bin / "java"
    java.write_text(
        '#!/bin/sh\nprintf \'TLC fixture output\\n\'\nsleep "${FAKE_JAVA_SECONDS:-0.3}"\nexit "${FAKE_JAVA_EXIT:-0}"\n'
    )
    try:
        yield fixture
    finally:
        tasks.stop_owned_tasks(fixture.work, fixture.work / "agent.log")
        deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            pending = list((fixture.work / ".tlc-tasks/jobs").glob("*/request.json"))
            if all(p.with_name("result.json").exists() for p in pending):
                break
            time.sleep(0.05)
        fixture.doCleanups()


def start_args(runtime: wrappers.RunModelCheckTests) -> dict[str, Any]:
    return {
        "work_dir": str(runtime.work),
        "spec_file": "MC.tla",
        "config_file": "MC.cfg",
        "options": ["-m", "1G", "-M", "1G", "-w", "1", "-t", "1"],
    }


@pytest.mark.asyncio
@pytest.mark.parametrize("code", [0, 12, 124, 2])
async def test_exit_receipt_is_not_a_verification_verdict(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch, code: int
) -> None:
    monkeypatch.setenv("FAKE_JAVA_EXIT", str(code))
    started = await tasks.start_tlc(**start_args(runtime))
    result = await tasks.wait_tlc([started["task_id"]], timeout_seconds=10)
    assert result["outcome"] == "finished"
    task = result["tasks"][0]
    assert task["status"] == "exited"
    assert task["exit_code"] == code
    assert Path(task["log_path"]).read_text() == "TLC fixture output\n"
    assert "verified" not in task and "passed" not in task
    assert json.loads(Path(task["result_path"]).read_text()) == task
    assert await tasks.wait_tlc([started["task_id"]]) == result


@pytest.mark.asyncio
async def test_wait_timeout_and_cancellation_do_not_restart_or_stop_tlc(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    started = await tasks.start_tlc(**start_args(runtime))
    task_id = started["task_id"]
    timed = await tasks.wait_tlc([task_id], timeout_seconds=0)
    assert timed["outcome"] == "wait_timeout"
    waiter = asyncio.create_task(tasks.wait_tlc([task_id]))
    await asyncio.sleep(0.1)
    waiter.cancel()
    with pytest.raises(asyncio.CancelledError):
        await waiter
    assert tasks.status(task_id)["status"] == "running"
    result = await tasks.wait_tlc([task_id], timeout_seconds=10)
    assert result["tasks"][0]["exit_code"] == 0
    assert len(list(tasks.tasks_root().iterdir())) == 1


@pytest.mark.asyncio
async def test_any_all_and_parallel_jobs_have_distinct_evidence(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    first = await tasks.start_tlc(**start_args(runtime))
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    second = await tasks.start_tlc(**start_args(runtime))
    ids = [first["task_id"], second["task_id"]]
    result = await tasks.wait_tlc(ids, timeout_seconds=10)
    assert result["tasks"][0]["status"] == "exited"
    assert result["tasks"][1]["status"] == "running"
    result = await tasks.wait_tlc(ids + ids, mode="all", timeout_seconds=10)
    assert len(result["tasks"]) == 2
    assert all(t["exit_code"] == 0 for t in result["tasks"])
    assert first["log_path"] != second["log_path"]


@pytest.mark.asyncio
async def test_admission_failure_surfaces_launcher_evidence(runtime: wrappers.RunModelCheckTests) -> None:
    args = start_args(runtime)
    args["options"] = ["-m", "4G", "-M", "4G", "-w", "1", "-t", "1"]
    started = await tasks.start_tlc(**args)
    result = (await tasks.wait_tlc([started["task_id"]], timeout_seconds=10))["tasks"][0]
    assert result["exit_code"] == 2
    assert "rejected" in Path(result["launcher_log_path"]).read_text()


@pytest.mark.asyncio
async def test_explicit_owner_cleanup_stops_only_owned_tasks(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    started = await tasks.start_tlc(**start_args(runtime))
    tasks.stop_owned_tasks(runtime.work, runtime.work / "another-agent.log")
    assert tasks.status(started["task_id"])["status"] == "running"
    tasks.stop_owned_tasks(runtime.work, runtime.work / "agent.log")
    result = (await tasks.wait_tlc([started["task_id"]], timeout_seconds=10))["tasks"][0]
    assert result["status"] == "interrupted"


@pytest.mark.asyncio
async def test_disappeared_launcher_stops_tlc(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "30")
    monkeypatch.setenv("SPECULA_TLC_TOOL_PARENT", str(os.getpid()))
    monkeypatch.setenv("SPECULA_TLC_TOOL_PARENT_IDENTITY", "not this process")
    started = await tasks.start_tlc(**start_args(runtime))
    result = await tasks.wait_tlc([started["task_id"]], timeout_seconds=10)
    assert result["tasks"][0]["status"] == "interrupted"


@pytest.mark.asyncio
@pytest.mark.parametrize("options", [["-t", "bad"], ["-o", "overwrite.log"], ["-s", "Other.tla"], [";"], ["-w"]])
async def test_invalid_start_has_no_task_side_effects(runtime: wrappers.RunModelCheckTests, options: list[str]) -> None:
    args = start_args(runtime)
    args["options"] = options
    with pytest.raises(ValueError):
        await tasks.start_tlc(**args)
    assert not tasks.tasks_root().exists()


@pytest.mark.asyncio
async def test_invalid_wait_has_no_side_effects(runtime: wrappers.RunModelCheckTests) -> None:
    for ids in ([], ["../escape"], ["0" * 32]):
        with pytest.raises(ValueError):
            await tasks.wait_tlc(ids)
    assert not tasks.tasks_root().exists()


@pytest.mark.asyncio
async def test_zero_tlc_deadline_preserves_wrapper_semantics(runtime: wrappers.RunModelCheckTests) -> None:
    args = start_args(runtime)
    args["options"][-1] = "0"
    started = await tasks.start_tlc(**args)
    result = await tasks.wait_tlc([started["task_id"]], timeout_seconds=10)
    assert result["tasks"][0]["exit_code"] == 0


def test_runtime_registration_is_local_and_preserves_budgets(tmp_path: Path) -> None:
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    env = {
        "SPECULA_WORK_DIR": str(tmp_path / "work"),
        "SPECULA_PHASE": "spec_validation",
        "SPECULA_TLC_MEMORY_LIMIT": "8G",
        "SPECULA_TLC_WORKER_LIMIT": "4",
        "SECRET": "never copy me",
    }
    tasks.prepare_environment(env, tmp_path / "agent.log", tmp_path)
    saved = json.loads(Path(env["SPECULA_TLC_TOOL_CONFIG"]).read_text())["mcpServers"]["specula_tlc"]
    assert saved["env"]["SPECULA_TLC_MEMORY_LIMIT"] == "8G"
    assert saved["env"]["SPECULA_TLC_WORKER_LIMIT"] == "4"
    assert "SECRET" not in saved["env"]
    assert "tool_timeout_sec=3720" in env["SPECULA_TLC_TOOL_CODEX"]
    assert json.loads(env["SPECULA_TLC_TOOL_JSON"])["mcpServers"]["specula_tlc"]["timeout"] == 3720000
    assert not (tmp_path / ".codex/config.toml").exists()


@pytest.mark.parametrize("agent", ["claude-code", "copilot-cli", "codex", "opencode", "pi"])
def test_incremental_compaction_and_tlc_tools_coexist(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, agent: str
) -> None:
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    env = {"SPECULA_WORK_DIR": str(tmp_path / "work"), "SPECULA_PHASE": "incremental"}
    tasks.prepare_environment(env, tmp_path / "agent.log", tmp_path)
    for key, value in env.items():
        monkeypatch.setenv(key, value)
    directory = tmp_path / "context"
    directory.mkdir()
    combined = context_runner.tool_environment(directory, tmp_path / "work", Path(sys.executable), agent)
    servers = json.loads(combined["SPECULA_CONTEXT_MCP_JSON"])["mcpServers"]
    assert set(servers) == {"specula_context", "specula_tlc"}
    if agent == "copilot-cli":
        assert servers["specula_tlc"]["timeout"] == tasks.CLIENT_TIMEOUT_MS


def test_blocking_phase_registers_tools_automatically(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    monkeypatch.setattr(phaselib, "SPECULA_ROOT", tmp_path)
    adapter = tmp_path / "fake.sh"
    log = tmp_path / "agent.log"
    adapter.write_text(
        f"#!{sys.executable}\n"
        "import json,os,sys\nfrom pathlib import Path\n"
        "config=json.loads(Path(os.environ['SPECULA_TLC_TOOL_CONFIG']).read_text())\n"
        "assert 'specula_tlc' in config['mcpServers']\n"
        f"Path({str(log)!r}).write_text('tools available')\n"
    )
    adapter.chmod(0o755)
    rc, text = phaselib.run_agent_blocking(
        adapter,
        "Smoke test",
        tmp_path / "prompt.md",
        log,
        phase_key="spec_validation",
        work_dir=tmp_path,
        claude_alias="claude",
    )
    assert rc == 0 and text == "tools available"


@pytest.mark.asyncio
async def test_real_mcp_disconnect_and_reconnect_reuses_task(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    params = StdioServerParameters(
        command=sys.executable, args=[str(tasks.ROOT / "tools/tlc_tools/mcp_server.py")], env=dict(os.environ)
    )
    async with stdio_client(params) as (reader, writer), ClientSession(reader, writer) as session:
        await session.initialize()
        listed = await session.list_tools()
        assert {t.name for t in listed.tools} == {"start_tlc", "wait_tlc"}
        started = await session.call_tool("start_tlc", start_args(runtime))
        assert not started.isError
        task_id = json.loads(started.content[0].text)["task_id"]  # type: ignore[union-attr]
        timed = await session.call_tool("wait_tlc", {"task_ids": [task_id], "timeout_seconds": 0})
        assert not timed.isError
    async with stdio_client(params) as (reader, writer), ClientSession(reader, writer) as session:
        await session.initialize()
        waited = await session.call_tool("wait_tlc", {"task_ids": [task_id], "timeout_seconds": 10})
        assert not waited.isError
        result = json.loads(waited.content[0].text)  # type: ignore[union-attr]
        assert result["tasks"][0]["exit_code"] == 0
    assert len(list(tasks.tasks_root().iterdir())) == 1


def test_pi_start_returns_before_tlc_exits(
    runtime: wrappers.RunModelCheckTests, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("FAKE_JAVA_SECONDS", "3")
    result = subprocess.run(
        [sys.executable, str(Path(tasks.__file__)), "start_tlc", json.dumps(start_args(runtime))],
        capture_output=True,
        text=True,
        timeout=2,
    )
    assert result.returncode == 0, result.stderr
    assert json.loads(result.stdout)["status"] == "running"


def test_lost_worker_is_not_success(runtime: wrappers.RunModelCheckTests) -> None:
    path = tasks.tasks_root() / ("a" * 32)
    path.mkdir(parents=True)
    (path / "request.json").write_text(json.dumps({"created_at": time.time() - 60, "owner": ""}))
    (path / "worker.json").write_text(json.dumps({"pid": os.getpid(), "identity": "different process"}))
    assert tasks.status(path.name)["status"] == "interrupted"
    assert tasks.status(path.name)["exit_code"] is None


@pytest.mark.parametrize("phase", ["spec_validation", "incremental"])
@pytest.mark.parametrize("agent", ["codex", "claude-code", "copilot-cli", "opencode", "pi"])
def test_all_adapters_receive_tools_without_skill_changes(tmp_path: Path, phase: str, agent: str) -> None:
    case = adapters.AdapterCase()
    tool = tmp_path / "tools/tlc_tools/.venv/bin"
    tool.mkdir(parents=True)
    (tool / "python").symlink_to(sys.executable)
    env = {"SPECULA_WORK_DIR": str(tmp_path / "work"), "SPECULA_PHASE": phase, "SPECULA_STOP_GATE": "off"}
    tasks.prepare_environment(env, tmp_path / "agent.log", tmp_path)
    env["COPILOT_HELP_TEXT"] = "--autopilot --additional-mcp-config"
    fake = {"claude-code": "claude", "copilot-cli": "copilot"}.get(agent, agent)
    fixture = json.dumps(adapters.CLAUDE_JSON) if agent == "claude-code" else ""
    if agent == "opencode":
        fixture = json.dumps({"type": "step_finish", "part": {"reason": "stop", "tokens": {}, "cost": 0}})
    elif agent == "pi":
        fixture = json.dumps(
            {"type": "message_end", "message": {"role": "assistant", "content": [], "stopReason": "stop"}}
        )
    try:
        observed = case.run_adapter(
            [str(tasks.ROOT / "scripts/launch/adapters" / f"{agent}.sh")],
            ["--prompt=tool registration smoke", "--max-turns=1", f"--log={tmp_path / 'agent.log'}"],
            fake_name=fake,
            fixture_text=fixture,
            env_extra=env,
            timeout=10,
        )
        assert observed["returncode"] == 0, observed["stderr"]
        argv = observed["argv"]
        if agent == "codex":
            assert "mcp_servers.specula_tlc=" + env["SPECULA_TLC_TOOL_CODEX"] in argv
        elif agent == "claude-code":
            assert argv[argv.index("--mcp-config") + 1] == env["SPECULA_TLC_TOOL_CONFIG"]
        elif agent == "copilot-cli":
            assert argv[argv.index("--additional-mcp-config") + 1] == env["SPECULA_TLC_TOOL_JSON"]
        elif agent == "opencode":
            config = json.loads(observed["opencode_config"])
            assert config["mcp"]["specula_tlc"]["timeout"] == tasks.CLIENT_TIMEOUT_MS
        else:
            assert argv[argv.index("--extension") + 1] == env["SPECULA_TLC_TOOL_EXTENSION"]
    finally:
        case.doCleanups()
