#!/usr/bin/env python3
"""Run isolated exact-old V0 prior-generation Agents."""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
BASELINES = ROOT / "baselines"
LOG_ROOT = ROOT / "logs/baselines"
CASE_IDS = [f"case-{number:03d}" for number in range(1, 13)]
CODEX = Path("/home/ubuntu/.codex/packages/standalone/releases/0.152.0-x86_64-unknown-linux-musl/bin/codex")
CODEX_HOST = CODEX.with_name("codex-code-mode-host")
AUTH = Path("/home/ubuntu/.codex/auth.json")
INSTALLATION_ID = Path("/home/ubuntu/.codex/installation_id")
RUSTUP = Path("/home/ubuntu/.rustup")
CARGO_BIN = Path("/home/ubuntu/.cargo/bin")
MODEL = "gpt-5.6-sol"
EFFORT = "xhigh"


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tree_sha256(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(b"\0")
        digest.update(bytes.fromhex(sha256(path)))
        digest.update(b"\0")
    return digest.hexdigest()


def read_usage(path: Path) -> dict[str, int]:
    totals: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("type") != "turn.completed" or not isinstance(event.get("usage"), dict):
            continue
        for key, value in event["usage"].items():
            if isinstance(value, int):
                totals[key] = totals.get(key, 0) + value
    return totals


def audit_network_activity(path: Path) -> dict[str, Any]:
    patterns = [
        re.compile(r"(?<![\w-])(?:curl|wget|gh)(?![\w-])"),
        re.compile(r"\bgit\s+(?:fetch|pull|clone|ls-remote)\b"),
        re.compile(r"\b(?:lynx|links|w3m)\b"),
        re.compile(r"\bpython(?:3)?\b.*\b(?:requests|urllib|httpx|aiohttp)\b.*https?://"),
    ]
    matches: list[dict[str, str]] = []
    web_items: list[dict[str, str]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        item = event.get("item")
        if isinstance(item, dict) and item.get("type") in {"web_search", "web_search_call"}:
            web_items.append({"line": str(line_number), "type": str(item.get("type"))})
        if not isinstance(item, dict) or item.get("type") != "command_execution":
            continue
        command = item.get("command")
        if not isinstance(command, str):
            continue
        if any(pattern.search(command) for pattern in patterns):
            matches.append({"line": str(line_number), "command": command[:2000]})
    return {
        "policy": "soft-controlled: model API and build dependencies allowed; history/research commands prohibited and audited",
        "prohibited_command_matches": matches,
        "web_items": web_items,
        "contaminated": bool(matches or web_items),
    }


def require(attempt: Path) -> None:
    required = [
        CODEX,
        CODEX_HOST,
        AUTH,
        INSTALLATION_ID,
        RUSTUP,
        CARGO_BIN,
        attempt / ".agents/skills",
        attempt / "lib",
        attempt / "tools",
        attempt / "source/.git",
        attempt / "work-source/.git",
        attempt / "prior/.specula-output",
        attempt / "scope.md",
        attempt / "input-manifest.json",
        attempt / "task.md",
        attempt / "final-schema.json",
        attempt / "preparation-manifest.json",
    ]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise RuntimeError(f"missing inputs: {missing}")


def bwrap_command(attempt: Path, codex_home: Path) -> list[str]:
    cache = attempt / ".cache"
    (cache / "tmp").mkdir(parents=True, exist_ok=True)
    command = [
        "bwrap",
        "--die-with-parent",
        "--unshare-all",
        "--share-net",
        "--new-session",
        "--clearenv",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--ro-bind",
        "/usr",
        "/usr",
        "--symlink",
        "usr/bin",
        "/bin",
        "--symlink",
        "usr/lib",
        "/lib",
        "--symlink",
        "usr/lib64",
        "/lib64",
        "--symlink",
        "usr/sbin",
        "/sbin",
        "--ro-bind",
        "/etc",
        "/etc",
        "--dir",
        "/run",
        "--dir",
        "/run/systemd",
        "--ro-bind",
        "/run/systemd/resolve",
        "/run/systemd/resolve",
        "--tmpfs",
        "/tmp",
        "--dir",
        "/home",
        "--dir",
        "/home/codex",
        "--bind",
        str(codex_home),
        "/home/codex/.codex",
        "--bind",
        str(cache / "m2"),
        "/home/codex/.m2",
        "--dir",
        "/work",
        "--ro-bind",
        str(attempt / "source"),
        "/work/source",
        "--bind",
        str(attempt / "work-source"),
        "/work/work-source",
        "--bind",
        str(attempt / "prior"),
        "/work/prior",
        "--bind",
        str(attempt / ".cache"),
        "/work/.cache",
    ]
    for relative in (
        ".agents",
        "lib",
        "tools",
        "scope.md",
        "input-manifest.json",
        "task.md",
        "final-schema.json",
        "preparation-manifest.json",
    ):
        command.extend(["--ro-bind", str(attempt / relative), f"/work/{relative}"])
    if (attempt / "audit").is_dir():
        command.extend(["--ro-bind", str(attempt / "audit"), "/work/audit"])
    command.extend(
        [
            "--ro-bind",
            str(RUSTUP),
            "/opt/rustup",
            "--ro-bind",
            str(CARGO_BIN),
            "/opt/cargo-bin",
            "--ro-bind",
            str(CODEX),
            "/codex",
            "--ro-bind",
            str(CODEX_HOST),
            "/codex-code-mode-host",
            "--setenv",
            "HOME",
            "/home/codex",
            "--setenv",
            "CODEX_HOME",
            "/home/codex/.codex",
            "--setenv",
            "PATH",
            "/work/tools/network-guard:/opt/cargo-bin:/usr/local/go/bin:/usr/bin:/bin",
            "--setenv",
            "RUSTUP_HOME",
            "/opt/rustup",
            "--setenv",
            "CARGO_HOME",
            "/work/.cache/cargo",
            "--setenv",
            "CARGO_TARGET_DIR",
            "/work/.cache/cargo-target",
            "--setenv",
            "GOCACHE",
            "/work/.cache/go-build",
            "--setenv",
            "GOMODCACHE",
            "/work/.cache/go-mod",
            "--setenv",
            "GOPATH",
            "/work/.cache/gopath",
            "--setenv",
            "REBAR_CACHE_DIR",
            "/work/.cache/rebar3",
            "--setenv",
            "TMPDIR",
            "/work/.cache/tmp",
            "--setenv",
            "SPECULA_ROOT",
            "/work",
            "--setenv",
            "LANG",
            "C.UTF-8",
            "--setenv",
            "USER",
            "codex",
            "--setenv",
            "SHELL",
            "/bin/bash",
            "--setenv",
            "TERM",
            "dumb",
            "--chdir",
            "/work",
            "/codex",
            "exec",
            "--ignore-user-config",
            "--strict-config",
            "--ephemeral",
            "--skip-git-repo-check",
            "--dangerously-bypass-approvals-and-sandbox",
            "--model",
            MODEL,
            "--config",
            'model_provider="openai"',
            "--config",
            f'model_reasoning_effort="{EFFORT}"',
            "--output-schema",
            "/work/final-schema.json",
            "--output-last-message",
            "/work/prior/final-response.json",
            "--json",
            "-",
        ]
    )
    return command


def launcher_environment() -> dict[str, str]:
    return {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}


async def pump_stream(reader: asyncio.StreamReader, destination: Path) -> None:
    with destination.open("wb") as stream:
        while True:
            chunk = await reader.read(1024 * 1024)
            if not chunk:
                break
            stream.write(chunk)
            stream.flush()


async def run_case(case_id: str, attempt_name: str, timeout: int, semaphore: asyncio.Semaphore) -> dict[str, Any]:
    async with semaphore:
        attempt = BASELINES / case_id / attempt_name
        require(attempt)
        final = attempt / "prior/final-response.json"
        log_dir = LOG_ROOT / case_id / attempt_name
        log_dir.mkdir(parents=True, exist_ok=True)
        manifest_path = log_dir / "run-manifest.json"
        if final.exists() or manifest_path.exists():
            raise RuntimeError(f"refusing to overwrite: {attempt}")
        started = datetime.now(timezone.utc)
        manifest: dict[str, Any] = {
            "schema_version": 1,
            "case_id": case_id,
            "attempt": attempt_name,
            "status": "RUNNING",
            "started_at_utc": started.isoformat(),
            "model": MODEL,
            "reasoning_effort": EFFORT,
            "timeout_seconds": timeout,
            "codex_sha256": sha256(CODEX),
            "codex_host_sha256": sha256(CODEX_HOST),
            "runner_sha256": sha256(Path(__file__)),
            "prompt_sha256": sha256(attempt / "task.md"),
            "input_manifest_sha256": sha256(attempt / "input-manifest.json"),
            "scope_sha256": sha256(attempt / "scope.md"),
            "schema_sha256": sha256(attempt / "final-schema.json"),
            "skills_tree_sha256": tree_sha256(attempt / ".agents"),
            "tools_tree_sha256": tree_sha256(attempt / "tools"),
            "lib_tree_sha256": tree_sha256(attempt / "lib"),
            "isolation": "bubblewrap unshare-all; attempt is the only writable host tree; task, scope, skills, tools, and libraries are overlaid read-only",
            "network_control": "soft: shared network required by model API and dependency resolution; research commands prohibited and audited",
        }
        manifest_path.write_text(dump_json(manifest))
        activity = log_dir / "codex-activity.jsonl"
        stderr_path = log_dir / "codex-stderr.log"
        with tempfile.TemporaryDirectory(prefix=f"specula-v0-{case_id}-", dir="/dev/shm") as home_text:
            home = Path(home_text)
            shutil.copy2(AUTH, home / "auth.json")
            shutil.copy2(INSTALLATION_ID, home / "installation_id")
            command = bwrap_command(attempt.resolve(), home)
            process = await asyncio.create_subprocess_exec(
                *command,
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                env=launcher_environment(),
                start_new_session=True,
            )
            assert process.stdin is not None and process.stdout is not None and process.stderr is not None
            stdout_task = asyncio.create_task(pump_stream(process.stdout, activity))
            stderr_task = asyncio.create_task(pump_stream(process.stderr, stderr_path))
            process.stdin.write((attempt / "task.md").read_bytes())
            await process.stdin.drain()
            process.stdin.close()
            try:
                await asyncio.wait_for(process.wait(), timeout=timeout)
                timed_out = False
            except asyncio.TimeoutError:
                timed_out = True
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    await asyncio.wait_for(process.wait(), timeout=30)
                except asyncio.TimeoutError:
                    os.killpg(process.pid, signal.SIGKILL)
                    await process.wait()
            await asyncio.gather(stdout_task, stderr_task)
        finished = datetime.now(timezone.utc)
        status = "TIMEOUT" if timed_out else ("COMPLETED" if process.returncode == 0 and final.is_file() else "FAILED")
        result: dict[str, Any] | None = None
        if final.is_file():
            try:
                parsed = json.loads(final.read_text())
                if isinstance(parsed, dict):
                    result = parsed
                else:
                    status = "INVALID_FINAL_JSON"
            except json.JSONDecodeError:
                status = "INVALID_FINAL_JSON"
        network_audit = audit_network_activity(activity)
        (log_dir / "network-audit.json").write_text(dump_json(network_audit))
        pristine_status = subprocess.run(
            ["/usr/bin/git", "-C", str(attempt / "source"), "status", "--porcelain"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        work_diff = subprocess.run(
            ["/usr/bin/git", "-C", str(attempt / "work-source"), "diff", "--binary", "HEAD"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        manifest.update(
            {
                "status": status,
                "exit_code": process.returncode,
                "timed_out": timed_out,
                "finished_at_utc": finished.isoformat(),
                "wall_seconds": (finished - started).total_seconds(),
                "usage": read_usage(activity),
                "activity_sha256": sha256(activity),
                "stderr_sha256": sha256(stderr_path),
                "workflow_status": result.get("workflow_status") if result else None,
                "trace_validation": result.get("trace_validation") if result else None,
                "model_checking": result.get("model_checking") if result else None,
                "network_audit": network_audit,
                "prior_tree_sha256": tree_sha256(attempt / "prior"),
                "pristine_source_clean": pristine_status.returncode == 0 and not pristine_status.stdout,
                "work_source_diff_sha256": hashlib.sha256(work_diff.stdout).hexdigest(),
            }
        )
        manifest_path.write_text(dump_json(manifest))
        print(
            f"{case_id}: {status} workflow={manifest['workflow_status']} trace={manifest['trace_validation']} mc={manifest['model_checking']} contaminated={network_audit['contaminated']} {manifest['wall_seconds']:.1f}s",
            flush=True,
        )
        return manifest


async def async_main(args: argparse.Namespace) -> int:
    selected = args.cases or CASE_IDS
    unknown = sorted(set(selected) - set(CASE_IDS))
    if unknown:
        raise SystemExit(f"unknown cases: {unknown}")
    if not 1 <= args.jobs <= 3:
        raise SystemExit("--jobs must be between 1 and 3")
    if len(selected) != len(set(selected)):
        raise SystemExit("duplicate --case values are not allowed")
    semaphore = asyncio.Semaphore(args.jobs)
    if Path(args.attempt).name != args.attempt or args.attempt in {".", ".."}:
        raise SystemExit("invalid --attempt")
    tasks = [run_case(case_id, args.attempt, args.timeout, semaphore) for case_id in selected]
    results = await asyncio.gather(*tasks, return_exceptions=True)
    failed = False
    summary: list[dict[str, Any]] = []
    for case_id, result in zip(selected, results, strict=True):
        if isinstance(result, BaseException):
            failed = True
            summary.append({"case_id": case_id, "status": "RUNNER_ERROR", "error": repr(result)})
            print(f"{case_id}: RUNNER_ERROR {result!r}", flush=True)
        else:
            summary.append(result)
            if result["status"] != "COMPLETED":
                failed = True
    summary_value = {
        "schema_version": 1,
        "finished_at_utc": datetime.now(timezone.utc).isoformat(),
        "jobs": args.jobs,
        "attempt": args.attempt,
        "timeout_seconds": args.timeout,
        "cases": summary,
    }
    (ROOT / f"baseline-run-summary.{args.attempt}.json").write_text(dump_json(summary_value))
    (ROOT / "baseline-run-summary.json").write_text(dump_json(summary_value))
    return 1 if failed else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=14400)
    parser.add_argument("--attempt", default="attempt-001")
    return asyncio.run(async_main(parser.parse_args()))


if __name__ == "__main__":
    raise SystemExit(main())
