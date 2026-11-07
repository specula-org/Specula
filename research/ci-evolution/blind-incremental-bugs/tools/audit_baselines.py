#!/usr/bin/env python3
"""Deterministically audit exact-old V0 priors before incremental use."""

from __future__ import annotations

import argparse
import json
import hashlib
import os
import re
import stat
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import jsonschema


SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
CASE_IDS = [f"case-{number:03d}" for number in range(1, 13)]
REQUIRED_FILES = (
    "modeling-brief.md",
    "analysis-report.md",
    "spec/base.tla",
    "spec/base.cfg",
    "spec/MC.tla",
    "spec/MC.cfg",
    "spec/Trace.tla",
    "spec/Trace.cfg",
)
REQUIRED_ALTERNATIVES = (
    ("spec/instrumentation-spec.md", "instrumentation-spec.md"),
    ("spec/brief-coverage.md", "brief-coverage.md"),
)
TLC_SUCCESS = "Model checking completed. No error has been found."
TLC_EMPTY_QUEUE = re.compile(r"\b0 states left on queue\.")


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


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


def activity_commands(path: Path) -> list[dict[str, Any]]:
    commands: list[dict[str, Any]] = []
    if not path.is_file():
        return commands
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        item = event.get("item")
        if event.get("type") != "item.completed" or not isinstance(item, dict) or item.get("type") != "command_execution":
            continue
        command = item.get("command")
        output = item.get("aggregated_output", "")
        if isinstance(command, str):
            commands.append(
                {
                    "id": item.get("id"),
                    "command": command,
                    "output": output if isinstance(output, str) else "",
                    "exit_code": item.get("exit_code"),
                }
            )
    return commands


def blind_activity_audit(path: Path) -> dict[str, Any]:
    command_pattern = re.compile(
        r"(?<![\w-])(?:curl|wget|gh)(?![\w-])"
        r"|\bgit\s+(?:fetch|pull|clone|ls-remote)\b"
        r"|\b(?:lynx|links|w3m)\b"
        r"|\bpython(?:3)?\b.*\b(?:requests|urllib|httpx|aiohttp)\b.*https?://"
        r"|(?:/proc/(?:self|1)/(?:mountinfo|environ|cmdline)|\bfindmnt\b)"
    )
    commands: list[dict[str, Any]] = []
    web_items: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        item = event.get("item")
        if not isinstance(item, dict):
            continue
        if item.get("type") in {"web_search", "web_search_call"}:
            web_items.append({"line": line_number, "type": item.get("type")})
        command = item.get("command") if item.get("type") == "command_execution" else None
        if isinstance(command, str) and command_pattern.search(command):
            commands.append({"line": line_number, "command": command[:2000]})
    return {
        "passed": not commands and not web_items,
        "prohibited_commands": commands,
        "web_items": web_items,
    }


def gold_leak_audit(case_id: str, prior: Path) -> dict[str, Any]:
    case_map = load_json(ROOT / "gold/case-map.json")
    candidates = load_json(ROOT / "gold/candidates.json")
    candidate_id = next(
        item["candidate_id"]
        for item in case_map["mapping"]
        if item["case_id"] == case_id
    )
    candidate = next(item for item in candidates["cases"] if item["id"] == candidate_id)
    tokens = {
        candidate_id,
        candidate["old_revision"],
        candidate["buggy_revision"],
        candidate["fixed_revision"],
        candidate["introducing_update"]["url"],
        *candidate["bug"].get("references", []),
    }
    if candidate.get("introducing_update", {}).get("pr"):
        tokens.add(candidate["introducing_update"]["pr"])
    if candidate.get("fix", {}).get("url"):
        tokens.add(candidate["fix"]["url"])
    files = [
        path
        for path in prior.iterdir()
        if path.is_file() and path.stat().st_size <= 5 * 1024 * 1024
    ]
    spec = prior / "spec"
    if spec.is_dir():
        files.extend(
            path
            for path in spec.rglob("*")
            if path.is_file()
            and "output" not in path.relative_to(spec).parts
            and path.stat().st_size <= 5 * 1024 * 1024
        )
    matches: list[dict[str, str]] = []
    for path in files:
        content = path.read_text(encoding="utf-8", errors="replace")
        for token in sorted(tokens):
            if token and token in content:
                matches.append({"path": str(path), "token": token})
    return {"passed": not matches, "matches": matches, "token_count": len(tokens)}


def is_trace_tlc(command: str) -> bool:
    lowered = command.lower()
    return ("tlc2.tlc" in lowered or "run_trace" in lowered) and (
        "trace.tla" in lowered or "trace.cfg" in lowered or "tracevalidation" in lowered
    )


def is_mc_tlc(command: str) -> bool:
    lowered = command.lower()
    if "tlc2.tlc" not in lowered or is_trace_tlc(command):
        return False
    if re.search(r"(?:-depth\s+(?:0|1)\b|-simulate\s+num=1\b)", lowered):
        return False
    return "mc.tla" in lowered or "mc.cfg" in lowered or "base.tla" in lowered or "base.cfg" in lowered


def run_sany(spec_dir: Path, module: str, log_path: Path, lib: Path) -> dict[str, Any]:
    classpath = f"{lib / 'tla2tools.jar'}:{lib / 'CommunityModules-deps.jar'}"
    try:
        with tempfile.TemporaryDirectory(prefix="specula-sany-audit-", dir="/dev/shm") as temporary:
            environment = os.environ.copy()
            environment["TMPDIR"] = temporary
            completed = subprocess.run(
                ["java", f"-Djava.io.tmpdir={temporary}", "-XX:-UsePerfData", "-cp", classpath, "tla2sany.SANY", module],
                cwd=spec_dir,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=120,
                check=False,
            )
        output = completed.stdout
        passed = completed.returncode == 0 and not re.search(
            r"(?:Semantic errors:\s*[1-9]|Parse Error|Lexical error|Cannot find source file)", output, re.IGNORECASE
        )
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + "\nAUDIT TIMEOUT\n"
        passed = False
        completed = None
    log_path.write_text(output, encoding="utf-8")
    return {
        "module": module,
        "passed": passed,
        "exit_code": completed.returncode if completed is not None else None,
        "log": str(log_path),
    }


def audit_case(case_id: str, attempt_name: str) -> dict[str, Any]:
    attempt = ROOT / "baselines" / case_id / attempt_name
    prior = attempt / "prior/.specula-output"
    run_logs = ROOT / "logs/baselines" / case_id / attempt_name
    audit_logs = ROOT / "logs/baseline-audit" / case_id / attempt_name
    audit_logs.mkdir(parents=True, exist_ok=True)
    blockers: list[str] = []
    warnings: list[str] = []
    checks: dict[str, Any] = {}

    missing = [
        relative
        for relative in REQUIRED_FILES
        if not (prior / relative).is_file() or (prior / relative).stat().st_size == 0
    ]
    for alternatives in REQUIRED_ALTERNATIVES:
        if not any((prior / relative).is_file() and (prior / relative).stat().st_size > 0 for relative in alternatives):
            missing.append(" | ".join(alternatives))
    checks["required_files"] = {"passed": not missing, "missing": missing}
    if missing:
        blockers.append("missing required prior files")
    harness_files = [path for path in (prior / "harness").rglob("*") if path.is_file()] if (prior / "harness").is_dir() else []
    run_scripts = [
        path
        for path in harness_files
        if path.name == "run.sh" and stat.S_IMODE(path.stat().st_mode) & 0o111
    ]
    checks["harness"] = {
        "passed": bool(run_scripts),
        "file_count": len(harness_files),
        "executable_run_scripts": [str(path) for path in run_scripts],
    }
    if not checks["harness"]["passed"]:
        blockers.append("missing executable harness run.sh")

    trace_results: list[dict[str, Any]] = []
    traces = (
        sorted(
            path
            for path in (prior / "traces").rglob("*")
            if path.is_file() and path.suffix in {".ndjson", ".jsonl"}
        )
        if (prior / "traces").is_dir()
        else []
    )
    for trace in traces:
        record = {
            "path": str(trace),
            "bytes": trace.stat().st_size,
            "lines": 0,
            "valid_json_lines": True,
            "valid_event_shape": True,
        }
        for line in trace.read_text(encoding="utf-8", errors="replace").splitlines():
            if not line.strip():
                continue
            record["lines"] += 1
            try:
                value = json.loads(line)
                event = value.get("event") if isinstance(value, dict) else None
                if not (
                    isinstance(event, dict)
                    and isinstance(event.get("name"), str)
                    and event["name"]
                    and len(event) >= 2
                ):
                    record["valid_event_shape"] = False
            except json.JSONDecodeError:
                record["valid_json_lines"] = False
        trace_results.append(record)
    nonempty_valid = [
        item
        for item in trace_results
        if item["bytes"] > 0
        and item["lines"] > 0
        and item["valid_json_lines"]
        and item["valid_event_shape"]
    ]
    checks["traces"] = {
        "passed": bool(nonempty_valid) and len(nonempty_valid) == len(trace_results),
        "count": len(trace_results),
        "nonempty_valid_count": len(nonempty_valid),
        "items": trace_results,
    }
    if not checks["traces"]["passed"]:
        blockers.append("fresh NDJSON traces are missing, empty, or malformed")

    schema_path = attempt / "final-schema.json"
    final_path = attempt / "prior/final-response.json"
    final: dict[str, Any] | None = None
    final_error = None
    try:
        candidate = load_json(final_path)
        jsonschema.validate(candidate, load_json(schema_path))
        if not isinstance(candidate, dict):
            raise TypeError("final response is not an object")
        final = candidate
    except Exception as exc:  # deterministic audit records exact schema/read failure
        final_error = f"{type(exc).__name__}: {exc}"
    checks["final_schema"] = {"passed": final is not None, "error": final_error, "value": final}
    if final is None:
        blockers.append("missing or invalid final response")
    else:
        if final["workflow_status"] not in {"COMPLETED", "COMPLETED_WITH_LIMITED_COVERAGE"}:
            blockers.append(f"workflow status is {final['workflow_status']}")
        if final["trace_validation"] not in {"PASSED", "LIMITED_COVERAGE"}:
            blockers.append(f"trace validation status is {final['trace_validation']}")
        if final["model_checking"] not in {"PASSED", "LIMITED_COVERAGE"}:
            blockers.append(f"model checking status is {final['model_checking']}")
        if final["blockers"]:
            blockers.append("Agent reported unresolved blockers")
        if "LIMITED_COVERAGE" in {
            final["workflow_status"], final["trace_validation"], final["model_checking"]
        }:
            warnings.append("coverage is explicitly limited; acceptance means usable validated prior, not proof")

    commands = activity_commands(run_logs / "codex-activity.jsonl")
    trace_indices = [index for index, item in enumerate(commands) if is_trace_tlc(item["command"])]
    mc_indices = [index for index, item in enumerate(commands) if is_mc_tlc(item["command"])]
    saved_logs = [path for path in (prior / "spec/output").rglob("*") if path.is_file()] if (prior / "spec/output").is_dir() else []
    trace_log_success = []
    mc_log_success = []
    for path in saved_logs:
        text = path.read_text(encoding="utf-8", errors="replace")
        if TLC_SUCCESS not in text or not TLC_EMPTY_QUEUE.search(text):
            continue
        relative = path.relative_to(prior / "spec/output").as_posix()
        if "trace" in relative.lower():
            trace_log_success.append(relative)
        elif (
            any(token in relative.lower() for token in ("mc", "model", "base"))
            and "reach" not in relative.lower()
            and "simulation" not in relative.lower()
        ):
            mc_log_success.append(relative)
    trace_first = bool(
        trace_indices
        and mc_indices
        and min(trace_indices) < min(mc_indices)
    )
    trace_commands_ok = bool(trace_indices) and any(commands[index]["exit_code"] == 0 for index in trace_indices)
    mc_commands_ok = bool(mc_indices) and any(commands[index]["exit_code"] == 0 for index in mc_indices)
    checks["execution_evidence"] = {
        "passed": (
            trace_commands_ok
            and mc_commands_ok
            and len(trace_log_success) >= len(nonempty_valid)
            and bool(mc_log_success)
            and trace_first
        ),
        "command_count": len(commands),
        "trace_tlc_commands": len(trace_indices),
        "trace_commands_exit_zero": trace_commands_ok,
        "mc_commands": len(mc_indices),
        "mc_commands_exit_zero": mc_commands_ok,
        "trace_success_logs": trace_log_success,
        "mc_success_logs": mc_log_success,
        "trace_first": trace_first,
    }
    if not checks["execution_evidence"]["passed"]:
        blockers.append("activity log lacks terminal trace-first TLC and model-checking evidence")

    replay_path = audit_logs / "tlc-replay/replay-manifest.json"
    replay = load_json(replay_path) if replay_path.is_file() else None
    replay_trace_hashes = {
        item.get("trace_sha256")
        for item in replay.get("trace_results", [])
        if isinstance(item, dict)
    } if replay else set()
    current_trace_hashes = {sha256(path) for path in traces}
    replay_passed = bool(
        replay
        and replay.get("verdict") == "PASS"
        and replay.get("all_traces_passed") is True
        and replay.get("all_models_passed") is True
        and replay_trace_hashes == current_trace_hashes
        and len(replay.get("model_results", [])) >= 1
    )
    checks["independent_tlc_replay"] = {
        "passed": replay_passed,
        "manifest": str(replay_path),
        "manifest_sha256": sha256(replay_path) if replay_path.is_file() else None,
        "value": replay,
    }
    if not replay_passed:
        blockers.append("independent trace/base/MC replay is missing or failed")

    network_path = run_logs / "network-audit.json"
    network = load_json(network_path) if network_path.is_file() else None
    direct_activity = blind_activity_audit(run_logs / "codex-activity.jsonl")
    checks["network"] = {
        "passed": bool(network) and not network.get("contaminated", True) and direct_activity["passed"],
        "value": network,
        "direct_activity": direct_activity,
    }
    if not checks["network"]["passed"]:
        blockers.append("network/history command audit is missing or contaminated")

    leak = gold_leak_audit(case_id, prior)
    checks["gold_leak"] = leak
    if not leak["passed"]:
        blockers.append("generated prior contains hidden candidate or future-version identifiers")

    source_manifest = load_json(attempt / "input-manifest.json")
    preparation = load_json(attempt / "preparation-manifest.json")
    pristine_status = subprocess.run(
        ["git", "-C", str(attempt / "source"), "status", "--porcelain"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    source_commit_count = subprocess.run(
        ["git", "-C", str(attempt / "source"), "rev-list", "--all", "--count"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    ).stdout.strip()
    source_subjects = subprocess.run(
        ["git", "-C", str(attempt / "source"), "log", "--format=%s", "--all"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    ).stdout.splitlines()
    source_remotes = subprocess.run(
        ["git", "-C", str(attempt / "source"), "remote"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    ).stdout.splitlines()
    declared = source_manifest.get("source", {})
    identity_matches = declared.get("sha256") == preparation.get("source_identity", {}).get("sha256")
    checks["pristine_source"] = {
        "passed": (
            pristine_status.returncode == 0
            and not pristine_status.stdout
            and source_commit_count == "1"
            and source_subjects == ["baseline"]
            and not source_remotes
            and identity_matches
        ),
        "status": pristine_status.stdout,
        "commit_count": source_commit_count,
        "subjects": source_subjects,
        "remotes": source_remotes,
        "declared_identity": declared,
        "preparation_identity": preparation.get("source_identity"),
        "identity_matches": identity_matches,
    }
    if not checks["pristine_source"]["passed"]:
        blockers.append("pristine exact-old source changed")

    sany_results = []
    spec_dir = prior / "spec"
    for module in ("base.tla", "MC.tla", "Trace.tla"):
        if (spec_dir / module).is_file():
            sany_results.append(
                run_sany(
                    spec_dir,
                    module,
                    audit_logs / f"sany-{module}.log",
                    attempt / "lib",
                )
            )
    checks["sany"] = {"passed": len(sany_results) == 3 and all(item["passed"] for item in sany_results), "items": sany_results}
    if not checks["sany"]["passed"]:
        blockers.append("one or more TLA+ modules fail deterministic SANY parsing")

    run_manifest_path = run_logs / "run-manifest.json"
    run_manifest = load_json(run_manifest_path) if run_manifest_path.is_file() else None
    checks["runner"] = {
        "passed": (
            bool(run_manifest)
            and run_manifest.get("status") == "COMPLETED"
            and run_manifest.get("exit_code") == 0
            and run_manifest.get("prior_tree_sha256") == tree_sha256(attempt / "prior")
        ),
        "value": run_manifest,
    }
    if not checks["runner"]["passed"]:
        blockers.append("runner did not finish cleanly")

    verdict = "REJECT" if blockers else "ACCEPT"
    result = {
        "schema_version": 1,
        "case_id": case_id,
        "attempt": attempt_name,
        "audited_at_utc": datetime.now(timezone.utc).isoformat(),
        "verdict": verdict,
        "checks": checks,
        "blockers": sorted(set(blockers)),
        "warnings": sorted(set(warnings)),
    }
    (attempt / "baseline-audit.json").write_text(dump_json(result), encoding="utf-8")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--attempt", default="attempt-004")
    parser.add_argument("--case", action="append", dest="cases")
    args = parser.parse_args()
    selected = args.cases or CASE_IDS
    unknown = sorted(set(selected) - set(CASE_IDS))
    if unknown:
        raise SystemExit(f"unknown cases: {unknown}")
    results = [audit_case(case_id, args.attempt) for case_id in selected]
    summary = {
        "schema_version": 1,
        "attempt": args.attempt,
        "audited_at_utc": datetime.now(timezone.utc).isoformat(),
        "counts": {verdict: sum(item["verdict"] == verdict for item in results) for verdict in ("ACCEPT", "LIMITED", "REJECT")},
        "cases": [{"case_id": item["case_id"], "verdict": item["verdict"], "blockers": item["blockers"], "warnings": item["warnings"]} for item in results],
    }
    (ROOT / "baseline-audit-summary.json").write_text(dump_json(summary), encoding="utf-8")
    print(dump_json(summary), end="")
    return 0 if all(item["verdict"] == "ACCEPT" for item in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
