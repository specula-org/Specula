#!/usr/bin/env python3
"""Independently replay canonical trace and model checks for a V0 prior."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
CASE_IDS = [f"case-{number:03d}" for number in range(1, 13)]
SUCCESS = "Model checking completed. No error has been found."
EMPTY_QUEUE = re.compile(r"\b0 states left on queue\.")


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_tlc(
    *,
    case_id: str,
    name: str,
    spec_dir: Path,
    lib: Path,
    module: str,
    config: str,
    log: Path,
    timeout: int,
    trace: Path | None = None,
) -> dict[str, Any]:
    classpath = f"{lib / 'tla2tools.jar'}:{lib / 'CommunityModules-deps.jar'}"
    environment = os.environ.copy()
    if trace is not None:
        environment["JSON"] = str(trace)
        environment["SPECULA_TRACE"] = str(trace)
        environment["TRACE_FILE"] = str(trace)
    with tempfile.TemporaryDirectory(prefix=f"specula-audit-{case_id}-{name}-", dir="/dev/shm") as state_dir:
        scratch_spec = Path(state_dir) / "spec"
        shutil.copytree(spec_dir, scratch_spec, symlinks=True)
        environment["TMPDIR"] = state_dir
        command = [
            "java",
            f"-Djava.io.tmpdir={state_dir}",
            "-XX:+UseParallelGC",
            "-XX:-UsePerfData",
            "-Xmx8G",
            "-cp",
            classpath,
            "tlc2.TLC",
            "-workers",
            "4",
            "-config",
            config,
            "-metadir",
            state_dir,
        ]
        if trace is not None:
            command.append("-deadlock")
        command.append(module)
        try:
            completed = subprocess.run(
                command,
                cwd=scratch_spec,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=timeout,
                text=True,
                check=False,
                start_new_session=True,
            )
            output = completed.stdout
            exit_code = completed.returncode
            timed_out = False
        except subprocess.TimeoutExpired as exc:
            raw = exc.stdout or ""
            output = raw.decode(errors="replace") if isinstance(raw, bytes) else raw
            output += f"\nAUDIT TIMEOUT after {timeout}s\n"
            exit_code = None
            timed_out = True
    log.write_text(output, encoding="utf-8")
    states = re.search(r"(\d+) states generated, (\d+) distinct states found", output)
    return {
        "name": name,
        "module": module,
        "config": config,
        "trace": str(trace) if trace is not None else None,
        "trace_sha256": sha256(trace) if trace is not None else None,
        "command": command,
        "timeout_seconds": timeout,
        "timed_out": timed_out,
        "exit_code": exit_code,
        "success": exit_code == 0 and SUCCESS in output and bool(EMPTY_QUEUE.search(output)),
        "states_generated": int(states.group(1)) if states else None,
        "distinct_states": int(states.group(2)) if states else None,
        "log": str(log),
        "log_sha256": sha256(log),
    }


def replay_trace(
    *,
    case_id: str,
    trace: Path,
    spec_dir: Path,
    lib: Path,
    output_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    stem = trace.name
    for suffix in (".ndjson", ".jsonl"):
        if stem.endswith(suffix):
            stem = stem[: -len(suffix)]
            break
    config_stem = stem.removesuffix(".tlc").replace("-", "_")
    specialized = spec_dir / f"Trace_{config_stem}.cfg"
    source_config = specialized if specialized.is_file() else spec_dir / "Trace.cfg"
    content = source_config.read_text(encoding="utf-8")
    rewritten, count = re.subn(
        r'(?m)^(\s*TraceFile\s*=\s*).+$',
        lambda match: match.group(1) + json.dumps(str(trace)),
        content,
    )
    if count:
        audit_config = output_dir / f"trace-{config_stem}.audit.cfg"
        audit_config.write_text(rewritten, encoding="utf-8")
        config = str(audit_config)
    else:
        config = str(source_config)
    return run_tlc(
        case_id=case_id,
        name=f"trace-{stem}",
        spec_dir=spec_dir,
        lib=lib,
        module="Trace.tla",
        config=config,
        log=output_dir / f"trace-{stem}.log",
        timeout=timeout,
        trace=trace,
    )


def replay_case(case_id: str, attempt_name: str, trace_timeout: int, model_timeout: int) -> dict[str, Any]:
    attempt = ROOT / "baselines" / case_id / attempt_name
    prior = attempt / "prior/.specula-output"
    spec = prior / "spec"
    lib = attempt / "lib"
    output_dir = ROOT / "logs/baseline-audit" / case_id / attempt_name / "tlc-replay"
    output_dir.mkdir(parents=True, exist_ok=True)
    required = [spec / "base.tla", spec / "base.cfg", spec / "MC.tla", spec / "MC.cfg", spec / "Trace.tla", spec / "Trace.cfg"]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise RuntimeError(f"{case_id}: missing canonical TLA inputs: {missing}")
    traces = sorted(
        path
        for path in (prior / "traces").rglob("*")
        if path.is_file() and path.suffix in {".ndjson", ".jsonl"}
    )
    if not traces:
        raise RuntimeError(f"{case_id}: no traces to replay")

    trace_results = [
        replay_trace(
            case_id=case_id,
            trace=trace,
            spec_dir=spec,
            lib=lib,
            output_dir=output_dir,
            timeout=trace_timeout,
        )
        for trace in traces
    ]
    model_results = []
    if all(item["success"] for item in trace_results):
        complete_config = "MC_complete_core.cfg" if (spec / "MC_complete_core.cfg").is_file() else "MC.cfg"
        model_results.append(
            run_tlc(
                case_id=case_id,
                name="mc-complete",
                spec_dir=spec,
                lib=lib,
                module="MC.tla",
                config=complete_config,
                log=output_dir / "mc-complete.log",
                timeout=model_timeout,
            )
        )
    result = {
        "schema_version": 1,
        "case_id": case_id,
        "attempt": attempt_name,
        "replayed_at_utc": datetime.now(timezone.utc).isoformat(),
        "ordering": "all trace replays completed before canonical base/MC replay",
        "trace_results": trace_results,
        "model_results": model_results,
        "all_traces_passed": bool(trace_results) and all(item["success"] for item in trace_results),
        "all_models_passed": len(model_results) == 1 and all(item["success"] for item in model_results),
    }
    result["verdict"] = "PASS" if result["all_traces_passed"] and result["all_models_passed"] else "FAIL"
    path = output_dir / "replay-manifest.json"
    path.write_text(dump_json(result), encoding="utf-8")
    result["manifest"] = str(path)
    result["manifest_sha256"] = sha256(path)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--attempt", default="attempt-004")
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--trace-timeout", type=int, default=300)
    parser.add_argument("--model-timeout", type=int, default=900)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    selected = args.cases or CASE_IDS
    unknown = sorted(set(selected) - set(CASE_IDS))
    if unknown:
        raise SystemExit(f"unknown cases: {unknown}")
    if not 1 <= args.jobs <= 3:
        raise SystemExit("--jobs must be between 1 and 3")
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = [
            executor.submit(
                replay_case,
                case_id,
                args.attempt,
                args.trace_timeout,
                args.model_timeout,
            )
            for case_id in selected
        ]
        results = [future.result() for future in futures]
    value = {
        "schema_version": 1,
        "attempt": args.attempt,
        "finished_at_utc": datetime.now(timezone.utc).isoformat(),
        "cases": results,
    }
    (ROOT / "baseline-tlc-replay-summary.json").write_text(dump_json(value), encoding="utf-8")
    print(dump_json(value), end="")
    return 0 if all(item["verdict"] == "PASS" for item in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
