#!/usr/bin/env python3
"""Run SANY or TLC, preserving output and exit status without a task deadline."""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from prepare import prepare


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("parse", "check"))
    parser.add_argument("spec", type=Path)
    parser.add_argument("--config", type=Path)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--heap", default="1g")
    parser.add_argument("--workers", type=int, default=1)
    # Keep flags for the underlying tool separate from the small runner interface.
    arguments = sys.argv[1:]
    separator = arguments.index("--") if "--" in arguments else len(arguments)
    args = parser.parse_args(arguments[:separator])
    extra = arguments[separator + 1 :]
    spec = args.spec.resolve()
    if not spec.is_file():
        parser.error(f"Model not found: {spec}")
    if args.workers < 1:
        parser.error("--workers must be positive")
    if args.config and not (spec.parent / args.config).is_file():
        parser.error(f"Config not found: {spec.parent / args.config}")
    log = args.log.resolve()
    receipt = log.with_name(log.name + ".run.json")
    trace = log.with_name(log.name + ".trace.json")
    if log.exists() or receipt.exists() or trace.exists():
        parser.error(f"Use a fresh log path; preserving existing artifacts: {log}")
    if any(argument.lower() == "-dumptrace" for argument in extra):
        parser.error("The runner already saves JSON counterexamples beside the log; omit -dumptrace")
    environment = prepare()
    command = [str(environment["java"]), f"-Xmx{args.heap}", "-cp", os.pathsep.join(environment["jars"])]
    command += ["tla2sany.SANY"] if args.mode == "parse" else ["tlc2.TLC", "-workers", str(args.workers)]
    if args.mode == "check":
        command += ["-dumptrace", "json", str(trace)]
    if args.config and args.mode == "check":
        command += ["-config", str(args.config)]
    command += [*extra, spec.name]
    record = {"command": command, "cwd": str(spec.parent), "started_at": datetime.now(timezone.utc).isoformat()}
    log.parent.mkdir(parents=True, exist_ok=True)
    interrupted_signal = signal.SIGINT

    def interrupt(signum: int, _frame: object) -> None:
        nonlocal interrupted_signal
        interrupted_signal = signum
        raise KeyboardInterrupt

    previous_term = signal.signal(signal.SIGTERM, interrupt)
    with log.open("x") as output:
        with receipt.open("x") as metadata:
            json.dump(record, metadata, indent=2)
        print(json.dumps({"log": str(log), "receipt": str(receipt)}), flush=True)
        process = None
        try:
            process = subprocess.Popen(command, cwd=spec.parent, stdout=output, stderr=subprocess.STDOUT)
            record["pid"] = process.pid
            receipt.write_text(json.dumps(record, indent=2) + "\n")
            code = process.wait()
        except KeyboardInterrupt:
            if process is not None:
                if process.poll() is None:
                    process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            record["interrupted"] = True
            code = 128 + interrupted_signal
        except OSError as error:
            record["error"] = str(error)
            code = 1
        record.update(exit_code=code, finished_at=datetime.now(timezone.utc).isoformat())
        receipt.write_text(json.dumps(record, indent=2) + "\n")
    signal.signal(signal.SIGTERM, previous_term)
    print(json.dumps({"exit_code": code, "log": str(log), "receipt": str(receipt)}), flush=True)
    return code if code >= 0 else 128 - code


if __name__ == "__main__":
    raise SystemExit(main())
