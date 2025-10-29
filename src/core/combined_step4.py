#!/usr/bin/env python3
"""
Combined Step 4 command: Syntactic sugar to run trace generation, instrumentation,
and Raft trace validation in a single command. Currently only supports Raft
trace collection and validation.

Example usage: (as if we concatenated the arguments for step4.1 and step4.2)
./specula step4 \
    --tla examples/etcd/spec/step3/Raft.tla \
    --cfg examples/etcd/spec/step3/Raft.cfg \
    --auto-config output/etcd/spec/step4/raft_config.yaml \
    --stub-template templates/instrumentation/go_trace_stub.template \
    --output examples/etcd/output/instrumented_raft.go \
    --verbose
    output/etcd/spec/step4/spec/
    examples/etcd/config/raft_config.yaml
    examples/etcd/source/raft.go
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path
import yaml


class CombinedPhase4:
    def __init__(self, args):
        self.args = args
        self.project_root = Path(__file__).resolve().parents[2]
        self.specula = str(self.project_root / "specula")

    def run(self):
        if "raft_config" not in self.args.auto_config:
            print(
                "Combined step4 command currently only supports Raft systems. "
                "See README for how to manually collect traces and run steps 4.1 and 4.2 separately."
            )
            return

        try:
            self._run_step41()
            self._run_step42()
            self._run_raft_trace_validation() # extend future systems here
        except subprocess.CalledProcessError as exc:
            cmd = " ".join(str(part) for part in exc.cmd)
            print(f"Command failed (exit {exc.returncode}): {cmd}")
            sys.exit(exc.returncode)

    def _run_step41(self):
        cmd = [self.specula, "step4.1"]
        if self.args.trace_config:
            cmd.extend(["--config", self.args.trace_config])
        if self.args.tla:
            cmd.extend(["--tla", self.args.tla])
        if self.args.cfg:
            cmd.extend(["--cfg", self.args.cfg])
        if self.args.prompt:
            cmd.extend(["--prompt", self.args.prompt])
        if self.args.llm_config:
            cmd.extend(["--llm-config", self.args.llm_config])
        if self.args.auto_config:
            cmd.extend(["--auto-config", self.args.auto_config])
        cmd.append(self.args.output_dir)
        subprocess.run(cmd, check=True, cwd=self.project_root)

    def _run_step42(self):
        cmd = [
            self.specula,
            "step4.2",
            self.args.instrument_config,
            self.args.source,
        ]
        if self.args.language:
            cmd.extend(["--language", self.args.language])
        if self.args.stub_template:
            cmd.extend(["--stub-template", self.args.stub_template])
        if self.args.output:
            cmd.extend(["--output", self.args.output])
        if self.args.validate_only:
            cmd.append("--validate-only")
        if self.args.generate_template:
            cmd.extend(["--generate-template", self.args.generate_template])
        if self.args.verbose:
            cmd.append("--verbose")
        subprocess.run(cmd, check=True, cwd=self.project_root)

    def _run_raft_trace_validation(self):
        if self.args.validate_only:
            print("Validate-only mode selected; skipping automated trace execution.")
            return

        # run Raft similar to generate trace.ndjson
        runner_dir = self.project_root / "examples" / "etcd" / "runners" / "raft_simulator"
        subprocess.run(["go", "run", "main.go"], check=True, cwd=runner_dir)

        # convert into TLA+ format
        etcd_root = self.project_root / "examples" / "etcd"
        subprocess.run(
            [
                "python3",
                "scripts/trace_converter.py",
                "-input",
                "./runners/raft_simulator/trace.ndjson",
                "-output",
                "./spec/step4/spec/",
                "-mode",
                "simple",
            ],
            check=True,
            cwd=etcd_root,
        )

        # run TLC for final trace validation
        spec_dir = etcd_root / "spec" / "step4" / "spec"
        tla_jar = self.project_root / "lib" / "tla2tools.jar"
        env = os.environ.copy()
        env["TRACE_PATH"] = "trace.ndjson"
        subprocess.run(
            [
                "java",
                "-cp",
                str(tla_jar),
                "tlc2.TLC",
                "-config",
                "specTrace.cfg",
                "specTrace.tla",
            ],
            check=True,
            cwd=spec_dir,
            env=env,
        )

    def _read_spec_name(self):
        config_path = Path(self.args.instrument_config)
        try:
            with open(config_path, "r", encoding="utf-8") as handle:
                data = yaml.safe_load(handle)
        except FileNotFoundError:
            print(f"Configuration file not found: {config_path}", file=sys.stderr)
            sys.exit(1)
        except yaml.YAMLError as exc:
            print(f"Failed to parse configuration file: {exc}", file=sys.stderr)
            sys.exit(1)

        if isinstance(data, dict):
            return data.get("spec_name")
        return None


def main():
    # taken from spectrace_generation.py and instrumentation.py
    parser = argparse.ArgumentParser(
        description="Run combined trace validation pipeline (Step 4)."
    )

    # spectrace_generation.py
    parser.add_argument("--config", dest="trace_config", help="Input configuration file (YAML)")
    parser.add_argument('--tla', help='Input TLA+ specification file (.tla)')
    parser.add_argument('--cfg', help='Input TLC configuration file (.cfg)')
    parser.add_argument('--prompt', help='Prompt template file (optional)')
    parser.add_argument('--llm-config', help='LLM configuration file (optional)')
    parser.add_argument('--auto-config', help='Output path for auto-generated config file (optional)')
    parser.add_argument('output_dir', help='Output directory for generated files')

    # instrumentation.py
    parser.add_argument(
        "instrument_config",
        metavar="config",
        help="TLA+ action configuration file for instrumentation",
    )
    parser.add_argument('source', help='Source code file to instrument')
    parser.add_argument('--language', help='Programming language (auto-detect if not specified)')
    parser.add_argument('--stub-template', help='Instrumentation stub template file')
    parser.add_argument('--output', '-o', help='Output file for instrumented code')
    parser.add_argument('--validate-only', action='store_true', help='Only validate, do not instrument')
    parser.add_argument('--generate-template', help='Generate template file for specified language')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')

    args = parser.parse_args()
    runner = CombinedPhase4(args)
    runner.run()


if __name__ == "__main__":
    main()
