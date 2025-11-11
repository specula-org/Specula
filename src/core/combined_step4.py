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

from src.systems.etcd.trace_generation.pipeline import EtcdTracePipeline


class CombinedPhase4:
    def __init__(self, args):
        self.args = args
        self.project_root = Path(__file__).resolve().parents[2]
        self.specula = str(self.project_root / "specula")
        self._generated_trace = None

    def run(self):
        if "raft_config" not in self.args.auto_config:
            print(
                "Combined step4 command currently only supports Raft systems. "
                "See README for how to manually collect traces and run steps 4.1 and 4.2 separately."
            )
            return

        try:
            if not self.args.with_exist_specTrace:
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
        if self.args.validate_only:
            print("Validate-only mode selected; skipping instrumentation and trace generation.")
            return

        source_arg = Path(self.args.source)
        if source_arg.exists():
            source_rel = source_arg.name
        else:
            source_rel = self.args.source

        pipeline_kwargs = {
            "config_path": Path(self.args.instrument_config),
            "source_rel_path": source_rel,
            "duration_seconds": self.args.duration,
        }
        if self.args.stub_template:
            pipeline_kwargs["stub_template"] = Path(self.args.stub_template)
        pipeline = EtcdTracePipeline(**pipeline_kwargs)
        self._generated_trace = pipeline.run()

    def _run_raft_trace_validation(self):
        if self.args.validate_only:
            print("Validate-only mode selected; skipping automated trace execution.")
            return

        if not self._generated_trace:
            print("No trace was generated. Cannot proceed with validation.")
            return

        print(f"Trace generated at: {self._generated_trace}")

        # Convert trace to TLA+ format
        converter_script = self.project_root / "demo" / "etcd" / "scripts" / "etcd_trace_converter.py"
        output_trace = Path(self.args.output_dir).resolve() / "trace.ndjson"

        print(f"Converting trace to TLA+ format...")
        subprocess.run(
            [
                "python3",
                str(converter_script),
                str(self._generated_trace),
                str(output_trace),
            ],
            check=True,
        )
        print(f"Converted trace saved to: {output_trace}")

        # Run TLC for final trace validation
        spec_dir = Path(self.args.output_dir).resolve()
        tla_jar = self.project_root / "lib" / "tla2tools.jar"

        # Clear TRACE_PATH and CONFIG_PATH to use default trace.ndjson
        env = os.environ.copy()
        env.pop("TRACE_PATH", None)
        env.pop("CONFIG_PATH", None)

        print(f"Running TLC validation...")
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
        print("Trace validation completed successfully!")

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
    parser.add_argument('--with-exist-specTrace', action='store_true', help='Skip specTrace generation (step4.1), use existing files in output_dir')
    parser.add_argument('--duration', type=int, default=10, help='Trace generation duration in seconds (default: 10)')

    args = parser.parse_args()
    runner = CombinedPhase4(args)
    runner.run()


if __name__ == "__main__":
    main()
