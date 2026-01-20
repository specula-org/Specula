#!/usr/bin/env python3
"""
TLC Coverage Analysis Tool

Collects and analyzes TLC coverage statistics for TLA+ specifications.
Supports both trace validation and model checking modes.

Coverage Definitions:
- Top-level statements: Only count statements that are not nested (no leading '|')
- All statements: Count all statements including nested sub-expressions

Examples:
    # Trace validation (top-level statements only)
    python tlc_coverage.py trace \\
        --spec-dir ./spec --trace-dir ./traces \\
        --modules etcdraft --exclude-range etcdraft:600-650

    # Trace validation (all statements including nested)
    python tlc_coverage.py trace --spec-dir ./spec --trace-dir ./traces --all

    # Model checking
    python tlc_coverage.py model --spec-dir ./spec \\
        --spec-file MCetcdraft.tla --config-file MCetcdraft.cfg

    # Compare two specs
    python tlc_coverage.py compare \\
        --spec-dir1 ./spec1 --trace-dir1 ./traces1 \\
        --spec-dir2 ./spec2 --trace-dir2 ./traces2
"""

import argparse
import subprocess
import re
import os
import sys
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Optional, Set, Dict, List, Tuple

# Default paths (relative to script location)
SCRIPT_DIR = Path(__file__).parent
DEFAULT_TLA_JAR = SCRIPT_DIR.parent / "lib" / "tla2tools.jar"

# Regex to parse TLC coverage output
COVERAGE_PATTERN = re.compile(
    r"line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+): (\d+)"
)


@dataclass
class CoverageResult:
    """Results of coverage analysis."""
    total: int = 0
    covered: int = 0
    uncovered_lines: Dict[str, Set[int]] = field(default_factory=lambda: defaultdict(set))

    @property
    def pct(self) -> float:
        return self.covered / self.total * 100 if self.total > 0 else 0.0

    @property
    def uncovered(self) -> int:
        return self.total - self.covered


def parse_exclude_range(spec: str) -> Tuple[str, int, int]:
    """Parse 'module:start-end' format."""
    if ':' not in spec:
        raise ValueError(f"Invalid format: {spec}. Expected 'module:start-end'")
    module, range_str = spec.split(':', 1)
    if '-' not in range_str:
        raise ValueError(f"Invalid range: {range_str}. Expected 'start-end'")
    start, end = range_str.split('-', 1)
    return module, int(start), int(end)


def run_tlc(spec_dir: Path, spec_file: str, config_file: str,
            tla_jar: Path, trace_file: Optional[Path] = None,
            timeout: int = 300) -> str:
    """Run TLC with coverage enabled."""
    env = os.environ.copy()
    if trace_file:
        env["JSON"] = str(trace_file)

    cmd = [
        "java", "-jar", str(tla_jar),
        "-coverage", "0",
        "-config", config_file,
        spec_file
    ]

    result = subprocess.run(
        cmd, cwd=spec_dir, env=env,
        capture_output=True, text=True, timeout=timeout
    )
    return result.stdout + result.stderr


def parse_coverage(output: str, modules: Set[str], exclude_ranges: Dict[str, List[Tuple[int, int]]],
                   top_level_only: bool = True) -> Dict[Tuple, int]:
    """Parse TLC coverage output."""
    coverage = {}

    for line in output.split("\n"):
        is_nested = line.lstrip().startswith("|")
        if top_level_only and is_nested:
            continue

        clean_line = line.lstrip(" |")
        match = COVERAGE_PATTERN.search(clean_line)
        if not match:
            continue

        line_start = int(match.group(1))
        col_start = int(match.group(2))
        line_end = int(match.group(3))
        col_end = int(match.group(4))
        module = match.group(5)
        count = int(match.group(6))

        # Filter by modules
        if modules and module not in modules:
            continue

        # Skip excluded ranges
        if module in exclude_ranges:
            skip = any(start <= line_start <= end for start, end in exclude_ranges[module])
            if skip:
                continue

        key = (module, line_start, col_start, line_end, col_end)
        coverage[key] = max(coverage.get(key, 0), count)

    return coverage


def analyze_traces(spec_dir: Path, trace_dir: Path, spec_file: str, config_file: str,
                   tla_jar: Path, modules: Set[str], exclude_ranges: Dict[str, List[Tuple[int, int]]],
                   top_level_only: bool, timeout: int, verbose: bool) -> CoverageResult:
    """Analyze coverage across multiple trace files."""
    trace_files = sorted(trace_dir.glob("*.ndjson"))
    if verbose:
        print(f"Found {len(trace_files)} trace files\n")

    all_stmts: Dict[Tuple, int] = {}

    for i, tf in enumerate(trace_files, 1):
        if verbose:
            print(f"[{i:2d}/{len(trace_files)}] {tf.name}...", end=" ", flush=True)
        try:
            output = run_tlc(spec_dir, spec_file, config_file, tla_jar, tf, timeout)
            if "Model checking completed" not in output and "states generated" not in output:
                if verbose:
                    print("FAILED")
                continue

            cov = parse_coverage(output, modules, exclude_ranges, top_level_only)
            for key, count in cov.items():
                all_stmts[key] = max(all_stmts.get(key, 0), count)

            if verbose:
                c = sum(1 for v in cov.values() if v > 0)
                print(f"OK ({c}/{len(cov)} = {c/len(cov)*100:.1f}%)" if cov else "OK (empty)")

        except subprocess.TimeoutExpired:
            if verbose:
                print("TIMEOUT")
        except Exception as e:
            if verbose:
                print(f"ERROR: {e}")

    return build_result(all_stmts)


def analyze_model(spec_dir: Path, spec_file: str, config_file: str, tla_jar: Path,
                  modules: Set[str], exclude_ranges: Dict[str, List[Tuple[int, int]]],
                  top_level_only: bool, timeout: int) -> CoverageResult:
    """Analyze coverage from model checking."""
    output = run_tlc(spec_dir, spec_file, config_file, tla_jar, timeout=timeout)
    cov = parse_coverage(output, modules, exclude_ranges, top_level_only)
    return build_result(cov)


def build_result(stmts: Dict[Tuple, int]) -> CoverageResult:
    """Build CoverageResult from statements dict."""
    result = CoverageResult()
    result.total = len(stmts)
    result.covered = sum(1 for c in stmts.values() if c > 0)
    for key, count in stmts.items():
        if count == 0:
            result.uncovered_lines[key[0]].add(key[1])
    return result


def print_result(result: CoverageResult, title: str):
    """Print coverage result."""
    print(f"\n{'=' * 70}")
    print(title)
    print('=' * 70)
    print(f"Total statements:     {result.total}")
    print(f"Covered statements:   {result.covered}")
    print(f"Uncovered statements: {result.uncovered}")
    print(f"\nCOVERAGE: {result.pct:.2f}%")

    if result.uncovered_lines:
        print(f"\n{'-' * 70}")
        print("UNCOVERED LINES BY MODULE")
        print('-' * 70)
        for module in sorted(result.uncovered_lines.keys()):
            lines = sorted(result.uncovered_lines[module])
            print(f"\n{module}.tla ({len(lines)} lines):")
            print(f"  {lines}")


def print_comparison(r1: CoverageResult, r2: CoverageResult, n1: str, n2: str):
    """Print comparison of two results."""
    print(f"\n{'=' * 70}")
    print("COVERAGE COMPARISON")
    print('=' * 70)
    print(f"{'Metric':<25} {n1:>20} {n2:>20}")
    print('-' * 70)
    print(f"{'Total statements':<25} {r1.total:>20} {r2.total:>20}")
    print(f"{'Covered statements':<25} {r1.covered:>20} {r2.covered:>20}")
    print(f"{'Uncovered statements':<25} {r1.uncovered:>20} {r2.uncovered:>20}")
    print(f"{'Coverage %':<25} {r1.pct:>19.2f}% {r2.pct:>19.2f}%")
    print('-' * 70)
    print(f"{'Difference':<25} {'':<20} {r2.pct - r1.pct:>+19.2f}%")


def main():
    parser = argparse.ArgumentParser(description="TLC Coverage Analysis Tool",
                                     formatter_class=argparse.RawDescriptionHelpFormatter,
                                     epilog=__doc__)
    parser.add_argument("--tla-jar", default=str(DEFAULT_TLA_JAR), help="Path to tla2tools.jar")
    parser.add_argument("--timeout", type=int, default=300, help="TLC timeout in seconds")

    sub = parser.add_subparsers(dest="cmd", required=True)

    # Trace mode
    p_trace = sub.add_parser("trace", help="Trace validation coverage")
    p_trace.add_argument("--spec-dir", required=True, help="Spec directory")
    p_trace.add_argument("--trace-dir", required=True, help="Traces directory")
    p_trace.add_argument("--spec-file", default="Traceetcdraft.tla")
    p_trace.add_argument("--config-file", default="Traceetcdraft.cfg")
    p_trace.add_argument("--modules", nargs="+", default=[], help="Modules to include")
    p_trace.add_argument("--exclude-range", nargs="*", default=[],
                         help="Exclude ranges: module:start-end (e.g., etcdraft:600-650)")
    p_trace.add_argument("--all", action="store_true", help="Include nested statements")
    p_trace.add_argument("--quiet", action="store_true")

    # Model mode
    p_model = sub.add_parser("model", help="Model checking coverage")
    p_model.add_argument("--spec-dir", required=True)
    p_model.add_argument("--spec-file", default="MCetcdraft.tla")
    p_model.add_argument("--config-file", default="MCetcdraft.cfg")
    p_model.add_argument("--modules", nargs="+", default=[])
    p_model.add_argument("--exclude-range", nargs="*", default=[])
    p_model.add_argument("--all", action="store_true")

    # Compare mode
    p_cmp = sub.add_parser("compare", help="Compare two specs")
    p_cmp.add_argument("--spec-dir1", required=True)
    p_cmp.add_argument("--spec-dir2", required=True)
    p_cmp.add_argument("--trace-dir1", help="Trace dir for spec1 (omit for model checking)")
    p_cmp.add_argument("--trace-dir2", help="Trace dir for spec2 (omit for model checking)")
    p_cmp.add_argument("--spec-file1", default="Traceetcdraft.tla")
    p_cmp.add_argument("--spec-file2", default="Traceetcdraft.tla")
    p_cmp.add_argument("--config-file1", default="Traceetcdraft.cfg")
    p_cmp.add_argument("--config-file2", default="Traceetcdraft.cfg")
    p_cmp.add_argument("--modules1", nargs="+", default=[])
    p_cmp.add_argument("--modules2", nargs="+", default=[])
    p_cmp.add_argument("--exclude-range1", nargs="*", default=[])
    p_cmp.add_argument("--exclude-range2", nargs="*", default=[])
    p_cmp.add_argument("--all", action="store_true")

    args = parser.parse_args()
    tla_jar = Path(args.tla_jar)

    if args.cmd == "trace":
        exclude = defaultdict(list)
        for spec in args.exclude_range:
            m, s, e = parse_exclude_range(spec)
            exclude[m].append((s, e))

        result = analyze_traces(
            Path(args.spec_dir), Path(args.trace_dir),
            args.spec_file, args.config_file, tla_jar,
            set(args.modules), dict(exclude),
            not args.all, args.timeout, not args.quiet
        )
        print_result(result, "TRACE VALIDATION COVERAGE")

    elif args.cmd == "model":
        exclude = defaultdict(list)
        for spec in args.exclude_range:
            m, s, e = parse_exclude_range(spec)
            exclude[m].append((s, e))

        result = analyze_model(
            Path(args.spec_dir), args.spec_file, args.config_file, tla_jar,
            set(args.modules), dict(exclude), not args.all, args.timeout
        )
        print_result(result, "MODEL CHECKING COVERAGE")

    elif args.cmd == "compare":
        exc1 = defaultdict(list)
        for spec in args.exclude_range1:
            m, s, e = parse_exclude_range(spec)
            exc1[m].append((s, e))

        exc2 = defaultdict(list)
        for spec in args.exclude_range2:
            m, s, e = parse_exclude_range(spec)
            exc2[m].append((s, e))

        top_level = not args.all

        if args.trace_dir1:
            r1 = analyze_traces(Path(args.spec_dir1), Path(args.trace_dir1),
                                args.spec_file1, args.config_file1, tla_jar,
                                set(args.modules1), dict(exc1), top_level, args.timeout, True)
        else:
            r1 = analyze_model(Path(args.spec_dir1), args.spec_file1, args.config_file1,
                               tla_jar, set(args.modules1), dict(exc1), top_level, args.timeout)

        if args.trace_dir2:
            r2 = analyze_traces(Path(args.spec_dir2), Path(args.trace_dir2),
                                args.spec_file2, args.config_file2, tla_jar,
                                set(args.modules2), dict(exc2), top_level, args.timeout, True)
        else:
            r2 = analyze_model(Path(args.spec_dir2), args.spec_file2, args.config_file2,
                               tla_jar, set(args.modules2), dict(exc2), top_level, args.timeout)

        print_comparison(r1, r2, Path(args.spec_dir1).name, Path(args.spec_dir2).name)


if __name__ == "__main__":
    main()
