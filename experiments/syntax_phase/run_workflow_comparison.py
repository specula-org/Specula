#!/usr/bin/env python3
"""
Basic harness for comparing Specula syntax workflows on benchmark specs.

Example:
    python experiments/syntax_phase/run_workflow_comparison.py \
        --workflows simple agentic --spec-number 1
"""

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Callable, Dict, List, Tuple, Any

# Ensure project root (contains src/) is on the import path
PROJECT_ROOT = Path(__file__).resolve().parents[2]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from src.llm.client import get_llm_client  # noqa: E402


def _load_simple_loop():
    from src.workflows.simple_loop import SimpleLoop

    return SimpleLoop


def _load_agentic_loop():
    from src.workflows.agentic_loop import AgenticLoop

    return AgenticLoop


def _load_agentic_loop_rag():
    from src.workflows.agentic_loop_rag import AgenticLoop_RAG

    return AgenticLoop_RAG


WORKFLOW_REGISTRY: Dict[str, Callable[[], Any]] = {
    "simple": _load_simple_loop,
    "simple_loop": _load_simple_loop,
    "agentic": _load_agentic_loop,
    "agentic_loop": _load_agentic_loop,
    "agentic_rag": _load_agentic_loop_rag,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run selected workflows against benchmark specs and compare accuracy."
    )
    parser.add_argument(
        "--workflows",
        "-w",
        nargs="+",
        required=True,
        help="Workflow names to evaluate (e.g. simple agentic agentic_rag).",
    )
    parser.add_argument(
        "--spec-number",
        "-n",
        required=True,
        help="Spec identifier or number (e.g. 1 or spec_001).",
    )
    parser.add_argument(
        "--dataset-root",
        default=PROJECT_ROOT / "experiments/syntax_phase/dataset",
        type=Path,
        help="Root directory containing benchmark specs.",
    )
    parser.add_argument(
        "--config",
        default=PROJECT_ROOT / "config.yaml",
        type=Path,
        help="Path to Specula configuration file.",
    )
    parser.add_argument(
        "--max-compilations",
        type=int,
        default=3,
        help="Maximum compilations per workflow run.",
    )
    parser.add_argument(
        "--knowledge-base",
        type=Path,
        default=PROJECT_ROOT / "src/rag/initial_errors.json",
        help="Knowledge base path for agentic_rag workflow.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=PROJECT_ROOT / "output/experiments/syntax_phase",
        help="Directory to store run summaries.",
    )
    return parser.parse_args()


def normalize_spec_number(raw_value: str) -> str:
    if raw_value.startswith("spec_"):
        return raw_value
    try:
        number = int(raw_value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            f"Invalid spec number '{raw_value}'. Expected integer or spec_XXX format."
        ) from exc
    return f"spec_{number:03d}"


def resolve_workflows(names: List[str]) -> List[Tuple[str, Any]]:
    resolved = []
    for name in names:
        key = name.lower()
        if key not in WORKFLOW_REGISTRY:
            available = ", ".join(sorted(set(WORKFLOW_REGISTRY.keys())))
            raise ValueError(f"Unknown workflow '{name}'. Available: {available}")
        loader = WORKFLOW_REGISTRY[key]
        try:
            workflow_cls = loader()
        except ModuleNotFoundError as exc:
            raise ImportError(
                f"Workflow '{name}' requires additional dependencies that are missing: {exc}"
            ) from exc
        resolved.append((key, workflow_cls))
    return resolved


def find_spec_files(dataset_root: Path, spec_identifier: str) -> List[Path]:
    pattern = f"**/{spec_identifier}/*.tla"
    return sorted(dataset_root.glob(pattern))


def describe_spec(dataset_root: Path, spec_path: Path) -> Dict[str, str]:
    try:
        parts = spec_path.relative_to(dataset_root).parts
    except ValueError:
        parts = spec_path.parts

    info = {"spec_path": str(spec_path)}

    if len(parts) >= 4:
        info.update(
            {
                "system": parts[0],
                "source": parts[1],
                "spec_id": parts[2],
                "filename": parts[3],
            }
        )
    else:
        info["filename"] = spec_path.name

    return info


def format_result_line(workflow_name: str, result: Dict[str, Any]) -> str:
    status = "✓" if result.get("success") else "✗"
    final_errors = result.get("final_error_count")
    error_note = "" if final_errors in (None, 0) else f" (errors remaining: {final_errors})"
    total_time = result.get("total_time")
    time_note = f", time: {total_time:.2f}s" if isinstance(total_time, (int, float)) else ""
    return f"  - {workflow_name}: {status}{error_note}{time_note}"


def main():
    args = parse_args()

    spec_identifier = normalize_spec_number(args.spec_number)
    dataset_root = args.dataset_root.resolve()

    if not dataset_root.exists():
        print(f"[error] Dataset root not found: {dataset_root}", file=sys.stderr)
        sys.exit(1)

    spec_files = find_spec_files(dataset_root, spec_identifier)
    if not spec_files:
        print(f"[error] No specs found for identifier '{spec_identifier}' under {dataset_root}")
        sys.exit(1)

    try:
        workflows = resolve_workflows(args.workflows)
    except ValueError as exc:
        print(f"[error] {exc}", file=sys.stderr)
        sys.exit(1)

    try:
        llm_client = get_llm_client(str(args.config))
    except Exception as exc:
        print(f"[error] Failed to initialize LLM client: {exc}", file=sys.stderr)
        sys.exit(1)

    run_timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    summary: Dict[str, Dict[str, Any]] = {}
    detailed_results: List[Dict[str, Any]] = []

    header_lines = [
        "=" * 80,
        "Specula Workflow Comparison",
        f"Spec identifier : {spec_identifier}",
        f"Dataset root    : {dataset_root}",
        f"Workflows       : {', '.join(name for name, _ in workflows)}",
        f"Config          : {args.config}",
        f"Specs found     : {len(spec_files)}",
        "=" * 80,
    ]

    report_lines: List[str] = header_lines.copy()

    for workflow_name, _ in workflows:
        summary[workflow_name] = {"total": 0, "success": 0, "failures": []}

    for spec_path in spec_files:
        spec_info = describe_spec(dataset_root, spec_path)
        spec_header = f"\nSpec: {spec_info.get('spec_path')}"
        report_lines.append(spec_header)
        print(spec_header)

        for workflow_name, workflow_cls in workflows:
            summary_entry = summary[workflow_name]
            summary_entry["total"] += 1

            workflow_kwargs = {"llm_client": llm_client, "max_compilations": args.max_compilations}
            if workflow_name == "agentic_rag":
                workflow_kwargs["knowledge_base_path"] = str(args.knowledge_base)

            workflow = workflow_cls(**workflow_kwargs)

            start_time = time.time()
            try:
                result = workflow.fix_spec(str(spec_path))
                elapsed = time.time() - start_time
                result_dict = result.to_dict()
                result_dict["measured_wall_time"] = elapsed
                success = result.success
            except Exception as exc:
                elapsed = time.time() - start_time
                result_dict = {
                    "success": False,
                    "error": str(exc),
                    "total_time": elapsed,
                    "final_error_count": None,
                }
                success = False

            detailed_record = {
                "workflow": workflow_name,
                "spec": spec_info,
                "result": result_dict,
            }
            detailed_results.append(detailed_record)

            if success:
                summary_entry["success"] += 1
            else:
                summary_entry.setdefault("errors", []).append(
                    {"spec": spec_info, "result": result_dict}
                )

            line = format_result_line(workflow_name, result_dict)
            report_lines.append(line)
            print(line)

    # Summary section
    report_lines.append("\nSummary:")
    print("\nSummary:")
    for workflow_name, stats in summary.items():
        total = stats["total"]
        success = stats["success"]
        rate = (success / total) * 100 if total else 0.0
        summary_line = f"  - {workflow_name}: {success}/{total} success ({rate:.1f}%)"
        report_lines.append(summary_line)
        print(summary_line)

    # Persist results
    text_output_path = output_dir / f"workflow_comparison_{run_timestamp}.txt"
    json_output_path = output_dir / f"workflow_comparison_{run_timestamp}.json"

    report_content = "\n".join(report_lines) + "\n"
    text_output_path.write_text(report_content)

    persisted = {
        "timestamp_utc": run_timestamp,
        "spec_identifier": spec_identifier,
        "dataset_root": str(dataset_root),
        "workflows": [name for name, _ in workflows],
        "max_compilations": args.max_compilations,
        "summary": summary,
        "details": detailed_results,
    }

    json_output_path.write_text(json.dumps(persisted, indent=2))

    print(f"\nResults written to {text_output_path} and {json_output_path}")


if __name__ == "__main__":
    main()
