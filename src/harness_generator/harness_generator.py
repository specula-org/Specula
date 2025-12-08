"""
Harness generator workflow using Codex.

Modes:
- draft: generate a harness plan draft and save it.
- full: generate draft, then use it to ask Codex to implement/run harness.
- apply: use an existing draft to ask Codex to implement/run harness.
"""

import argparse
import datetime
import shutil
from pathlib import Path
from typing import Tuple

from src.agent.codex import CodexClient, CodexConfig, PermissionMode

REPO_ROOT = Path(__file__).resolve().parents[2]
PROMPTS_DIR = Path(__file__).resolve().parent.parent / "prompts" / "harness_generator"
OUTPUT_ROOT = REPO_ROOT / "output" / "agent_results"
DRAFT_DIR = OUTPUT_ROOT / "draft"
HARNESS_DIR = OUTPUT_ROOT / "harness"


def _timestamp() -> str:
    return datetime.datetime.now().strftime("%Y%m%d-%H%M%S")


def _timestamped_path(base_dir: Path, prefix: str, stamp: str, suffix: str = ".md") -> Path:
    base_dir.mkdir(parents=True, exist_ok=True)
    return base_dir / f"{prefix}-{stamp}{suffix}"


def _load_prompt(name: str) -> str:
    path = PROMPTS_DIR / name
    return path.read_text(encoding="utf-8")


def _render(template: str, values: dict) -> str:
    rendered = template
    for key, val in values.items():
        rendered = rendered.replace("{" + key + "}", val)
    return rendered


def _run_codex(prompt: str, permission_mode: PermissionMode, codex_bin: str, workdir: Path) -> Tuple[str, int, str]:
    """Run Codex and return stdout, returncode, stderr."""
    client = CodexClient(CodexConfig(codex_binary=codex_bin, workdir=str(workdir)))
    result = client.run(prompt=prompt, permission_mode=permission_mode)
    return result.stdout, result.returncode, result.stderr


def generate_draft(repo_path: Path, permission_mode: PermissionMode, codex_bin: str, workdir: Path) -> Tuple[Path, Path]:
    prompt = _render(_load_prompt("draft_prompt.txt"), {"repo_path": str(repo_path)})
    stdout, returncode, stderr = _run_codex(prompt, permission_mode, codex_bin, workdir)

    stamp = _timestamp()
    draft_path = _timestamped_path(DRAFT_DIR, "harness-draft", stamp)
    meta_path = _timestamped_path(DRAFT_DIR, "harness-draft-meta", stamp)

    # Draft: only Codex stdout
    draft_path.write_text(stdout, encoding="utf-8")

    # Metadata/log: prompt + stderr + return code
    meta_content = [
        "# Harness draft metadata",
        f"Repo: {repo_path}",
        f"Return code: {returncode}",
        "",
        "## Prompt",
        prompt,
    ]
    if stderr:
        meta_content.extend(["", "## Stderr", stderr])
    meta_path.write_text("\n".join(meta_content), encoding="utf-8")
    return draft_path, meta_path


def apply_harness(repo_path: Path, draft_path: Path, permission_mode: PermissionMode, codex_bin: str, workdir: Path) -> Tuple[Path, Path]:
    draft_text = draft_path.read_text(encoding="utf-8")
    prompt = _render(
        _load_prompt("harness_prompt.txt"),
        {"repo_path": str(repo_path), "draft_path": str(draft_path), "draft": draft_text},
    )
    stdout, returncode, stderr = _run_codex(prompt, permission_mode, codex_bin, workdir)

    stamp = _timestamp()
    harness_path = _timestamped_path(HARNESS_DIR, "harness-run", stamp)
    meta_path = _timestamped_path(HARNESS_DIR, "harness-run-meta", stamp)

    # Harness report: Codex stdout only
    harness_path.write_text(stdout, encoding="utf-8")

    # Metadata/log: prompt + stderr + return code
    meta_content = [
        "# Harness run metadata",
        f"Repo: {repo_path}",
        f"Draft: {draft_path}",
        f"Return code: {returncode}",
        "",
        "## Prompt",
        prompt,
    ]
    if stderr:
        meta_content.extend(["", "## Stderr", stderr])
    meta_path.write_text("\n".join(meta_content), encoding="utf-8")
    return harness_path, meta_path


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Harness generator using Codex.")
    parser.add_argument("--mode", choices=["draft", "full", "apply"], required=True, help="draft only, full pipeline, or apply an existing draft")
    parser.add_argument("--repo-path", default=".", help="Path to the repository root for Codex context")
    parser.add_argument("--draft-path", help="Existing draft path (required for mode=apply)")
    parser.add_argument("--codex-bin", default="codex", help="Codex CLI binary name or path")
    parser.add_argument("--permission", choices=["sandbox", "full_access"], default="sandbox", help="Codex permission mode")
    parser.add_argument("--workdir", help="Working directory for Codex (default: repo-path)")
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    repo_path = Path(args.repo_path).resolve()
    workdir = Path(args.workdir).resolve() if args.workdir else repo_path

    if shutil.which(args.codex_bin) is None:
        raise FileNotFoundError(f"Codex binary '{args.codex_bin}' not found in PATH")

    mode: str = args.mode
    permission_mode: PermissionMode = args.permission  # type: ignore[assignment]

    if mode == "draft":
        draft_path, meta_path = generate_draft(repo_path, permission_mode, args.codex_bin, workdir)
        print(f"Draft written to {draft_path}")
        print(f"Draft metadata written to {meta_path}")
        return

    if mode == "apply":
        if not args.draft_path:
            raise ValueError("mode=apply requires --draft-path")
        draft_path = Path(args.draft_path).resolve()
        harness_path, meta_path = apply_harness(repo_path, draft_path, permission_mode, args.codex_bin, workdir)
        print(f"Harness run report written to {harness_path}")
        print(f"Harness metadata written to {meta_path}")
        return

    # mode == "full"
    draft_path, draft_meta = generate_draft(repo_path, permission_mode, args.codex_bin, workdir)
    harness_path, harness_meta = apply_harness(repo_path, draft_path, permission_mode, args.codex_bin, workdir)
    print(f"Draft written to {draft_path}")
    print(f"Draft metadata written to {draft_meta}")
    print(f"Harness run report written to {harness_path}")
    print(f"Harness metadata written to {harness_meta}")


if __name__ == "__main__":
    main()
