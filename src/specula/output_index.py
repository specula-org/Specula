"""Deterministic, human-readable navigation for Specula run outputs.

The indexes are derived views only: pipeline, repair, resume, and confirmation
never consume them. The renderer is limited to fixed files and shallow
directory scans; it never walks runtime trees recursively.
"""

from __future__ import annotations

import html
import os
import secrets
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import quote_from_bytes

INDEX_FILENAME = "index.md"
PIPELINE_LOG_ENV = "SPECULA_PIPELINE_LOG"
_NOT_AVAILABLE = "Not available"


@dataclass(frozen=True)
class TargetOutput:
    """One target row in a run index."""

    name: str
    work_dir: Path
    output_root: Path


def is_safe_target_name(name: str) -> bool:
    """Whether name can be used as one output-layout path component."""
    try:
        os.fsencode(name)
    except UnicodeError:
        return False
    candidate = Path(name)
    return (
        bool(name.strip())
        and name not in (".", "..")
        and not candidate.is_absolute()
        and candidate.parts == (name,)
        and not any(ord(character) < 32 for character in name)
    )


def _is_file(path: Path) -> bool:
    try:
        return not path.is_symlink() and path.is_file()
    except (OSError, UnicodeError):
        return False


def _is_file_under(root: Path, path: Path) -> bool:
    """Accept a file only when every component below root is non-symlink."""
    try:
        relative = path.relative_to(root)
    except ValueError:
        return False
    current = root
    try:
        if current.is_symlink():
            return False
        for part in relative.parts:
            current /= part
            if current.is_symlink():
                return False
        return current.is_file()
    except (OSError, UnicodeError):
        return False


def _is_dir_under(root: Path, path: Path) -> bool:
    """Accept a directory only when every component below root is non-symlink."""
    try:
        relative = path.relative_to(root)
    except ValueError:
        return False
    current = root
    try:
        if current.is_symlink():
            return False
        for part in relative.parts:
            current /= part
            if current.is_symlink():
                return False
        return current.is_dir()
    except (OSError, UnicodeError):
        return False


def _path_below_root_is_symlink_free(root: Path, path: Path) -> bool:
    """Lexically confine path to root and reject symlinks below that root."""
    normalized_root = Path(os.path.abspath(root))
    normalized_path = Path(os.path.abspath(path))
    try:
        relative = normalized_path.relative_to(normalized_root)
    except ValueError:
        return False
    current = normalized_root
    try:
        for part in relative.parts:
            current /= part
            if current.is_symlink():
                return False
    except (OSError, UnicodeError):
        return False
    return True


def _markdown_text(value: str) -> str:
    """One safe Markdown table/heading fragment."""
    one_line = " ".join(value.splitlines()).strip()
    one_line = one_line.encode("utf-8", errors="replace").decode("utf-8")
    escaped = html.escape(one_line, quote=False)
    return escaped.replace("\\", "\\\\").replace("|", "\\|").replace("[", "\\[").replace("]", "\\]")


def _relative_url(base: Path, target: Path) -> str:
    relative = os.path.relpath(target, start=base).replace(os.sep, "/")
    return quote_from_bytes(os.fsencode(relative), safe="/._~-")


def _link(label: str, target: Path, base: Path) -> str:
    return f"[{_markdown_text(label)}]({_relative_url(base, target)})"


def _document(label: str, target: Path, base: Path) -> str:
    if _is_file_under(base, target):
        return _link(label, target, base)
    return f"{_markdown_text(label)}: {_NOT_AVAILABLE}"


def _reproduction_files(work_dir: Path, finding_id: str) -> list[Path]:
    repro_dir = work_dir / "repro"
    if not _is_dir_under(work_dir, repro_dir):
        return []
    prefix = f"test_bug{finding_id}_"
    try:
        entries = sorted(repro_dir.iterdir(), key=lambda path: path.name)
    except OSError:
        return []
    return [path for path in entries if path.name.startswith(prefix) and _is_file_under(work_dir, path)]


def _confirmation_rows(work_dir: Path) -> list[str]:
    confirmation_dir = work_dir / "confirmation"
    if not _is_dir_under(work_dir, confirmation_dir):
        return []
    try:
        finding_dirs = sorted(confirmation_dir.iterdir(), key=lambda path: path.name)
    except OSError:
        return []

    rows: list[str] = []
    for finding_dir in finding_dirs:
        if finding_dir.name.startswith(".") or not _is_dir_under(work_dir, finding_dir):
            continue
        investigation = finding_dir / "investigation.md"
        debate = finding_dir / "debate.md"
        reproductions = _reproduction_files(work_dir, finding_dir.name)
        if not _is_file_under(work_dir, investigation) and not _is_file_under(work_dir, debate) and not reproductions:
            continue

        investigation_cell = (
            _link("Read", investigation, work_dir) if _is_file_under(work_dir, investigation) else _NOT_AVAILABLE
        )
        debate_cell = _link("Read", debate, work_dir) if _is_file_under(work_dir, debate) else _NOT_AVAILABLE
        reproduction_cell = (
            " · ".join(_link(path.name, path, work_dir) for path in reproductions) if reproductions else _NOT_AVAILABLE
        )
        rows.append(
            f"| {_markdown_text(finding_dir.name)} | {investigation_cell} | {debate_cell} | {reproduction_cell} |"
        )
    return rows


def render_target_index(name: str, work_dir: Path, *, pipeline_log: Path | None = None) -> str:
    """Render the approved human-facing target navigation."""
    spec_dir = work_dir / "spec"
    lines = [
        f"# {_markdown_text(name)} Results",
        "",
        "## Final Reports",
        "",
        (
            f"- {_document('Confirmation report', work_dir / 'confirmed-bugs.md', work_dir)} "
            "— Confirmation results and supporting evidence"
        ),
        (f"- {_document('Severity report', work_dir / 'bug-severity.md', work_dir)} — Impact assessment"),
        "",
        "> Availability means that a document exists. It does not imply review approval",
        "> or confirmation of every finding.",
        "",
        "## Supporting Analysis",
        "",
        "| Step | Document | What it contains |",
        "|---:|---|---|",
        (
            f"| 1 | {_document('Modeling brief', work_dir / 'modeling-brief.md', work_dir)} "
            "| System model, bug families, and proposed invariants |"
        ),
        (
            f"| 2 | {_document('Analysis report', work_dir / 'analysis-report.md', work_dir)} "
            "| Detailed source-code investigation |"
        ),
        (
            f"| 3 | {_document('Spec coverage', spec_dir / 'brief-coverage.md', work_dir)} · "
            f"{_document('Instrumentation map', spec_dir / 'instrumentation-spec.md', work_dir)} "
            "| How the analysis was translated into the model |"
        ),
        (
            f"| 4 | {_document('Validation changelog', spec_dir / 'changelog.md', work_dir)} "
            "| Model corrections and validation history |"
        ),
        (
            f"| 5 | {_document('Model-checking report', spec_dir / 'bug-report.md', work_dir)} "
            "| Candidate findings from model checking |"
        ),
    ]

    confirmation_rows = _confirmation_rows(work_dir)
    if confirmation_rows:
        lines += [
            "",
            "## Confirmation Details",
            "",
            "| Finding | Investigation | Discussion | Reproduction |",
            "|---|---|---|---|",
            *confirmation_rows,
        ]

    technical: list[str] = []
    models = [
        _link(path.name, path, work_dir)
        for path in (spec_dir / "base.tla", spec_dir / "MC.tla", spec_dir / "Trace.tla")
        if _is_file_under(work_dir, path)
    ]
    if models:
        technical.append(f"- TLA+ models: {' · '.join(models)}")
    harness_guide = work_dir / "harness" / "INSTRUMENTATION.md"
    if _is_file_under(work_dir, harness_guide):
        technical.append(f"- Harness guide: {_link('INSTRUMENTATION.md', harness_guide, work_dir)}")
    repair_ledger = spec_dir / "repair-ledger.md"
    if _is_file_under(work_dir, repair_ledger):
        technical.append(f"- Repair history: {_link('repair-ledger.md', repair_ledger, work_dir)}")
    if technical:
        lines += ["", "## Technical Details", "", *technical]

    if pipeline_log is not None and _is_file(pipeline_log):
        lines += [
            "",
            "## Troubleshooting",
            "",
            f"- Full pipeline log: {_link('pipeline.log', pipeline_log, work_dir)}",
        ]

    return "\n".join(lines) + "\n"


def render_run_index(
    run_root: Path,
    targets: list[TargetOutput],
    *,
    summary: Path,
    pipeline_log: Path,
) -> str:
    """Render the intentionally minimal run-level target chooser."""
    lines = [
        "# Specula Run",
        "",
        "Select a target to browse its results or open its final reports directly.",
        "",
        "## Targets",
        "",
        "| Target | Results | Confirmation | Severity |",
        "|---|---|---|---|",
    ]
    for target in targets:
        target_index = target.work_dir / INDEX_FILENAME
        result = (
            _link("Open results", target_index, run_root)
            if _path_below_root_is_symlink_free(target.output_root, target_index) and _is_file(target_index)
            else _NOT_AVAILABLE
        )
        confirmation_report = target.work_dir / "confirmed-bugs.md"
        confirmation = (
            _link("Open report", confirmation_report, run_root)
            if _path_below_root_is_symlink_free(target.output_root, confirmation_report)
            and _is_file(confirmation_report)
            else _NOT_AVAILABLE
        )
        severity_report = target.work_dir / "bug-severity.md"
        severity = (
            _link("Open report", severity_report, run_root)
            if _path_below_root_is_symlink_free(target.output_root, severity_report) and _is_file(severity_report)
            else _NOT_AVAILABLE
        )
        lines.append(f"| {_markdown_text(target.name)} | {result} | {confirmation} | {severity} |")

    summary_cell = (
        _link("pipeline-summary.md", summary, run_root) if _is_file_under(run_root, summary) else _NOT_AVAILABLE
    )
    log_cell = (
        _link("pipeline.log", pipeline_log, run_root) if _is_file_under(run_root, pipeline_log) else _NOT_AVAILABLE
    )
    lines += [
        "",
        "## Run Status",
        "",
        f"- Final summary: {summary_cell}",
        f"- Full pipeline log: {log_cell}",
    ]
    return "\n".join(lines) + "\n"


def _atomic_write_if_changed(path: Path, content: str) -> bool:
    """Publish a complete index, preserving the previous file on failure."""
    parent = path.parent
    parent.mkdir(parents=True, exist_ok=True)
    if parent.is_symlink() or not parent.is_dir():
        raise OSError(f"index parent is not a safe directory: {parent}")

    if _is_file(path):
        try:
            if path.read_text(encoding="utf-8") == content:
                return False
        except (OSError, UnicodeError):
            pass

    temporary = parent / f".{path.name}.{os.getpid()}.{secrets.token_hex(8)}.tmp"
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o666)
    try:
        handle = os.fdopen(fd, "w", encoding="utf-8")
    except BaseException:
        os.close(fd)
        temporary.unlink(missing_ok=True)
        raise
    try:
        with handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)
    return True


def write_target_index(
    name: str,
    work_dir: Path,
    *,
    output_root: Path,
    pipeline_log: Path | None = None,
) -> bool:
    """Create or refresh one target index. Returns whether bytes changed."""
    if not _path_below_root_is_symlink_free(output_root, work_dir):
        raise OSError(f"target output escapes its layout root or crosses a symlink: {work_dir}")
    if work_dir.exists() and (work_dir.is_symlink() or not work_dir.is_dir()):
        raise OSError(f"target output is not a safe directory: {work_dir}")
    content = render_target_index(name, work_dir, pipeline_log=pipeline_log)
    return _atomic_write_if_changed(work_dir / INDEX_FILENAME, content)


def write_run_index(
    run_root: Path,
    targets: list[TargetOutput],
    *,
    summary: Path,
    pipeline_log: Path,
) -> bool:
    """Create or refresh the run-level target chooser."""
    if run_root.exists() and (run_root.is_symlink() or not run_root.is_dir()):
        raise OSError(f"run output is not a safe directory: {run_root}")
    content = render_run_index(run_root, targets, summary=summary, pipeline_log=pipeline_log)
    return _atomic_write_if_changed(run_root / INDEX_FILENAME, content)
