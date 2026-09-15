"""Compute CI verdicts from current finding dispositions."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from specula import ci_init, persistent_findings
from specula.ci_store import CIError, read_json, write_json
from specula.resource_summary import _confirmation_finding_statuses

FILENAME = "ci-verdict.json"
BUG_EXIT_CODE = 2
VERDICTS = {"PASS", "WARNING", "FAIL"}
BUG_STATUSES = {"REPRODUCED", "ENV_LIMITED"}
LIVE_STATUSES = BUG_STATUSES | {"MASKED"}
TERMINAL_STATUSES = LIVE_STATUSES | {"FALSE POSITIVE", "DROPPED", "FIXED", "NEEDS MORE INFO", "DEFERRED"}


def conclusion(findings: list[dict[str, Any]]) -> str:
    statuses = {finding["status"] for finding in findings}
    if statuses & BUG_STATUSES:
        return "FAIL"
    return "WARNING" if "MASKED" in statuses else "PASS"


def exit_code(verdict: object) -> int:
    if not isinstance(verdict, str) or verdict not in VERDICTS:
        raise CIError("missing or invalid CI verdict")
    return BUG_EXIT_CODE if verdict == "FAIL" else 0


def _read(work: Path, run_id: str | None = None) -> dict[str, Any]:
    if not ci_init._regular_file(work, FILENAME):
        raise CIError(f"missing current {FILENAME}")
    record = read_json(work / FILENAME)
    if type(record.get("version")) is not int or record["version"] != 1:
        raise CIError("unsupported CI verdict version")
    if not isinstance(record.get("run_id"), str) or not record["run_id"]:
        raise CIError("CI verdict must identify its run")
    if run_id is not None and record["run_id"] != run_id:
        raise CIError("CI verdict belongs to another run")
    findings = record.get("findings")
    if not isinstance(findings, list):
        raise CIError("CI verdict must contain a findings list, including when empty")
    seen: set[str] = set()
    for finding in findings:
        if not isinstance(finding, dict):
            raise CIError("invalid CI finding")
        fid, status, evidence = (finding.get(key) for key in ("id", "status", "evidence"))
        if (
            not isinstance(fid, str)
            or re.fullmatch(r"[A-Za-z0-9._-]+", fid) is None
            or fid in {".", ".."}
            or fid in seen
        ):
            raise CIError("CI finding IDs must be unique and nonempty")
        seen.add(fid)
        if status == "PENDING REPAIR":
            raise CIError(f"{fid}: CI workflow did not converge (PENDING REPAIR)")
        if not isinstance(status, str) or status not in TERMINAL_STATUSES:
            raise CIError(f"{fid}: unresolved or invalid CI finding status: {status}")
        if not isinstance(evidence, str) or not evidence:
            raise CIError(f"{fid}: missing current confirmation evidence")
        path = Path(evidence)
        if "reuse" not in finding and path.as_posix().startswith(
            (persistent_findings.DIRECTORY + "/", persistent_findings.RECEIPTS + "/")
        ):
            raise CIError(f"{fid}: historical evidence requires a checked reuse receipt")
        if (
            path.is_absolute()
            or ".." in path.parts
            or evidence == FILENAME
            or not path.parts
            or not (path.parts[0] in ci_init.ASSET_DIRS or (len(path.parts) == 1 and path.suffix == ".md"))
            or not ci_init._regular_file(work, evidence)
            or not (work / evidence).read_bytes().strip()
        ):
            raise CIError(f"{fid}: confirmation evidence must be a retained, nonempty file inside the work directory")
    return record


def prior_findings(work: Path) -> dict[str, str]:
    """Read prior finding IDs and dispositions for rechecking."""
    if (work / FILENAME).exists() or (work / FILENAME).is_symlink():
        return {finding["id"]: finding["status"] for finding in _read(work)["findings"]}
    if ci_init._regular_file(work, "confirmed-bugs.md"):
        statuses = _confirmation_finding_statuses((work / "confirmed-bugs.md").read_text(), impact_only=False)
        if statuses is not None:
            return statuses
    return {}


def read(work: Path, run_id: str | None = None, *, previous: Path | None = None, source: Path | None = None) -> str:
    record = _read(work, run_id)
    reused = [finding for finding in record["findings"] if "reuse" in finding]
    if reused:
        if source is None:
            source, _, context_previous = persistent_findings.context(work)
            previous = previous or context_previous
        for finding in reused:
            persistent_findings.validate_reuse(work, source, record["run_id"], finding, previous)
    required = set(persistent_findings.index(work))
    if previous is not None:
        required.update(fid for fid, status in prior_findings(previous).items() if status in LIVE_STATUSES)
    if required:
        current = {finding["id"]: finding["status"] for finding in record["findings"]}
        missing = required - current.keys()
        if missing:
            raise CIError(f"prior findings need current confirmation: {', '.join(sorted(missing))}")
        if any(current[fid] == "DROPPED" for fid in required):
            raise CIError("prior confirmed findings cannot be dropped; record a current confirmation or repair verdict")
        if any(current[fid] in {"NEEDS MORE INFO", "DEFERRED"} for fid in required):
            raise CIError("prior unresolved defects require a completed recheck or applicable historical conclusion")
    return conclusion(record["findings"])


def finalize(work: Path, source: Path, run_id: str, *, previous: Path | None = None) -> str:
    """Accept checked reuse receipts, then publish the small active issue set."""
    record = _read(work, run_id)
    persistent_findings.merge_receipts(work, record)
    # Validate before updating the registry or removing any resolved issue.
    for finding in record["findings"]:
        if "reuse" in finding:
            persistent_findings.validate_reuse(work, source, run_id, finding, previous)
    write_json(work / FILENAME, record)
    verdict = read(work, run_id, previous=previous, source=source)
    persistent_findings.reconcile(work, source, run_id, record["findings"])
    if (work / "ci-report.md").is_file():
        _report_reuse(work, record["findings"])
    return verdict


def seed_issues(work: Path, old_source: Path, previous: Path) -> None:
    """Give legacy baselines a small index without claiming they are reusable."""
    if (work / persistent_findings.INDEX).exists():
        return
    if (previous / FILENAME).exists():
        record = _read(previous)
        findings = record["findings"]
        run_id = record["run_id"]
    else:
        findings = [
            {"id": fid, "status": status, "evidence": "confirmed-bugs.md"}
            for fid, status in prior_findings(previous).items()
        ]
        run_id = "legacy"
    persistent_findings.reconcile(work, old_source, run_id, findings)


def from_confirmation(work: Path, run_id: str) -> str:
    """Build the initialization verdict from the canonical confirmation report."""
    if not ci_init._regular_file(work, "confirmed-bugs.md"):
        raise CIError("missing CI initialization confirmation report")
    statuses = _confirmation_finding_statuses((work / "confirmed-bugs.md").read_text(), impact_only=False)
    if statuses is None:
        raise CIError("cannot read CI initialization finding dispositions")
    findings = persistent_findings.confirmation_findings(work, run_id)
    record = {
        "version": 1,
        "run_id": run_id,
        "findings": findings,
    }
    write_json(work / FILENAME, record)
    return read(work, run_id)


def _report_reuse(work: Path, findings: list[dict[str, Any]]) -> None:
    reused = [finding for finding in findings if "reuse" in finding]
    report = work / "ci-report.md"
    start, end = "<!-- issue-reuse:start -->", "<!-- issue-reuse:end -->"
    content = report.read_text()
    content = re.sub(re.escape(start) + r".*?" + re.escape(end) + r"\n?", "", content, flags=re.S)
    if not reused:
        report.write_text(content.rstrip() + "\n")
        return
    rows = "\n".join(
        f"- **{finding['id']}** ({finding['status']}): still unresolved; historical conclusion reused. "
        f"[Evidence and limits]({finding['evidence']})."
        for finding in reused
    )
    report.write_text(content.rstrip() + f"\n\n{start}\n## Reused unresolved findings\n\n{rows}\n{end}\n")
