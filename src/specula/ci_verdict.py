"""Compute CI verdicts from current finding dispositions."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from specula import ci_init
from specula.ci_store import CIError, read_json, write_json
from specula.resource_summary import _confirmation_finding_statuses

FILENAME = "ci-verdict.json"
BUG_EXIT_CODE = 2
VERDICTS = {"PASS", "WARNING", "FAIL"}
BUG_STATUSES = {"REPRODUCED", "ENV_LIMITED"}
LIVE_STATUSES = BUG_STATUSES | {"MASKED"}
TERMINAL_STATUSES = LIVE_STATUSES | {"FALSE POSITIVE", "DROPPED", "FIXED"}


def conclusion(findings: list[dict[str, str]]) -> str:
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
        if not isinstance(status, str) or status not in TERMINAL_STATUSES:
            raise CIError(f"{fid}: unresolved or invalid CI finding status: {status}")
        if not isinstance(evidence, str) or not evidence:
            raise CIError(f"{fid}: missing current confirmation evidence")
        path = Path(evidence)
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


def read(work: Path, run_id: str | None = None, *, previous: Path | None = None) -> str:
    record = _read(work, run_id)
    if previous is not None:
        required = {fid for fid, status in prior_findings(previous).items() if status in LIVE_STATUSES}
        current = {finding["id"]: finding["status"] for finding in record["findings"]}
        missing = required - current.keys()
        if missing:
            raise CIError(f"prior findings need current confirmation: {', '.join(sorted(missing))}")
        if any(current[fid] == "DROPPED" for fid in required):
            raise CIError("prior confirmed findings cannot be dropped; record a current confirmation or repair verdict")
    return conclusion(record["findings"])


def from_confirmation(work: Path, run_id: str) -> str:
    """Build the initialization verdict from the canonical confirmation report."""
    if not ci_init._regular_file(work, "confirmed-bugs.md"):
        raise CIError("missing CI initialization confirmation report")
    statuses = _confirmation_finding_statuses((work / "confirmed-bugs.md").read_text(), impact_only=False)
    if statuses is None:
        raise CIError("cannot read CI initialization finding dispositions")
    record = {
        "version": 1,
        "run_id": run_id,
        "findings": [
            {"id": fid, "status": status, "evidence": "confirmed-bugs.md"} for fid, status in statuses.items()
        ],
    }
    write_json(work / FILENAME, record)
    return read(work, run_id)
