"""Render incremental CI deliverables from one final result, using the existing issue store."""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

from specula import ci_init, ci_verdict
from specula import persistent_findings as issues
from specula.ci_store import CIError, read_json, write_json

FILENAME = "spec/final-result.json"
VERSION_KEY = "final_result_version"
REPORTS = ("ci-report.md", "confirmed-bugs.md", "bug-severity.md", ".summary-findings.md")
SEVERITIES = ("Critical", "High", "Medium", "Low")


def enabled(inputs: dict[str, Any]) -> bool:
    if VERSION_KEY not in inputs:
        return False  # Runs created before this format keep their original contract.
    version = inputs[VERSION_KEY]
    if type(version) is not int or version != 1:
        raise CIError("unsupported incremental final-result version")
    return True


def _text(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise CIError(f"final result requires nonempty {field}")
    return " ".join(value.split())


def _evidence(work: Path, value: Any) -> list[str]:
    if not isinstance(value, list) or not value:
        raise CIError("each current finding requires evidence paths")
    result = []
    for item in value:
        if not isinstance(item, str):
            raise CIError("evidence paths must be strings")
        path = Path(item)
        if (
            path.is_absolute()
            or not path.parts
            or ".." in path.parts
            or not (path.parts[0] in ci_init.ASSET_DIRS or (len(path.parts) == 1 and path.suffix == ".md"))
            or path.as_posix() in (*REPORTS, FILENAME, ci_verdict.FILENAME)
            or path.as_posix().startswith((issues.DIRECTORY + "/", issues.RECEIPTS + "/"))
            or not ci_init._regular_file(work, item)
            or not (work / item).read_bytes().strip()
        ):
            raise CIError(f"invalid current confirmation evidence: {item}")
        result.append(path.as_posix())
    return list(dict.fromkeys(result))


def _proposal(work: Path, source: Path, run_id: str, finding: dict[str, Any]) -> dict[str, Any]:
    proposal = {
        key: finding[key] for key in ("id", "title", "status", "source", "cause", "trigger", "consequence", "evidence")
    }
    metadata = finding.get("persistence", {})
    proposal.update(reusable=False, sites=[], actions=[], invariants=[], premises=[], dependencies=[])
    # Missing or invalid reuse metadata costs a future recheck, not this run's result.
    try:
        if not isinstance(metadata, dict):
            raise ValueError("persistence must be an object")
        for key in ("sites", "actions", "invariants", "premises"):
            proposal[key] = issues._strings(metadata.get(key, []), key)
        deps = metadata.get("dependencies", [])
        if not isinstance(deps, list) or any(not isinstance(dep, dict) for dep in deps):
            raise ValueError("dependencies must be selectors")
        for dep in deps:
            issues._dependency_bytes(dep, source, work)
        proposal["dependencies"] = deps
        proposal["reusable"] = bool(
            proposal["premises"]
            and any(dep.get("root") == "source" for dep in deps)
            and (not (proposal["actions"] or proposal["invariants"]) or any(dep.get("root") == "work" for dep in deps))
        )
    except (ValueError, TypeError, OSError):
        proposal.update(reusable=False, sites=[], actions=[], invariants=[], premises=[], dependencies=[])
    if (work / issues._record_path(finding["id"])).exists():
        prior = issues.load(work, finding["id"])
        if prior["origin_run"] != run_id:
            proposal["revises"] = issues.record_digest(work, finding["id"])
    return proposal


def _read(work: Path, source: Path, run_id: str, previous: Path | None) -> dict[str, Any]:
    if not ci_init._regular_file(work, FILENAME):
        raise CIError(f"missing current {FILENAME}")
    document = read_json(work / FILENAME)
    if type(document.get("version")) is not int or document["version"] != 1 or document.get("run_id") != run_id:
        raise CIError("final result must identify version 1 and the current run")
    document["summary"] = _text(document.get("summary"), "summary")
    limits = document.get("validation_limits", [])
    if not isinstance(limits, list):
        raise CIError("validation_limits must be a list")
    document["validation_limits"] = [_text(value, "validation limit") for value in limits]
    findings = document.get("findings")
    if not isinstance(findings, list):
        raise CIError("final result requires a findings list (empty when there are no findings)")
    seen: set[str] = set()
    for finding in findings:
        if not isinstance(finding, dict):
            raise CIError("each finding must be an object")
        fid = finding.get("id")
        if (
            not isinstance(fid, str)
            or re.fullmatch(r"[A-Za-z0-9._-]+", fid) is None
            or fid in {".", ".."}
            or fid in seen
        ):
            raise CIError("finding IDs must be unique and nonempty")
        seen.add(fid)
        if "reuse" in finding:
            reason = _text(finding["reuse"], f"{fid} reuse reason")
            prior = issues.load(work, fid)
            issues._validate_origin(work, prior, run_id, previous)
            invalid = issues.check(work, source, fid)
            if invalid:
                raise CIError(f"{fid}: reanalysis required: {'; '.join(invalid)}")
            # A reuse decision inherits the original conclusion; it is not a fresh confirmation.
            if "status" in finding and finding["status"] != prior["status"]:
                raise CIError(f"{fid}: reuse cannot change the historical status")
            for key in ("title", "status", "source", "cause", "trigger", "consequence"):
                finding[key] = prior[key]
            finding["reuse"] = reason
        else:
            status = finding.get("status")
            if not isinstance(status, str) or status not in ci_verdict.TERMINAL_STATUSES:
                raise CIError(f"{fid}: unresolved or invalid final status: {status}")
            if finding.get("source") not in ("model-checking", "code-review"):
                raise CIError(f"{fid}: source must be model-checking or code-review")
            for key in ("title", "cause", "trigger", "consequence"):
                finding[key] = _text(finding.get(key), f"{fid} {key}")
            if len(finding["title"]) > 160:
                raise CIError(f"{fid}: title must be at most 160 characters")
            finding["evidence"] = _evidence(work, finding.get("evidence"))
        severity = finding.get("severity")
        if severity is not None and severity not in SEVERITIES:
            raise CIError(f"{fid}: invalid severity")
        if finding["status"] not in issues.LIVE:
            finding["severity"] = None

    required = set(issues.index(work))
    if previous is not None:
        required.update(fid for fid, status in ci_verdict.prior_findings(previous).items() if status in issues.LIVE)
    missing = required - seen
    if missing:
        raise CIError(f"prior findings need current confirmation: {', '.join(sorted(missing))}")
    for finding in findings:
        if finding["id"] in required and finding["status"] in {"DROPPED", "NEEDS MORE INFO", "DEFERRED"}:
            raise CIError(
                f"{finding['id']}: prior unresolved defect requires confirmation, reuse, or a supported repair"
            )
    return document


def _reports(document: dict[str, Any]) -> dict[str, str]:
    findings = document["findings"]
    live = [f for f in findings if f["status"] in issues.LIVE]
    counts = {status: sum(f["status"] == status for f in findings) for status in ci_verdict.TERMINAL_STATUSES}
    totals = f"Reproduced bugs: {counts['REPRODUCED']}; other unresolved findings: {len(live) - counts['REPRODUCED']}; other dispositions: {len(findings) - len(live)}."
    limits = document["validation_limits"] or ["No additional validation limits were recorded."]
    confirmed = [
        "# Confirmation Report",
        "",
        totals,
        "",
        "| Entry | Finding | Status | Counts as final bug? |",
        "|---|---|---|---|",
    ]
    for number, finding in enumerate(findings, 1):
        confirmed.append(
            f"| {number} | {finding['id']} | {finding['status']} | {'yes' if finding['status'] == 'REPRODUCED' else 'no'} |"
        )
    confirmed.append("")
    severity = ["# Severity Classification", "", "## Summary", "", f"- Total entries: {len(findings)}"]
    severity.extend(f"- {level}: {sum(f.get('severity') == level for f in findings)}" for level in SEVERITIES)
    severity.extend(
        [
            f"- Unassessed unresolved findings: {sum(not f.get('severity') for f in live)}",
            "",
            "## Per-entry classification",
            "",
            "| Entry | Finding | Status | Severity | Reasoning |",
            "|---|---|---|---|---|",
        ]
    )
    fragment = [totals, "", "## Findings", ""]
    for number, finding in enumerate(findings, 1):
        fid, status = finding["id"], finding["status"]
        kind = "Still unresolved; historical conclusion reused" if "reuse" in finding else "Current confirmation"
        links = ", ".join(f"[evidence {i}](<{path}>)" for i, path in enumerate(finding["evidence"], 1))
        confirmed.extend(
            [
                f"## Entry {number}: {finding['title']}",
                "",
                f"- **Finding ID**: {fid}",
                f"- **Status**: {status}",
                f"- **Source**: {'MC' if finding['source'] == 'model-checking' else 'Code Review'}",
                f"- **Confirmation**: {kind}.",
                f"- **Description**: {finding['cause']}",
                f"- **Trigger scenario**: {finding['trigger']}",
                f"- **Impact**: {finding['consequence']}",
                f"- **Evidence**: {links}",
            ]
        )
        if finding.get("not_reusable"):
            confirmed.append("- **Persistence**: Not automatically reusable; reuse metadata is incomplete or invalid.")
        confirmed.append("")
        impact = finding["consequence"].replace("|", "\\|")
        severity.append(f"| {number} | {fid} | {status} | {finding.get('severity') or '—'} | {impact} |")
        if status in issues.LIVE:
            fragment.append(f"- **{fid} — {finding['title']}** — Status: `{status}`. Impact: {finding['consequence']}.")
    fragment.extend(
        [
            f"- Other dispositions: {len(findings) - len(live)}.",
            "",
            "## Validation limits",
            "",
            *(f"- {limit}" for limit in limits),
        ]
    )
    confirmed.extend(["## Validation limits", "", *(f"- {limit}" for limit in limits)])
    report = [
        "# Incremental CI report",
        "",
        document["summary"],
        "",
        f"CI verdict: **{ci_verdict.conclusion(findings)}**. {totals}",
        "",
        "[Findings and evidence](confirmed-bugs.md) · [Severity](bug-severity.md)",
        "",
        "## Validation limits",
        "",
        *(f"- {limit}" for limit in limits),
    ]
    return dict(
        zip(REPORTS, ("\n".join(lines) + "\n" for lines in (report, confirmed, severity, fragment)), strict=True)
    )


def generate(work: Path, source: Path, run_id: str, previous: Path | None) -> str:
    """Generate and validate the same outputs used by publication; never advance the CI baseline."""
    document = _read(work, source, run_id, previous)
    verdict_findings = []
    for finding in document["findings"]:
        fid = finding["id"]
        if "reuse" in finding:
            receipt = issues.reuse_issue(work, source, run_id, fid, finding["reuse"])
            verdict_findings.append(receipt)
            finding["evidence"] = [receipt["evidence"]]
        else:
            # A changed final decision supersedes an earlier preview's reuse receipt.
            for suffix in (".json", ".md"):
                path = f"{issues.RECEIPTS}/{fid}{suffix}"
                if ci_init._regular_file(work, path):
                    (work / path).unlink()
            if finding["status"] in issues.LIVE:
                proposal = _proposal(work, source, run_id, finding)
                directory = ci_init._directory(work, "spec/issue-input")
                write_json(directory / f"{fid}.json", proposal)
                issues.record_issue(work, source, run_id, proposal)
                finding["not_reusable"] = not proposal["reusable"]
            verdict_findings.append(
                {
                    "id": fid,
                    "status": finding["status"],
                    "evidence": finding["evidence"][0],
                    "source": finding["source"],
                }
            )
    for filename, content in _reports(document).items():
        # Replace the directory entry rather than following an output symlink.
        with tempfile.NamedTemporaryFile(mode="w", dir=work, prefix=".ci-result-", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(content)
        try:
            temporary.replace(work / filename)
        finally:
            temporary.unlink(missing_ok=True)
    write_json(work / ci_verdict.FILENAME, {"version": 1, "run_id": run_id, "findings": verdict_findings})
    return ci_verdict.finalize(work, source, run_id, previous=previous)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="specula ci-result", description="Generate incremental CI reports from spec/final-result.json."
    )
    parser.add_argument("--work", required=True, type=Path, help="the incremental run's .specula-output directory")
    args = parser.parse_args(argv)
    try:
        work = args.work.absolute()
        source, run_id, previous = issues.context(work)
        inputs = read_json(source.parent / "ci-input.json")
        if not enabled(inputs) or "old_model" not in inputs:
            raise CIError("this command is only for incremental runs using the final-result format")
        verdict = generate(work, source, run_id, previous)
        print(f"Generated and validated CI results: {verdict}. The current baseline has not been advanced.")
        return 0  # A valid bug result is not a generation error.
    except (OSError, ValueError, KeyError, CIError) as exc:
        print(f"Cannot generate CI results: {exc}. Correct {FILENAME} and rerun, or resume the run.", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
