"""Confirm Phase 1 Scenarios before modeling (``specula run --confirm-first``).

``only`` confirms the Scenario candidates and stops. ``continue`` confirms them,
seals the results under ``confirm-first/``, runs the model phases unchanged, and
then confirms only the model-checking findings that do not repeat an earlier
confirmed defect, together with any Scenario candidate whose confirmation could
not finish. This module owns the sealed record and the candidate merge;
confirmation itself stays in confirmlib.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Any

MODES = ("only", "continue")
DIRECTORY = "confirm-first"
STATE = f"{DIRECTORY}/state.json"
CANDIDATES = f"{DIRECTORY}/candidates.json"
REPORT = f"{DIRECTORY}/confirmed-bugs.md"
# Raw output of the model-checking consolidation, before the dispatcher merges
# the sealed Scenario candidates into spec/candidates.json.
MODEL_CANDIDATES = "spec/model-candidates.json"
MATCH_KEY = "confirm_first_match"
DOC_KEY = "confirm_first"
# Earlier verdicts that already establish a real defect. A model-checking
# finding that repeats one reuses it; any other earlier verdict is confirmed
# again with the counterexample.
REUSED = frozenset({"REPRODUCED", "ENV_LIMITED", "MASKED"})
# A candidate whose confirmation could not finish (for example, a provider kept
# refusing the turn). It is sealed without a verdict and confirmed again after
# modeling instead of holding the model phases back.
INCOMPLETE = "INCOMPLETE"
_INCOMPLETE_ROW = re.compile(r"^\|\s*\d+\s*\|\s*(\S+?)\s*\|\s*INCOMPLETE\s*\|", re.MULTILINE)

_VERSION = 1
_STAGING = ".confirm-first.tmp"
# (work-relative source, name inside the sealed directory)
_MOVED = (
    ("spec/candidates.json", "candidates.json"),
    ("confirmed-bugs.md", "confirmed-bugs.md"),
    ("spec/.candidates-cache.json", ".candidates-cache.json"),
)


class SealError(RuntimeError):
    """The sealed Scenario results are missing, incomplete, or changed."""


@dataclass(frozen=True)
class Sealed:
    candidates: list[dict[str, Any]]
    statuses: dict[str, str]
    brief_sha256: str

    @property
    def ids(self) -> list[str]:
        return [str(candidate["id"]) for candidate in self.candidates]

    @property
    def incomplete(self) -> list[str]:
        return [fid for fid in self.ids if self.statuses.get(fid) == INCOMPLETE]


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _regular(path: Path) -> bool:
    return path.is_file() and not path.is_symlink()


def _brief_digest(work: Path) -> str:
    brief = work / "modeling-brief.md"
    return _sha(brief) if _regular(brief) else ""


def _read_findings(path: Path) -> list[dict[str, Any]]:
    try:
        doc = json.loads(path.read_text())
    except (OSError, UnicodeError, ValueError) as exc:
        raise SealError(f"cannot read {path}: {exc}") from exc
    findings = doc.get("findings") if isinstance(doc, dict) else None
    if not isinstance(findings, list) or not all(
        isinstance(item, dict) and isinstance(item.get("id"), str) for item in findings
    ):
        raise SealError(f"{path} has no valid findings list")
    return findings


def _remove(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.exists():
        shutil.rmtree(path)


def sealed_exists(work: Path) -> bool:
    return (work / DIRECTORY).exists() or (work / DIRECTORY).is_symlink()


def interrupted(work: Path) -> bool:
    """A seal started but did not finish; :func:`seal` completes it."""
    return (work / _STAGING).exists() or (work / _STAGING).is_symlink()


def seal(work: Path) -> Sealed:
    """Move the Scenario confirmation results out of the model phases' way.

    Per-finding evidence stays under ``confirmation/`` and ``repro/``; the
    record binds each verdict by digest. Moves go through a staging directory
    renamed into place last, so an interrupted seal is completed, not repeated.
    """
    if sealed_exists(work):
        return load(work)
    staging = work / _STAGING
    if staging.is_symlink() or (staging.exists() and not staging.is_dir()):
        raise SealError(f"unsafe staging path: {staging}")

    def current(source: str, name: str) -> Path:
        original = work / source
        if original.is_symlink():
            raise SealError(f"refusing to seal a symlink: {original}")
        return original if original.exists() else staging / name

    # Validate before moving anything: a failed seal must leave the Scenario
    # confirmation outputs where a rerun of that confirmation expects them.
    candidates, report = (current(source, name) for source, name in _MOVED[:2])
    for path in (candidates, report):
        if not _regular(path):
            raise SealError(f"Scenario confirmation did not produce {path.name}")
    verdicts: dict[str, dict[str, str]] = {}
    try:
        incomplete = set(_INCOMPLETE_ROW.findall(report.read_text()))
    except (OSError, UnicodeError) as exc:
        raise SealError(f"cannot read {report}: {exc}") from exc
    for finding in _read_findings(candidates):
        fid = finding["id"]
        verdict = work / "confirmation" / fid / "verdict.json"
        if fid in incomplete:
            verdicts[fid] = {"status": INCOMPLETE}
            continue
        if not _regular(verdict):
            raise SealError(f"{fid} has no final verdict; resume the Scenario confirmation")
        try:
            status = json.loads(verdict.read_text()).get("status")
        except (OSError, UnicodeError, ValueError, AttributeError) as exc:
            raise SealError(f"{fid}: unreadable verdict: {exc}") from exc
        if not isinstance(status, str) or not status:
            raise SealError(f"{fid}: verdict has no status")
        verdicts[fid] = {"status": status, "sha256": _sha(verdict)}
    staging.mkdir(exist_ok=True)
    for source, name in _MOVED:
        original = work / source
        if original.exists() and not original.is_symlink():
            os.replace(original, staging / name)
    candidates = staging / "candidates.json"
    report = staging / "confirmed-bugs.md"
    log = work / "bug-confirmation.log"
    if _regular(log):
        shutil.copy2(log, staging / "bug-confirmation.log")
    state = {
        "version": _VERSION,
        "brief_sha256": _brief_digest(work),
        "candidates_sha256": _sha(candidates),
        "report_sha256": _sha(report),
        "verdicts": verdicts,
    }
    tmp = staging / "state.json.tmp"
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")
    tmp.replace(staging / "state.json")
    os.replace(staging, work / DIRECTORY)
    return load(work)


def load(work: Path) -> Sealed:
    """Return the sealed results after checking every bound file."""
    state_path = work / STATE
    if not _regular(state_path) or (work / DIRECTORY).is_symlink():
        raise SealError(f"no sealed Scenario confirmation at {work / DIRECTORY}")
    try:
        state = json.loads(state_path.read_text())
    except (OSError, UnicodeError, ValueError) as exc:
        raise SealError(f"cannot read {state_path}: {exc}") from exc
    verdicts = state.get("verdicts") if isinstance(state, dict) else None
    if state.get("version") != _VERSION or not isinstance(verdicts, dict):
        raise SealError(f"unsupported Scenario confirmation record: {state_path}")
    for relative, key in ((CANDIDATES, "candidates_sha256"), (REPORT, "report_sha256")):
        path = work / relative
        if not _regular(path) or _sha(path) != state.get(key):
            raise SealError(f"{path} changed after the Scenario confirmation was sealed")
    candidates = _read_findings(work / CANDIDATES)
    statuses: dict[str, str] = {}
    for candidate in candidates:
        fid = candidate["id"]
        entry = verdicts.get(fid)
        if isinstance(entry, dict) and entry.get("status") == INCOMPLETE:
            # No verdict was bound; the late confirmation may write one.
            statuses[fid] = INCOMPLETE
            continue
        verdict = work / "confirmation" / fid / "verdict.json"
        if not isinstance(entry, dict) or not _regular(verdict) or _sha(verdict) != entry.get("sha256"):
            raise SealError(f"{fid}: verdict changed after the Scenario confirmation was sealed")
        statuses[fid] = str(entry["status"])
    brief = state.get("brief_sha256")
    return Sealed(candidates, statuses, brief if isinstance(brief, str) else "")


def has_current_seal(work: Path) -> bool:
    """Whether a finished, valid seal exists for the current modeling brief."""
    if interrupted(work) or not sealed_exists(work):
        return False
    return load(work).brief_sha256 == _brief_digest(work)


def is_current(work: Path) -> bool:
    """Like :func:`has_current_seal`, after completing an interrupted seal."""
    if interrupted(work):
        seal(work)
    return has_current_seal(work)


def discard(work: Path) -> None:
    """Drop a seal made for an earlier modeling brief."""
    _remove(work / DIRECTORY)


def merge(model_findings: list[Any], sealed: Sealed) -> tuple[dict[str, Any], list[str]]:
    """Build the Phase-4 candidate list from model checking and the seal.

    A model-checking finding that repeats an earlier defect with a reused
    verdict moves to ``covered`` and is not confirmed again. The others are
    confirmed normally, followed by the sealed Scenario candidates, whose
    verdicts are carried. Returns the document and warnings for ignored input.
    """
    early = set(sealed.ids)
    kept: list[dict[str, Any]] = []
    covered: list[dict[str, Any]] = []
    warnings: list[str] = []
    for index, item in enumerate(model_findings):
        if not isinstance(item, dict):
            warnings.append(f"findings[{index}] is not an object; ignored")
            continue
        fid = item.get("id")
        if item.get("source") != "model-checking":
            warnings.append(f"{fid!r} is not a model-checking finding; ignored")
            continue
        raw = item.get(MATCH_KEY)
        values = raw if isinstance(raw, list) else []
        matches = list(dict.fromkeys(value for value in values if isinstance(value, str) and value in early))
        unknown = [value for value in values if value not in early]
        if unknown or (raw is not None and not isinstance(raw, list)):
            warnings.append(f"{fid}: ignored unknown {MATCH_KEY} value(s): {unknown or raw!r}")
        entry = {**item, MATCH_KEY: matches}
        if any(sealed.statuses.get(match) in REUSED for match in matches):
            covered.append(entry)
        else:
            kept.append(entry)
    doc = {
        "generated_by": "consolidate",
        "findings": kept + list(sealed.candidates),
        DOC_KEY: {"scenario_candidates": sealed.ids, "covered": covered},
    }
    return doc, warnings


def covered_ids(doc: dict[str, Any]) -> set[str]:
    section = doc.get(DOC_KEY)
    covered = section.get("covered") if isinstance(section, dict) else None
    if not isinstance(covered, list):
        return set()
    return {str(item["id"]) for item in covered if isinstance(item, dict) and "id" in item}


def report_notes(doc: dict[str, Any]) -> dict[str, str]:
    """Report text for each sealed candidate that model checking matched."""
    section = doc.get(DOC_KEY)
    if not isinstance(section, dict):
        return {}
    covered = section.get("covered")
    findings = doc.get("findings")
    lines: dict[str, list[str]] = {}
    groups: tuple[tuple[list[Any], str], ...] = (
        (covered if isinstance(covered, list) else [], "Same defect; this earlier verdict is reused."),
        (findings if isinstance(findings, list) else [], "Confirmed separately with its counterexample."),
    )
    for items, note in groups:
        for item in items:
            if not isinstance(item, dict) or item.get("source") != "model-checking":
                continue
            title = " ".join(str(item.get("title", "")).split())
            for match in item.get(MATCH_KEY) or []:
                lines.setdefault(str(match), []).append(f"- {item.get('id')}: {title}. {note}")
    return {fid: "## Model checking\n" + "\n".join(entries) for fid, entries in lines.items()}


def summary(work: Path) -> str | None:
    """One pipeline-summary line for a ``continue`` run, or None without a seal."""
    try:
        sealed = load(work)
    except SealError:
        return None
    reproduced = sum(status == "REPRODUCED" for status in sealed.statuses.values())
    incomplete = len(sealed.incomplete)
    retried = f", {incomplete} incomplete and confirmed again after modeling" if incomplete else ""
    line = (
        f"{len(sealed.candidates)} Scenario candidate(s) confirmed before modeling "
        f"({reproduced} reproduced{retried}; report: {REPORT})"
    )
    try:
        doc = json.loads((work / "spec" / "candidates.json").read_text())
    except (OSError, UnicodeError, ValueError):
        return line
    if not isinstance(doc, dict) or not isinstance(doc.get(DOC_KEY), dict):
        return line
    findings = doc.get("findings")
    model = [
        item
        for item in (findings if isinstance(findings, list) else [])
        if isinstance(item, dict) and item.get("source") == "model-checking"
    ]
    reused = len(covered_ids(doc))
    rematched = sum(bool(item.get(MATCH_KEY)) for item in model)
    return (
        f"{line}; model checking: {len(model) + reused} finding(s) — {reused} repeated an earlier "
        f"confirmed defect, {rematched} matched an unconfirmed Scenario candidate, "
        f"{len(model) - rematched} new"
    )
