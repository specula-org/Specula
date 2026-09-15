"""Persistent, dependency-scoped records of unresolved findings.

The workflow decides semantic identity and premise applicability. This module
checks the recorded inputs and evidence, and never runs confirmation itself.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import re
import secrets
import shutil
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from specula.snapshotlib import clean_git_environment

DIRECTORY = "spec/persistent-findings"
RECEIPTS = "spec/finding-reuse"
CONTEXT = "persistent-findings-context.json"
LIVE = {"REPRODUCED", "ENV_LIMITED", "MASKED"}
INDEX = f"{DIRECTORY}/index.json"


class FindingsError(ValueError):
    """A persistent finding cannot be recorded or reused with these inputs."""


def _directory(root: Path, relative: str) -> Path:
    current = root
    for part in ("", *Path(relative).parts):
        current = current / part
        with contextlib.suppress(FileExistsError):
            current.mkdir()
        if not stat.S_ISDIR(current.lstat().st_mode):
            raise FindingsError(f"not a real findings directory: {current}")
    return current


def _regular_file(root: Path, relative: str) -> bool:
    current = root
    try:
        if not stat.S_ISDIR(current.lstat().st_mode):
            return False
        for part in Path(relative).parts:
            current /= part
            mode = current.lstat().st_mode
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                return False
        return stat.S_ISREG(current.lstat().st_mode)
    except OSError:
        return False


def read_json(path: Path) -> dict[str, Any]:
    if not stat.S_ISREG(path.lstat().st_mode):
        raise FindingsError(f"not a regular findings record: {path}")
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise FindingsError(f"not a findings record: {path}")
    return value


def write_json(path: Path, value: object) -> None:
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(8)}")
    with temporary.open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
    temporary.replace(path)


def _source_revision(source: Path) -> str:
    try:
        result = subprocess.run(
            ["git", "-c", "core.fsmonitor=false", "-C", str(source), "rev-parse", "HEAD"],
            env=clean_git_environment(),
            capture_output=True,
            text=True,
            check=True,
        )
        return result.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unversioned source; see dependency fingerprints"


def _id(value: object) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", value) is None or value == "index":
        raise FindingsError("invalid unresolved issue ID")
    return value


def _text(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise FindingsError(f"issue {field} must be nonempty text")
    return value


def _strings(value: object, field: str) -> list[str]:
    if not isinstance(value, list) or any(not isinstance(item, str) or not item.strip() for item in value):
        raise FindingsError(f"issue {field} must be a list of nonempty strings")
    return value


def _path(value: object) -> str:
    text = _text(value, "path")
    path = Path(text)
    if path.is_absolute() or not path.parts or any(part in {"..", ".git"} for part in path.parts):
        raise FindingsError("issue paths must be relative, without parent or Git metadata components")
    return path.as_posix()


def _bytes(root: Path, relative: str) -> bytes:
    relative = _path(relative)
    if not _regular_file(root, relative):
        raise FindingsError(f"missing or unsafe issue input: {relative}")
    return (root / relative).read_bytes()


def _digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _record_path(fid: str) -> str:
    return f"{DIRECTORY}/{_id(fid)}.json"


def record_digest(work: Path, fid: str) -> str:
    return _digest(_bytes(work, _record_path(fid)))


def load(work: Path, fid: str) -> dict[str, Any]:
    record = json.loads(_bytes(work, _record_path(fid)))
    if (
        not isinstance(record, dict)
        or type(record.get("version")) is not int
        or record["version"] != 1
        or record.get("id") != fid
        or not isinstance(record.get("status"), str)
        or record["status"] not in LIVE
        or type(record.get("reusable")) is not bool
    ):
        raise FindingsError(f"{fid}: invalid unresolved issue record")
    for key in ("title", "cause", "trigger", "consequence", "origin_run", "source_revision"):
        _text(record.get(key), key)
    for key in ("sites", "actions", "invariants", "premises"):
        _strings(record.get(key), key)
    for key in ("dependencies", "evidence"):
        values = record.get(key)
        if not isinstance(values, list) or any(not isinstance(value, dict) for value in values):
            raise FindingsError(f"{fid}: invalid {key}")
    if not record["evidence"] or (record["reusable"] and not record["premises"]):
        raise FindingsError(f"{fid}: missing evidence or applicability premises")
    return record


def import_history(work: Path, previous: Path) -> None:
    """Make a supplied history searchable before source checkout completes."""
    work.mkdir(parents=True, exist_ok=True)
    _directory(work, "")
    if previous != work.resolve() and (previous / INDEX).exists():
        if (work / DIRECTORY).exists():
            # CI/BYOM may already have copied the same registry as an artifact.
            if index(work) != index(previous):
                raise FindingsError("current and supplied historical finding registries differ")
        else:
            for path in sorted((previous / DIRECTORY).rglob("*")):
                if path.is_dir() and not path.is_symlink():
                    continue
                relative = path.relative_to(previous).as_posix()
                content = _bytes(previous, relative)
                _directory(work, str(Path(relative).parent))
                (work / relative).write_bytes(content)
                (work / relative).chmod(path.stat().st_mode & 0o777)


def configure(
    work: Path, source: Path, run_id: str, previous: Path | None = None, *, fresh_context: bool = False
) -> None:
    """Bind explicit run inputs and import only the supplied unresolved records."""
    source = source.resolve()
    previous = previous.resolve() if previous is not None else None
    if previous == work.resolve():
        previous = None
    if not source.is_dir() or not run_id:
        raise FindingsError("persistent findings require a source directory and run ID")
    work.mkdir(parents=True, exist_ok=True)
    _directory(work, "")
    expected: dict[str, Any] = {
        "version": 1,
        "source": str(source),
        "run_id": run_id,
        "previous": str(previous) if previous else None,
    }
    if previous is not None and not previous.is_dir():
        raise FindingsError("supplied findings history is not a directory")
    restart_binding = False
    if (work / CONTEXT).exists():
        saved = read_json(work / CONTEXT)
        if saved.get("run_id") == run_id:
            changed = {key for key, value in expected.items() if saved.get(key) != value}
            if not changed and not fresh_context:
                return
            if changed and (not fresh_context or changed != {"source"}):
                raise FindingsError("persistent finding inputs changed within the same run")
            restart_binding = True
    if previous is not None and not restart_binding:
        import_history(work, previous)
    expected["inherited_records"] = {fid: record_digest(work, fid) for fid in index(work)}
    if (work / RECEIPTS).exists():
        _directory(work, RECEIPTS)
        shutil.rmtree(work / RECEIPTS)
    write_json(work / CONTEXT, expected)


def context(work: Path) -> tuple[Path, str, Path | None]:
    saved = json.loads(_bytes(work, CONTEXT))
    if not isinstance(saved, dict) or saved.get("version") != 1:
        raise FindingsError("invalid persistent finding context")
    source = Path(_text(saved.get("source"), "source"))
    run_id = _text(saved.get("run_id"), "run ID")
    previous = Path(saved["previous"]) if saved.get("previous") is not None else None
    if not source.is_absolute() or (previous is not None and not previous.is_absolute()):
        raise FindingsError("persistent finding context paths must be absolute")
    return source, run_id, previous


def _validate_origin(work: Path, record: dict[str, Any], run_id: str, previous: Path | None) -> None:
    if record["origin_run"] == run_id:
        return
    fid = record["id"]
    if previous is not None:
        if _bytes(work, _record_path(fid)) == _bytes(previous, _record_path(fid)):
            return
    elif (work / CONTEXT).exists():
        saved = read_json(work / CONTEXT)
        if saved.get("run_id") == run_id and saved.get("inherited_records", {}).get(fid) == record_digest(work, fid):
            return
    raise FindingsError(f"{fid}: historical issue differs from the prior published record")


def _dependency_bytes(dep: dict[str, Any], source: Path, work: Path) -> bytes:
    root = dep.get("root")
    if root not in ("source", "work"):
        raise FindingsError("issue dependency root must be source or work")
    path = _path(dep.get("path"))
    if root == "work" and (path.startswith(DIRECTORY + "/") or path.startswith(RECEIPTS + "/")):
        raise FindingsError("issue metadata cannot be a dependency of itself")
    content = _bytes(source if root == "source" else work, path)
    if "start" not in dep and "end" not in dep:
        return content
    # Literal, unique boundary lines avoid language-specific parsers and line
    # number drift. Include both boundaries in the fingerprint.
    start = _text(dep.get("start"), "dependency start")
    end = _text(dep.get("end"), "dependency end")
    if "\n" in start or "\n" in end:
        raise FindingsError("dependency boundaries must be single lines")
    lines = content.decode("utf-8").splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if line.rstrip("\r\n") == start]
    ends = [i for i, line in enumerate(lines) if line.rstrip("\r\n") == end]
    if len(starts) != 1 or len(ends) != 1 or starts[0] > ends[0]:
        raise FindingsError(f"missing or ambiguous dependency boundaries: {path}")
    return "".join(lines[starts[0] : ends[0] + 1]).encode("utf-8")


def check(work: Path, source: Path, fid: str) -> list[str]:
    """Return invalidation reasons without loading evidence into the conversation."""
    record = load(work, fid)
    if record.get("reusable") is not True:
        return ["No complete dependency record; analyze this issue once before reuse."]
    if record.get("source") not in {"model-checking", "code-review"}:
        return ["Missing original discovery source; reanalysis required."]
    reasons: list[str] = []
    deps = record.get("dependencies")
    if not isinstance(deps, list) or not deps or not any(d.get("root") == "source" for d in deps):
        return ["Missing source dependency scope."]
    for dep in deps:
        try:
            if _digest(_dependency_bytes(dep, source, work)) != dep.get("sha256"):
                reasons.append(f"Changed {dep['root']} dependency: {dep['path']}")
        except (FindingsError, OSError, UnicodeError) as exc:
            reasons.append(str(exc))
    for evidence in record["evidence"]:
        try:
            if _digest(_bytes(work, evidence["path"])) != evidence["sha256"]:
                reasons.append(f"Changed historical evidence: {evidence['path']}")
        except (FindingsError, OSError) as exc:
            reasons.append(str(exc))
    return reasons


def index(work: Path) -> dict[str, Any]:
    if not (work / INDEX).exists():
        return {}
    value = json.loads(_bytes(work, INDEX))
    if not isinstance(value, dict):
        raise FindingsError("invalid unresolved issue index")
    return value


def rebuild_index(work: Path) -> None:
    summaries = {}
    for path in sorted((work / DIRECTORY).glob("*.json")):
        if path.name == "index.json":
            continue
        record = load(work, path.stem)
        summaries[record["id"]] = {
            key: record[key] for key in ("id", "title", "status", "sites", "actions", "invariants", "reusable")
        }
        summaries[record["id"]]["cause"] = record["cause"][:240]
    _directory(work, DIRECTORY)
    write_json(work / INDEX, summaries)


def lookup(work: Path, queries: list[str], *, limit: int = 5, offset: int = 0) -> list[dict[str, Any]]:
    if not 1 <= limit <= 20 or offset < 0:
        raise FindingsError("lookup limit must be 1..20 and offset must be nonnegative")
    terms = [term.casefold() for term in queries if term.strip()]
    scored = []
    for fid, summary in index(work).items():
        haystack = json.dumps(summary, ensure_ascii=False).casefold()
        score = sum(term in haystack for term in terms)
        if score or not terms:
            scored.append((score, fid, summary))
    scored.sort(key=lambda item: (-item[0], item[1]))
    results = []
    for _, _, summary in scored[offset : offset + limit]:
        summary = dict(summary)
        for field in ("sites", "actions", "invariants"):
            values = summary[field]
            summary[field] = sorted(values, key=lambda value: not any(t in value.casefold() for t in terms))[:5]
        results.append(summary)
    return results


def record_issue(
    work: Path, source: Path, run_id: str, proposal: dict[str, Any], *, rebuild: bool = True
) -> dict[str, Any]:
    fid = _id(proposal.get("id"))
    status = proposal.get("status")
    if not isinstance(status, str) or status not in LIVE:
        raise FindingsError("only REPRODUCED, ENV_LIMITED and MASKED issues are persisted")
    if (work / _record_path(fid)).exists():
        prior = load(work, fid)
        if prior["reusable"] and prior["origin_run"] != run_id and proposal.get("revises") != record_digest(work, fid):
            raise FindingsError(
                f"{fid}: ID already belongs to a historical issue; cite its record digest in revises or use a new ID"
            )
    revision = _source_revision(source)
    record: dict[str, Any] = {
        "version": 1,
        "id": fid,
        "status": status,
        "source": proposal.get("source", "unknown"),
        "origin_run": run_id,
        "source_revision": revision,
        "reusable": proposal.get("reusable", True),
    }
    if type(record["reusable"]) is not bool:
        raise FindingsError("issue reusable must be boolean")
    if record["reusable"] and record["source"] not in {"model-checking", "code-review"}:
        raise FindingsError("reusable findings require their original model-checking or code-review source")
    for key in ("title", "cause", "trigger", "consequence"):
        record[key] = _text(proposal.get(key), key)
    if len(record["title"]) > 160:
        raise FindingsError("issue title must be at most 160 characters")
    for key in ("sites", "actions", "invariants", "premises"):
        record[key] = _strings(proposal.get(key), key)
    deps = proposal.get("dependencies")
    if not isinstance(deps, list) or any(not isinstance(dep, dict) for dep in deps):
        raise FindingsError("issue dependencies must be a list of selectors")
    if record["reusable"] and (not record["premises"] or not any(d.get("root") == "source" for d in deps)):
        raise FindingsError("reusable issues require explicit premises and source dependencies")
    if (
        record["reusable"]
        and (record["actions"] or record["invariants"])
        and not any(d.get("root") == "work" for d in deps)
    ):
        raise FindingsError("issues linked to model actions/invariants require model dependencies")
    record["dependencies"] = [{**dep, "sha256": _digest(_dependency_bytes(dep, source, work))} for dep in deps]
    evidence = _strings(proposal.get("evidence"), "evidence")
    if not evidence:
        raise FindingsError("issue evidence must not be empty")
    # Read everything before replacing a previous issue. Retain just this
    # issue's selected evidence, without accumulating copies on each update.
    captured = []
    for name in evidence:
        name = _path(name)
        if name.startswith(DIRECTORY + "/") or name.startswith(RECEIPTS + "/"):
            raise FindingsError("fresh analysis must cite current evidence outside the issue registry")
        content = _bytes(work, name)
        if not content.strip():
            raise FindingsError(f"empty issue evidence: {name}")
        captured.append((name, content, (work / name).stat().st_mode & 0o777))
    destination = f"{DIRECTORY}/evidence/{fid}"
    if (work / destination).exists():
        _directory(work, destination)
        shutil.rmtree(work / destination)
    record["evidence"] = []
    for name, content, mode in captured:
        relative = f"{destination}/{name}"
        _directory(work, str(Path(relative).parent))
        (work / relative).write_bytes(content)
        (work / relative).chmod(mode)
        record["evidence"].append({"original": name, "path": relative, "sha256": _digest(content)})
    _directory(work, DIRECTORY)
    write_json(work / _record_path(fid), record)
    for suffix in (".json", ".md"):
        (work / RECEIPTS / f"{fid}{suffix}").unlink(missing_ok=True)
    if rebuild:
        rebuild_index(work)
    return record


def reuse_issue(work: Path, source: Path, run_id: str, fid: str, reason: str) -> dict[str, Any]:
    reason = _text(reason, "reuse reason")
    reasons = check(work, source, fid)
    if reasons:
        raise FindingsError(f"{fid}: reanalysis required: {'; '.join(reasons)}")
    record = load(work, fid)
    evidence = f"{RECEIPTS}/{fid}.md"
    finding: dict[str, Any] = {
        "id": fid,
        "status": record["status"],
        "evidence": evidence,
        "reuse": {
            "run_id": run_id,
            "record_sha256": _digest(_bytes(work, _record_path(fid))),
            "reason": reason,
        },
    }
    _directory(work, RECEIPTS)
    links = "\n".join(f"- [Historical evidence](../../{item['path']})" for item in record["evidence"])
    (work / evidence).write_text(
        f"# {fid}: {record['title']}\n\nStill unresolved; historical conclusion reused.\n\n"
        f"Status: {record['status']}\nOriginal run: {record['origin_run']}\n"
        f"Original source: {record['source_revision']}\nCurrent run: {run_id}\n\n"
        f"Applicability: {reason}\n\nPremises and evidence limits:\n"
        + "\n".join(f"- {premise}" for premise in record["premises"])
        + f"\n\n{links}\n"
    )
    finding["reuse"]["evidence_sha256"] = _digest(_bytes(work, evidence))
    write_json(work / RECEIPTS / f"{fid}.json", finding)
    return finding


def validate_reuse(work: Path, source: Path, run_id: str, finding: dict[str, Any], previous: Path | None) -> None:
    fid = _id(finding["id"])
    receipt = finding.get("reuse")
    record = load(work, fid)
    if (
        not isinstance(receipt, dict)
        or receipt.get("run_id") != run_id
        or receipt.get("record_sha256") != _digest(_bytes(work, _record_path(fid)))
        or finding["status"] != record["status"]
        or receipt.get("evidence_sha256") != _digest(_bytes(work, finding["evidence"]))
    ):
        raise FindingsError(f"{fid}: reuse receipt does not match this run, record and disposition")
    _text(receipt.get("reason"), "reuse reason")
    _validate_origin(work, record, run_id, previous)
    reasons = check(work, source, fid)
    if reasons:
        raise FindingsError(f"{fid}: reanalysis required: {'; '.join(reasons)}")


def merge_receipts(work: Path, record: dict[str, Any]) -> None:
    """Carry an explicitly checked old issue even when it was not rediscovered."""
    present = {
        finding["id"]: finding
        for finding in record["findings"]
        if isinstance(finding, dict) and isinstance(finding.get("id"), str)
    }
    for path in sorted((work / RECEIPTS).glob("*.json")):
        fid = _id(path.stem)
        finding = json.loads(_bytes(work, f"{RECEIPTS}/{path.name}"))
        if not isinstance(finding, dict) or finding.get("id") != fid:
            raise FindingsError("invalid issue reuse receipt")
        if fid not in present:
            record["findings"].append(finding)
            present[fid] = finding
        else:
            current = present[fid]
            if (
                "reuse" not in current
                and current.get("status") == finding.get("status")
                and isinstance(current.get("evidence"), str)
                and isinstance(finding.get("evidence"), str)
                and Path(current["evidence"]) == Path(finding["evidence"])
            ):
                current["reuse"] = finding.get("reuse")


def receipts(work: Path) -> list[dict[str, Any]]:
    result: dict[str, Any] = {"findings": []}
    merge_receipts(work, result)
    return list(result["findings"])


def confirmation_findings(work: Path, run_id: str) -> list[dict[str, Any]]:
    from specula.resource_summary import _confirmation_finding_statuses

    statuses = _confirmation_finding_statuses(_bytes(work, "confirmed-bugs.md").decode(), impact_only=False)
    if statuses is None:
        raise FindingsError("cannot read final confirmation dispositions")
    result = []
    for fid, status in statuses.items():
        evidence = "confirmed-bugs.md"
        discovery = "unknown"
        worker = f"confirmation/{_id(fid)}/verdict.json"
        if status in LIVE and _regular_file(work, worker):
            saved = read_json(work / worker)
            body = saved.get("body")
            if saved.get("status") == status and isinstance(body, str) and body.strip():
                match = re.search(r"(?m)^- \*\*Source\*\*: (MC|Code Review)\b", body)
                if match:
                    discovery = "model-checking" if match[1] == "MC" else "code-review"
                evidence = f"spec/finding-confirmation/{fid}.md"
                _directory(work, "spec/finding-confirmation")
                (work / evidence).write_text(f"# {fid}\n\nStatus: {status}\nRun: {run_id}\n\n{body}\n")
        result.append({"id": fid, "status": status, "evidence": evidence, "source": discovery})
    by_id = {finding["id"]: finding for finding in result}
    retained = receipts(work)
    for receipt in retained:
        source, context_run, previous = context(work)
        if context_run != run_id:
            raise FindingsError("confirmation and persistent findings belong to different runs")
        fid = receipt["id"]
        if fid in by_id and by_id[fid]["status"] in {"FIXED", "FALSE POSITIVE"}:
            continue
        if fid not in by_id or by_id[fid]["status"] != receipt["status"]:
            raise FindingsError(f"{fid}: reuse is missing from the final confirmation report")
        validate_reuse(work, source, run_id, receipt, previous)
        by_id[fid] = receipt
    return list(by_id.values())


def finalize_confirmation(work: Path) -> None:
    if not _regular_file(work, "confirmed-bugs.md"):
        return
    source, run_id, _ = context(work)
    reconcile(work, source, run_id, confirmation_findings(work, run_id))


def reused_body(work: Path, fid: str) -> str:
    record = load(work, fid)
    source = "MC" if record["source"] == "model-checking" else "Code Review"
    return (
        f"- **Source**: {source}\n"
        f"- **Novelty**: KNOWN (cite: run/{record['origin_run']}/{fid}; fix-status: unfixed)\n\n"
        f"## Description\n{record['cause']}\n\n## Trigger scenario\n{record['trigger']}\n\n"
        f"## Reproduction result\nStill unresolved; historical conclusion reused. {record['consequence']}\n"
        f"Evidence and limits: [{fid}]({RECEIPTS}/{fid}.md)\n"
    )


def reconcile(work: Path, source: Path, run_id: str, findings: list[dict[str, Any]]) -> None:
    """Publish only current unresolved entries; fixed/dismissed entries are deleted."""
    live = {finding["id"]: finding for finding in findings if finding["status"] in LIVE}
    binding = read_json(work / CONTEXT) if _regular_file(work, CONTEXT) else {}
    inherited = (
        binding.get("inherited_records", {})
        if binding.get("run_id") == run_id and binding.get("source") == str(source.resolve())
        else {}
    )
    for fid, finding in live.items():
        if "reuse" in finding:
            continue  # The original record/evidence stays byte-identical.
        registered = load(work, fid) if (work / _record_path(fid)).exists() else None
        # A fresh source binding can inherit records with the same run ID.
        if (
            registered is not None
            and registered["origin_run"] == run_id
            and registered["reusable"]
            and inherited.get(fid) != record_digest(work, fid)
        ):
            if registered["status"] != finding["status"] or check(work, source, fid):
                raise FindingsError(f"{fid}: recorded conclusion changed; reanalyze and record it again")
        proposal_path = f"spec/issue-input/{_id(fid)}.json"
        worker_path = f"confirmation/{fid}/issue.json"
        if not (work / proposal_path).exists():
            proposal_path = worker_path
        if (work / proposal_path).exists():
            proposal = json.loads(_bytes(work, proposal_path))
            if not isinstance(proposal, dict) or proposal.get("id") != fid:
                raise FindingsError(f"{fid}: invalid issue proposal")
            # A changed verdict may introduce different consequences/premises.
            # Keep it visible but do not reuse stale worker metadata.
            if proposal.get("status") != finding["status"]:
                proposal["reusable"] = False
            proposal["status"] = finding["status"]
            if finding.get("source") in {"model-checking", "code-review"}:
                proposal["source"] = finding["source"]
            proposal["evidence"] = list(dict.fromkeys([finding["evidence"], *proposal.get("evidence", [])]))
            record_issue(work, source, run_id, proposal, rebuild=False)
        elif (work / _record_path(fid)).exists() and load(work, fid)["origin_run"] == run_id:
            registered = load(work, fid)
            if registered["status"] != finding["status"] or (registered["reusable"] and check(work, source, fid)):
                raise FindingsError(f"{fid}: current issue record needs updating after analysis")
            if not any(
                item["original"] == finding["evidence"] and item["sha256"] == _digest(_bytes(work, finding["evidence"]))
                for item in registered["evidence"]
            ):
                raise FindingsError(f"{fid}: issue record does not contain the current confirmation evidence")
        else:
            if registered is not None and registered["reusable"]:
                raise FindingsError(f"{fid}: fresh reanalysis requires updated issue metadata or a valid reuse receipt")
            # Older outputs remain searchable but do not acquire invented
            # dependency scopes or automatically become eligible for reuse.
            record_issue(
                work,
                source,
                run_id,
                {
                    "id": fid,
                    "status": finding["status"],
                    "source": finding.get("source", "unknown"),
                    "title": fid,
                    "cause": "Prior confirmation lacks a dependency record; reanalysis required.",
                    "trigger": "See confirmation evidence.",
                    "consequence": "See confirmation evidence.",
                    "sites": [],
                    "actions": [],
                    "invariants": [],
                    "premises": [],
                    "dependencies": [],
                    "evidence": [finding["evidence"]],
                    "reusable": False,
                },
                rebuild=False,
            )
    resolved = {finding["id"] for finding in findings if finding["status"] in {"FIXED", "FALSE POSITIVE"}}
    for path in (work / DIRECTORY).glob("*.json"):
        if path.name != "index.json" and path.stem in resolved:
            fid = _id(path.stem)
            path.unlink()
            evidence = f"{DIRECTORY}/evidence/{fid}"
            if (work / evidence).exists():
                _directory(work, evidence)
                shutil.rmtree(work / evidence)
            for suffix in (".json", ".md"):
                (work / RECEIPTS / f"{fid}{suffix}").unlink(missing_ok=True)
    rebuild_index(work)
    proposals = "spec/issue-input"
    if (work / proposals).exists():
        _directory(work, proposals)
        shutil.rmtree(work / proposals)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="specula findings", description="Look up and reuse persistent findings.")
    parser.add_argument("--work", required=True, type=Path, help="target's .specula-output directory")
    parser.add_argument("--source", type=Path, help="source directory, required for init")
    parser.add_argument("--run-id", help="run identity, required for init")
    parser.add_argument("--previous", type=Path, help="optional prior .specula-output directory for init")
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("init", help="bind run inputs and import supplied historical records")
    search = commands.add_parser("lookup", help="return a small page of matching summaries")
    search.add_argument("--query", action="append", default=[])
    search.add_argument("--limit", type=int, default=5)
    search.add_argument("--offset", type=int, default=0)
    for name in ("show", "check", "reuse"):
        sub = commands.add_parser(name)
        sub.add_argument("--id", required=True)
        if name == "reuse":
            sub.add_argument("--reason", required=True, help="same mechanism/consequence and unchanged premises")
    save = commands.add_parser("record", help="capture a completed issue and its selected dependencies/evidence")
    save.add_argument("--input", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        work = args.work.absolute()
        if args.command != "init" and any(value is not None for value in (args.source, args.run_id, args.previous)):
            raise FindingsError("--source, --run-id and --previous are inputs to init")
        result: object
        if args.command == "init":
            if args.source is None or args.run_id is None:
                raise FindingsError("init requires --source and --run-id")
            configure(work, args.source, args.run_id, args.previous)
            result = {"run_id": args.run_id, "work": str(work)}
        elif args.command == "lookup":
            result = lookup(work, args.query, limit=args.limit, offset=args.offset)
        elif args.command == "show":
            result = {**load(work, args.id), "record_sha256": record_digest(work, args.id)}
        else:
            source, run_id, previous = context(work)
            if args.command == "check":
                result = {"id": args.id, "reanalysis_reasons": check(work, source, args.id)}
            elif args.command == "reuse":
                # Check baseline provenance before publishing the receipt.
                historical = load(work, args.id)
                _validate_origin(work, historical, run_id, previous)
                result = reuse_issue(work, source, run_id, args.id, args.reason)
            else:
                saved = record_issue(work, source, run_id, read_json(args.input))
                result = {"id": saved["id"], "status": saved["status"], "record": _record_path(saved["id"])}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"Issue reuse unavailable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
