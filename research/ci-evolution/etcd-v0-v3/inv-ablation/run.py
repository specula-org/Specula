"""Invariant-maintenance ablation on the etcd V0-V3 transitions (#188 section 3.2).

Each run gives one arm's prompt and the original judge input packet to a fresh `claude -p`
session and keeps its decision. Packets are rebuilt from etcd-io/raft git objects and from
spec files found by sha256 in this repository, and are checked against the hashes Qian
recorded in agent-runs/inv-judge-V0x-1/input-manifest.json before anything runs.

Usage:
  python3 run.py prepare V03                 # rebuild and verify one packet only
  python3 run.py run A1 V03                  # one run, rep 1
  python3 run.py run A0,A1 V01,V02,V03 --reps 3 --jobs 3
  python3 run.py --summarize                 # rebuild results/summary.md
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPERIMENT = HERE.parent
SPECULA = EXPERIMENT.parents[2]
WORK = Path(os.environ.get("INV_ABLATION_WORK", "/mydata/bingzhuo/inv-ablation"))
ETCD = Path(os.environ.get("ETCD_RAFT_GIT", WORK / "etcd"))
RESULTS = HERE / "results"

REVISIONS = {
    "V00": "d58d5d159ae1a1f644a10003f2d8b3b807cd0b3a",
    "V01": "46580dcf61734b12ae757dbabdf31c2b862acd68",
    "V02": "3ea6503e58b03833d7d32a4ffcd3a76db9ea2520",
    "V03": "bd3c759d61f003970d62095f04f3df5d977c8c78",
}
PREVIOUS = {"V01": "V00", "V02": "V01", "V03": "V02"}
ARMS = {
    "A0": "prompts/A0-skill-rules.md",
    "A1": "prompts/A1-judge.md",
    "A2": "prompts/A2-judge-evidence.md",
    "A3": "prompts/A3-two-axis.md",
}
# Arms that execute TLC/Go run in sandbox.sh with Bash; the judge-only arms keep the
# read-only tool set they were first run with.
EXECUTING = {"A2", "A3"}
NETWORK = re.compile(r"\b(curl|wget|git\s+(clone|fetch|pull)|go\s+get|pip3?\s+install|apt|nc|ssh|https?://)")

MODEL = "claude-opus-5-5"
EFFORT = "xhigh"
TOOLS = "Read,Glob,Grep,Write,Edit"
EXEC_TOOLS = "Bash,Read,Glob,Grep,Write,Edit"
BUDGET_USD = 25
EXEC_BUDGET_USD = 40
MAX_ATTEMPTS = 8


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def spec_index() -> dict[str, Path]:
    index: dict[str, Path] = {}
    patterns = ("research/**/*.tla", "research/**/*.cfg")
    for pattern in patterns:
        for p in sorted(glob.glob(str(SPECULA / pattern), recursive=True)):
            if "/inv-ablation/" in p:
                continue
            index.setdefault(sha256(Path(p).read_bytes()), Path(p))
    return index


def prepare(transition: str, dest: Path) -> dict:
    """Rebuild the original judge packet (without TASK.md) into dest and verify every file."""
    original = EXPERIMENT / f"agent-runs/inv-judge-{transition}-1"
    manifest = json.loads((original / "input-manifest.json").read_text())
    revs = {"old": REVISIONS[PREVIOUS[transition]], "new": REVISIONS[transition]}
    index = spec_index()
    dest.mkdir(parents=True)
    verified, missing = [], []
    for key, digest in sorted(manifest.items()):
        if key == "TASK.md":
            continue  # replaced by the arm's prompt
        parts = key.split("/")
        if key == "update.patch":
            data = (original / key).read_bytes()
        elif parts[1] == "source":
            proc = subprocess.run(
                ["git", "-C", str(ETCD), "show", f"{revs[parts[0]]}:{'/'.join(parts[2:])}"], capture_output=True
            )
            data = proc.stdout if proc.returncode == 0 else None
        elif parts[1] == "spec":
            src = index.get(digest)
            data = src.read_bytes() if src else None
        else:
            raise SystemExit(f"unexpected packet entry {key}")
        if data is None:
            missing.append(key)
            continue
        if sha256(data) != digest:
            raise SystemExit(f"{transition}: {key} does not match the recorded sha256")
        target = dest / key
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        verified.append(key)
    (dest / "out").mkdir()
    return {"transition": transition, "verified": len(verified), "missing": missing}


def clean_env() -> dict:
    drop = ("SPECULA_", "CLAUDECODE", "CLAUDE_CODE_ENTRYPOINT", "CLAUDE_CODE_SSE_PORT", "VSCODE_", "TERM_PROGRAM")
    env = {k: v for k, v in os.environ.items() if not k.startswith(drop)}
    env["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] = "1"
    return env


def run_one(arm: str, transition: str, rep: int, attempt: int = 1) -> dict:
    run_id = f"{arm}-{transition}-r{rep}"
    out_dir = RESULTS / run_id
    if out_dir.exists():
        return {"run": run_id, "status": "skipped, results exist"}
    base = WORK / "runs" / run_id
    if base.exists():
        shutil.rmtree(base)
    workspace = base / "workspace"
    packet = prepare(transition, workspace)
    prompt = (HERE / ARMS[arm]).read_text()
    (workspace / "TASK.md").write_text(prompt)
    log = base / "stream.jsonl"
    executing = arm in EXECUTING
    tools = EXEC_TOOLS if executing else TOOLS
    cmd = [
        "claude", "-p", prompt,
        "--model", MODEL, "--effort", EFFORT,
        "--tools", tools,
        "--permission-mode", "acceptEdits",
        "--strict-mcp-config", "--setting-sources", "",
        "--no-session-persistence",
        "--max-budget-usd", str(EXEC_BUDGET_USD if executing else BUDGET_USD),
        "--output-format", "stream-json", "--verbose",
    ]
    if executing:
        cmd = [str(HERE / "sandbox.sh"), str(workspace), "--", *cmd[:3], "--allowedTools", "Bash", *cmd[3:]]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t0 = time.monotonic()
    with log.open("w") as out, (base / "stderr.log").open("w") as err:
        proc = subprocess.run(cmd, cwd=workspace, stdout=out, stderr=err, env=clean_env(), stdin=subprocess.DEVNULL)
    seconds = round(time.monotonic() - t0, 1)

    result, tool_uses, bash, order = {}, {}, [], []
    for line in log.read_text().splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("type") == "result":
            result = event
        if event.get("type") == "assistant":
            for block in event.get("message", {}).get("content", []):
                if block.get("type") == "tool_use":
                    tool_uses[block["name"]] = tool_uses.get(block["name"], 0) + 1
                    args = block.get("input", {})
                    if block["name"] == "Bash":
                        bash.append(args.get("command", ""))
                        order.append("bash")
                    elif block["name"] in ("Write", "Edit") and str(args.get("file_path", "")).endswith("decision.initial.json"):
                        order.append(block["name"].lower() + "-initial")

    if not result or result.get("is_error"):
        # An API failure (usage limit, overload, crash) says nothing about the method:
        # keep the attempt aside, never as a result, and retry after a usage-limit reset.
        reason = str(result.get("result") or "no result event")[:300]
        stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        invalid = WORK / "invalid" / f"{run_id}-attempt{attempt}-{stamp}"
        invalid.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(base), str(invalid))
        (invalid / "invalid.json").write_text(json.dumps({
            "run": run_id, "attempt": attempt, "reason": reason, "seconds": seconds,
            "cost_usd": result.get("total_cost_usd"), "api_error_status": result.get("api_error_status"),
        }, indent=2) + "\n")
        wait = limit_wait(reason)
        if wait is not None and attempt < MAX_ATTEMPTS:
            print(json.dumps({"run": run_id, "status": "usage limit, retrying", "sleep_seconds": wait}), flush=True)
            time.sleep(wait)
            return run_one(arm, transition, rep, attempt + 1)
        return {"run": run_id, "status": "invalid", "reason": reason}

    out_dir.mkdir(parents=True)
    produced = []
    for name in ("decision.initial.json", "decision.json", "decision.md", "evidence.json"):
        src = workspace / "out" / name
        if src.exists():
            shutil.copy(src, out_dir / name)
            produced.append(name)
    evidence_files = copy_evidence(workspace, out_dir / "evidence")
    decision_ok = False
    if "decision.json" in produced:
        try:
            json.loads((out_dir / "decision.json").read_text())
            decision_ok = True
        except json.JSONDecodeError:
            pass
    record = {
        "run": run_id,
        "arm": arm,
        "transition": transition,
        "rep": rep,
        "model": MODEL,
        "effort": EFFORT,
        "tools": tools,
        "sandboxed": executing,
        "prompt": ARMS[arm],
        "prompt_sha256": sha256(prompt.encode()),
        "packet": packet,
        "started_at": started,
        "attempt": attempt,
        "seconds": seconds,
        "exit_code": proc.returncode,
        "subtype": result.get("subtype"),
        "cost_usd": result.get("total_cost_usd"),
        "turns": result.get("num_turns"),
        "usage": result.get("usage"),
        "permission_denials": result.get("permission_denials"),
        "tool_uses": tool_uses,
        "produced": produced,
        "evidence_files": evidence_files,
        "audit": audit(bash, order) if executing else None,
        "decision_json_parses": decision_ok,
        "log": str(log),
        "log_sha256": sha256(log.read_bytes()),
        "command": [c if c != prompt else f"<{ARMS[arm]}>" for c in cmd],
    }
    (out_dir / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    if result.get("result"):
        (out_dir / "final.md").write_text(result["result"])
    return {k: record[k] for k in ("run", "exit_code", "subtype", "cost_usd", "seconds", "turns", "produced")}


def limit_wait(reason: str) -> int | None:
    """Seconds to wait before retrying after a usage-limit message, or None if it was another error."""
    if "limit" not in reason.lower():
        return None
    match = re.search(r"resets (\d{1,2})(?::(\d{2}))?\s*(am|pm)\s*\(([^)]+)\)", reason, re.I)
    if not match:
        return 1800
    from zoneinfo import ZoneInfo

    hour, minute, ampm, tz = int(match.group(1)), int(match.group(2) or 0), match.group(3).lower(), match.group(4)
    hour = hour % 12 + (12 if ampm == "pm" else 0)
    now = datetime.datetime.now(ZoneInfo(tz))
    reset = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
    if reset <= now:
        reset += datetime.timedelta(days=1)
    wait = (reset - now).total_seconds()
    if wait > 6 * 3600:  # a usage window is at most five hours away, so the reset has already passed
        wait = 0
    return int(wait) + 180


def copy_evidence(workspace: Path, dest: Path) -> int:
    """Keep the files the agent created under evidence/ (not copies of packet files)."""
    root = workspace / "evidence"
    if not root.exists():
        return 0
    packet = {sha256(p.read_bytes()) for sub in ("old", "new") for p in (workspace / sub).rglob("*") if p.is_file()}
    kept = 0
    for p in sorted(root.rglob("*")):
        if not p.is_file() or p.stat().st_size > 2_000_000:
            continue
        if p.name in ("go.mod", "go.sum") or sha256(p.read_bytes()) in packet:
            continue
        target = dest / p.relative_to(root)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(p, target)
        kept += 1
    return kept


def audit(bash: list[str], order: list[str]) -> dict:
    first_bash = order.index("bash") if "bash" in order else None
    initial = next((i for i, o in enumerate(order) if o.endswith("-initial")), None)
    edits_after = [i for i, o in enumerate(order) if o.endswith("-initial")][1:]
    return {
        "bash_commands": len(bash),
        "network_like_commands": [c[:300] for c in bash if NETWORK.search(c)],
        "initial_written_before_first_bash": initial is not None and (first_bash is None or initial < first_bash),
        "initial_rewritten_later": len(edits_after),
    }


def summarize() -> None:
    rows = []
    for path in sorted(RESULTS.glob("*/run.json")):
        r = json.loads(path.read_text())
        score = path.parent / "score.json"
        scored = json.loads(score.read_text()).get("summary", "") if score.exists() else ""
        cost = f"{r['cost_usd']:.2f}" if r.get("cost_usd") is not None else "?"
        rows.append(
            f"| `{r['run']}` | {r['arm']} | {r['transition']} | {r['subtype']} | {'yes' if r['decision_json_parses'] else 'no'}"
            f" | {cost} | {r['seconds']:.0f} | {r.get('turns')} | {scored} |"
        )
    head = "| Run | Arm | Transition | Outcome | decision.json | USD | Seconds | Turns | Score |\n|---|---|---|---|---|---:|---:|---:|---|\n"
    (RESULTS / "summary.md").write_text(head + "\n".join(rows) + "\n")
    print((RESULTS / "summary.md").read_text())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", nargs="?", choices=["prepare", "run"])
    parser.add_argument("arms_or_transition", nargs="?")
    parser.add_argument("transitions", nargs="?")
    parser.add_argument("--reps", type=int, default=1)
    parser.add_argument("--first-rep", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--summarize", action="store_true")
    args = parser.parse_args()
    if args.summarize:
        summarize()
        return
    if args.command == "prepare":
        dest = WORK / "packets" / args.arms_or_transition
        if dest.exists():
            shutil.rmtree(dest)
        print(json.dumps(prepare(args.arms_or_transition, dest)))
        return
    jobs = [
        (arm, transition, rep)
        for transition in args.transitions.split(",")
        for arm in args.arms_or_transition.split(",")
        for rep in range(args.first_rep, args.first_rep + args.reps)
    ]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for outcome in pool.map(lambda job: run_one(*job), jobs):
            print(json.dumps(outcome), flush=True)
    summarize()


if __name__ == "__main__":
    main()
