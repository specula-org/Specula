"""Characterization oracle for the Specula bash orchestration layer.

This is migration **step 0**: it pins the *current* behavior of the bash
launchers/adapters as normalized golden snapshots, so the Python rewrites
(steps 1/3/5/6) can be diffed against a fixed baseline ("did my Python behave
like the bash it replaced?").

No pytest needed to run the oracle directly, but it imports the `specula`
package — install it (`pip install -e .`) or put `src/` on PYTHONPATH first. The
pytest wrapper (test_characterization.py) exposes the same cases to CI.

Usage:
    python3 tests/characterization/oracle.py --check     # diff vs golden (default; exit 1 on mismatch)
    python3 tests/characterization/oracle.py --update     # (re)write golden snapshots
    python3 tests/characterization/oracle.py --list       # list case names
    python3 tests/characterization/oracle.py --check -k adapter   # filter by substring
                                                                  # (an exact case name selects only that case)

Each case produces a deterministic, normalized text snapshot. Volatile bits
(absolute paths, timestamps, tmp dirs) are replaced with <PLACEHOLDERS> so the
snapshot is stable across machines and runs.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
GOLDEN_DIR = HERE / "golden"
FIXTURES = HERE / "fixtures"
# tests/characterization/ -> tests/ -> repo root
SPECULA_ROOT = HERE.parent.parent
LAUNCH = SPECULA_ROOT / "scripts" / "launch"
ADAPTER = LAUNCH / "adapters" / "claude-code.sh"
ADAPTER_MODULE = "specula.adapters.claude_code"

# single source for the nested-session env vars the adapter strips
from specula.adapters.claude_code import SESSION_ENV_VARS  # noqa: E402


def _adapter_cmd() -> list[str]:
    """Which adapter implementation the adapter cases exercise. Controlled by
    SPECULA_ADAPTER_IMPL:
      unset/other → the installed adapter (`claude-code.sh`, now a shim to python)
      "python"    → run the Python port directly (parity check)
      <a path>    → run `bash <path>` (e.g. the pre-cutover bash original, to
                    capture ground-truth goldens or re-verify parity against it)."""
    impl = os.environ.get("SPECULA_ADAPTER_IMPL", "")
    if impl == "python":
        # sys.executable, not "python3": the module lives in the installed
        # `specula` package, so use the interpreter that has it (the suite's venv).
        return [sys.executable, "-m", ADAPTER_MODULE]
    if impl and os.path.exists(impl):
        return ["bash", impl]
    return ["bash", str(ADAPTER)]


PKG = SPECULA_ROOT / "src" / "specula"
PHASELIB = PKG / "phaselib.py"
PIPELINELIB = PKG / "pipelinelib.py"

EXP = SPECULA_ROOT / "scripts" / "exp"
SCHEDULER = EXP / "scheduler.sh"
SCHEDULERLIB = PKG / "schedulerlib.py"


def _launcher_cmd(script: str) -> list[str]:
    """Which phase-launcher implementation the dry-run/gate/summary cases exercise:
    unset/other → the installed launcher (`launch_<phase>.sh`, now a shim to python)
    "python"    → run phaselib.py directly with the phase key from the script name
                  (launch_<key>.sh -> <key>) — the step-3 parity check. The
                  pipeline is the exception: it lives in pipelinelib.py, not a
                  phaselib phase key.
    <a path>    → run `bash <path>` (e.g. a pre-cutover bash launcher materialized
                  under scripts/launch/, to capture ground-truth goldens or
                  re-verify parity against the bash). Run one case at a time in
                  this mode, since the path overrides the script for every case."""
    impl = os.environ.get("SPECULA_LAUNCHER_IMPL", "")
    if impl == "python":
        if script == "launch_pipeline.sh":
            return ["python3", str(PIPELINELIB)]
        key = script[len("launch_") : -len(".sh")]
        return ["python3", str(PHASELIB), key]
    if impl and os.path.exists(impl):
        return ["bash", impl]
    return ["bash", str(LAUNCH / script)]


# ── normalization ───────────────────────────────────────────────────────────
def normalize(text: str, extra: dict[str, str] | None = None) -> str:
    """Replace volatile substrings with stable placeholders.

    `extra` maps absolute strings (e.g. a tmp dir) -> placeholder; applied
    longest-first so nested paths don't partially match.
    """
    subs = dict(extra or {})
    subs[str(SPECULA_ROOT)] = "<ROOT>"
    subs[str(Path.home())] = "<HOME>"
    for needle in sorted(subs, key=len, reverse=True):
        if needle:
            text = text.replace(needle, subs[needle])
    out = []
    for line in text.splitlines():
        out.append(_norm_line(line))
    # trailing newline normalized away; snapshots compared line-wise
    return "\n".join(out).rstrip("\n") + "\n"


def _norm_line(line: str) -> str:
    import re

    # claude spawn failure: bash "…: claude: command not found" vs the python port's
    # "failed to run claude: …" collapse to one placeholder (whole line replaced) so
    # the missing-claude case is three-way consistent (orig bash ≡ python ≡ shim).
    if "command not found" in line or "failed to run claude" in line:
        return "<CLAUDE-SPAWN-ERROR>"
    # [HH:MM:SS] log timestamps -> [TIME]
    line = re.sub(r"\[\d{2}:\d{2}:\d{2}\]", "[TIME]", line)
    # launched-agent PIDs -> <PID> (full-run summary path)
    line = re.sub(r"PID=\d+", "PID=<PID>", line)
    # ISO-8601 datetimes (date -Iseconds) -> <DATE>
    line = re.sub(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:[+-]\d{2}:\d{2}|Z)?", "<DATE>", line)
    # "completed in 0m 1s" elapsed -> <ELAPSED>
    line = re.sub(r"completed in \d+m \d+s", "completed in <ELAPSED>", line)
    # quota gate "sleeping 12345s" (now-relative) -> <SECS>
    line = re.sub(r"sleeping \d+s", "sleeping <SECS>s", line)
    # scheduler log() prefix "[YYYY-MM-DD HH:MM:SS]" -> [TS]
    line = re.sub(r"\[\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}\]", "[TS]", line)
    # scheduler RUN_ID (date +%Y%m%d_%H%M%S: run= banner, Logs: path) -> <RUN_ID>
    line = re.sub(r"\b\d{8}_\d{6}\b", "<RUN_ID>", line)
    # scheduler task wall time "(success, 3s, attempt 1)" -> <N>s
    line = re.sub(r", \d+s, attempt", ", <N>s, attempt", line)
    # minted isolated run ids (generate_run_id: 20260703-153000-a1b2) -> <RID>
    line = re.sub(r"\b\d{8}-\d{6}-[0-9a-f]{4}\b", "<RID>", line)
    return line


# ── helpers ─────────────────────────────────────────────────────────────────
def _clean_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    """A predictable env: no ambient Claude config that could redirect the
    adapter, controlled PATH."""
    env = dict(os.environ)
    for var in (
        "VIRTUAL_ENV",
        "CLAUDE_CONFIG_DIR",
        *SESSION_ENV_VARS,
        # popped so command construction is deterministic regardless of ambient env
        "CLAUDE_EFFORT",
        "CLAUDE_MODEL",
        "CLAUDE_ALIAS",
        # fake-claude recorder channels: an ambient value would redirect every
        # case's stub into it (cases re-inject their own via `extra`)
        "CLAUDE_ARGV_FILE",
        "CLAUDE_STDIN_FILE",
        "CLAUDE_CONFIG_DIR_FILE",
        # ambient git redirection would swing the seeded repos' commit counts
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        # pipeline knobs read from env: an ambient value would swing the banner's
        # repair cap and the quota gate's thresholds/wait bound
        "MAX_REPAIR_ROUNDS",
        "QUOTA_5H",
        "QUOTA_7D",
        "QUOTA_MAX_WAITS",
        # an ambient isolation root would reroute every $PWD-derived path the
        # legacy goldens pin (step 4 workspace control)
        "SPECULA_RUN_DIR",
    ):
        env.pop(var, None)
    env["PATH"] = "/usr/bin:/bin:" + env.get("PATH", "")
    if extra:
        env.update(extra)
    return env


def _write_fake_claude(bindir: Path, fixture: Path) -> None:
    """A stub `claude` that ignores args, drains stdin (the prompt), and prints
    the fixture JSON — so the adapter's post-processing runs hermetically."""
    bindir.mkdir(parents=True, exist_ok=True)
    stub = bindir / "claude"
    stub.write_text(
        "#!/usr/bin/env bash\n"
        # record the args the adapter passed (for command-construction cases);
        # no-op when CLAUDE_ARGV_FILE is unset, so output cases are unaffected.
        'printf "%s\\n" "$@" > "${CLAUDE_ARGV_FILE:-/dev/null}"\n'
        # record the CLAUDE_CONFIG_DIR the adapter exported (alias -> config-dir
        # mapping); no-op when CLAUDE_CONFIG_DIR_FILE is unset.
        'printf "%s\\n" "${CLAUDE_CONFIG_DIR:-}" > "${CLAUDE_CONFIG_DIR_FILE:-/dev/null}"\n'
        # record the prompt on stdin (for review, which passes it inline); drains
        # to /dev/null when CLAUDE_STDIN_FILE is unset, so other cases are unaffected.
        'cat > "${CLAUDE_STDIN_FILE:-/dev/null}"\n'
        f"cat {json.dumps(str(fixture))}\n"
    )
    stub.chmod(stub.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)


def _init_git_repo(path: Path, commit: bool = False) -> None:
    """A real (valid) repo: a fake with only .git/HEAD is rejected by git, whose
    repo discovery then ascends PAST the tempdir — with TMPDIR inside any checkout
    the commit count comes from the enclosing repo and the golden goes flaky.
    commit=True adds one empty commit so `git rev-list --count HEAD` succeeds
    ('1 commits' — the success branch no other case exercises)."""
    path.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init", "-q", str(path)], check=True, env=_clean_env())
    if commit:
        subprocess.run(
            [
                "git",
                "-C",
                str(path),
                "-c",
                "user.name=oracle",
                "-c",
                "user.email=oracle@test",
                "commit",
                "-q",
                "--allow-empty",
                "-m",
                "seed",
            ],
            check=True,
            env=_clean_env(),
        )


def _seed_files(root: Path, seed: dict[str, str | bytes] | None) -> None:
    """Create seed files under root (relpath -> content). bytes values are written
    raw — used to plant non-UTF-8 bytes a text write would reject."""
    for rel, content in (seed or {}).items():
        f = root / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(content, bytes):
            f.write_bytes(content)
        else:
            f.write_text(content)


# ── case runners ────────────────────────────────────────────────────────────
def run_adapter_case(
    fixture_name: str,
    session_id: str = "",
    session_jsonl: list[str] | None = None,
    inline_prompt: str | None = None,
    with_claude: bool = True,
) -> str:
    """Feed a canned `claude` JSON response through the adapter (bash or python
    port, per SPECULA_ADAPTER_IMPL); snapshot exit code + derived .log +
    .usage.json.

    inline_prompt: if given, pass `--prompt=...` (exercising the mktemp path)
    instead of `--prompt-file=...`.

    with_claude=False: don't put a `claude` on PATH, so the spawn fails — pins the
    "claude missing" path (bash writes the shell error into RAW_JSON and carries
    on → exit 0 + parse_failed; the python port mirrors that).

    When session_jsonl is given, plant a fake session transcript at the path the
    num_turns fixup looks up ($CLAUDE_CONFIG_DIR/projects/-<cwd>/<sid>.jsonl) so
    that branch is exercised. `base` is resolved (realpath) so it matches the
    adapter's os.getcwd()-derived project key."""
    fixture = FIXTURES / fixture_name
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        prompt = base / "prompt.md"
        prompt.write_text("dummy prompt\n")
        log = base / "out.log"
        if session_jsonl is not None:
            # CLAUDE_CONFIG_DIR = $HOME/.testalias (HOME=base); proj key from cwd=base
            proj_key = str(base).replace("/", "-").lstrip("-")
            proj_dir = base / ".testalias" / "projects" / f"-{proj_key}"
            proj_dir.mkdir(parents=True, exist_ok=True)
            (proj_dir / f"{session_id}.jsonl").write_text("\n".join(session_jsonl) + "\n")
        # PATH controls `claude` presence (with_claude → fake on PATH).
        if with_claude:
            _write_fake_claude(bindir, fixture)
            path = f"{bindir}:/usr/bin:/bin"
        else:
            path = "/usr/bin:/bin"
        env = _clean_env({"PATH": path, "HOME": str(base)})
        prompt_arg = f"--prompt={inline_prompt}" if inline_prompt is not None else f"--prompt-file={prompt}"
        proc = subprocess.run(
            _adapter_cmd() + [prompt_arg, "--claude-alias=testalias", f"--log={log}"],
            cwd=str(base),
            env=env,
            capture_output=True,
            text=True,
        )
        parts = [f"exit_code: {proc.returncode}", ""]
        for name, p in [(".log", log), (".usage.json", base / "out.usage.json")]:
            parts.append(f"=== {name} ===")
            parts.append(p.read_text() if p.exists() else "<MISSING>")
            parts.append("")
        raw = normalize("\n".join(parts), {str(base): "<TMP>"})
    return raw


def run_adapter_cmd_case(
    flags: list[str],
    env_extra: dict[str, str] | None = None,
    record: str = "argv",
    claude_alias: str | None = "testalias",
) -> str:
    """Pin what the spawned `claude` observes for a given flag/env combo. The fake
    `claude` records into the channel selected by `record`:
      "argv"      — the exact argv (--effort/--model/--max-budget assembly, incl.
                    the skip-on-default/zero/empty branches)
      "configdir" — the CLAUDE_CONFIG_DIR the adapter exported (the alias sets the
                    config dir, $HOME/.<alias>, not an argv flag, so the argv
                    channel can't see it); prefixed with the exit code so a run
                    that never reaches claude can't silently pin <MISSING>

    env_extra: ambient env to set (e.g. CLAUDE_EFFORT="") — pins the bash
    ${VAR:-default} rule that an exported-but-empty var still means the default.
    claude_alias: value for --claude-alias; None omits the flag entirely, "" pins
    the empty-flag path (guarded only by the config-dir line's own default)."""
    recorder_var, header = {
        "argv": ("CLAUDE_ARGV_FILE", "claude argv"),
        "configdir": ("CLAUDE_CONFIG_DIR_FILE", "CLAUDE_CONFIG_DIR seen by claude"),
    }[record]
    fixture = FIXTURES / "claude_normal.json"
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, fixture)
        prompt = base / "prompt.md"
        prompt.write_text("dummy prompt\n")
        record_file = base / "recorded.txt"
        env = _clean_env(
            {
                "PATH": f"{bindir}:/usr/bin:/bin",
                "HOME": str(base),
                recorder_var: str(record_file),
                **(env_extra or {}),
            }
        )
        alias_flags = [] if claude_alias is None else [f"--claude-alias={claude_alias}"]
        proc = subprocess.run(
            _adapter_cmd() + [f"--prompt-file={prompt}", *alias_flags, f"--log={base}/out.log", *flags],
            cwd=str(base),
            env=env,
            capture_output=True,
            text=True,
        )
        recorded = record_file.read_text() if record_file.exists() else "<MISSING>"
        snap = f"=== {header} ===\n{recorded}"
        if record == "configdir":
            snap = f"exit_code: {proc.returncode}\n\n" + snap
        return normalize(snap, {str(base): "<TMP>"})


def run_adapter_error_case(flags: list[str]) -> str:
    """Pin the validation contract: snapshot exit code + stderr for a deliberately
    invalid invocation. `@BASE@` in a flag is replaced with the tmp dir."""
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, FIXTURES / "claude_normal.json")
        env = _clean_env({"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(base)})
        resolved = [f.replace("@BASE@", str(base)) for f in flags]
        proc = subprocess.run(
            _adapter_cmd() + resolved,
            cwd=str(base),
            env=env,
            capture_output=True,
            text=True,
        )
        return normalize(
            f"exit_code: {proc.returncode}\n\n=== stderr ===\n{proc.stderr}",
            {str(base): "<TMP>"},
        )


def run_dryrun_case(
    script: str,
    target: str,
    seed: dict[str, str | bytes] | None = None,
    prompt_rel: str = ".specula-output/.prompt.md",
    use_artifact: bool = True,
    extra_flags: list[str] | None = None,
    snapshot_prompt: bool = True,
    bad_artifact: bool = False,
    check_only: bool = False,
    repos: list[str] | None = None,
) -> str:
    """Run a phase launcher with --dry-run (or --check) in an isolated cwd;
    snapshot stdout, plus the generated prompt file (the exact prompt handed to
    the agent) unless snapshot_prompt=False. One runner covers the dry-run,
    precondition-gate, bad-artifact and check-only case families, so harness
    changes (env hygiene, normalization) apply to all of them at once.

    seed: files to create under the work cwd first (relpath -> content) so a
    downstream phase's prerequisites are satisfied and it reaches the dry-run
    print (e.g. seed modeling-brief.md for spec_generation).
    prompt_rel: where this phase writes its prompt (spec_generation uses
    .spec-gen-prompt.md, not .prompt.md).
    use_artifact: pass --artifact (bug_classification takes none).
    extra_flags: phase-specific flags (validation --repair; confirmation --recheck).
    snapshot_prompt: False for gate/check cases, which never reach the prompt.
    bad_artifact: point --artifact at a nonexistent path — pins the graceful
    degrade (`OK <name> (? commits)` + exit 0, bash `cd ... || echo "?"`), the
    contract the port once broke with a FileNotFoundError on subprocess cwd.
    check_only: run --check instead of --dry-run (pins the check-ok message).
    repos: relpaths under the work cwd to create as REAL one-commit git repos
    (for <name>/artifact/<repo> discovery cases; see _init_git_repo on why a
    fake .git is not hermetic). GIT_CEILING_DIRECTORIES stops repo discovery at
    the tempdir so non-repo cwds can't resolve an enclosing checkout either."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        work = tmp / "work"
        work.mkdir()
        _seed_files(work, seed)
        for rel in repos or []:
            _init_git_repo(work / rel, commit=True)
        env = _clean_env({"HOME": str(tmp), "GIT_CEILING_DIRECTORIES": str(tmp)})
        mode = "--check" if check_only else "--dry-run"
        cmd = _launcher_cmd(script) + [mode, *(extra_flags or [])]
        subs = {str(work): "<WORK>", str(tmp): "<TMP>"}
        if bad_artifact:
            bad = tmp / "no-such-repo"
            cmd.append(f"--artifact={bad}")
            subs[str(bad)] = "<BAD-ARTIFACT>"
        elif use_artifact:
            artifact = tmp / "artifact"
            _init_git_repo(artifact)
            cmd.append(f"--artifact={artifact}")
            subs[str(artifact)] = "<ARTIFACT>"
        cmd.append(target)
        proc = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True)
        parts = [f"exit_code: {proc.returncode}", "", "=== stdout ===", proc.stdout, ""]
        if snapshot_prompt:
            prompt = work / prompt_rel
            parts.append(f"=== {prompt.name} ===")
            parts.append(prompt.read_text() if prompt.exists() else "<MISSING>")
            parts.append("")
        raw = normalize("\n".join(parts), subs)
    return raw


def run_help_case(script: str, pre_args: list[str] | None = None) -> str:
    """Pin --help: the bash launchers printed their full header comment (usage,
    examples, the complete option list) via sed; the port must keep that text.
    pre_args: launch_review.sh requires a phase argument before --help (the bash
    parsed `$1` as the phase unconditionally — same contract, pinned as-is)."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(
            _launcher_cmd(script) + [*(pre_args or []), "--help"],
            cwd=tmp,
            env=env,
            capture_output=True,
            text=True,
        )
        return normalize(f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n")


def run_review_case(
    phase: str, seed: dict[str, str | bytes] | None = None, fixture_name: str = "claude_normal.json"
) -> str:
    """Pin the review launcher, which has no --dry-run (it always spawns an agent).
    Run it with a fake `claude` that records the inline prompt it receives on stdin,
    and snapshot stdout (banner / per-name lines / summary) + that captured prompt
    (+ stderr when non-empty — adapter diagnostics pass through since the exit-code
    propagation fix).

    seed: pre-create the phase's review file (relpath -> content) so the summary's
    *populated* branch fires ('review written (N lines)', counting via wc -l);
    without it the summary reports 'no review file generated'.
    fixture_name: the canned claude response; claude_ratelimit.json makes the
    adapter exit 75 (EX_TEMPFAIL), which must abort the launcher with 75 exactly
    as bash `set -e` + `pid=$(adapter ...)` did."""
    fixture = FIXTURES / fixture_name
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, fixture)
        work = base / "work"
        work.mkdir()
        _seed_files(work, seed)
        stdin_file = base / "captured_prompt.txt"
        env = _clean_env({"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(base), "CLAUDE_STDIN_FILE": str(stdin_file)})
        proc = subprocess.run(
            _launcher_cmd("launch_review.sh") + [phase, "footest"],
            cwd=str(work),
            env=env,
            capture_output=True,
            text=True,
        )
        parts = [f"exit_code: {proc.returncode}", "", "=== stdout ===", proc.stdout, ""]
        parts.append("=== review prompt (agent stdin) ===")
        parts.append(stdin_file.read_text() if stdin_file.exists() else "<MISSING>")
        parts.append("")
        if proc.stderr.strip():
            parts.append("=== stderr ===")
            parts.append(proc.stderr)
            parts.append("")
        return normalize("\n".join(parts), {str(work): "<WORK>", str(base): "<TMP>"})


def run_summary_case(
    script: str,
    target: str,
    seed: dict[str, str | bytes],
    use_artifact: bool = True,
) -> str:
    """Run a phase launcher in FULL mode (no --dry-run/--check) with a fake `claude`
    and pre-seeded files; snapshot stdout. This is the only case that reaches the
    post-launch summary path — both summarize()'s *populated* branch (the OK/~~/
    written lines that count .md/.tla lines via wc -l) and the per-phase
    `Monitor: tail -f …` hint — neither of which the dry-run/gate cases exercise.

    `seed` writes BOTH the phase's prerequisites (so check() passes and the run
    proceeds) and its output files (so summarize sees them), relative to the work
    cwd (single-target → under .specula-output/). The agent is faked, so its own
    output files never appear; only the seeded ones drive the summary. Launched-
    agent PIDs are normalized to <PID>. bytes seed values are written raw (plant
    a non-UTF-8 byte in a counted file to pin byte-safe counting). stderr is
    snapshotted only when non-empty, so a summarize() crash is self-diagnosing."""
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, FIXTURES / "claude_normal.json")
        work = base / "work"
        work.mkdir()
        _seed_files(work, seed)
        env = _clean_env({"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(base), "GIT_CEILING_DIRECTORIES": str(base)})
        cmd = _launcher_cmd(script)
        subs = {str(work): "<WORK>", str(base): "<TMP>"}
        if use_artifact:
            artifact = base / "artifact"
            _init_git_repo(artifact)
            cmd = cmd + [f"--artifact={artifact}"]
            subs[str(artifact)] = "<ARTIFACT>"
        cmd = cmd + [target]
        proc = subprocess.run(cmd, cwd=str(work), env=env, capture_output=True, text=True)
        parts = [f"exit_code: {proc.returncode}", "", "=== stdout ===", proc.stdout, ""]
        if proc.stderr.strip():
            parts += ["=== stderr ===", proc.stderr, ""]
        return normalize("\n".join(parts), subs)


def run_pipeline_case(flags: list[str], target: str) -> str:
    """Run launch_pipeline.sh --dry-run with a given --skip-* combo; snapshot the
    phase sequencing + repair-loop gating. Hermetic: HOME points at an empty tmp
    so the quota gate's usage.sh finds no credentials, warns, and proceeds (no
    network); dry-run prints each phase's command instead of launching agents.
    Runs --no-isolate since the default flip (step 7d): these cases pin the
    legacy $PWD layout, now behind the escape hatch (and isolating here would
    write runs/ into the real repo). pipeline_default_isolate covers the new
    default hermetically."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        artifact = tmp / "artifact"
        _init_git_repo(artifact)
        work = tmp / "work"
        work.mkdir()
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(
            _launcher_cmd("launch_pipeline.sh")
            + [
                "--dry-run",
                "--no-isolate",
                f"--artifact={artifact}",
                *flags,
                target,
            ],
            cwd=work,
            env=env,
            capture_output=True,
            text=True,
        )
        raw = normalize(
            f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n",
            {str(artifact): "<ARTIFACT>", str(work): "<WORK>", str(tmp): "<TMP>"},
        )
    return raw


def run_pipeline_full_case(
    flags: list[str], target: str, seed: dict[str, Any], snapshot_files: list[str] | None = None
) -> str:
    """Full pipeline run (no --dry-run): fake `claude` + seeded phase
    prerequisites/outputs. Reaches everything the dry-run cases can't: the
    `main 2>&1 | tee pipeline.log` plumbing, the real phase subprocess sequencing
    under set -e, the repair loop's reset / no-progress / terminal branches,
    regenerate_ledger, and generate_summary's populated branches (wc -l counts,
    du -h log sizes, resolved/deferred tallies).

    snapshot_files: work-relative paths appended to the snapshot after the run
    (RR files post-transition, the regenerated ledger). pipeline.log is asserted
    byte-identical to captured stdout — the tee contract."""
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, FIXTURES / "claude_normal.json")
        work = base / "work"
        work.mkdir()
        _seed_files(work, seed)
        artifact = base / "artifact"
        _init_git_repo(artifact)
        env = _clean_env({"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(base), "GIT_CEILING_DIRECTORIES": str(base)})
        # --no-isolate: these cases pin the legacy layout (step 7d flip)
        cmd = _launcher_cmd("launch_pipeline.sh") + ["--no-isolate", f"--artifact={artifact}", *flags, target]
        proc = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True)
        parts = [f"exit_code: {proc.returncode}", "", "=== stdout ===", proc.stdout, ""]
        plog = work / ".specula-output" / "pipeline.log"
        if plog.is_file():
            tee_ok = plog.read_text() == proc.stdout
            parts += ["=== pipeline.log (tee) ===", "identical to stdout" if tee_ok else "!! DIFFERS FROM STDOUT", ""]
        else:
            parts += ["=== pipeline.log (tee) ===", "<MISSING>", ""]
        for rel in snapshot_files or []:
            f = work / rel
            parts += [f"=== {rel} ===", f.read_text() if f.is_file() else "<MISSING>", ""]
        if proc.stderr.strip():
            parts += ["=== stderr ===", proc.stderr, ""]
        return normalize("\n".join(parts), {str(artifact): "<ARTIFACT>", str(work): "<WORK>", str(base): "<TMP>"})


def run_pipeline_cd_case() -> str:
    """Single target whose case-studies/<name>/ dir exists → main() cd's into it
    before running the phases: pins the 'Single target: cd to …' log, the summary
    landing in the case dir, and pipeline.log staying in the LAUNCH cwd (the tee
    opens before the cd). Hermetic via a copied tree: SCRIPT_DIR/SPECULA_ROOT
    derive from the entry script's location, so the pipeline entry + adapters/ +
    the python ports are copied under a tmp specroot with a seeded
    case-studies/footest/ (the real repo has no such case study, and writing into
    a real one wouldn't be hermetic). The tmp tree has no scripts/exp/usage.sh,
    which also pins the quota gate's missing-usage-script branch (silent proceed —
    no WARN lines)."""
    impl = os.environ.get("SPECULA_LAUNCHER_IMPL", "")
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        root = tmp / "specroot"
        launch = root / "scripts" / "launch"
        (launch / "adapters").mkdir(parents=True)
        # dry-run only existence-checks the adapter, never runs it
        shutil.copy2(ADAPTER, launch / "adapters" / "claude-code.sh")
        pkg = root / "src" / "specula"
        pkg.mkdir(parents=True)
        # regular package beats any installed `specula` on sys.path, so the
        # copied pipelinelib's `from specula.phaselib import …` stays hermetic
        (pkg / "__init__.py").write_text("")
        for py in ("phaselib.py", "pipelinelib.py"):
            if (PKG / py).exists():
                shutil.copy2(PKG / py, pkg / py)
        entry_src = Path(impl) if impl and impl != "python" and os.path.exists(impl) else LAUNCH / "launch_pipeline.sh"
        shutil.copy2(entry_src, launch / "launch_pipeline.sh")
        (root / "case-studies" / "footest").mkdir(parents=True)
        work = tmp / "work"
        work.mkdir()
        if impl == "python":
            cmd = ["python3", str(pkg / "pipelinelib.py")]
        else:
            cmd = ["bash", str(launch / "launch_pipeline.sh")]
        env = _clean_env({"HOME": str(tmp)})
        # --no-isolate: this case pins the legacy single-target cd branch (7d flip)
        proc = subprocess.run(
            cmd + ["--dry-run", "--no-isolate", "footest"], cwd=work, env=env, capture_output=True, text=True
        )
        case_out = root / "case-studies" / "footest" / ".specula-output"
        locs = [
            f"pipeline.log in launch cwd: {'yes' if (work / '.specula-output' / 'pipeline.log').is_file() else 'NO'}",
            f"summary in case dir: {'yes' if (case_out / 'pipeline-summary.md').is_file() else 'NO'}",
            f"summary in launch cwd: {'yes (BUG)' if (work / '.specula-output' / 'pipeline-summary.md').is_file() else 'no'}",
        ]
        parts = [
            f"exit_code: {proc.returncode}",
            "",
            "=== stdout ===",
            proc.stdout,
            "",
            "=== file locations ===",
            *locs,
            "",
        ]
        if proc.stderr.strip():
            parts += ["=== stderr ===", proc.stderr, ""]
        return normalize("\n".join(parts), {str(root): "<SPECROOT>", str(work): "<WORK>", str(tmp): "<TMP>"})


def run_pipeline_default_isolate_case() -> str:
    """The default flip (step 7d): no isolation flag, no ambient env — the
    pipeline mints runs/<run-id>/ under SPECULA_ROOT and reroots everything
    there. Hermetic via the same copied-specroot trick as the cd case (the
    minted run must land in a tmp specroot, not the real repo). Pins: the Run
    banner, no single-target cd, pipeline.log/run.json/summary at the run
    root, the runs/latest symlink, and both the launch cwd and the canonical
    case dir staying untouched."""
    impl = os.environ.get("SPECULA_LAUNCHER_IMPL", "")
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        root = tmp / "specroot"
        launch = root / "scripts" / "launch"
        (launch / "adapters").mkdir(parents=True)
        shutil.copy2(ADAPTER, launch / "adapters" / "claude-code.sh")
        pkg = root / "src" / "specula"
        pkg.mkdir(parents=True)
        (pkg / "__init__.py").write_text("")
        for py in ("phaselib.py", "pipelinelib.py"):
            if (PKG / py).exists():
                shutil.copy2(PKG / py, pkg / py)
        entry_src = Path(impl) if impl and impl != "python" and os.path.exists(impl) else LAUNCH / "launch_pipeline.sh"
        shutil.copy2(entry_src, launch / "launch_pipeline.sh")
        (root / "case-studies" / "footest").mkdir(parents=True)
        work = tmp / "work"
        work.mkdir()
        if impl == "python":
            cmd = ["python3", str(pkg / "pipelinelib.py")]
        else:
            cmd = ["bash", str(launch / "launch_pipeline.sh")]
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(cmd + ["--dry-run", "footest"], cwd=work, env=env, capture_output=True, text=True)
        runs_dir = root / "runs"
        runs = sorted(d for d in runs_dir.iterdir() if d.is_dir() and not d.is_symlink()) if runs_dir.is_dir() else []
        run = runs[0] if len(runs) == 1 else None
        latest_ok = (
            run is not None and (runs_dir / "latest").is_symlink() and os.readlink(runs_dir / "latest") == run.name
        )
        locs = [
            f"exactly one run dir: {'yes' if len(runs) == 1 else 'NO (' + str(len(runs)) + ')'}",
            f"pipeline.log at run root: {'yes' if run and (run / 'pipeline.log').is_file() else 'NO'}",
            f"run.json at run root: {'yes' if run and (run / 'run.json').is_file() else 'NO'}",
            f"summary at run root: {'yes' if run and (run / 'pipeline-summary.md').is_file() else 'NO'}",
            f"latest symlink -> run: {'yes' if latest_ok else 'NO'}",
            f"launch cwd untouched: {'yes' if not (work / '.specula-output').exists() else 'NO'}",
            f"case dir untouched: {'yes' if not (root / 'case-studies' / 'footest' / '.specula-output').exists() else 'NO'}",
        ]
        parts = [
            f"exit_code: {proc.returncode}",
            "",
            "=== stdout ===",
            proc.stdout,
            "",
            "=== file locations ===",
            *locs,
            "",
        ]
        if proc.stderr.strip():
            parts += ["=== stderr ===", proc.stderr, ""]
        return normalize("\n".join(parts), {str(root): "<SPECROOT>", str(work): "<WORK>", str(tmp): "<TMP>"})


def _pipeline_helper_impl() -> tuple[str, Path]:
    """Which implementation the sourced-helper cases (repair state machine, quota
    gate) drive. The bash originals aren't standalone commands — those drivers
    source launch_pipeline.sh (main call stripped) to reach its helper functions;
    the python drivers import pipelinelib and call the same-named ports, printing
    the same lines (that equivalence is exactly what the shared golden proves).
      SPECULA_LAUNCHER_IMPL unset → installed: the bash body while it exists,
                    pipelinelib.py once launch_pipeline.sh is a shim
      "python"    → pipelinelib.py
      <a path>    → that bash source (ground-truth capture / re-verification)"""
    impl = os.environ.get("SPECULA_LAUNCHER_IMPL", "")
    if impl == "python":
        return "python", PIPELINELIB
    if impl and os.path.exists(impl):
        return "bash", Path(impl)
    installed = LAUNCH / "launch_pipeline.sh"
    if "pipelinelib.py" in installed.read_text():
        return "python", PIPELINELIB
    return "bash", installed


def _pipeline_functions_only(src: Path) -> str:
    """A bash pipeline source with the trailing `main` invocation stripped, so it
    can be sourced to expose the repair-loop/quota helper functions without
    running the whole pipeline. The top-level `mkdir .specula-output` that
    remains runs harmlessly inside the test's tmp cwd."""
    lines = src.read_text().splitlines(keepends=True)
    cut = next((i for i, ln in enumerate(lines) if ln.startswith("main 2>&1")), len(lines))
    return "".join(lines[:cut])


def _run_pipeline_driver(
    bash_tpl: str, py_tpl: str, subs: dict[str, str], tmp: Path
) -> subprocess.CompletedProcess[str]:
    """Materialize and run the bash or python variant of a helper driver, per
    _pipeline_helper_impl. `subs` maps @TOKEN@ -> value in the chosen template;
    @FNONLY@ (bash: the sourceable pipeline functions) and @SRC@ (python:
    the package root, so `from specula import pipelinelib` works) are filled in here."""
    kind, src = _pipeline_helper_impl()
    if kind == "bash":
        fnonly = tmp / "pipeline_fnonly.sh"
        fnonly.write_text(_pipeline_functions_only(src))
        text = bash_tpl.replace("@FNONLY@", str(fnonly))
        driver, runner = tmp / "driver.sh", "bash"
    else:
        text = py_tpl.replace("@SRC@", str(SPECULA_ROOT / "src"))
        driver, runner = tmp / "driver.py", "python3"
    for token, val in subs.items():
        text = text.replace(token, val)
    driver.write_text(text)
    return subprocess.run(
        [runner, str(driver)], cwd=tmp, env=_clean_env({"HOME": str(tmp)}), capture_output=True, text=True
    )


def _rr_fixture(rr_id: str, status: str, bug_id: str = "DA-1 | agreement safety violated", round_: int = 1) -> str:
    """A repair-request file in the confirmed frontmatter format (see
    .claude/skills/bug-confirmation/references/repair-request-format.md)."""
    return f"""\
---
id: {rr_id}
bug_id: {bug_id}
target: base.tla
status: {status}
round: {round_}
---

# Repair Request {rr_id}

The spec models the QC without binding it to the proposal value.

## History
- created (bug confirmation): QC reuse enables value forgery
"""


_RR_FIXTURE = _rr_fixture("RR-001", "OPEN")

# Drives the repair helpers through a real OPEN -> IN_REPAIR -> RESOLVED
# sequence; @FNONLY@/@RR@ are substituted with tmp paths before running.
_REPAIR_DRIVER = """\
#!/usr/bin/env bash
RR="@RR@"
set --                      # clear positional args so the sourced arg-parser sees none
source "@FNONLY@"
set +euo pipefail           # relax; we invoke the helpers manually below

echo "== field reads (pre) =="
echo "id=$(rr_field "$RR" id)"
echo "status=$(rr_status "$RR")"
echo "round=$(rr_field "$RR" round)"
echo "bug_id=$(rr_field "$RR" bug_id)"
echo
echo "== transition OPEN -> IN_REPAIR =="
rr_set_status "$RR" IN_REPAIR "picked up by repair phase (round 1)"
echo "status=$(rr_status "$RR")"
echo
echo "== transition IN_REPAIR -> RESOLVED =="
rr_set_status "$RR" RESOLVED "fix verified by re-check"
echo "status=$(rr_status "$RR")"
echo
echo "== final file content =="
cat "$RR"
"""

_REPAIR_DRIVER_PY = """\
import sys

sys.path.insert(0, "@SRC@")
from specula import pipelinelib as pl

RR = "@RR@"
print("== field reads (pre) ==")
print("id=" + pl.rr_field(RR, "id"))
print("status=" + pl.rr_status(RR))
print("round=" + pl.rr_field(RR, "round"))
print("bug_id=" + pl.rr_field(RR, "bug_id"))
print()
print("== transition OPEN -> IN_REPAIR ==")
pl.rr_set_status(RR, "IN_REPAIR", "picked up by repair phase (round 1)")
print("status=" + pl.rr_status(RR))
print()
print("== transition IN_REPAIR -> RESOLVED ==")
pl.rr_set_status(RR, "RESOLVED", "fix verified by re-check")
print("status=" + pl.rr_status(RR))
print()
print("== final file content ==")
sys.stdout.write(open(RR).read())
"""


def run_repair_case() -> str:
    """Characterize the repair-loop state-machine primitives (rr_field / rr_status
    / rr_set_status) — the atomic ops step 5 must reimplement, incl. the embedded
    python mutator that rewrites `status:` and appends a History bullet."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        rr = tmp / "RR-001.md"
        rr.write_text(_RR_FIXTURE)
        proc = _run_pipeline_driver(_REPAIR_DRIVER, _REPAIR_DRIVER_PY, {"@RR@": str(rr)}, tmp)
        out = f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n"
        if proc.stderr.strip():
            out += f"\n=== stderr ===\n{proc.stderr}\n"
        return normalize(out, {str(rr): "<RR>", str(tmp): "<TMP>"})


# rr_field/rr_set_status edge behaviors the port must copy exactly.
_RR_EDGE_FIXTURES = {
    # status buried past line 25: rr_field's sed window (1,25) misses it → reads
    # empty; rr_set_status rewrites nothing but still appends the History bullet
    "RR-E1.md": ("---\nid: RR-E1\n" + "".join(f"pad{i}: x\n" for i in range(24)) + "status: BURIED\n---\n\n# body\n"),
    # no trailing newline: the mutator must terminate the last line before
    # appending the bullet (the cmdsub-trailing-newline pitfall family)
    "RR-E2.md": "---\nid: RR-E2\nstatus: OPEN\n---\n\n# body\n- last line no newline",
    # duplicate status lines inside the window: reads take the FIRST match; the
    # mutator rewrites only the first
    "RR-E3.md": "---\nid: RR-E3\nstatus: OPEN\nstatus: RESOLVED\n---\n\n# body\n",
}

_REPAIR_EDGE_DRIVER = """\
#!/usr/bin/env bash
RRDIR="@RRDIR@"
set --
source "@FNONLY@"
set +euo pipefail

for f in "$RRDIR"/RR-E*.md; do
  echo "== $(basename "$f") =="
  echo "pre-status=[$(rr_status "$f")]"
  rr_set_status "$f" IN_REPAIR "edge transition (round 1)"
  echo "post-status=[$(rr_status "$f")]"
  echo "-- content --"
  cat "$f"
  echo
done
"""

_REPAIR_EDGE_DRIVER_PY = """\
import locale
import sys
from pathlib import Path

sys.path.insert(0, "@SRC@")
from specula import pipelinelib as pl  # import sets LC_COLLATE (bash glob order)

for f in sorted(Path("@RRDIR@").glob("RR-E*.md"), key=lambda p: locale.strxfrm(p.name)):
    print(f"== {f.name} ==")
    print(f"pre-status=[{pl.rr_status(f)}]")
    pl.rr_set_status(f, "IN_REPAIR", "edge transition (round 1)")
    print(f"post-status=[{pl.rr_status(f)}]")
    print("-- content --")
    sys.stdout.write(f.read_text())
    print()
"""


def run_repair_edges_case() -> str:
    """Pin the RR helper edge behaviors (see _RR_EDGE_FIXTURES): the 25-line
    frontmatter window, the missing-trailing-newline append, first-match wins."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        rrdir = tmp / "rr"
        rrdir.mkdir()
        for name, content in _RR_EDGE_FIXTURES.items():
            (rrdir / name).write_text(content)
        proc = _run_pipeline_driver(_REPAIR_EDGE_DRIVER, _REPAIR_EDGE_DRIVER_PY, {"@RRDIR@": str(rrdir)}, tmp)
        out = f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n"
        if proc.stderr.strip():
            out += f"\n=== stderr ===\n{proc.stderr}\n"
        return normalize(out, {str(rrdir): "<RRDIR>", str(tmp): "<TMP>"})


# Drives wait_for_quota with a stubbed usage source + stubbed sleep, so the real
# decision logic runs on fixed input without network or blocking.
# QUOTA_MAX_WAITS=1 → one "over" detection then bounded abort.
_QUOTA_DRIVER = """\
#!/usr/bin/env bash
set --
source "@FNONLY@"
set +euo pipefail
USAGE_SCRIPT="@FAKEUSAGE@"          # override the real credentialed usage.sh
QUOTA_5H=@Q5@; QUOTA_7D=@Q7@; QUOTA_MAX_WAITS=1
@SLEEP_STUB@
wait_for_quota
echo "wait_for_quota returned: $?"   # only reached on the 'ok' (proceed) path
"""

_QUOTA_DRIVER_PY = """\
import sys

sys.path.insert(0, "@SRC@")
from specula import pipelinelib as pl

rc = pl.wait_for_quota(
    usage_script="@FAKEUSAGE@",
    q5="@Q5@",
    q7="@Q7@",
    max_waits="1",
    claude_alias="claude",
    sleep_fn=@PY_SLEEP@,
)
print(f"wait_for_quota returned: {rc}")  # only reached on the 'ok' (proceed) path
"""


def run_quota_case(usage_json: str, q5: int, q7: int, record_sleep: bool = False, fetch_fail: bool = False) -> str:
    """Characterize the quota gate's decision on a fixed usage snapshot: 5h is
    checked before 7d, strictly `>` threshold, over→WAIT (bounded by MAX_WAITS
    then abort), fetch/parse-error→proceed. The two-layer QUOTA_5H/QUOTA_7D env
    is the known step-5 landmine this pins.

    record_sleep: the sleep stub prints the computed wait — pins the
    deterministic sleep-duration branches (no resets_at → 600s; resets_at in the
    past → negative, clamped to 60s) that the `sleeping <SECS>s` normalization
    would otherwise erase.
    fetch_fail: the usage script exits non-zero → WARN + proceed."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        fake_usage = tmp / "fake_usage.sh"
        if fetch_fail:
            fake_usage.write_text("#!/usr/bin/env bash\nexit 3\n")
        else:
            fake_usage.write_text("#!/usr/bin/env bash\ncat <<'JSON'\n" + usage_json + "\nJSON\n")
        fake_usage.chmod(0o755)
        subs = {
            "@FAKEUSAGE@": str(fake_usage),
            "@Q5@": str(q5),
            "@Q7@": str(q7),
            # stubs: never actually block; optionally record the computed wait
            "@SLEEP_STUB@": ('sleep() { echo "  [stub] sleep ${1}s"; }' if record_sleep else "sleep() { :; }"),
            "@PY_SLEEP@": ('lambda s: print(f"  [stub] sleep {s}s")' if record_sleep else "lambda s: None"),
        }
        proc = _run_pipeline_driver(_QUOTA_DRIVER, _QUOTA_DRIVER_PY, subs, tmp)
        out = f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n"
        if proc.stderr.strip():
            out += f"\n=== stderr ===\n{proc.stderr}\n"
        return normalize(out, {str(tmp): "<TMP>"})


# prerequisite fixtures for the downstream phases' happy-path dry-runs
_VALIDATION_SEED: dict[str, str | bytes] = {
    # base.tla deliberately has NO trailing newline, to pin the wc-l vs splitlines
    # line-count edge in the "specs OK (NL)" check (bash wc-l = 2, not 3).
    ".specula-output/spec/base.tla": "---- MODULE base ----\nx == 1\n====",
    ".specula-output/spec/MC.tla": "---- MODULE MC ----\n====\n",
    ".specula-output/spec/Trace.tla": "---- MODULE Trace ----\n====\n",
    ".specula-output/spec/instrumentation-spec.md": "# instrumentation\n",
}
_CONFIRMATION_SEED: dict[str, str | bytes] = {
    ".specula-output/spec/bug-report.md": "# Bug Report\n\n## MC-1: something\n",
    ".specula-output/modeling-brief.md": "# Modeling Brief\n",
}

# summary-path fixtures: each merges the phase's *prerequisites* (so check() passes
# and the run proceeds to launch+summary) with the *output* files a completed agent
# would have written (so summarize()'s populated branch fires). Line counts are
# chosen to exercise wc -l (trailing-newline files → N == newline count).
_SUMMARY_CODE_ANALYSIS: dict[str, str | bytes] = {
    ".specula-output/modeling-brief.md": "# Modeling Brief\nfamily A: crash window\nfamily B: missing guard\n",
}
_SUMMARY_SPEC_GENERATION: dict[str, str | bytes] = {
    ".specula-output/modeling-brief.md": "# Modeling Brief\n",  # prereq
    ".specula-output/spec/base.tla": "---- MODULE base ----\nx == 1\n====\n",  # output (3 lines)
    ".specula-output/spec/MC.tla": "---- MODULE MC ----\n====\n",
    ".specula-output/spec/Trace.tla": "---- MODULE Trace ----\n====\n",
    ".specula-output/spec/instrumentation-spec.md": "# instrumentation\n",
}
_SUMMARY_HARNESS: dict[str, str | bytes] = {
    ".specula-output/spec/base.tla": "---- MODULE base ----\n====\n",  # prereq
    ".specula-output/spec/Trace.tla": "---- MODULE Trace ----\n====\n",  # prereq
    ".specula-output/spec/instrumentation-spec.md": "# instrumentation\n",  # prereq
    ".specula-output/harness/run.sh": "#!/usr/bin/env bash\n",  # output
    ".specula-output/harness/INSTRUMENTATION.md": "# guide\n",  # output
    ".specula-output/traces/t1.ndjson": '{"e":1}\n',  # output
}
_SUMMARY_BUG_CLASSIFICATION: dict[str, str | bytes] = {
    ".specula-output/spec/confirmed-bugs.md": "# Confirmed Bugs\n\n## Bug 1\n",  # prereq (non-empty)
    ".specula-output/spec/bug-severity.md": (
        "# Bug Severity\n\n## Summary\n"
        "- Total bugs: 5\n- Critical: 1\n- High: 2\n- Medium: 1\n- Low: 1\n- FALSE POSITIVE: 0\n"
    ),  # output (grep-counted)
}
_SUMMARY_SPEC_VALIDATION: dict[str, str | bytes] = {
    **_VALIDATION_SEED,  # prereqs (base.tla has no trailing NL → check shows 2L)
    ".specula-output/spec/changelog.md": "# Changelog\n\n- fixed X\n- fixed Y\n",  # output (4 lines)
}
_SUMMARY_BUG_CONFIRMATION: dict[str, str | bytes] = {
    **_CONFIRMATION_SEED,  # prereqs (bug-report.md + modeling-brief.md)
    ".specula-output/spec/confirmed-bugs.md": "# Confirmed Bugs\n\n## DA-1\n## DA-2\n",  # output (4 lines)
    ".specula-output/repro/test_bug1.py": "def test():\n    pass\n",  # repro test (counted)
}

# full-pipeline fixtures: every phase's prerequisites AND outputs, so each check()
# passes, every phase runs (fake agent), and generate_summary's populated branch
# fires for every section. Review files are seeded too (reviews stay skipped) —
# "written (N lines)" for analysis/validation, "empty (check log)" for specgen.
_PIPELINE_FULL_SEED = {
    ".specula-output/modeling-brief.md": "# Modeling Brief\nfamily A: crash window\nfamily B: missing guard\n",
    ".specula-output/spec/base.tla": "---- MODULE base ----\nx == 1\n====\n",
    ".specula-output/spec/MC.tla": "---- MODULE MC ----\n====\n",
    ".specula-output/spec/Trace.tla": "---- MODULE Trace ----\n====\n",
    ".specula-output/spec/instrumentation-spec.md": "# instrumentation\n",
    ".specula-output/harness/run.sh": "#!/usr/bin/env bash\n",
    ".specula-output/harness/INSTRUMENTATION.md": "# guide\n",
    ".specula-output/traces/t1.ndjson": '{"e":1}\n',
    ".specula-output/spec/changelog.md": "# Changelog\n\n- fixed X\n- fixed Y\n",
    ".specula-output/spec/bug-report.md": "# Bug Report\n\n## MC-1: something\n",
    ".specula-output/spec/confirmed-bugs.md": "# Confirmed Bugs\n\n## DA-1\n## DA-2\n",
    ".specula-output/spec/bug-severity.md": "# Bug Severity\n\n- Total bugs: 2\n",
    ".specula-output/review-analysis.md": "# Review\n\n- point 1\n",
    ".specula-output/spec/review-specgen.md": "",
    ".specula-output/spec/review-validation.md": "# Review\n\n- ok\n",
}

# repair-loop fixtures: only confirmation runs (phases 1–3 + 4b skipped); the loop
# itself invokes phase 3 --repair (needs the validation prereqs) and phase 4
# --recheck (needs the confirmation prereqs). The fake agent never transitions a
# request, so round 1 must detect "no progress" and stop rather than spin.
_REPAIR_LOOP_SKIPS = [
    "--skip-analysis",
    "--skip-specgen",
    "--skip-harness",
    "--skip-validation",
    "--skip-classification",
]
_REPAIR_LOOP_SEED = {
    **_VALIDATION_SEED,
    **_CONFIRMATION_SEED,
    ".specula-output/spec/repair-requests/RR-001.md": _rr_fixture("RR-001", "OPEN"),
    # IN_REPAIR = a prior run died mid-repair; the orchestrator must reset it to
    # OPEN (crash recovery) before entering the loop
    ".specula-output/spec/repair-requests/RR-002.md": _rr_fixture(
        "RR-002", "IN_REPAIR", bug_id="DA-27 | ordering", round_=2
    ),
}
_RR_SNAPSHOT_FILES = [
    ".specula-output/spec/repair-requests/RR-001.md",
    ".specula-output/spec/repair-requests/RR-002.md",
    ".specula-output/spec/repair-ledger.md",
]


# ── scheduler (step 6) ──────────────────────────────────────────────────────
# The scheduler derives SPECULA_ROOT from its own path and writes logs/ +
# case-studies/ under it, so every case materializes the implementation under
# test inside a throwaway specroot, with usage.sh / launch_pipeline.sh replaced
# by stubs in that tree (both are invoked by absolute path, not PATH) and
# `sleep` stubbed via PATH (bash's sleep is the external command, so the poll /
# stagger / backoff / quota waits all return instantly).

# under both thresholds -> the quota gate proceeds silently (the default stub,
# so unrelated cases carry no WARN noise)
_SCHED_USAGE_UNDER = (
    '{"five_hour":{"utilization":10,"resets_at":"2099-01-01T00:00:00+00:00"},'
    '"seven_day":{"utilization":10,"resets_at":"2099-01-08T00:00:00+00:00"}}'
)

# stateful usage stub: over threshold on the first call, under afterwards —
# drives one full wait_for_quota sleep cycle then proceeds. @OVER@ is the
# first-call JSON; @STATE@ a per-case counter file.
_SCHED_USAGE_OVER_ONCE = """\
#!/usr/bin/env bash
n=$(cat "@STATE@" 2>/dev/null || echo 0); n=$((n+1)); printf %s "$n" > "@STATE@"
if [ "$n" -le 1 ]; then cat <<'JSON'
@OVER@
JSON
else cat <<'JSON'
{"five_hour":{"utilization":10,"resets_at":"2099-01-01T00:00:00+00:00"},"seven_day":{"utilization":10,"resets_at":"2099-01-08T00:00:00+00:00"}}
JSON
fi
"""

# fake launch_pipeline.sh: records its argv + the QUOTA_* env the scheduler
# exported (the --threshold forwarding contract), then succeeds.
_SCHED_PIPELINE_OK = """\
#!/usr/bin/env bash
{ printf 'argv: %s\\n' "$*"; echo "env: QUOTA_5H=${QUOTA_5H:-unset} QUOTA_7D=${QUOTA_7D:-unset}"; } >> "@MARKER@"
echo "fake pipeline ok"
"""

# fails with a transient marker on the first call, succeeds on the second
_SCHED_PIPELINE_FLAKY = """\
#!/usr/bin/env bash
n=$(cat "@STATE@" 2>/dev/null || echo 0); n=$((n+1)); printf %s "$n" > "@STATE@"
if [ "$n" -le 1 ]; then echo "API Error: 529 overloaded_error"; exit 1; fi
echo "fake pipeline ok"
"""

# fails silently, but writes an "API Error" phase-1 agent.log into the isolated
# run dir it was handed via --run-id — end-to-end proof that the scheduler's
# transient probe reads the same path the pipeline actually writes
_SCHED_PIPELINE_AGENTLOG = """\
#!/usr/bin/env bash
root="$(cd "$(dirname "$0")/../.." && pwd)"
rid=""
for a in "$@"; do case "$a" in --run-id=*) rid="${a#*=}";; esac; done
d="$root/runs/$rid/footest/.specula-output"
mkdir -p "$d"
echo "API Error: overloaded" > "$d/agent.log"
exit 1
"""

# tripwire default: a case that never expects to launch the pipeline fails
# loudly (exit 97 in the task log -> FAIL line) instead of silently "passing"
_SCHED_PIPELINE_TRIPWIRE = '#!/usr/bin/env bash\necho "REAL PIPELINE INVOKED"; exit 97\n'


def run_scheduler_case(
    queue: str,
    flags: list[str],
    usage_json: str | None = _SCHED_USAGE_UNDER,
    usage_script: str | None = None,
    pipeline_script: str = _SCHED_PIPELINE_TRIPWIRE,
    seed: dict[str, str | bytes] | None = None,
    prompt: str | None = None,
    snapshot: list[str] | None = None,
    record_sleeps: bool = False,
) -> str:
    """Run scheduler.sh hermetically in a throwaway specroot; snapshot exit code,
    stdout (== scheduler.log — asserted, the log() tee contract), status files,
    and optionally recorded sleeps / extra files.

    queue: tasks.queue content, written into the specroot (tabs are semantic).
    flags: scheduler argv beyond --queue (space-separated value style, as bash).
    usage_json: fixed usage.sh output; None plants NO usage.sh (the fetch-fail
    WARN + proceed branch). usage_script overrides with a full stub body
    (@STATE@ -> a per-case counter file) for stateful over-then-under gates.
    pipeline_script: fake launch_pipeline.sh body (@STATE@/@MARKER@ substituted;
    the marker file records argv + forwarded QUOTA env). Defaults to a tripwire
    so dry-run/setup-only cases prove the real pipeline is never invoked.
    prompt: content of a specroot-relative myprompt.md passed as `--prompt
    myprompt.md` — also pins the cwd-relative-to-absolute resolution.
    snapshot: specroot-relative files appended (e.g. the written .prompt-extra.md).
    record_sleeps: append the sleep stub's recorded durations, with the
    poll/stagger constants (30/3) dropped — their count depends on how fast a
    background task exits, only the quota/backoff sleeps are deterministic."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td).resolve()
        root = tmp / "specroot"
        exp = root / "scripts" / "exp"
        launch = root / "scripts" / "launch"
        exp.mkdir(parents=True)
        launch.mkdir(parents=True)

        impl = os.environ.get("SPECULA_SCHEDULER_IMPL", "")
        src = Path(impl) if impl and impl != "python" and os.path.exists(impl) else SCHEDULER
        shutil.copy2(src, exp / "scheduler.sh")
        pkg = root / "src" / "specula"
        pkg.mkdir(parents=True)
        if SCHEDULERLIB.exists():
            shutil.copy2(SCHEDULERLIB, pkg / "schedulerlib.py")
        cmd = ["python3", str(pkg / "schedulerlib.py")] if impl == "python" else ["bash", str(exp / "scheduler.sh")]

        qfile = root / "tasks.queue"
        qfile.write_text(queue)
        state = tmp / "stub-state"
        marker = root / "pipeline-calls.txt"
        if usage_script is not None:
            (exp / "usage.sh").write_text(usage_script.replace("@STATE@", str(state)))
        elif usage_json is not None:
            (exp / "usage.sh").write_text("#!/usr/bin/env bash\ncat <<'JSON'\n" + usage_json + "\nJSON\n")
        (launch / "launch_pipeline.sh").write_text(
            pipeline_script.replace("@STATE@", str(state)).replace("@MARKER@", str(marker))
        )
        _seed_files(root, seed)

        sleeps = tmp / "sleeps.txt"
        bindir = tmp / "bin"
        bindir.mkdir()
        stub = bindir / "sleep"
        stub.write_text(f'#!/usr/bin/env bash\necho "$1" >> "{sleeps}"\n')
        stub.chmod(0o755)

        argv = cmd + ["--queue", str(qfile), *flags]
        if prompt is not None:
            (root / "myprompt.md").write_text(prompt)
            argv += ["--prompt", "myprompt.md"]
        env = _clean_env({"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(tmp)})
        try:
            proc = subprocess.run(argv, cwd=root, env=env, capture_output=True, text=True, timeout=120)
            rc, stdout, stderr = proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired as e:  # a leaked real sleep would hang CI
            rc, stdout, stderr = -1, str(e.stdout or ""), "TIMEOUT (a sleep escaped the stub?)"

        parts = [f"exit_code: {rc}", "", "=== stdout ===", stdout, ""]
        logdirs = sorted((root / "logs" / "scheduler").glob("*")) if (root / "logs").is_dir() else []
        slog = logdirs[0] / "scheduler.log" if logdirs else None
        parts.append("=== scheduler.log (tee) ===")
        if slog is not None and slog.is_file():
            parts.append("identical to stdout" if slog.read_text() == stdout else "!! DIFFERS FROM STDOUT")
        else:
            parts.append("<NO LOG DIR>")
        parts.append("")
        parts.append("=== status files ===")
        status = sorted(logdirs[0].glob("status/*"), key=lambda p: int(p.name)) if logdirs else []
        parts += [f"{p.name}: {p.read_text().strip()}" for p in status] or ["<NONE>"]
        parts.append("")
        if record_sleeps:
            vals = sleeps.read_text().split() if sleeps.is_file() else []
            parts.append("=== recorded sleeps (poll/stagger dropped) ===")
            parts += [v for v in vals if v not in ("3", "30")] or ["<NONE>"]
            parts.append("")
        for rel in snapshot or []:
            f = root / rel
            parts += [f"=== {rel} ===", f.read_text() if f.is_file() else "<MISSING>", ""]
        if stderr.strip():
            parts += ["=== stderr ===", stderr, ""]
        return normalize("\n".join(parts), {str(root): "<SPECROOT>", str(tmp): "<TMP>"})


# a queue whose artifact dirs are pre-seeded (a .git dir satisfies the bash
# `-d .git` probe) so real-mode cases never reach the network clone
_SCHED_QUEUE_2 = "footest|foo/bar|Go|Raft demo\nbartest|baz/qux|Rust|Paxos notes\n"
_SCHED_SEED_2: dict[str, str | bytes] = {
    "case-studies/footest/artifact/bar/.git/HEAD": "ref: refs/heads/main\n",
    "case-studies/bartest/artifact/qux/.git/HEAD": "ref: refs/heads/main\n",
}
_SCHED_OVER_5H_PAST = (
    '{"five_hour":{"utilization":86,"resets_at":"2000-01-01T00:00:00+00:00"},'
    '"seven_day":{"utilization":10,"resets_at":"2099-01-08T00:00:00+00:00"}}'
)
_SCHED_OVER_5H_NORESET = '{"five_hour":{"utilization":86},"seven_day":{"utilization":10}}'


# ── case registry ───────────────────────────────────────────────────────────
# name -> zero-arg callable returning the normalized snapshot string.
CASES: dict[str, Callable[[], str]] = {
    # step 1 target: adapter post-processing (JSON -> .log/.usage.json, exit codes)
    "adapter_normal": lambda: run_adapter_case("claude_normal.json"),
    "adapter_ratelimit": lambda: run_adapter_case("claude_ratelimit.json"),
    "adapter_malformed": lambda: run_adapter_case("claude_malformed.txt"),
    # non-UTF-8 claude output: deliberate deviation from the bash, which died with
    # a UnicodeDecodeError (non-zero exit, no .usage.json, rate-limit exit-75 lost).
    # The port degrades to U+FFFD in .log + parse_failed on the normal exit path.
    # Golden is python-truth by design; the pre-cutover bash fails this case.
    "adapter_nonutf8": lambda: run_adapter_case("claude_nonutf8.txt"),
    "adapter_with_session": lambda: run_adapter_case(
        "claude_session.json",
        session_id="sess-abc",
        session_jsonl=[
            '{"type":"user","message":{"content":"hi"}}',
            '{"type":"assistant","message":{"content":[{"type":"text","text":"t"},{"type":"tool_use","name":"Bash"}]}}',
            '{"type":"assistant","message":{"content":[{"type":"tool_use","name":"Read"},{"type":"tool_use","name":"Edit"}]}}',
            '{"type":"assistant","message":{"content":[{"type":"text","text":"done"}]}}',
        ],
    ),
    "adapter_inline_prompt": lambda: run_adapter_case("claude_normal.json", inline_prompt="analyze this system"),
    # claude can't be spawned (missing from PATH): exit 0 + error-in-.log + parse_failed
    "adapter_claude_missing": lambda: run_adapter_case("claude_normal.json", with_claude=False),
    # command construction: how flags become the `claude` invocation
    "adapter_cmd_default": lambda: run_adapter_cmd_case([]),
    "adapter_cmd_all_flags": lambda: run_adapter_cmd_case(["--effort=high", "--model=sonnet", "--max-budget=5"]),
    "adapter_cmd_skips": lambda: run_adapter_cmd_case(["--effort=default", "--max-budget=0"]),
    # exported-but-empty CLAUDE_EFFORT must still mean --effort max (bash ${:-max})
    "adapter_cmd_empty_effort_env": lambda: run_adapter_cmd_case([], env_extra={"CLAUDE_EFFORT": ""}),
    # alias -> CLAUDE_CONFIG_DIR contract, all three entry points: exported-but-empty
    # env, empty --claude-alias= flag (guarded only by the config-dir line's own
    # default — the env default can't save it), and an ambient CLAUDE_CONFIG_DIR
    # that the adapter must override (alias is authoritative, never inherited)
    "adapter_configdir_empty_alias": lambda: run_adapter_cmd_case(
        [], env_extra={"CLAUDE_ALIAS": ""}, record="configdir", claude_alias=None
    ),
    "adapter_configdir_empty_alias_flag": lambda: run_adapter_cmd_case([], record="configdir", claude_alias=""),
    "adapter_configdir_ambient_override": lambda: run_adapter_cmd_case(
        [], env_extra={"CLAUDE_CONFIG_DIR": "/elsewhere/.other"}, record="configdir", claude_alias=None
    ),
    # validation contract: exit code + stderr on bad invocations
    "adapter_err_no_log": lambda: run_adapter_error_case(["--prompt=x"]),
    "adapter_err_both_prompt": lambda: run_adapter_error_case(
        ["--prompt=x", "--prompt-file=@BASE@/p.md", "--log=@BASE@/o.log"]
    ),
    "adapter_err_no_prompt": lambda: run_adapter_error_case(["--log=@BASE@/o.log"]),
    "adapter_err_prompt_file_missing": lambda: run_adapter_error_case(
        ["--prompt-file=@BASE@/nope.md", "--log=@BASE@/o.log"]
    ),
    "adapter_err_unknown_opt": lambda: run_adapter_error_case(["--bogus"]),
    # step 3 target: phase-launcher dry-run (arg parse, path calc, agent command, prompt)
    "dryrun_code_analysis": lambda: run_dryrun_case("launch_code_analysis.sh", "footest|foo/bar|Go|Raft demo"),
    # regression guard: bad --artifact path degrades to "? commits", never crashes (F1)
    "bad_artifact_code_analysis": lambda: run_dryrun_case(
        "launch_code_analysis.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False, bad_artifact=True
    ),
    # find_repo_dir must skip a hidden .git-bearing dir (bash glob */ never matches
    # dotdirs) and pick the real repo — pinned twice: the check line ('1 commits',
    # realrepo is a real one-commit repo; .hidden would give '?') and the prompt's
    # Repository line (F5). Also the only coverage of rev-list's success branch.
    "dryrun_code_analysis_hidden_repo": lambda: run_dryrun_case(
        "launch_code_analysis.sh",
        "footest|foo/bar|Go|Raft demo",
        use_artifact=False,
        seed={"footest/artifact/.hidden/.git/HEAD": "ref: refs/heads/main\n"},
        repos=["footest/artifact/realrepo"],
    ),
    # artifact/ containing ONLY ineligible (hidden) dirs: the loop exhausts and the
    # single-target fallthrough returns $PWD — Repository becomes the work cwd
    "dryrun_code_analysis_dotdir_only": lambda: run_dryrun_case(
        "launch_code_analysis.sh",
        "footest|foo/bar|Go|Raft demo",
        use_artifact=False,
        seed={"footest/artifact/.hidden/.git/HEAD": "ref: refs/heads/main\n"},
    ),
    # a 5th '|'-separated field folds into the reference (bash `IFS='|' read` gave
    # the last variable the whole remainder, pipes included) — pins the prompt's
    # Reference Algorithm line; golden captured from the pre-cutover bash
    "dryrun_code_analysis_pipe_reference": lambda: run_dryrun_case(
        "launch_code_analysis.sh", "footest|foo/bar|Go|Raft demo|and Paxos notes"
    ),
    # --max-turns is a deprecated verbatim passthrough (adapter ignores it): a
    # non-numeric value must survive to the banner and the dry-run command line
    # exactly as under bash; golden captured from the pre-cutover bash
    "dryrun_code_analysis_maxturns_verbatim": lambda: run_dryrun_case(
        "launch_code_analysis.sh",
        "footest|foo/bar|Go|Raft demo",
        snapshot_prompt=False,
        extra_flags=["--max-turns=abc"],
    ),
    # deliberate deviation: --max-parallel IS arithmetic (throttle bound), and bash
    # accepted garbage only to hang forever in the throttle loop (empty crashed the
    # arithmetic mid-run) — the port fails fast with a one-line error, exit 1.
    # Golden is python-truth by design; the pre-cutover bash fails this case.
    "bad_max_parallel_code_analysis": lambda: run_dryrun_case(
        "launch_code_analysis.sh",
        "footest|foo/bar|Go|Raft demo",
        snapshot_prompt=False,
        use_artifact=False,
        extra_flags=["--max-parallel=abc"],
    ),
    "dryrun_spec_generation": lambda: run_dryrun_case(
        "launch_spec_generation.sh",
        "footest",
        seed={
            ".specula-output/modeling-brief.md": "# Modeling Brief\nfamily A: crash window\nfamily B: missing guard\n"
        },
        prompt_rel=".specula-output/.spec-gen-prompt.md",
    ),
    "dryrun_harness_generation": lambda: run_dryrun_case(
        "launch_harness_generation.sh",
        "footest",
        seed={
            ".specula-output/spec/base.tla": "---- MODULE base ----\n====\n",
            ".specula-output/spec/Trace.tla": "---- MODULE Trace ----\n====\n",
            ".specula-output/spec/instrumentation-spec.md": "# instrumentation\n",
        },
        prompt_rel=".specula-output/.harness-gen-prompt.md",
    ),
    "dryrun_bug_classification": lambda: run_dryrun_case(
        "launch_bug_classification.sh",
        "footest",
        seed={".specula-output/spec/confirmed-bugs.md": "# Confirmed Bugs\n\n## Bug 1: something\n"},
        prompt_rel=".specula-output/.bug-classification-prompt.md",
        use_artifact=False,
    ),
    "dryrun_spec_validation": lambda: run_dryrun_case(
        "launch_spec_validation.sh",
        "footest",
        seed=_VALIDATION_SEED,
        prompt_rel=".specula-output/.spec-validation-prompt.md",
    ),
    "dryrun_spec_validation_repair": lambda: run_dryrun_case(
        "launch_spec_validation.sh",
        "footest",
        seed=_VALIDATION_SEED,
        prompt_rel=".specula-output/.spec-repair-prompt.md",
        extra_flags=["--repair"],
    ),
    "dryrun_bug_confirmation": lambda: run_dryrun_case(
        "launch_bug_confirmation.sh",
        "footest",
        seed=_CONFIRMATION_SEED,
        prompt_rel=".specula-output/.bug-confirmation-prompt.md",
    ),
    "dryrun_bug_confirmation_recheck": lambda: run_dryrun_case(
        "launch_bug_confirmation.sh",
        "footest",
        seed=_CONFIRMATION_SEED,
        prompt_rel=".specula-output/.bug-recheck-prompt.md",
        extra_flags=["--recheck", "--max-repair-rounds=3"],
    ),
    # step 3 target: review launcher (the outlier — no --dry-run; pin via captured prompt)
    "review_analysis": lambda: run_review_case("analysis"),
    "review_specgen": lambda: run_review_case("specgen"),
    "review_validation": lambda: run_review_case("validation"),
    # review summary's populated branch (review file present -> 'review written (N lines)')
    "review_analysis_populated": lambda: run_review_case(
        "analysis", seed={".specula-output/review-analysis.md": "# Review\n\n- point 1\n- point 2\n"}
    ),
    # adapter failure propagation: rate limit -> adapter exit 75 -> launcher exit 75,
    # diagnostics on stderr, no PID line (bash set -e + pid=$(...) contract)
    "review_ratelimit": lambda: run_review_case("analysis", fixture_name="claude_ratelimit.json"),
    # step 5 target: launch_pipeline.sh phase sequencing + repair-loop gating under --skip-*
    "pipeline_seq_full": lambda: run_pipeline_case([], "footest|foo/bar|Go|Raft demo"),
    "pipeline_seq_resume": lambda: run_pipeline_case(
        ["--skip-analysis", "--skip-specgen", "--skip-harness"],
        "footest|foo/bar|Go|Raft demo",
    ),
    "pipeline_seq_skip_repair": lambda: run_pipeline_case(["--skip-repair-loop"], "footest|foo/bar|Go|Raft demo"),
    # reviews are disabled by default — this is the only case exercising run_review's
    # enabled branch (REVIEW banners + launch_review.sh command lines)
    "pipeline_seq_reviews": lambda: run_pipeline_case(["--enable-reviews"], "footest|foo/bar|Go|Raft demo"),
    # step 3 target: downstream-phase precondition gates (input contract each enforces)
    "gate_spec_generation": lambda: run_dryrun_case(
        "launch_spec_generation.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False
    ),
    "gate_harness_generation": lambda: run_dryrun_case(
        "launch_harness_generation.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False
    ),
    "gate_spec_validation": lambda: run_dryrun_case(
        "launch_spec_validation.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False
    ),
    "gate_bug_confirmation": lambda: run_dryrun_case(
        "launch_bug_confirmation.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False
    ),
    "gate_bug_classification": lambda: run_dryrun_case(
        "launch_bug_classification.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False, use_artifact=False
    ),
    # --check success path: per-phase OK message ("All repos OK." for code_analysis,
    # "All prerequisites OK." for the rest — bash wording restored)
    "check_ok_code_analysis": lambda: run_dryrun_case(
        "launch_code_analysis.sh", "footest|foo/bar|Go|Raft demo", snapshot_prompt=False, check_only=True
    ),
    "check_ok_spec_generation": lambda: run_dryrun_case(
        "launch_spec_generation.sh",
        "footest",
        seed={".specula-output/modeling-brief.md": "# Modeling Brief\n"},
        snapshot_prompt=False,
        check_only=True,
    ),
    # --help: full usage text (the bash header comment) for every launcher;
    # review needs a phase arg before --help (bash parsed $1 as the phase)
    "help_code_analysis": lambda: run_help_case("launch_code_analysis.sh"),
    "help_spec_generation": lambda: run_help_case("launch_spec_generation.sh"),
    "help_harness_generation": lambda: run_help_case("launch_harness_generation.sh"),
    "help_bug_classification": lambda: run_help_case("launch_bug_classification.sh"),
    "help_spec_validation": lambda: run_help_case("launch_spec_validation.sh"),
    "help_bug_confirmation": lambda: run_help_case("launch_bug_confirmation.sh"),
    "help_review": lambda: run_help_case("launch_review.sh", pre_args=["analysis"]),
    "help_pipeline": lambda: run_help_case("launch_pipeline.sh"),
    # step 3 target: post-launch summary path — summarize()'s populated branch
    # (OK/~~/written lines counting .md/.tla via wc -l) + per-phase Monitor hint,
    # neither reached by dry-run/gate. Full run with a faked agent + seeded outputs.
    "summary_code_analysis": lambda: run_summary_case(
        "launch_code_analysis.sh", "footest|foo/bar|Go|Raft demo", _SUMMARY_CODE_ANALYSIS
    ),
    "summary_spec_generation": lambda: run_summary_case(
        "launch_spec_generation.sh", "footest", _SUMMARY_SPEC_GENERATION
    ),
    "summary_harness_generation": lambda: run_summary_case("launch_harness_generation.sh", "footest", _SUMMARY_HARNESS),
    "summary_bug_classification": lambda: run_summary_case(
        "launch_bug_classification.sh", "footest", _SUMMARY_BUG_CLASSIFICATION, use_artifact=False
    ),
    "summary_spec_validation": lambda: run_summary_case(
        "launch_spec_validation.sh", "footest", _SUMMARY_SPEC_VALIDATION
    ),
    "summary_bug_confirmation": lambda: run_summary_case(
        "launch_bug_confirmation.sh", "footest", _SUMMARY_BUG_CONFIRMATION
    ),
    # summarize must count a non-UTF-8 output file by bytes like wc -l and never
    # crash: \xff pins the no-crash half (strict read_text() raises), and the
    # missing trailing newline pins the counting half ('2 lines' = newline count;
    # a splitlines-based regression would report 3) (F3)
    "summary_code_analysis_nonutf8": lambda: run_summary_case(
        "launch_code_analysis.sh",
        "footest|foo/bar|Go|Raft demo",
        {".specula-output/modeling-brief.md": b"# Modeling Brief\n\xff\nfamily A"},
    ),
    # step 5 target: repair-loop state-machine primitives (rr_set_status mutator)
    "repair_state_machine": run_repair_case,
    # step 5 target: quota gate decision table (5h-before-7d, strict >, over->bounded wait)
    "quota_under": lambda: run_quota_case(
        '{"five_hour":{"utilization":50,"resets_at":"2099-01-01T00:00:00+00:00"},'
        '"seven_day":{"utilization":50,"resets_at":"2099-01-08T00:00:00+00:00"}}',
        q5=85,
        q7=95,
    ),
    "quota_over_5h": lambda: run_quota_case(
        '{"five_hour":{"utilization":86,"resets_at":"2099-01-01T00:00:00+00:00"},'
        '"seven_day":{"utilization":50,"resets_at":"2099-01-08T00:00:00+00:00"}}',
        q5=85,
        q7=95,
    ),
    "quota_over_7d": lambda: run_quota_case(
        '{"five_hour":{"utilization":50,"resets_at":"2099-01-01T00:00:00+00:00"},'
        '"seven_day":{"utilization":96,"resets_at":"2099-01-08T00:00:00+00:00"}}',
        q5=85,
        q7=95,
    ),
    # utilization exactly AT the threshold is not over (strict >)
    "quota_at_limit": lambda: run_quota_case(
        '{"five_hour":{"utilization":85,"resets_at":"2099-01-01T00:00:00+00:00"},'
        '"seven_day":{"utilization":95,"resets_at":"2099-01-08T00:00:00+00:00"}}',
        q5=85,
        q7=95,
    ),
    # usage script exits non-zero -> WARN fetch failed + proceed
    "quota_fetch_fail": lambda: run_quota_case("", q5=85, q7=95, fetch_fail=True),
    # usage output isn't JSON -> WARN parse failed + proceed
    "quota_malformed_json": lambda: run_quota_case("not json {", q5=85, q7=95),
    # over-limit with NO resets_at -> the fixed 600s wait branch (recorded sleep)
    "quota_no_resets_at": lambda: run_quota_case(
        '{"five_hour":{"utilization":86},"seven_day":{"utilization":50}}',
        q5=85,
        q7=95,
        record_sleep=True,
    ),
    # resets_at in the past -> negative wait, clamped to the 60s floor (recorded sleep)
    "quota_resets_past": lambda: run_quota_case(
        '{"five_hour":{"utilization":86,"resets_at":"2000-01-01T00:00:00+00:00"},'
        '"seven_day":{"utilization":50,"resets_at":"2000-01-08T00:00:00+00:00"}}',
        q5=85,
        q7=95,
        record_sleep=True,
    ),
    # step 5 target: rr_field/rr_set_status edge behaviors (25-line window,
    # missing trailing newline, duplicate status lines)
    "repair_rr_edges": run_repair_edges_case,
    # step 5 target: single-target cd branch — summary in the case dir,
    # pipeline.log in the launch cwd, quota silent when usage.sh is absent
    "pipeline_single_target_cd": run_pipeline_cd_case,
    "pipeline_default_isolate": run_pipeline_default_isolate_case,
    # step 5 target: full pipeline run (fake agent, all phases) — the tee into
    # pipeline.log, set -e sequencing, generate_summary's populated branches
    "pipeline_full_run": lambda: run_pipeline_full_case([], "footest|foo/bar|Go|Raft demo", _PIPELINE_FULL_SEED),
    # step 5 target: repair loop live round — crash-recovery reset (IN_REPAIR ->
    # OPEN), one repair+recheck round, no-progress stop, regenerated ledger
    "pipeline_repair_loop": lambda: run_pipeline_full_case(
        [*_REPAIR_LOOP_SKIPS, "--max-repair-rounds=2"],
        "footest|foo/bar|Go|Raft demo",
        _REPAIR_LOOP_SEED,
        snapshot_files=_RR_SNAPSHOT_FILES,
    ),
    # step 5 target: repair loop with only terminal requests — 0 rounds, summary
    # tallies resolved/deferred via the status grep
    "pipeline_repair_all_terminal": lambda: run_pipeline_full_case(
        _REPAIR_LOOP_SKIPS,
        "footest|foo/bar|Go|Raft demo",
        {
            **_CONFIRMATION_SEED,
            ".specula-output/spec/repair-requests/RR-001.md": _rr_fixture("RR-001", "RESOLVED"),
            ".specula-output/spec/repair-requests/RR-002.md": _rr_fixture(
                "RR-002", "DEFERRED", bug_id="DA-27 | ordering", round_=3
            ),
        },
        snapshot_files=[".specula-output/spec/repair-ledger.md"],
    ),
    # step 6 target: scheduler --help (originally the bash header comment via
    # sed; the cutover dropped the advertised-but-never-implemented per-task
    # prompt_file queue column and documents the per-task isolation)
    "help_scheduler": lambda: run_scheduler_case("", ["--help"]),
    # step 6 target: argument/queue error contract
    "sched_err_unknown_flag": lambda: run_scheduler_case("footest|foo/bar|Go|r\n", ["--bogus"]),
    "sched_err_missing_queue": lambda: run_scheduler_case(
        "", ["--queue", "/nonexistent/tasks.queue", "--workers", "1"]
    ),
    "sched_empty_queue": lambda: run_scheduler_case("# only a comment\n\n", ["--workers", "1"]),
    # step 6 target: dry-run lifecycle — banner, setup phase (and the second
    # setup_task call inside run_task: the DRY-RUN clone/cp lines repeat), the
    # exact launch_pipeline.sh command lines (per-task --run-id isolation, flags
    # word-split from the queue, --claude-alias/--max-turns forwarding),
    # relative --prompt resolution, dry-run status files, and the summary's DRY
    # rows (counted in no tally: Success=0 Failed=0 Skipped=0)
    "sched_dryrun_full": lambda: run_scheduler_case(
        "# nightly batch\nfootest|foo/bar|Go|Raft demo\t--skip-analysis --skip-specgen\nbartest|baz/qux|Rust|Paxos notes\n",
        ["--dry-run", "--workers", "1", "--max-turns", "7", "--claude-alias", "myalias"],
        prompt="Verify liveness.\n",
    ),
    # queue-parsing edges: comments (indented too), a tabs-only line is blank
    # (cutover fix: under bash it became a phantom task with an empty name), a
    # third tab column folds into the pipeline flags (the per-task prompt_file
    # column was never implemented), a no-pipe target passes through whole,
    # multiple flags survive word-splitting
    "sched_queue_variants": lambda: run_scheduler_case(
        "  # indented comment\n"
        "\t\t\n"
        "alpha|a/b|Go|ref\t--flag-one --flag-two=x\tthird-col.md\n"
        "beta|c/d|Rust|r2\n"
        "gamma-no-pipes\n",
        ["--dry-run", "--workers", "1"],
    ),
    # --setup-only, real mode: pre-seeded .git dir skips the clone, --prompt is
    # actually copied into case-studies/<name>/.prompt-extra.md, no worker runs
    "sched_setup_only": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--setup-only", "--workers", "1"],
        seed=_SCHED_SEED_2,
        prompt="Check the election safety property.\n",
        snapshot=["case-studies/footest/.prompt-extra.md"],
    ),
    # full real-mode lifecycle, 1 worker (deterministic ordering): START/DONE per
    # task, per-task success status, summary tallies, and the fake pipeline's
    # marker pinning the exact argv + the QUOTA_5H/7D env forwarded from
    # --threshold/--threshold-7day
    "sched_full_run": lambda: run_scheduler_case(
        _SCHED_QUEUE_2,
        ["--workers", "1", "--threshold", "70", "--threshold-7day", "90"],
        pipeline_script=_SCHED_PIPELINE_OK,
        seed=_SCHED_SEED_2,
        snapshot=["pipeline-calls.txt"],
    ),
    # transient API failure -> RETRY with 180s*attempt backoff -> success on
    # attempt 2 (the task log grep branch)
    "sched_retry_transient": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--workers", "1"],
        pipeline_script=_SCHED_PIPELINE_FLAKY,
        seed=_SCHED_SEED_2,
        record_sleeps=True,
    ),
    # the agent.log transient probe reads the isolated run's real phase-1 log
    # (the fake pipeline writes it via its --run-id, proving scheduler and
    # pipeline agree on the path): silent exit-1 becomes retries; attempt 3 is
    # transient too but not retried (attempt < max_retries), FAIL at attempt 3,
    # scheduler still exits 0 (task failures never affect the exit code)
    "sched_retry_agentlog_exhaust": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--workers", "1"],
        pipeline_script=_SCHED_PIPELINE_AGENTLOG,
        seed=_SCHED_SEED_2,
        record_sleeps=True,
    ),
    # non-transient failure: no retry, FAIL at attempt 1, Failed=1, exit 0
    "sched_fail_nontransient": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--workers", "1"],
        pipeline_script='#!/usr/bin/env bash\necho "boom"; exit 1\n',
        seed=_SCHED_SEED_2,
    ),
    # step 6 target: quota gate. Over 5h with a past resets_at -> negative wait
    # clamped to the 60s floor, one reset consumed, then proceeds
    "sched_quota_wait_past_reset": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--dry-run", "--workers", "1", "--windows", "3"],
        usage_script=_SCHED_USAGE_OVER_ONCE.replace("@OVER@", _SCHED_OVER_5H_PAST),
        record_sleeps=True,
    ),
    # over with NO resets_at -> the fixed 600s branch ("no reset time")
    "sched_quota_no_reset_time": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--dry-run", "--workers", "1", "--windows", "3"],
        usage_script=_SCHED_USAGE_OVER_ONCE.replace("@OVER@", _SCHED_OVER_5H_NORESET),
        record_sleeps=True,
    ),
    # --windows 0 and permanently over: the first over-detection exhausts the
    # budget — never sleeps, drains, task left not-started (Skipped), exit 0
    "sched_quota_exhaust": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--dry-run", "--workers", "1", "--windows", "0"],
        usage_json=_SCHED_OVER_5H_PAST,
        record_sleeps=True,
    ),
    # usage.sh missing entirely -> "WARN: usage fetch failed" + proceed
    "sched_quota_fetch_fail": lambda: run_scheduler_case(
        "footest|foo/bar|Go|Raft demo\n",
        ["--dry-run", "--workers", "1"],
        usage_json=None,
    ),
}


# ── driver ──────────────────────────────────────────────────────────────────
def golden_path(name: str) -> Path:
    return GOLDEN_DIR / f"{name}.txt"


def cmd_update(names: list[str]) -> int:
    GOLDEN_DIR.mkdir(parents=True, exist_ok=True)
    for name in names:
        snap = CASES[name]()
        golden_path(name).write_text(snap)
        print(f"  updated  {name}  ({len(snap.splitlines())} lines)")
    return 0


def cmd_check(names: list[str]) -> int:
    # Cases are hermetic (own tempdir + _clean_env), so they run concurrently;
    # results are reported in registry order. Subprocess-bound: ~10x wall-time win.
    def _run(name: str) -> tuple[str, str | None, str | None]:
        gp = golden_path(name)
        if not gp.exists():
            return name, None, None
        return name, CASES[name](), gp.read_text()

    with ThreadPoolExecutor(max_workers=min(12, os.cpu_count() or 4)) as ex:
        results = list(ex.map(_run, names))

    failed = 0
    for name, actual, expected in results:
        if expected is None:
            print(f"  MISSING GOLDEN  {name}  (run --update)")
            failed += 1
        elif actual == expected:
            print(f"  ok       {name}")
        else:
            failed += 1
            print(f"  FAIL     {name}")
            # actual is None only when expected is None (handled above), so both are str.
            assert actual is not None
            diff = difflib.unified_diff(
                expected.splitlines(),
                actual.splitlines(),
                fromfile=f"golden/{name}.txt",
                tofile="actual",
                lineterm="",
            )
            for line in diff:
                print("    " + line)
    print(f"\n{len(names) - failed}/{len(names)} passed")
    return 1 if failed else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--check", action="store_true", help="diff vs golden (default)")
    g.add_argument("--update", action="store_true", help="(re)write golden snapshots")
    g.add_argument("--list", action="store_true", help="list case names")
    ap.add_argument("-k", metavar="SUBSTR", help="only cases whose name contains SUBSTR")
    args = ap.parse_args()

    # -k matching an exact case name selects only that case (several case names
    # are substrings of others, e.g. dryrun_code_analysis[_hidden_repo] — plain
    # substring matching could silently --update a sibling's golden too)
    names = [args.k] if args.k and args.k in CASES else [n for n in CASES if not args.k or args.k in n]
    if not names:
        print(f"no cases match -k {args.k!r}", file=sys.stderr)
        return 2

    if args.list:
        for n in names:
            print(n)
        return 0
    if args.update:
        return cmd_update(names)
    return cmd_check(names)


if __name__ == "__main__":
    raise SystemExit(main())
