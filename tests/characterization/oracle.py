"""Characterization oracle for the Specula bash orchestration layer.

This is migration **step 0**: it pins the *current* behavior of the bash
launchers/adapters as normalized golden snapshots, so the Python rewrites
(steps 1/3/5/6) can be diffed against a fixed baseline ("did my Python behave
like the bash it replaced?").

Stdlib-only (no pytest/pip needed), so it runs under any `python3`; the pytest
wrapper (test_characterization.py) exposes the same cases to CI.

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
import stat
import subprocess
import sys
import tempfile
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

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


PHASELIB = LAUNCH / "phaselib.py"


def _launcher_cmd(script: str) -> list[str]:
    """Which phase-launcher implementation the dry-run/gate/summary cases exercise:
    unset/other → the installed launcher (`launch_<phase>.sh`, now a shim to python)
    "python"    → run phaselib.py directly with the phase key from the script name
                  (launch_<key>.sh -> <key>) — the step-3 parity check.
    <a path>    → run `bash <path>` (e.g. a pre-cutover bash launcher materialized
                  under scripts/launch/, to capture ground-truth goldens or
                  re-verify parity against the bash). Run one case at a time in
                  this mode, since the path overrides the script for every case."""
    impl = os.environ.get("SPECULA_LAUNCHER_IMPL", "")
    if impl == "python":
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
        env = _clean_env(
            {"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(base), "CLAUDE_STDIN_FILE": str(stdin_file)}
        )
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
        env = _clean_env(
            {"PATH": f"{bindir}:/usr/bin:/bin", "HOME": str(base), "GIT_CEILING_DIRECTORIES": str(base)}
        )
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
    network); dry-run prints each phase's command instead of launching agents."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        artifact = tmp / "artifact"
        _init_git_repo(artifact)
        work = tmp / "work"
        work.mkdir()
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(
            [
                "bash",
                str(LAUNCH / "launch_pipeline.sh"),
                "--dry-run",
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


def _pipeline_functions_only() -> str:
    """launch_pipeline.sh with the trailing `main` invocation stripped, so it can
    be sourced to expose the repair-loop helper functions without running the
    whole pipeline. The top-level `mkdir .specula-output` that remains runs
    harmlessly inside the test's tmp cwd."""
    src = (LAUNCH / "launch_pipeline.sh").read_text().splitlines(keepends=True)
    cut = next((i for i, ln in enumerate(src) if ln.startswith("main 2>&1")), len(src))
    return "".join(src[:cut])


_RR_FIXTURE = """\
---
id: RR-001
bug_id: DA-1 | agreement safety violated
target: base.tla
status: OPEN
round: 1
---

# Repair Request RR-001

The spec models the QC without binding it to the proposal value.

## History
- created (bug confirmation): QC reuse enables value forgery
"""

# Drives the sourced repair helpers through a real OPEN -> IN_REPAIR -> RESOLVED
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


def run_repair_case() -> str:
    """Characterize the repair-loop state-machine primitives (rr_field / rr_status
    / rr_set_status) — the atomic ops step 5 must reimplement, incl. the embedded
    python mutator that rewrites `status:` and appends a History bullet."""
    fnonly_src = _pipeline_functions_only()
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        fnonly = tmp / "pipeline_fnonly.sh"
        fnonly.write_text(fnonly_src)
        rr = tmp / "RR-001.md"
        rr.write_text(_RR_FIXTURE)
        driver = tmp / "driver.sh"
        driver.write_text(_REPAIR_DRIVER.replace("@FNONLY@", str(fnonly)).replace("@RR@", str(rr)))
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(["bash", str(driver)], cwd=tmp, env=env, capture_output=True, text=True)
        out = f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n"
        if proc.stderr.strip():
            out += f"\n=== stderr ===\n{proc.stderr}\n"
        return normalize(out, {str(rr): "<RR>", str(fnonly): "<FNONLY>", str(tmp): "<TMP>"})


# Drives the sourced wait_for_quota with a stubbed usage source + stubbed sleep,
# so the real decision logic runs on fixed input without network or blocking.
# QUOTA_MAX_WAITS=1 → one "over" detection then bounded abort.
_QUOTA_DRIVER = """\
#!/usr/bin/env bash
set --
source "@FNONLY@"
set +euo pipefail
USAGE_SCRIPT="@FAKEUSAGE@"          # override the real credentialed usage.sh
QUOTA_5H=@Q5@; QUOTA_7D=@Q7@; QUOTA_MAX_WAITS=1
sleep() { :; }                       # stub: never actually block
wait_for_quota
echo "wait_for_quota returned: $?"   # only reached on the 'ok' (proceed) path
"""


def run_quota_case(usage_json: str, q5: int, q7: int) -> str:
    """Characterize the quota gate's decision on a fixed usage snapshot: 5h is
    checked before 7d, strictly `>` threshold, over→WAIT (bounded by MAX_WAITS
    then abort), fetch-error→proceed. The two-layer QUOTA_5H/QUOTA_7D env is the
    known step-5 landmine this pins."""
    fnonly_src = _pipeline_functions_only()
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        fnonly = tmp / "pipeline_fnonly.sh"
        fnonly.write_text(fnonly_src)
        fake_usage = tmp / "fake_usage.sh"
        fake_usage.write_text("#!/usr/bin/env bash\ncat <<'JSON'\n" + usage_json + "\nJSON\n")
        fake_usage.chmod(0o755)
        driver = tmp / "driver.sh"
        driver.write_text(
            _QUOTA_DRIVER.replace("@FNONLY@", str(fnonly))
            .replace("@FAKEUSAGE@", str(fake_usage))
            .replace("@Q5@", str(q5))
            .replace("@Q7@", str(q7))
        )
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(["bash", str(driver)], cwd=tmp, env=env, capture_output=True, text=True)
        out = f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n"
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
