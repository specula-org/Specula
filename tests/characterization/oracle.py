#!/usr/bin/env python3
"""Characterization oracle for the Specula bash orchestration layer.

This is migration **step 0**: it pins the *current* behavior of the bash
launchers/adapters as normalized golden snapshots, so the Python rewrites
(steps 1/3/5/6) can be diffed against a fixed baseline ("did my Python behave
like the bash it replaced?").

Deliberately stdlib-only (no pytest/pip needed) — the repo `.venv` is corrupted
(see memory reference_broken_venv_pytest); step 2 wires this into pytest/CI.

Usage:
    python3 tests/characterization/oracle.py --check     # diff vs golden (default; exit 1 on mismatch)
    python3 tests/characterization/oracle.py --update     # (re)write golden snapshots
    python3 tests/characterization/oracle.py --list       # list case names
    python3 tests/characterization/oracle.py --check -k adapter   # filter by substring

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
from pathlib import Path

HERE = Path(__file__).resolve().parent
GOLDEN_DIR = HERE / "golden"
FIXTURES = HERE / "fixtures"
# tests/characterization/ -> tests/ -> repo root
SPECULA_ROOT = HERE.parent.parent
LAUNCH = SPECULA_ROOT / "scripts" / "launch"
ADAPTER = LAUNCH / "adapters" / "claude-code.sh"
ADAPTER_PY = LAUNCH / "adapters" / "claude_code.py"


def _adapter_cmd() -> list[str]:
    """Which adapter implementation the adapter cases exercise. Controlled by
    SPECULA_ADAPTER_IMPL:
      unset/other → the installed adapter (`claude-code.sh`, now a shim to python)
      "python"    → run the Python port directly (parity check)
      <a path>    → run `bash <path>` (e.g. the pre-cutover bash original, to
                    capture ground-truth goldens or re-verify parity against it)."""
    impl = os.environ.get("SPECULA_ADAPTER_IMPL", "")
    if impl == "python":
        return ["python3", str(ADAPTER_PY)]
    if impl and os.path.exists(impl):
        return ["bash", impl]
    return ["bash", str(ADAPTER)]


PHASELIB = LAUNCH / "phaselib.py"


def _launcher_cmd(script: str) -> list[str]:
    """Which phase-launcher implementation the dry-run/gate cases exercise. Default:
    the bash launcher (or its shim). SPECULA_LAUNCHER_IMPL=python runs phaselib.py
    with the phase key derived from the script name (launch_<key>.sh -> <key>) — the
    step-3 parity check against the bash-captured goldens."""
    if os.environ.get("SPECULA_LAUNCHER_IMPL") == "python":
        key = script[len("launch_") : -len(".sh")]
        return ["python3", str(PHASELIB), key]
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
    # ISO-8601 datetimes (date -Iseconds) -> <DATE>
    line = re.sub(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:[+-]\d{2}:\d{2}|Z)?", "<DATE>", line)
    # "completed in 0m 1s" elapsed -> <ELAPSED>
    line = re.sub(r"completed in \d+m \d+s", "completed in <ELAPSED>", line)
    # quota gate "sleeping 12345s" (now-relative) -> <SECS>
    line = re.sub(r"sleeping \d+s", "sleeping <SECS>s", line)
    return line


# ── helpers ─────────────────────────────────────────────────────────────────
def _clean_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    """A predictable env: system python (no broken venv .pth noise), no
    ambient Claude config that could redirect the adapter."""
    env = dict(os.environ)
    for var in (
        "VIRTUAL_ENV",
        "CLAUDE_CONFIG_DIR",
        "CLAUDECODE",
        "CLAUDE_CODE_SSE_PORT",
        "CLAUDE_CODE_ENTRYPOINT",
        # popped so command construction is deterministic regardless of ambient env
        "CLAUDE_EFFORT",
        "CLAUDE_MODEL",
        "CLAUDE_ALIAS",
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
        # record the prompt on stdin (for review, which passes it inline); drains
        # to /dev/null when CLAUDE_STDIN_FILE is unset, so other cases are unaffected.
        'cat > "${CLAUDE_STDIN_FILE:-/dev/null}"\n'
        f"cat {json.dumps(str(fixture))}\n"
    )
    stub.chmod(stub.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)


def _init_git_repo(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init", "-q", str(path)], check=True, env=_clean_env())


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
        # PATH override (no ambient dirs appended) so `claude` presence is controlled:
        # with_claude=True → fake claude on PATH; False → only /usr/bin:/bin (no claude).
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


def run_adapter_cmd_case(flags: list[str]) -> str:
    """Pin command construction: snapshot the exact argv the adapter passes to
    `claude` for a given flag combo (--effort/--model/--max-budget assembly, incl.
    the skip-on-default/zero/empty branches). The fake `claude` records its args."""
    fixture = FIXTURES / "claude_normal.json"
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, fixture)
        prompt = base / "prompt.md"
        prompt.write_text("dummy prompt\n")
        argv_file = base / "claude_argv.txt"
        env = _clean_env(
            {
                "PATH": f"{bindir}:/usr/bin:/bin",
                "HOME": str(base),
                "CLAUDE_ARGV_FILE": str(argv_file),
            }
        )
        subprocess.run(
            _adapter_cmd() + [f"--prompt-file={prompt}", "--claude-alias=testalias", f"--log={base}/out.log", *flags],
            cwd=str(base),
            env=env,
            capture_output=True,
            text=True,
        )
        argv = argv_file.read_text() if argv_file.exists() else "<MISSING>"
        return normalize(f"=== claude argv ===\n{argv}", {str(base): "<TMP>"})


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
    seed: dict[str, str] | None = None,
    prompt_rel: str = ".specula-output/.prompt.md",
    use_artifact: bool = True,
    extra_flags: list[str] | None = None,
) -> str:
    """Run a phase launcher with --dry-run in an isolated cwd; snapshot stdout plus
    the generated prompt file (the exact prompt handed to the agent).

    seed: files to create under the work cwd first (relpath -> content) so a
    downstream phase's prerequisites are satisfied and it reaches the dry-run
    print (e.g. seed modeling-brief.md for spec_generation).
    prompt_rel: where this phase writes its prompt (spec_generation uses
    .spec-gen-prompt.md, not .prompt.md).
    use_artifact: pass --artifact (bug_classification takes none).
    extra_flags: phase-specific flags (validation --repair; confirmation --recheck)."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        work = tmp / "work"
        work.mkdir()
        for rel, content in (seed or {}).items():
            f = work / rel
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(content)
        env = _clean_env({"HOME": str(tmp)})
        cmd = _launcher_cmd(script) + ["--dry-run", *(extra_flags or [])]
        subs = {str(work): "<WORK>", str(tmp): "<TMP>"}
        if use_artifact:
            artifact = tmp / "artifact"
            _init_git_repo(artifact)
            cmd.append(f"--artifact={artifact}")
            subs[str(artifact)] = "<ARTIFACT>"
        cmd.append(target)
        proc = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True)
        parts = [f"exit_code: {proc.returncode}", "", "=== stdout ===", proc.stdout, ""]
        prompt = work / prompt_rel
        parts.append(f"=== {prompt.name} ===")
        parts.append(prompt.read_text() if prompt.exists() else "<MISSING>")
        parts.append("")
        raw = normalize("\n".join(parts), subs)
    return raw


def run_review_case(phase: str) -> str:
    """Pin the review launcher, which has no --dry-run (it always spawns an agent).
    Run it with a fake `claude` that records the inline prompt it receives on stdin,
    and snapshot stdout (banner / per-name lines / summary) + that captured prompt."""
    fixture = FIXTURES / "claude_normal.json"
    with tempfile.TemporaryDirectory() as td:
        base = Path(td).resolve()
        bindir = base / "bin"
        _write_fake_claude(bindir, fixture)
        work = base / "work"
        work.mkdir()
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
        return normalize("\n".join(parts), {str(work): "<WORK>", str(base): "<TMP>"})


def run_gate_case(script: str, target: str, use_artifact: bool = True) -> str:
    """Run a downstream phase launcher --dry-run with NO prior-phase outputs, to
    pin its precondition gate — the input contract each phase enforces before it
    will run (exit code + the 'Missing prerequisites' message step 3 must keep)."""
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        work = tmp / "work"
        work.mkdir()
        args = _launcher_cmd(script) + ["--dry-run"]
        subs = {str(work): "<WORK>", str(tmp): "<TMP>"}
        if use_artifact:
            artifact = tmp / "artifact"
            _init_git_repo(artifact)
            args.append(f"--artifact={artifact}")
            subs[str(artifact)] = "<ARTIFACT>"
        args.append(target)
        env = _clean_env({"HOME": str(tmp)})
        proc = subprocess.run(args, cwd=work, env=env, capture_output=True, text=True)
        return normalize(f"exit_code: {proc.returncode}\n\n=== stdout ===\n{proc.stdout}\n", subs)


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
_VALIDATION_SEED = {
    ".specula-output/spec/base.tla": "---- MODULE base ----\nx == 1\n====\n",
    ".specula-output/spec/MC.tla": "---- MODULE MC ----\n====\n",
    ".specula-output/spec/Trace.tla": "---- MODULE Trace ----\n====\n",
    ".specula-output/spec/instrumentation-spec.md": "# instrumentation\n",
}
_CONFIRMATION_SEED = {
    ".specula-output/spec/bug-report.md": "# Bug Report\n\n## MC-1: something\n",
    ".specula-output/modeling-brief.md": "# Modeling Brief\n",
}


# ── case registry ───────────────────────────────────────────────────────────
# name -> zero-arg callable returning the normalized snapshot string.
CASES: dict[str, callable] = {
    # step 1 target: adapter post-processing (JSON -> .log/.usage.json, exit codes)
    "adapter_normal": lambda: run_adapter_case("claude_normal.json"),
    "adapter_ratelimit": lambda: run_adapter_case("claude_ratelimit.json"),
    "adapter_malformed": lambda: run_adapter_case("claude_malformed.txt"),
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
    # step 5 target: launch_pipeline.sh phase sequencing + repair-loop gating under --skip-*
    "pipeline_seq_full": lambda: run_pipeline_case([], "footest|foo/bar|Go|Raft demo"),
    "pipeline_seq_resume": lambda: run_pipeline_case(
        ["--skip-analysis", "--skip-specgen", "--skip-harness"],
        "footest|foo/bar|Go|Raft demo",
    ),
    "pipeline_seq_skip_repair": lambda: run_pipeline_case(["--skip-repair-loop"], "footest|foo/bar|Go|Raft demo"),
    # step 3 target: downstream-phase precondition gates (input contract each enforces)
    "gate_spec_generation": lambda: run_gate_case("launch_spec_generation.sh", "footest|foo/bar|Go|Raft demo"),
    "gate_harness_generation": lambda: run_gate_case("launch_harness_generation.sh", "footest|foo/bar|Go|Raft demo"),
    "gate_spec_validation": lambda: run_gate_case("launch_spec_validation.sh", "footest|foo/bar|Go|Raft demo"),
    "gate_bug_confirmation": lambda: run_gate_case("launch_bug_confirmation.sh", "footest|foo/bar|Go|Raft demo"),
    "gate_bug_classification": lambda: run_gate_case(
        "launch_bug_classification.sh", "footest|foo/bar|Go|Raft demo", use_artifact=False
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
    failed = 0
    for name in names:
        gp = golden_path(name)
        if not gp.exists():
            print(f"  MISSING GOLDEN  {name}  (run --update)")
            failed += 1
            continue
        actual = CASES[name]()
        expected = gp.read_text()
        if actual == expected:
            print(f"  ok       {name}")
        else:
            failed += 1
            print(f"  FAIL     {name}")
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

    names = [n for n in CASES if not args.k or args.k in n]
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
