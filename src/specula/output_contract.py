"""Output contract of a continuous main session.

In continuous orchestration one agent session writes every Phase 1-3 output,
so the confirmation handoff requires only what Specula's code or a later agent
reads as input. The other files the stage skills describe are recommendations:
the agent writes them when they help it or a later reader. Phased
orchestration keeps the full contract, because there those files are the
hand-off medium between separate agents.

Required, with their consumers:

- ``modeling-brief.md``: confirmation step 0 merges its code-review Scenarios
  (``confirmlib.consolidate``); the confirmation launcher's check requires it.
- ``spec/base.tla``, ``spec/MC.tla``, ``spec/Trace.tla``: the model that
  confirmation binds verdicts to, the repair rounds re-check, and the summary
  reports; MC and Trace extend base.
- ``spec/MC.cfg``, ``spec/Trace.cfg``: the configurations model checking and
  trace validation run, including the full trace re-validation of a repair.
- ``harness/run.sh``: trace re-collection and the trace re-validation of
  repairs.
- ``spec/bug-report.md`` and ``spec/findings.json``: the confirmation inputs;
  ``findings.json`` must pass the dispatcher's own MC-input validation.

Each file must be non-empty and each required module must parse with SANY.
Traces are expected whenever the harness can run, but, as in phased mode, a
handoff without them is accepted: the gap becomes a validation limit of the
target's summary instead of failing a target whose model checking and
code-review candidates are still worth confirming. ``SPECULA_STRICT_OUTPUTS=on`` restores
the full contract for ablation: the prompt lists every phase output as
required and the handoff requires each of them. A run keeps the value it was
created with (see ``pipelinelib``).

SANY runs the way the rest of Specula runs the TLA+ tools: ``java`` from
``PATH`` with ``lib/tla2tools.jar`` (plus ``lib/CommunityModules-deps.jar``)
from this Specula tree, else from ``$SPECULA_ROOT`` (as in
``scripts/tlc/run_model_check.sh``), in the spec directory, as the trace
debugger's ``validate_spec_syntax`` tool does.
"""

from __future__ import annotations

import os
import re
import shlex
import shutil
import subprocess
import tempfile
from pathlib import Path

STRICT_ENV = "SPECULA_STRICT_OUTPUTS"
_OFF_VALUES = frozenset({"0", "false", "no", "off"})

# The continuous controller's per-target state; only continuous runs have it.
MAIN_STATE_FILE = ".context-control/main-state.json"

SPEC_FILES = ("spec/base.tla", "spec/MC.tla", "spec/MC.cfg", "spec/Trace.tla", "spec/Trace.cfg")
SANY_MODULES = ("spec/base.tla", "spec/MC.tla", "spec/Trace.tla")
TRACES_DIR = "traces"
REQUIRED_FILES = (
    "modeling-brief.md",
    *SPEC_FILES,
    "harness/run.sh",
    "spec/bug-report.md",
    "spec/findings.json",
)
# Files the stage skills describe that no consumer reads in continuous mode.
ADVISORY_FILES = (
    "analysis-report.md",
    "spec/base.cfg",
    "spec/brief-coverage.md",
    "spec/instrumentation-spec.md",
    "harness/apply.sh",
    "harness/INSTRUMENTATION.md",
    "spec/changelog.md",
)
ADVISORY_DIRS = ("harness/src",)

_HINTS = {
    "modeling-brief.md": "the code-analysis skill's modeling brief; confirmation reads its code-review Scenarios",
    "spec/base.tla": "the base specification",
    "spec/MC.tla": "the model-checking specification",
    "spec/MC.cfg": "the model-checking configuration",
    "spec/Trace.tla": "the trace-validation specification",
    "spec/Trace.cfg": "the trace-validation configuration",
    "harness/run.sh": "the one-command script that builds the instrumented code, runs it, and collects traces",
    "spec/bug-report.md": "the bug-hunting report, also when model checking found nothing",
    "spec/findings.json": 'the findings index (`"findings": []` when model checking found nothing)',
    # Required only with SPECULA_STRICT_OUTPUTS=on.
    "analysis-report.md": "the code-analysis audit trail",
    "spec/base.cfg": "the base configuration",
    "spec/brief-coverage.md": "the spec-generation brief-coverage audit",
    "spec/instrumentation-spec.md": "the instrumentation mapping",
    "harness/apply.sh": "the script that applies the instrumentation",
    "harness/INSTRUMENTATION.md": "the guide for adjusting the instrumentation",
    "spec/changelog.md": "the validation changelog",
}
TRACES_LIMIT = (
    "No execution traces were collected, so trace validation did not compare the model with the "
    "implementation; spec/bug-report.md records why."
)
SANY_TIMEOUT_S = 120
_SANY_ERRORS = re.compile(r"^\*\*\* Errors: *[1-9]|^Semantic errors:", re.MULTILINE)
_SANY_NOISE = ("Parsing file ", "Semantic processing of module ", "Linting of module ", "****** SANY")
_ROOT = Path(__file__).resolve().parents[2]


class SanyUnavailable(RuntimeError):
    """SANY cannot run here, so the required modules cannot be checked."""


def strict() -> bool:
    """Whether ``SPECULA_STRICT_OUTPUTS`` restores the full contract (default off)."""
    value = os.environ.get(STRICT_ENV, "").strip().lower()
    return bool(value) and value not in _OFF_VALUES


def required_files(*, strict: bool) -> tuple[str, ...]:
    return REQUIRED_FILES + ADVISORY_FILES if strict else REQUIRED_FILES


def _has_content(path: Path) -> bool:
    try:
        return path.is_file() and bool(path.read_text(errors="replace").strip())
    except OSError:
        return False


def sany_tools() -> tuple[str, list[Path]]:
    """``java`` and the TLA+ tool jars, resolved like ``scripts/tlc/run_model_check.sh``."""
    roots = [_ROOT]
    env_root = os.environ.get("SPECULA_ROOT")
    if env_root and Path(env_root) != _ROOT:
        roots.append(Path(env_root))
    for root in roots:
        jar = root / "lib" / "tla2tools.jar"
        if jar.is_file():
            community = root / "lib" / "CommunityModules-deps.jar"
            jars = [jar, community] if community.is_file() else [jar]
            break
    else:
        searched = " and ".join(str(root / "lib") for root in roots)
        raise SanyUnavailable(f"tla2tools.jar not found in {searched} (scripts/infra/setup.sh installs it)")
    java = shutil.which("java")
    if java is None:
        raise SanyUnavailable("java was not found on PATH")
    return java, jars


def sany_command(java: str, jars: list[Path], module: str) -> list[str]:
    return [java, "-cp", os.pathsep.join(str(jar) for jar in jars), "tla2sany.SANY", module]


def sany_problem(spec_dir: Path, module: str, java: str, jars: list[Path]) -> str | None:
    """Parse one module with SANY in ``spec_dir``; return the problem or None."""
    command = sany_command(java, jars, module)
    # SANY unpacks its standard modules below java.io.tmpdir; keep that under TMPDIR.
    with tempfile.TemporaryDirectory(prefix="specula-sany-") as scratch:
        try:
            result = subprocess.run(
                [command[0], f"-Djava.io.tmpdir={scratch}", *command[1:]],
                cwd=spec_dir,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                errors="replace",
                timeout=SANY_TIMEOUT_S,
            )
        except subprocess.TimeoutExpired as exc:
            raise SanyUnavailable(f"SANY did not finish {module} within {SANY_TIMEOUT_S}s") from exc
        except OSError as exc:
            raise SanyUnavailable(f"cannot run SANY: {exc}") from exc
    output = result.stdout + result.stderr
    # Some SANY releases exit 0 after semantic errors; their error count still shows them.
    if result.returncode == 0 and _SANY_ERRORS.search(output) is None:
        return None
    lines = [line.rstrip() for line in output.splitlines() if line.strip() and not line.startswith(_SANY_NOISE)]
    detail = "\n".join(f"    {line}" for line in lines[-20:]) or "    (no output)"
    rerun = f"cd {shlex.quote(str(spec_dir))} && {shlex.join(command)}"
    status = f"exit {result.returncode}" if result.returncode else "semantic errors"
    return (
        f"`spec/{module}` does not parse with SANY ({status}). "
        f"Fix the errors it reports; rerun the check with `{rerun}`:\n{detail}"
    )


def traces_collected(work: Path) -> bool:
    """Whether ``traces/`` holds at least one non-empty ``*.ndjson`` trace."""
    traces = work / TRACES_DIR
    if traces.is_dir() and not traces.is_symlink():
        for path in traces.rglob("*.ndjson"):
            try:
                if path.is_file() and path.stat().st_size > 0:
                    return True
            except OSError:
                continue
    return False


def handoff_limits(work: Path) -> list[str]:
    """Validation limits an accepted handoff carries into the target's summary."""
    return [] if traces_collected(work) else [TRACES_LIMIT]


def handoff_problems(work: Path, *, strict: bool) -> list[str]:
    """Actionable problems with the required outputs in ``work``; empty when the handoff is valid.

    Raises SanyUnavailable when the modules cannot be parsed in this environment.
    """
    from specula.confirmlib import _expected_mc_ids

    problems: list[str] = []
    for relative in required_files(strict=strict):
        path = work / relative
        if not path.is_file():
            problems.append(f"`{relative}` is missing: write {_HINTS[relative]}.")
        elif not _has_content(path):
            problems.append(f"`{relative}` is empty.")
    if strict:
        for relative in ADVISORY_DIRS:
            directory = work / relative
            if not directory.is_dir() or not any(path.is_file() for path in directory.rglob("*")):
                problems.append(f"`{relative}/` is missing or empty: write the harness sources it holds.")
    findings = work / "spec" / "findings.json"
    if _has_content(findings):
        _, errors = _expected_mc_ids(work / "spec")
        problems += [
            f"`spec/findings.json`: {error.removeprefix('invalid findings.json: ')} "
            "(see the validation skill's findings format)"
            for error in errors
        ]
    modules = [relative for relative in SANY_MODULES if _has_content(work / relative)]
    if modules:
        java, jars = sany_tools()
        for relative in modules:
            problem = sany_problem(work / "spec", Path(relative).name, java, jars)
            if problem is not None:
                problems.append(problem)
    return problems
