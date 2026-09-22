"""Native Codex configuration loading, without starting a model session."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CODEX = shutil.which("codex")


@pytest.mark.skipif(CODEX is None, reason="requires the native Codex CLI")
@pytest.mark.parametrize(
    ("user_config", "project_config", "enabled"),
    [
        ("[features]\ncode_mode=true\n", "", "true"),
        ("[features.code_mode]\nenabled=true\n", "", "true"),
        ("[features]\ncode_mode=false\n", "", "false"),
        ("[features.code_mode]\nenabled=false\n", "", "false"),
        ("", "", None),
        ("[features]\ncode_mode=false\n", "[features]\ncode_mode=true\n", "true"),
        ("[features]\ncode_mode=true\n", "[features]\ncode_mode=false\n", "false"),
    ],
    ids=["boolean-on", "table-on", "boolean-off", "table-off", "unset", "project-on", "project-off"],
)
def test_tlc_override_preserves_native_code_mode(
    tmp_path: Path, user_config: str, project_config: str, enabled: str | None
) -> None:
    assert CODEX is not None
    profile = tmp_path / "codex-home"
    work = tmp_path / "project"
    bindir = tmp_path / "bin"
    for directory in (profile, work, bindir):
        directory.mkdir()
    (work / ".git").mkdir()
    config = profile / "config.toml"
    config.write_text(user_config + f'\n[projects.{json.dumps(str(work))}]\ntrust_level="trusted"\n')
    if project_config:
        (work / ".codex").mkdir()
        (work / ".codex/config.toml").write_text(project_config)
    originals = {path: path.read_bytes() for path in tmp_path.rglob("*.toml")}

    # Delegate config reads to the native CLI, then replace only model execution
    # with another native config read using the adapter's exact -c arguments.
    wrapper = bindir / "codex"
    wrapper.write_text(
        "#!/usr/bin/env python3\n"
        "import json, os, subprocess, sys\n"
        "from pathlib import Path\n"
        "binary = os.environ['NATIVE_CODEX']\n"
        "args = sys.argv[1:]\n"
        "if args[:2] == ['features', 'list']:\n"
        "    raise SystemExit(subprocess.run([binary, *args]).returncode)\n"
        "overrides = []\n"
        "for index, arg in enumerate(args):\n"
        "    if arg == '-c': overrides.extend([arg, args[index + 1]])\n"
        "Path('adapter-argv.json').write_text(json.dumps(args))\n"
        "result = subprocess.run([binary, 'features', 'list', *overrides], capture_output=True, text=True)\n"
        "Path('effective-features.txt').write_text(result.stdout)\n"
        "if result.returncode:\n"
        "    print(result.stderr, file=sys.stderr)\n"
        "    raise SystemExit(result.returncode)\n"
        "print(json.dumps({'type': 'thread.started', 'thread_id': 'config-probe'}))\n"
        "print(json.dumps({'type': 'turn.completed', 'usage': {}}))\n"
    )
    wrapper.chmod(0o755)
    env = {key: value for key, value in os.environ.items() if not key.startswith(("SPECULA_", "CODEX_"))}
    env.update(
        {
            "CODEX_HOME": str(profile),
            "NATIVE_CODEX": str(Path(CODEX).resolve()),
            "PATH": f"{bindir}:/usr/bin:/bin",
            "SPECULA_STOP_GATE": "off",
            "SPECULA_TLC_TOOL_CODEX": '{command="python3",args=[],tool_timeout_sec=3720}',
        }
    )
    before = subprocess.run(
        [env["NATIVE_CODEX"], "features", "list"], cwd=work, env=env, capture_output=True, text=True, timeout=15
    )
    assert before.returncode == 0, before.stderr
    expected = next(line.split()[-1] for line in before.stdout.splitlines() if line.split()[0] == "code_mode")
    if enabled is not None:
        assert expected == enabled
    result = subprocess.run(
        [
            "bash",
            str(ROOT / "scripts/launch/adapters/codex.sh"),
            "--prompt=config probe",
            "--max-turns=0",
            f"--log={tmp_path / 'agent.log'}",
        ],
        cwd=work,
        env=env,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stderr
    effective = (work / "effective-features.txt").read_text()
    observed = next(line.split()[-1] for line in effective.splitlines() if line.split()[0] == "code_mode")
    assert observed == expected
    argv = json.loads((work / "adapter-argv.json").read_text())
    assert 'features.code_mode.direct_only_tool_namespaces=["mcp__specula_tlc"]' in argv
    assert all(path.read_bytes() == data for path, data in originals.items())
