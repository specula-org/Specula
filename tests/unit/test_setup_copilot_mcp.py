"""Hermetic behavior tests for GitHub Copilot CLI MCP setup."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path
from typing import TypedDict

REPO_ROOT = Path(__file__).resolve().parents[2]
COPILOT_MCP_HELPER = REPO_ROOT / "scripts" / "infra" / "copilot_mcp.sh"

RUNNER = r"""
set -euo pipefail
print_status() { printf '[INFO] %s\n' "$1"; }
print_success() { printf '[SUCCESS] %s\n' "$1"; }
print_warning() { printf '[WARNING] %s\n' "$1"; }
source "$1"
shift
setup_copilot_mcp_servers "$@"
"""

FAKE_COPILOT = r"""#!/usr/bin/env python3
import json
import os
import sys

args = sys.argv[1:]
with open(os.devnull) as devnull:
    stdin_is_dev_null = os.path.sameopenfile(0, devnull.fileno())
with open(os.environ["FAKE_COPILOT_LOG"], "a", encoding="utf-8") as stream:
    stream.write(
        json.dumps(
            {
                "argv": args,
                "copilot_home": os.environ.get("COPILOT_HOME"),
                "stdin_is_dev_null": stdin_is_dev_null,
            }
        )
        + "\n"
    )

if args == ["--version"]:
    print(f'GitHub Copilot CLI {os.environ.get("FAKE_COPILOT_VERSION", "1.0.70")}')
    raise SystemExit(int(os.environ.get("FAKE_COPILOT_VERSION_RC", "0")))

if args == ["mcp", "list", "--json"]:
    list_rc = int(os.environ.get("FAKE_COPILOT_LIST_RC", "0"))
    if list_rc:
        print("simulated config validation failure", file=sys.stderr)
        raise SystemExit(list_rc)
    if list_json := os.environ.get("FAKE_COPILOT_LIST_JSON"):
        print(list_json)
        raise SystemExit(0)

    config_file = os.path.join(os.environ["COPILOT_HOME"], "mcp-config.json")
    try:
        if os.path.exists(config_file):
            with open(config_file, encoding="utf-8-sig") as stream:
                payload = json.load(stream)
        else:
            payload = {"mcpServers": {}}
        if not isinstance(payload, dict):
            raise ValueError("top-level configuration must be an object")
        servers = payload.get("mcpServers", {})
        if not isinstance(servers, dict):
            raise ValueError("mcpServers must be an object")
        normalized = {}
        for name, entry in servers.items():
            if not isinstance(entry, dict):
                raise ValueError("server entry must be an object")
            env = entry.get("env")
            if env is not None and (
                not isinstance(env, dict)
                or any(not isinstance(key, str) or not isinstance(value, str) for key, value in env.items())
            ):
                raise ValueError("environment values must be strings")
            normalized[name] = {**entry, "source": "user"}
    except (OSError, TypeError, ValueError) as exc:
        print(f"invalid MCP configuration: {exc}", file=sys.stderr)
        raise SystemExit(7)
    print(json.dumps({"mcpServers": normalized}))
    raise SystemExit(0)

if args[:2] == ["mcp", "add"]:
    add_rc = int(os.environ.get("FAKE_COPILOT_ADD_RC", "0"))
    if add_rc:
        print("simulated add failure", file=sys.stderr)
        raise SystemExit(add_rc)
    print(f'Added server "{args[2]}"')
    raise SystemExit(0)

print(f"unexpected arguments: {args!r}", file=sys.stderr)
raise SystemExit(2)
"""


class CopilotCall(TypedDict):
    argv: list[str]
    copilot_home: str | None
    stdin_is_dev_null: bool


class TestCopilotMcpSetup(unittest.TestCase):
    def run_setup(
        self,
        root: Path,
        entries: list[str],
        *,
        existing: str = "absent",
        version: str = "1.0.70",
        version_rc: int = 0,
        add_rc: int = 0,
    ) -> tuple[subprocess.CompletedProcess[str], list[CopilotCall]]:
        bin_dir = root / "bin"
        bin_dir.mkdir()
        fake_copilot = bin_dir / "copilot"
        fake_copilot.write_text(textwrap.dedent(FAKE_COPILOT))
        fake_copilot.chmod(0o755)

        home = root / "home"
        home.mkdir()
        config_dir = root / "copilot config"
        config_dir.mkdir()
        project_root = root / "Specula checkout"
        log_file = root / "copilot-calls.jsonl"
        list_json: str | None = None
        first_name, first_python, first_server = entries[0].split("|")
        if existing == "invalid":
            (config_dir / "mcp-config.json").write_text("{")
        elif existing == "wrong_shape":
            (config_dir / "mcp-config.json").write_text("[]")
        elif existing == "invalid_servers":
            (config_dir / "mcp-config.json").write_text(json.dumps({"mcpServers": []}))
        elif existing == "null_servers":
            (config_dir / "mcp-config.json").write_text(json.dumps({"mcpServers": None}))
        elif existing == "null_entry":
            (config_dir / "mcp-config.json").write_text(json.dumps({"mcpServers": {first_name: None}}))
        elif existing == "top_level_collision":
            (config_dir / "mcp-config.json").write_text(
                json.dumps(
                    {
                        first_name: {
                            "tools": ["*"],
                            "type": "local",
                            "command": first_python,
                            "args": [first_server],
                            "env": {"SPECULA_ROOT": str(project_root)},
                        },
                        "mcpServers": {},
                    }
                )
            )
        elif existing == "symlink":
            managed_config = root / "managed-mcp-config.json"
            managed_config.write_text(json.dumps({"mcpServers": {}}))
            (config_dir / "mcp-config.json").symlink_to(managed_config)
        elif existing != "absent":
            command = first_python
            server = first_server
            configured_project = str(project_root)
            if existing == "conflict":
                command = "/other/python"
                server = "/other/server.py"
                configured_project = "/other/checkout"
            server_config: dict[str, object] = {
                "type": "local",
                "command": command,
                "args": [server],
                "env": {
                    "SPECULA_ROOT": configured_project,
                    "USER_SETTING": "preserved",
                },
            }
            if existing == "invalid_schema":
                server_config["env"] = {
                    "SPECULA_ROOT": str(project_root),
                    "BAD": 123,
                }
            if existing != "omitted_tools":
                server_config["tools"] = [] if existing == "restricted" else ["*"]
            payload = {
                "$schema": "https://example.test/copilot-mcp.schema.json",
                "unrelatedTopLevelField": {"preserve": True},
                "mcpServers": {
                    "third_party": {
                        "type": "local",
                        "command": "/third-party/server",
                        "args": [],
                        "tools": ["*"],
                    },
                    first_name: server_config,
                },
            }
            if existing == "jsonc_match":
                (config_dir / "mcp-config.json").write_text(
                    textwrap.dedent(
                        f"""\
                        {{
                          // Copilot accepts comments and trailing commas.
                          "mcpServers": {{
                            {json.dumps(first_name)}: {json.dumps(server_config)},
                          }},
                        }}
                        """
                    )
                )
                list_json = json.dumps(
                    {
                        "mcpServers": {
                            first_name: {
                                **server_config,
                                "source": "user",
                            }
                        },
                    }
                )
            elif existing == "bom_match":
                (config_dir / "mcp-config.json").write_bytes(b"\xef\xbb\xbf" + json.dumps(payload).encode())
            else:
                (config_dir / "mcp-config.json").write_text(json.dumps(payload, indent=2))

        env = os.environ.copy()
        env.update(
            {
                "PATH": f"{bin_dir}:{env['PATH']}",
                "HOME": str(home),
                "FAKE_COPILOT_LOG": str(log_file),
                "FAKE_COPILOT_VERSION": version,
                "FAKE_COPILOT_VERSION_RC": str(version_rc),
                "FAKE_COPILOT_ADD_RC": str(add_rc),
            }
        )
        if list_json is not None:
            env["FAKE_COPILOT_LIST_JSON"] = list_json
        result = subprocess.run(
            [
                "bash",
                "-c",
                RUNNER,
                "copilot-mcp-test",
                str(COPILOT_MCP_HELPER),
                str(config_dir),
                str(project_root),
                *entries,
            ],
            cwd=root,
            env=env,
            capture_output=True,
            text=True,
            input="sentinel stdin",
            timeout=10,
            check=False,
        )
        calls = [json.loads(line) for line in log_file.read_text().splitlines()]
        return result, calls

    def test_adds_all_servers_to_copilot_home(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entries = [
                f"tracedebugger|{root / 'trace venv/bin/python'}|{root / 'trace tool/mcp_server.py'}",
                f"spec_analyzer|{root / 'spec venv/bin/python'}|{root / 'spec tool/mcp_server.py'}",
                f"inv_checking_tool|{root / 'inv venv/bin/python'}|{root / 'inv tool/mcp_server.py'}",
            ]

            result, calls = self.run_setup(root, entries)

            self.assertEqual(result.returncode, 0, result.stderr)
            config_dir = str(root / "copilot config")
            project_root = str(root / "Specula checkout")
            add_calls = [call for call in calls if call["argv"][:2] == ["mcp", "add"]]
            self.assertEqual(len(add_calls), 3)
            for entry, call in zip(entries, add_calls, strict=True):
                name, python_path, server_path = entry.split("|")
                self.assertEqual(
                    call["argv"],
                    [
                        "mcp",
                        "add",
                        name,
                        "--env",
                        f"SPECULA_ROOT={project_root}",
                        "--",
                        python_path,
                        server_path,
                    ],
                )
            self.assertTrue(all(call["copilot_home"] == config_dir for call in calls))
            self.assertTrue(all(call["stdin_is_dev_null"] for call in calls))
            self.assertEqual(result.stdout.count("Copilot MCP configured:"), 3)
            self.assertFalse((root / "home/.copilot").exists())

    def test_matching_existing_server_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="match")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
            self.assertIn("Copilot MCP already configured: tracedebugger", result.stdout)

    def test_copilot_normalized_jsonc_and_bom_configs_are_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)

            for existing in ("jsonc_match", "bom_match"):
                with self.subTest(existing=existing):
                    case_root = root / existing
                    case_root.mkdir()
                    entry = f"tracedebugger|{case_root / 'python'}|{case_root / 'mcp_server.py'}"

                    result, calls = self.run_setup(case_root, [entry], existing=existing)

                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(
                        [call["argv"] for call in calls],
                        [["--version"], ["mcp", "list", "--json"]],
                    )
                    self.assertIn("Copilot MCP already configured: tracedebugger", result.stdout)
                    config_bytes = (case_root / "copilot config/mcp-config.json").read_bytes()
                    marker = b"// Copilot accepts" if existing == "jsonc_match" else b"\xef\xbb\xbf"
                    self.assertIn(marker, config_bytes)

    def test_conflicting_existing_server_is_left_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="conflict")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
            self.assertIn("Copilot MCP 'tracedebugger' from user configuration conflicts", result.stdout)
            self.assertNotIn("mcp remove", result.stdout)
            config = json.loads((root / "copilot config/mcp-config.json").read_text())
            self.assertEqual(config["mcpServers"]["tracedebugger"]["command"], "/other/python")
            self.assertIn("third_party", config["mcpServers"])
            self.assertIn("unrelatedTopLevelField", config)

    def test_existing_server_with_no_enabled_tools_is_a_conflict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="restricted")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
            self.assertIn("Copilot MCP 'tracedebugger' from user configuration conflicts", result.stdout)

    def test_existing_server_with_omitted_tools_uses_default_all(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="omitted_tools")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
            self.assertIn("Copilot MCP already configured: tracedebugger", result.stdout)

    def test_unrecognized_existing_config_is_left_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="invalid")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
            self.assertIn("could not be validated by Copilot and was left unchanged", result.stdout)

    def test_schema_invalid_config_is_not_reported_as_configured(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="invalid_schema")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
            self.assertIn("could not be validated by Copilot and was left unchanged", result.stdout)
            self.assertNotIn("Copilot MCP already configured", result.stdout)

    def test_symlinked_config_is_left_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="symlink")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"]])
            config_file = root / "copilot config/mcp-config.json"
            self.assertTrue(config_file.is_symlink())
            self.assertEqual(json.loads(config_file.read_text()), {"mcpServers": {}})
            self.assertIn("is a symbolic link and was left unchanged", result.stdout)

    def test_valid_but_wrong_shaped_config_is_left_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            for existing in ("wrong_shape", "invalid_servers", "null_servers", "null_entry"):
                with self.subTest(existing=existing):
                    case_root = root / existing
                    case_root.mkdir()
                    result, calls = self.run_setup(case_root, [entry], existing=existing)

                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual([call["argv"] for call in calls], [["--version"], ["mcp", "list", "--json"]])
                    self.assertIn("could not be validated by Copilot and was left unchanged", result.stdout)

    def test_top_level_name_does_not_hide_missing_wrapped_server(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], existing="top_level_collision")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(calls[-1]["argv"][:3], ["mcp", "add", "tracedebugger"])
            self.assertIn("Copilot MCP configured: tracedebugger", result.stdout)

    def test_old_cli_warns_without_attempting_configuration(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], version="1.0.69")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([call["argv"] for call in calls], [["--version"]])
            self.assertIn("requires Copilot CLI 1.0.70 or newer", result.stdout)

    def test_failed_or_unrecognized_version_warns_without_configuration(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)

            for version, version_rc in (("1.0.70", 7), ("unknown", 0)):
                with self.subTest(version=version, version_rc=version_rc):
                    case_root = root / f"case-{version_rc}-{version.replace('.', '-')}"
                    case_root.mkdir()
                    entry = f"tracedebugger|{case_root / 'python'}|{case_root / 'mcp_server.py'}"

                    result, calls = self.run_setup(
                        case_root,
                        [entry],
                        version=version,
                        version_rc=version_rc,
                    )

                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual([call["argv"] for call in calls], [["--version"]])
                    self.assertIn("upgrade to the latest Copilot CLI", result.stdout)

    def test_add_failure_warns_without_failing_setup(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            entry = f"tracedebugger|{root / 'python'}|{root / 'mcp_server.py'}"

            result, calls = self.run_setup(root, [entry], add_rc=7)

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(calls[-1]["argv"][:2], ["mcp", "add"])
            self.assertIn("auto-config failed", result.stdout)
            self.assertIn("simulated add failure", result.stdout)
            self.assertIn("copilot mcp add", result.stdout)


if __name__ == "__main__":
    unittest.main()
