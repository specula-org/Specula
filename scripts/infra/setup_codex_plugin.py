#!/usr/bin/env python3
"""Generate and install the local Specula Codex plugin."""

from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import sys


PLUGIN_NAME = "specula-codex"
MARKETPLACE_NAME = "specula"
LEGACY_MCP_NAMES = ("tracedebugger", "spec_analyzer", "inv_checking_tool")


def build_plugin_manifest() -> dict:
    return {
        "name": PLUGIN_NAME,
        "version": "0.1.0",
        "description": (
            "Specula TLA+ workflow skills and MCP tools for code analysis, "
            "spec generation, trace validation, and bug confirmation."
        ),
        "author": {
            "name": "Specula-org",
            "url": "https://github.com/specula-org/Specula",
        },
        "homepage": "https://github.com/specula-org/Specula",
        "repository": "https://github.com/specula-org/Specula",
        "license": "Apache-2.0",
        "keywords": [
            "tla",
            "formal-methods",
            "model-checking",
            "trace-validation",
            "bug-finding",
        ],
        "skills": "./skills/",
        "mcpServers": "./.mcp.json",
        "interface": {
            "displayName": "Specula",
            "shortDescription": "Run Specula's TLA+ bug-finding workflow from Codex.",
            "longDescription": (
                "Specula packages workflow skills and MCP tools for analyzing "
                "system implementations, generating TLA+ specifications, "
                "validating traces, running model checking, and confirming "
                "bugs in source code."
            ),
            "developerName": "Specula-org",
            "category": "Developer Tools",
            "capabilities": ["Interactive", "Read", "Write"],
            "websiteURL": "https://github.com/specula-org/Specula",
            "privacyPolicyURL": "https://github.com/specula-org/Specula",
            "termsOfServiceURL": "https://github.com/specula-org/Specula",
            "defaultPrompt": [
                "Run Specula code analysis on this repository.",
                "Generate TLA+ specs from this modeling brief.",
                "Validate this trace against the TLA+ spec.",
            ],
            "brandColor": "#2563EB",
            "screenshots": [],
        },
    }


def build_mcp_config(project_root: pathlib.Path) -> dict:
    servers = {
        "tracedebugger": (
            "tools/trace_debugger/.venv/bin/python",
            "tools/trace_debugger/mcp_server.py",
        ),
        "spec_analyzer": (
            "tools/spec_analyzer/.venv/bin/python",
            "tools/spec_analyzer/mcp_server.py",
        ),
        "inv_checking_tool": (
            "tools/inv_checking_tool/.venv/bin/python",
            "tools/inv_checking_tool/mcp_server.py",
        ),
    }

    return {
        "mcpServers": {
            name: {
                "command": str(project_root / python_path),
                "args": [str(project_root / server_path)],
                "env": {"SPECULA_ROOT": str(project_root)},
            }
            for name, (python_path, server_path) in servers.items()
        }
    }


def build_marketplace_manifest() -> dict:
    return {
        "name": MARKETPLACE_NAME,
        "interface": {"displayName": "Specula"},
        "plugins": [
            {
                "name": PLUGIN_NAME,
                "source": {
                    "source": "local",
                    "path": f"./plugins/{PLUGIN_NAME}",
                },
                "policy": {
                    "installation": "AVAILABLE",
                    "authentication": "ON_INSTALL",
                },
                "category": "Developer Tools",
            }
        ],
    }


def write_json(path: pathlib.Path, value: dict) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def generate_plugin(project_root: pathlib.Path, plugin_root: pathlib.Path) -> None:
    skills_source = project_root / "skills"
    if not skills_source.is_dir():
        raise SystemExit(f"Skills directory not found: {skills_source}")

    if plugin_root.exists():
        shutil.rmtree(plugin_root)

    plugin_dir = plugin_root / "plugins" / PLUGIN_NAME
    (plugin_dir / ".codex-plugin").mkdir(parents=True)
    shutil.copytree(
        skills_source,
        plugin_dir / "skills",
        ignore=shutil.ignore_patterns("__pycache__", ".DS_Store"),
    )

    write_json(plugin_dir / ".codex-plugin" / "plugin.json", build_plugin_manifest())
    write_json(plugin_dir / ".mcp.json", build_mcp_config(project_root))

    marketplace_dir = plugin_root / ".agents" / "plugins"
    marketplace_dir.mkdir(parents=True)
    write_json(marketplace_dir / "marketplace.json", build_marketplace_manifest())


def run(command: list[str], *, check: bool = True, quiet: bool = False) -> subprocess.CompletedProcess:
    stdout = subprocess.DEVNULL if quiet else None
    stderr = subprocess.DEVNULL if quiet else None
    return subprocess.run(command, check=check, stdout=stdout, stderr=stderr)


def install_plugin(plugin_root: pathlib.Path) -> None:
    if shutil.which("codex") is None:
        raise SystemExit("codex is required to install the Specula Codex plugin")

    run(["codex", "plugin", "marketplace", "remove", MARKETPLACE_NAME], check=False, quiet=True)
    run(["codex", "plugin", "marketplace", "add", str(plugin_root)])

    for mcp_name in LEGACY_MCP_NAMES:
        run(["codex", "mcp", "remove", mcp_name], check=False, quiet=True)

    run(["codex", "plugin", "add", f"{PLUGIN_NAME}@{MARKETPLACE_NAME}"])


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", required=True, type=pathlib.Path)
    parser.add_argument("--plugin-root", required=True, type=pathlib.Path)
    parser.add_argument(
        "--no-install",
        action="store_true",
        help="Generate plugin files without changing Codex configuration.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    project_root = args.project_root.resolve()
    plugin_root = args.plugin_root.resolve()

    generate_plugin(project_root, plugin_root)
    if not args.no_install:
        install_plugin(plugin_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
