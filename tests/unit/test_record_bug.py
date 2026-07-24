from __future__ import annotations

import argparse
import importlib.util
import sys
import types
from pathlib import Path
from unittest import mock


def load_record_bug() -> types.ModuleType:
    path = Path(__file__).resolve().parents[2] / "scripts" / "infra" / "record_bug.py"
    spec = importlib.util.spec_from_file_location("record_bug", path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    with mock.patch.dict(sys.modules, {"gspread": types.ModuleType("gspread")}):
        spec.loader.exec_module(module)
    return module


def test_build_detailed_row_uses_scenario_column() -> None:
    module = load_record_bug()
    args = argparse.Namespace(
        system="system",
        protocol="raft",
        finding="finding",
        severity="High",
        scenario="Scenario 2",
        discovery_method="MC-BFS",
        root_cause="cause",
        affected_code="src/file.py:1",
        reference=None,
        url=None,
        status=None,
        notes=None,
    )

    row = module.build_detailed_row(7, args)

    assert row[5] == "Scenario 2"


def test_update_bug_writes_scenario_column() -> None:
    module = load_record_bug()

    class Worksheet:
        def __init__(self) -> None:
            self.updates: list[tuple[int, int, str]] = []

        def get_all_values(self) -> list[list[str]]:
            return [module.DETAILED_COLUMNS, ["7"]]

        def update_cell(self, row: int, column: int, value: str) -> None:
            self.updates.append((row, column, value))

    worksheet = Worksheet()
    args = argparse.Namespace(
        sheet="new-detailed",
        number=7,
        scenario="Scenario 3",
        reference=None,
        url=None,
        status=None,
        notes=None,
        severity=None,
        discovery_method=None,
        root_cause=None,
        affected_code=None,
    )
    with (
        mock.patch.object(module, "get_client", return_value=object()),
        mock.patch.object(module, "get_worksheet", return_value=(object(), worksheet)),
    ):
        module.update_bug(args)

    assert worksheet.updates == [(2, 6, "Scenario 3")]


def test_append_cli_parses_scenario_option() -> None:
    module = load_record_bug()
    argv = [
        "record_bug.py",
        "append",
        "--system",
        "system",
        "--protocol",
        "raft",
        "--finding",
        "finding",
        "--scenario",
        "Scenario 4",
    ]
    with (
        mock.patch.object(sys, "argv", argv),
        mock.patch.object(module, "append_bug") as append_bug,
    ):
        module.main()

    assert append_bug.call_args.args[0].scenario == "Scenario 4"
