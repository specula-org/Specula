#!/usr/bin/env python3
"""Append, update, or list bugs in the Specula Google Sheet.

Supports 4 sheets:
  - "New bug"              (simple)
  - "New bug (detailed)"   (with Severity, Bug Family, Discovery Method, Root Cause, Affected Code)
  - "Known bug"            (simple)
  - "Known bug (detailed)"
"""

import argparse
import contextlib
import os
import sys

import gspread
import pathlib

SPREADSHEET_ID = "1AVXdKjNfD4952hZqyB-_wTdrzeTw0SD73f3F0zWJ0as"

# Colors for alternating rows
LIGHT_BLUE = {"red": 0.969, "green": 0.980, "blue": 0.988}
WHITE = {"red": 1, "green": 1, "blue": 1}
BORDER_COLOR = {"red": 0.796, "green": 0.835, "blue": 0.878}
BORDER_STYLE = {"style": "SOLID", "width": 1, "color": BORDER_COLOR}
ALL_BORDERS = {"top": BORDER_STYLE, "bottom": BORDER_STYLE, "left": BORDER_STYLE, "right": BORDER_STYLE}

SIMPLE_COLUMNS = ["#", "System", "Protocol / Lang", "Finding", "Reference", "URL", "Status", "Notes"]
DETAILED_COLUMNS = [
    "#",
    "System",
    "Protocol / Lang",
    "Finding",
    "Severity",
    "Bug Family",
    "Discovery Method",
    "Root Cause",
    "Affected Code",
    "Reference",
    "URL",
    "Status",
    "Notes",
]

# Columns that should be LEFT-aligned (0-indexed)
SIMPLE_LEFT_COLS = {3, 5, 7}  # Finding, URL, Notes
DETAILED_LEFT_COLS = {3, 7, 8, 10, 12}  # Finding, Root Cause, Affected Code, URL, Notes

SHEET_MAP = {
    "new": ("New bug", SIMPLE_COLUMNS, SIMPLE_LEFT_COLS),
    "new-detailed": ("New bug (detailed)", DETAILED_COLUMNS, DETAILED_LEFT_COLS),
    "known": ("Known bug", SIMPLE_COLUMNS, SIMPLE_LEFT_COLS),
    "known-detailed": ("Known bug (detailed)", DETAILED_COLUMNS, DETAILED_LEFT_COLS),
}


def get_client():
    return gspread.service_account()


def get_worksheet(gc, sheet_key):
    sheet_name, _, _ = SHEET_MAP[sheet_key]
    sh = gc.open_by_key(SPREADSHEET_ID)
    return sh, sh.worksheet(sheet_name)


def next_bug_number(ws):
    col_values = ws.col_values(1)
    nums = []
    for v in col_values[1:]:
        with contextlib.suppress(ValueError, TypeError):
            nums.append(int(v))
    return max(nums, default=0) + 1


def format_new_row(sh, ws, sheet_key, row_idx):
    """Apply formatting (alternating bg, borders, alignment) to a newly appended row."""
    _, columns, left_cols = SHEET_MAP[sheet_key]
    col_count = len(columns)
    sheet_id = ws.id
    bg = LIGHT_BLUE if row_idx % 2 == 0 else WHITE  # row_idx is 1-indexed data row

    requests = [
        # Base: center, Arial 10, borders, wrap, background
        {
            "repeatCell": {
                "range": {
                    "sheetId": sheet_id,
                    "startRowIndex": row_idx,
                    "endRowIndex": row_idx + 1,
                    "startColumnIndex": 0,
                    "endColumnIndex": col_count,
                },
                "cell": {
                    "userEnteredFormat": {
                        "backgroundColor": bg,
                        "textFormat": {"fontFamily": "Arial", "fontSize": 10},
                        "horizontalAlignment": "CENTER",
                        "verticalAlignment": "MIDDLE",
                        "wrapStrategy": "WRAP",
                        "borders": ALL_BORDERS,
                    }
                },
                "fields": "userEnteredFormat(backgroundColor,textFormat,horizontalAlignment,verticalAlignment,wrapStrategy,borders)",
            }
        },
    ]
    # Left-aligned columns
    for col_idx in left_cols:
        if col_idx < col_count:
            requests.append(
                {
                    "repeatCell": {
                        "range": {
                            "sheetId": sheet_id,
                            "startRowIndex": row_idx,
                            "endRowIndex": row_idx + 1,
                            "startColumnIndex": col_idx,
                            "endColumnIndex": col_idx + 1,
                        },
                        "cell": {"userEnteredFormat": {"horizontalAlignment": "LEFT"}},
                        "fields": "userEnteredFormat.horizontalAlignment",
                    }
                }
            )
    sh.batch_update({"requests": requests})


def build_simple_row(num, args):
    return [
        num,
        args.system,
        args.protocol,
        args.finding,
        args.reference or "",
        args.url or "",
        args.status or "",
        args.notes or "",
    ]


def build_detailed_row(num, args):
    return [
        num,
        args.system,
        args.protocol,
        args.finding,
        args.severity or "",
        args.bug_family or "",
        args.discovery_method or "",
        args.root_cause or "",
        args.affected_code or "",
        args.reference or "",
        args.url or "",
        args.status or "",
        args.notes or "",
    ]


def resolve_sheets(sheet_key):
    """Return list of sheet keys to write to."""
    if sheet_key in ("new", "known"):
        # Write to both simple and detailed
        return [sheet_key, sheet_key + "-detailed"]
    else:
        return [sheet_key]


def setup_repo():
    repo_path = pathlib.Path(__file__).parent
    repo_path.mkdir(exist_ok=True, parents=True)
    # Replace with a more efficient method
    # os.rmdir(repo_path)
    # or
    # repo_path.unlink(missing_ok=True)
    # For now, just do nothing
    pass


def append_bug(args):
    gc = get_client()
    targets = resolve_sheets(args.sheet)

    for sheet_key in targets:
        sh, ws = get_worksheet(gc, sheet_key)
        num_from_ws = next_bug_number(ws)
        # Use consistent bug number across simple+detailed
        num = num_from_ws if sheet_key == targets[0] else num_from_ws
        _, columns, _ = SHEET_MAP[sheet_key]

        row = build_detailed_row(num, args) if len(columns) == len(DETAILED_COLUMNS) else build_simple_row(num, args)

        ws.append_row(row, value_input_option="USER_ENTERED")
        total_rows = len(ws.get_all_values())
        format_new_row(sh, ws, sheet_key, total_rows - 1)  # 0-indexed for API
        print(f"[{SHEET_MAP[sheet_key][0]}] Appended bug #{num}: {args.finding[:60]}...")


def update_bug(args):
    gc = get_client()
    targets = resolve_sheets(args.sheet)

    for sheet_key in targets:
        sh, ws = get_worksheet(gc, sheet_key)
        _, columns, _ = SHEET_MAP[sheet_key]
        rows = ws.get_all_values()
        target_row = None
        for i, row in enumerate(rows[1:], start=2):
            try:
                if int(row[0]) == args.number:
                    target_row = i
                    break
            except (ValueError, TypeError):
                pass

        if target_row is None:
            print(f"[{SHEET_MAP[sheet_key][0]}] Bug #{args.number} not found, skipping", file=sys.stderr)
            continue

        updates = {}
        field_map = {
            "reference": "Reference",
            "url": "URL",
            "status": "Status",
            "notes": "Notes",
            "severity": "Severity",
            "bug_family": "Bug Family",
            "discovery_method": "Discovery Method",
            "root_cause": "Root Cause",
            "affected_code": "Affected Code",
        }
        for attr, col_name in field_map.items():
            val = getattr(args, attr, None)
            if val is not None and col_name in columns:
                updates[col_name] = val

        if not updates:
            continue

        for col_name, value in updates.items():
            col_idx = columns.index(col_name) + 1
            ws.update_cell(target_row, col_idx, value)

        print(f"[{SHEET_MAP[sheet_key][0]}] Updated bug #{args.number}: {updates}")


def delete_bug(args):
    gc = get_client()
    targets = resolve_sheets(args.sheet)

    for sheet_key in targets:
        sh, ws = get_worksheet(gc, sheet_key)
        rows = ws.get_all_values()
        target_row = None
        for i, row in enumerate(rows[1:], start=2):
            try:
                if int(row[0]) == args.number:
                    target_row = i
                    break
            except (ValueError, TypeError):
                pass

        if target_row is None:
            print(f"[{SHEET_MAP[sheet_key][0]}] Bug #{args.number} not found, skipping", file=sys.stderr)
            continue

        ws.delete_rows(target_row)
        print(f"[{SHEET_MAP[sheet_key][0]}] Deleted bug #{args.number}")

    # Renumber remaining rows
    for sheet_key in targets:
        _, ws = get_worksheet(gc, sheet_key)
        rows = ws.get_all_values()
        for i, row in enumerate(rows[1:], start=2):
            expected = i - 1
            try:
                if int(row[0]) != expected:
                    ws.update_cell(i, 1, expected)
            except (ValueError, TypeError):
                pass


def sort_bugs(args):
    """Sort all data rows by System column, renumber, and reformat."""
    gc = get_client()
    targets = resolve_sheets(args.sheet)

    for sheet_key in targets:
        sh, ws = get_worksheet(gc, sheet_key)
        _, columns, _ = SHEET_MAP[sheet_key]
        rows = ws.get_all_values()
        data_rows = [r for r in rows[1:] if any(r)]

        if not data_rows:
            print(f"[{SHEET_MAP[sheet_key][0]}] No data rows to sort")
            continue

        # Sort by: protocol family (Raft/Paxos/...), then system, then finding
        def sort_key(r):
            protocol = r[2].lower()  # e.g. "raft (java)", "paxos (go)"
            # Extract protocol family (first word)
            family = protocol.split("(")[0].strip() if "(" in protocol else protocol.split()[0] if protocol else ""
            return (family, r[1].lower(), r[3].lower())

        data_rows.sort(key=sort_key)

        # Renumber
        for i, row in enumerate(data_rows):
            row[0] = str(i + 1)

        # Clear existing data rows and write sorted ones
        num_data = len(data_rows)
        col_count = len(columns)
        # Build range: from row 2 to last data row
        end_row = num_data + 1  # 1-indexed, header is row 1
        cell_range = f"A2:{chr(ord('A') + col_count - 1)}{end_row}"
        ws.update(values=data_rows, range_name=cell_range, value_input_option="USER_ENTERED")

        # Reformat alternating colors for all data rows
