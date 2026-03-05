#!/usr/bin/env python3
"""Append, update, or list bugs in the Specula Google Sheet.

Supports 4 sheets:
  - "New bug"              (simple)
  - "New bug (detailed)"   (with Severity, Bug Family, Discovery Method, Root Cause, Affected Code)
  - "Known bug"            (simple)
  - "Known bug (detailed)"
"""

import argparse
import sys

import gspread

SPREADSHEET_ID = "1AVXdKjNfD4952hZqyB-_wTdrzeTw0SD73f3F0zWJ0as"

# Colors for alternating rows
LIGHT_BLUE = {"red": 0.969, "green": 0.980, "blue": 0.988}
WHITE = {"red": 1, "green": 1, "blue": 1}
BORDER_COLOR = {"red": 0.796, "green": 0.835, "blue": 0.878}
BORDER_STYLE = {"style": "SOLID", "width": 1, "color": BORDER_COLOR}
ALL_BORDERS = {"top": BORDER_STYLE, "bottom": BORDER_STYLE, "left": BORDER_STYLE, "right": BORDER_STYLE}

SIMPLE_COLUMNS = ["#", "System", "Protocol / Lang", "Finding", "Reference", "URL", "Status", "Notes"]
DETAILED_COLUMNS = ["#", "System", "Protocol / Lang", "Finding", "Severity", "Bug Family",
                    "Discovery Method", "Root Cause", "Affected Code", "Reference", "URL", "Status", "Notes"]

# Columns that should be LEFT-aligned (0-indexed)
SIMPLE_LEFT_COLS = {3, 5, 7}    # Finding, URL, Notes
DETAILED_LEFT_COLS = {3, 7, 8, 10, 12}  # Finding, Root Cause, Affected Code, URL, Notes

SHEET_MAP = {
    "new":             ("New bug",              SIMPLE_COLUMNS,   SIMPLE_LEFT_COLS),
    "new-detailed":    ("New bug (detailed)",   DETAILED_COLUMNS, DETAILED_LEFT_COLS),
    "known":           ("Known bug",            SIMPLE_COLUMNS,   SIMPLE_LEFT_COLS),
    "known-detailed":  ("Known bug (detailed)", DETAILED_COLUMNS, DETAILED_LEFT_COLS),
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
        try:
            nums.append(int(v))
        except (ValueError, TypeError):
            pass
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
                "range": {"sheetId": sheet_id, "startRowIndex": row_idx, "endRowIndex": row_idx + 1,
                          "startColumnIndex": 0, "endColumnIndex": col_count},
                "cell": {"userEnteredFormat": {
                    "backgroundColor": bg,
                    "textFormat": {"fontFamily": "Arial", "fontSize": 10},
                    "horizontalAlignment": "CENTER",
                    "verticalAlignment": "MIDDLE",
                    "wrapStrategy": "WRAP",
                    "borders": ALL_BORDERS,
                }},
                "fields": "userEnteredFormat(backgroundColor,textFormat,horizontalAlignment,verticalAlignment,wrapStrategy,borders)",
            }
        },
    ]
    # Left-aligned columns
    for col_idx in left_cols:
        if col_idx < col_count:
            requests.append({
                "repeatCell": {
                    "range": {"sheetId": sheet_id, "startRowIndex": row_idx, "endRowIndex": row_idx + 1,
                              "startColumnIndex": col_idx, "endColumnIndex": col_idx + 1},
                    "cell": {"userEnteredFormat": {"horizontalAlignment": "LEFT"}},
                    "fields": "userEnteredFormat.horizontalAlignment",
                }
            })
    sh.batch_update({"requests": requests})


def build_simple_row(num, args):
    return [num, args.system, args.protocol, args.finding,
            args.reference or "", args.url or "", args.status or "", args.notes or ""]


def build_detailed_row(num, args):
    return [num, args.system, args.protocol, args.finding,
            args.severity or "", args.bug_family or "", args.discovery_method or "",
            args.root_cause or "", args.affected_code or "",
            args.reference or "", args.url or "", args.status or "", args.notes or ""]


def resolve_sheets(sheet_key):
    """Return list of sheet keys to write to."""
    if sheet_key in ("new", "known"):
        # Write to both simple and detailed
        return [sheet_key, sheet_key + "-detailed"]
    else:
        return [sheet_key]


def append_bug(args):
    gc = get_client()
    targets = resolve_sheets(args.sheet)

    for sheet_key in targets:
        sh, ws = get_worksheet(gc, sheet_key)
        num_from_ws = next_bug_number(ws)
        # Use consistent bug number across simple+detailed
        num = num_from_ws if sheet_key == targets[0] else num_from_ws
        _, columns, _ = SHEET_MAP[sheet_key]

        if len(columns) == len(DETAILED_COLUMNS):
            row = build_detailed_row(num, args)
        else:
            row = build_simple_row(num, args)

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
            "reference": "Reference", "url": "URL", "status": "Status", "notes": "Notes",
            "severity": "Severity", "bug_family": "Bug Family",
            "discovery_method": "Discovery Method", "root_cause": "Root Cause",
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


def list_bugs(args):
    gc = get_client()
    sheet_key = args.sheet if args.sheet in SHEET_MAP else "new"
    _, ws = get_worksheet(gc, sheet_key)
    rows = ws.get_all_values()
    header = rows[0]
    print(f"=== {SHEET_MAP[sheet_key][0]} ===")
    print("\t".join(header))
    print("-" * 120)
    for row in rows[1:]:
        if any(row):
            print("\t".join(row))


def main():
    parser = argparse.ArgumentParser(description="Specula Bug Tracker")
    sub = parser.add_subparsers(dest="command", required=True)

    # --- append ---
    p_add = sub.add_parser("append", help="Add a new bug")
    p_add.add_argument("--sheet", choices=["new", "known"], default="new",
                       help="Target: 'new' (writes to New bug + detailed) or 'known' (writes to Known bug + detailed)")
    p_add.add_argument("--system", required=True, help="System name")
    p_add.add_argument("--protocol", required=True, help="Protocol / Lang")
    p_add.add_argument("--finding", required=True, help="Bug description")
    p_add.add_argument("--severity", help="Critical / Medium / Minor")
    p_add.add_argument("--bug-family", help="Bug family name")
    p_add.add_argument("--discovery-method", help="MC-BFS / MC-Simulation / Trace Validation / Code Review")
    p_add.add_argument("--root-cause", help="Brief root cause description")
    p_add.add_argument("--affected-code", help="file:line references")
    p_add.add_argument("--reference", help="PR/Issue reference")
    p_add.add_argument("--url", help="GitHub URL")
    p_add.add_argument("--status", help="Status")
    p_add.add_argument("--notes", help="Additional notes")

    # --- update ---
    p_upd = sub.add_parser("update", help="Update an existing bug")
    p_upd.add_argument("--sheet", choices=["new", "known"], default="new",
                       help="Target: 'new' or 'known' (updates both simple + detailed)")
    p_upd.add_argument("--number", type=int, required=True, help="Bug number to update")
    p_upd.add_argument("--severity", help="New severity")
    p_upd.add_argument("--bug-family", help="New bug family")
    p_upd.add_argument("--discovery-method", help="New discovery method")
    p_upd.add_argument("--root-cause", help="New root cause")
    p_upd.add_argument("--affected-code", help="New affected code")
    p_upd.add_argument("--reference", help="New reference")
    p_upd.add_argument("--url", help="New URL")
    p_upd.add_argument("--status", help="New status")
    p_upd.add_argument("--notes", help="New notes")

    # --- delete ---
    p_del = sub.add_parser("delete", help="Delete a bug by number")
    p_del.add_argument("--sheet", choices=["new", "known"], default="new",
                       help="Target: 'new' or 'known' (deletes from both simple + detailed)")
    p_del.add_argument("--number", type=int, required=True, help="Bug number to delete")

    # --- list ---
    p_list = sub.add_parser("list", help="List all bugs")
    p_list.add_argument("--sheet", choices=list(SHEET_MAP.keys()), default="new",
                        help="Which sheet to list")

    args = parser.parse_args()
    if args.command == "append":
        append_bug(args)
    elif args.command == "update":
        update_bug(args)
    elif args.command == "delete":
        delete_bug(args)
    elif args.command == "list":
        list_bugs(args)


if __name__ == "__main__":
    main()
