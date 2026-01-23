#!/usr/bin/env python3
"""Command-line interface for TLC Output Reader.

This CLI provides convenient access to TLC model checking results,
allowing users to inspect invariant violations, view states, and
compare execution traces.

Usage:
    python -m tools.inv_checking_tool <file> [options]

Examples:
    # Show summary
    python cli.py output.log --summary

    # Show specific state
    python cli.py output.log --state 1
    python cli.py output.log --state last
    python cli.py output.log --state -1

    # Show multiple states
    python cli.py output.log --states 1:5
    python cli.py output.log --states -3:
    python cli.py output.log --states 1,5,10

    # Show specific variable
    python cli.py output.log --state 1 --var currentTerm
    python cli.py output.log --state last --var log.s1.entries

    # Compare states
    python cli.py output.log --diff -2 -1

    # Track variable changes
    python cli.py output.log --track currentTerm

    # Show all actions
    python cli.py output.log --actions
"""

import argparse
import json
import sys
from pathlib import Path
from typing import List, Optional

# Handle both direct execution and module execution
try:
    from .tlc_output_reader import TLCOutputReader
    from .utils.path_parser import format_value
except ImportError:
    # Direct execution - add parent directories to path
    import os
    current_dir = os.path.dirname(os.path.abspath(__file__))
    parent_dir = os.path.dirname(current_dir)  # inv_checking_tool
    tools_dir = os.path.dirname(parent_dir)    # tools
    sys.path.insert(0, tools_dir)
    from inv_checking_tool.src.tlc_output_reader import TLCOutputReader
    from inv_checking_tool.src.utils.path_parser import format_value


def create_parser() -> argparse.ArgumentParser:
    """Create the argument parser."""
    parser = argparse.ArgumentParser(
        description="TLC Output Reader - Analyze TLC model checking results",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Show summary of the trace
  %(prog)s output.log --summary

  # Show first and last states
  %(prog)s output.log --state 1
  %(prog)s output.log --state last

  # Show a range of states
  %(prog)s output.log --states 1:5
  %(prog)s output.log --states -3:

  # Show specific variable in a state
  %(prog)s output.log --state 10 --var currentTerm
  %(prog)s output.log --state last --var log.s1.entries[0]

  # Compare two states
  %(prog)s output.log --diff -2 -1

  # Track variable changes across trace
  %(prog)s output.log --track state

  # Show action sequence
  %(prog)s output.log --actions
        """
    )

    parser.add_argument(
        "file",
        type=str,
        help="Path to TLC output file",
    )

    # Main operation modes (mutually exclusive)
    mode_group = parser.add_mutually_exclusive_group()

    mode_group.add_argument(
        "--summary", "-s",
        action="store_true",
        help="Show trace summary (violated invariant, trace length, etc.)",
    )

    mode_group.add_argument(
        "--state",
        type=str,
        metavar="INDEX",
        help="Show a specific state (1-indexed, negative for from-end, or 'first'/'last')",
    )

    mode_group.add_argument(
        "--states",
        type=str,
        metavar="RANGE",
        help="Show multiple states (e.g., '1:5', '-3:', '1,5,10')",
    )

    mode_group.add_argument(
        "--diff",
        nargs=2,
        metavar=("STATE1", "STATE2"),
        help="Compare two states and show differences",
    )

    mode_group.add_argument(
        "--track",
        type=str,
        metavar="VARIABLE",
        help="Track changes to a variable across the trace",
    )

    mode_group.add_argument(
        "--actions",
        action="store_true",
        help="Show the sequence of actions in the trace",
    )

    mode_group.add_argument(
        "--variables",
        action="store_true",
        help="List all variables in the trace",
    )

    # Options that modify output
    parser.add_argument(
        "--var", "-v",
        type=str,
        metavar="PATH",
        action="append",
        dest="var_paths",
        help="Variable path to show (can be used multiple times). "
             "Supports dot notation: 'log.s1.entries[0]'",
    )

    parser.add_argument(
        "--json", "-j",
        action="store_true",
        help="Output in JSON format",
    )

    parser.add_argument(
        "--compact", "-c",
        action="store_true",
        help="Compact output (less whitespace)",
    )

    parser.add_argument(
        "--max-depth",
        type=int,
        default=4,
        metavar="N",
        help="Maximum depth for nested structure display (default: 4)",
    )

    return parser


def output_json(data, compact: bool = False) -> None:
    """Output data as JSON."""
    indent = None if compact else 2
    print(json.dumps(data, indent=indent, default=str))


def handle_summary(reader: TLCOutputReader, args) -> None:
    """Handle --summary command."""
    if args.json:
        summary = reader.get_summary()
        output_json({
            "violation_type": summary.violation_type,
            "violation_name": summary.violation_name,
            "trace_length": summary.trace_length,
            "actions": summary.actions,
            "statistics": summary.statistics,
        }, args.compact)
    else:
        print(reader.format_summary())


def handle_state(reader: TLCOutputReader, args) -> None:
    """Handle --state command."""
    # Parse the index
    try:
        if args.state.lower() in ("first", "last"):
            index = args.state.lower()
        else:
            index = int(args.state)
    except ValueError:
        print(f"Error: Invalid state index: {args.state}", file=sys.stderr)
        sys.exit(1)

    # Determine which variables to show
    variables = args.var_paths if args.var_paths else None

    try:
        if args.var_paths and len(args.var_paths) == 1 and '.' in args.var_paths[0]:
            # Single path query - get just that value
            value = reader.get_variable_at_path(index, args.var_paths[0])
            if args.json:
                output_json({"path": args.var_paths[0], "value": value}, args.compact)
            else:
                print(format_value(value, max_depth=args.max_depth))
        else:
            # Get full state or filtered state
            state = reader.get_state(index, variables)
            if args.json:
                output_json({
                    "index": state.index,
                    "action": state.action,
                    "action_detail": state.action_detail,
                    "variables": state.variables,
                }, args.compact)
            else:
                print(reader.format_state(index, variables, max_depth=args.max_depth))
    except (IndexError, ValueError) as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


def handle_states(reader: TLCOutputReader, args) -> None:
    """Handle --states command."""
    variables = args.var_paths if args.var_paths else None

    try:
        states = reader.get_states(args.states, variables)

        if args.json:
            output_json([{
                "index": s.index,
                "action": s.action,
                "variables": s.variables,
            } for s in states], args.compact)
        else:
            for state in states:
                print(reader.format_state(state.index, variables, max_depth=args.max_depth))
                print()
    except (IndexError, ValueError) as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


def handle_diff(reader: TLCOutputReader, args) -> None:
    """Handle --diff command."""
    try:
        index1 = int(args.diff[0]) if args.diff[0].lstrip('-').isdigit() else args.diff[0]
        index2 = int(args.diff[1]) if args.diff[1].lstrip('-').isdigit() else args.diff[1]
    except ValueError:
        print(f"Error: Invalid state indices: {args.diff}", file=sys.stderr)
        sys.exit(1)

    try:
        diff = reader.compare_states(index1, index2)

        if args.json:
            output_json(diff, args.compact)
        else:
            print(f"Comparing State {diff['state1_index']} -> State {diff['state2_index']}")
            print(f"Actions: {diff['state1_action']} -> {diff['state2_action']}")
            print()

            if not diff['changed_variables']:
                print("No changes detected.")
            else:
                print(f"Changed variables ({len(diff['changed_variables'])}):")
                for var_name in diff['changed_variables']:
                    change = diff['changes'][var_name]
                    print(f"\n  {var_name}:")
                    print(f"    Before: {format_value(change['before'], max_depth=2)}")
                    print(f"    After:  {format_value(change['after'], max_depth=2)}")
    except (IndexError, ValueError) as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


def handle_track(reader: TLCOutputReader, args) -> None:
    """Handle --track command."""
    # Check if tracking a path
    if '.' in args.track:
        parts = args.track.split('.', 1)
        var_name, path = parts[0], parts[1]
    else:
        var_name, path = args.track, None

    changes = reader.find_variable_changes(var_name, path)

    if args.json:
        output_json(changes, args.compact)
    else:
        print(f"Tracking: {args.track}")
        print(f"Total changes: {len(changes)}")
        print()

        if not changes:
            print("No changes detected.")
        else:
            for i, change in enumerate(changes, 1):
                print(f"Change {i}: State {change['from_state']} -> {change['to_state']} ({change['action']})")
                if not args.compact:
                    print(f"  Before: {format_value(change['before'], max_depth=2)}")
                    print(f"  After:  {format_value(change['after'], max_depth=2)}")
                    print()


def handle_actions(reader: TLCOutputReader, args) -> None:
    """Handle --actions command."""
    actions = reader.get_actions_list()

    if args.json:
        output_json(actions, args.compact)
    else:
        print(f"Action Sequence ({len(actions)} states):")
        print()
        for action_info in actions:
            if args.compact:
                print(f"{action_info['index']:3d}. {action_info['action']}")
            else:
                print(f"State {action_info['index']:3d}: {action_info['action']}")
                if action_info['detail']:
                    print(f"            {action_info['detail']}")


def handle_variables(reader: TLCOutputReader, args) -> None:
    """Handle --variables command."""
    variables = reader.get_all_variables()

    if args.json:
        output_json(variables, args.compact)
    else:
        print(f"Variables ({len(variables)}):")
        for var in variables:
            print(f"  - {var}")


def main() -> None:
    """Main entry point."""
    parser = create_parser()
    args = parser.parse_args()

    # Validate file exists
    if not Path(args.file).exists():
        print(f"Error: File not found: {args.file}", file=sys.stderr)
        sys.exit(1)

    # Load the TLC output
    try:
        reader = TLCOutputReader(args.file)
    except ValueError as e:
        print(f"Error: Failed to parse TLC output: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    # Default to summary if no operation specified
    if not any([args.summary, args.state, args.states, args.diff, args.track, args.actions, args.variables]):
        args.summary = True

    # Dispatch to appropriate handler
    if args.summary:
        handle_summary(reader, args)
    elif args.state:
        handle_state(reader, args)
    elif args.states:
        handle_states(reader, args)
    elif args.diff:
        handle_diff(reader, args)
    elif args.track:
        handle_track(reader, args)
    elif args.actions:
        handle_actions(reader, args)
    elif args.variables:
        handle_variables(reader, args)


if __name__ == "__main__":
    main()
