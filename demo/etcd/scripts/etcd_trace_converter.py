#!/usr/bin/env python3
"""
Convert etcd raft trace to TLA+ trace format for specTrace.tla validation
"""
import json
import sys
import argparse

def convert_trace(input_file, output_file):
    """Convert etcd trace to TLA+ format"""

    with open(input_file, 'r') as f:
        events = [json.loads(line.strip()) for line in f if line.strip()]

    if not events:
        print("No events found in input trace")
        return

    output_lines = []

    # Line 1: Configuration
    config = {
        "Server": ["1", "2", "3"],
        "MaxTerm": ["3"],
        "MaxLogLen": ["3"],
        "None": ["0"]
    }
    output_lines.append(json.dumps(config))

    # Track state for each node
    node_states = {
        "1": {"term": 0, "state": "StateFollower"},
        "2": {"term": 0, "state": "StateFollower"},
        "3": {"term": 0, "state": "StateFollower"}
    }

    # Process each event
    for event in events:
        # Handle both old format (action/node_id) and new format (name/nid)
        action = event.get("name") or event.get("action", "Step")
        node_id = str(event.get("nid") or event.get("node_id", "1"))

        # Skip tickElection events - not in spec
        if action == "tickElection":
            continue

        # Update node state - handle both formats
        if "cluster_state" in event:
            # Old format from raft_simulator
            for nid, nstate in event["cluster_state"].items():
                node_key = nid.replace("node_", "")
                if node_key in node_states:
                    node_states[node_key]["term"] = nstate.get("term", 0)
                    node_states[node_key]["state"] = nstate.get("state", "Follower")
        elif "state" in event:
            # New format from instrumented trace
            if node_id in node_states:
                node_states[node_id]["term"] = event["state"].get("term", 0)
            if "role" in event:
                role = event["role"].replace("State", "")
                if node_id in node_states:
                    node_states[node_id]["state"] = "State" + role

        # Build TLA+ trace line with state updates
        trace_line = {
            "currentTerm": [{
                "op": "Update",
                "path": [],
                "args": [{
                    "1": node_states["1"]["term"],
                    "2": node_states["2"]["term"],
                    "3": node_states["3"]["term"]
                }]
            }],
            "state": [{
                "op": "Update",
                "path": [],
                "args": [{
                    "1": "State" + node_states["1"]["state"].replace("State", ""),
                    "2": "State" + node_states["2"]["state"].replace("State", ""),
                    "3": "State" + node_states["3"]["state"].replace("State", "")
                }]
            }],
            "event": action
        }

        output_lines.append(json.dumps(trace_line))

    # Write output
    with open(output_file, 'w') as f:
        for line in output_lines:
            f.write(line + '\n')

    print(f"Converted {len(output_lines)-1} events (plus config)")
    print(f"Output: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='Convert etcd trace to TLA+ format')
    parser.add_argument('input', help='Input trace file (NDJSON)')
    parser.add_argument('output', help='Output trace file')
    args = parser.parse_args()

    convert_trace(args.input, args.output)

if __name__ == '__main__':
    main()
