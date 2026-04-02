#!/usr/bin/env python3
"""Preprocess NDJSON trace files for TLA+ trace validation.

Maps concrete hex addresses to abstract server IDs (s1, s2, s3)
and concrete block hashes to abstract values (v1, v2, ...).
"""
import json
import sys
from collections import OrderedDict


def collect_ids(events):
    """Collect all unique server IDs and block hash values from trace events."""
    servers = OrderedDict()
    values = OrderedDict()

    for evt in events:
        e = evt["event"]
        nid = e["nid"]
        if nid not in servers:
            servers[nid] = f"s{len(servers) + 1}"

        if "msg" in e:
            msg = e["msg"]
            for field in ("source", "dest"):
                if field in msg and msg[field] and msg[field] not in servers:
                    servers[msg[field]] = f"s{len(servers) + 1}"
            val = msg.get("value", "nil")
            if val and val != "nil" and val not in values:
                values[val] = f"v{len(values) + 1}"

        state = e["state"]
        for field in ("lockedValue", "validValue"):
            val = state.get(field, "nil")
            if val and val != "nil" and val not in values:
                values[val] = f"v{len(values) + 1}"

    return servers, values


def remap_event(evt, servers, values):
    """Remap concrete IDs/values to abstract ones."""
    e = evt["event"]
    e["nid"] = servers.get(e["nid"], e["nid"])

    state = e["state"]
    for field in ("lockedValue", "validValue"):
        val = state.get(field, "nil")
        if val != "nil":
            state[field] = values.get(val, val)

    if "msg" in e:
        msg = e["msg"]
        for field in ("source", "dest"):
            if field in msg and msg[field]:
                msg[field] = servers.get(msg[field], msg[field])
        val = msg.get("value", "nil")
        if val != "nil":
            msg["value"] = values.get(val, val)

    return evt


def main():
    if len(sys.argv) < 2:
        print("Usage: preprocess_trace.py <input.ndjson> [output.ndjson]", file=sys.stderr)
        sys.exit(1)

    input_path = sys.argv[1]
    output_path = sys.argv[2] if len(sys.argv) > 2 else None

    with open(input_path) as f:
        events = [json.loads(line) for line in f if line.strip()]

    servers, values = collect_ids(events)

    print(f"Server mapping: {dict(servers)}", file=sys.stderr)
    print(f"Value mapping:  {dict(values)}", file=sys.stderr)

    remapped = [remap_event(evt, servers, values) for evt in events]

    if output_path:
        with open(output_path, "w") as f:
            for evt in remapped:
                f.write(json.dumps(evt, separators=(",", ":")) + "\n")
    else:
        for evt in remapped:
            print(json.dumps(evt, separators=(",", ":")))


if __name__ == "__main__":
    main()
