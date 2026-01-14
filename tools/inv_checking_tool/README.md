# TLC Output Reader

A tool for parsing and analyzing TLC model checker output, designed to help AI agents debug invariant violations efficiently.

## Features

- **Parse TLC Output**: Handles various formats including raw TLC output, simulation logs, and wrapped output with ANSI codes
- **State Navigation**: Access states by index (1-indexed, negative, "first"/"last")
- **Nested Path Query**: Query nested values using dot notation (e.g., `log.s1.entries[0].term`)
- **State Comparison**: Find differences between any two states
- **Variable Tracking**: Track changes to a variable across the entire trace
- **MCP Integration**: Expose functionality as MCP tools for AI agents

## Directory Structure

```
tools/inv_checking_tool/
├── __init__.py                    # Package exports
├── __main__.py                    # CLI entry (python -m)
├── mcp_server.py                  # MCP server entry point
├── README.md
├── src/
│   ├── trace_reader.py            # TLA+ parser
│   ├── tlc_output_reader.py       # Main TLCOutputReader class
│   ├── cli.py                     # Command-line interface
│   ├── utils/
│   │   ├── preprocessing.py       # File preprocessing
│   │   └── path_parser.py         # Path parsing utilities
│   └── mcp/
│       ├── server.py              # MCP server implementation
│       └── handlers/              # MCP tool handlers
│           ├── summary.py         # get_tlc_summary
│           ├── state.py           # get_tlc_state
│           └── compare.py         # compare_tlc_states
└── tests/
    ├── test_tlc_output_reader.py  # 50 core tests
    └── test_mcp_handlers.py       # 14 MCP handler tests
```

## Installation

No additional dependencies required beyond the standard library and `mcp` package.

## Usage

### Command Line Interface

```bash
# Show summary
python -m tools.inv_checking_tool nohup.out --summary

# Show specific state
python -m tools.inv_checking_tool nohup.out --state 1
python -m tools.inv_checking_tool nohup.out --state last
python -m tools.inv_checking_tool nohup.out --state -1

# Show multiple states
python -m tools.inv_checking_tool nohup.out --states 1:5
python -m tools.inv_checking_tool nohup.out --states="-3:"

# Query nested variable
python -m tools.inv_checking_tool nohup.out --state last --var currentTerm.s1

# Compare states
python -m tools.inv_checking_tool nohup.out --diff -2 -1

# Track variable changes
python -m tools.inv_checking_tool nohup.out --track state.s1

# JSON output
python -m tools.inv_checking_tool nohup.out --summary --json
```

### Python API

```python
from tools.inv_checking_tool import TLCOutputReader

reader = TLCOutputReader("path/to/nohup.out")

# Get summary
summary = reader.get_summary()
print(f"Violated: {summary.violation_name}")
print(f"Trace length: {summary.trace_length}")

# Get state (1-indexed, supports negative indexing)
first_state = reader.get_state(1)
last_state = reader.get_state(-1)
last_state = reader.get_state("last")

# Query nested value
term = reader.get_variable_at_path(-1, "currentTerm.s1")
entry = reader.get_variable_at_path(1, "log.s1.entries[0].term")

# Compare states
diff = reader.compare_states(-2, -1)
print(diff["changed_variables"])

# Track variable changes
changes = reader.find_variable_changes("currentTerm")

# Search states with predicate
leader_states = reader.search_states(
    lambda s: s.get("state", {}).get("s1") == "Leader"
)
```

### MCP Server

Start the MCP server:

```bash
python tools/inv_checking_tool/mcp_server.py
```

Add to your MCP client configuration (e.g., Claude Desktop):

```json
{
  "mcpServers": {
    "tlc-output-reader": {
      "command": "python3",
      "args": ["/path/to/tools/inv_checking_tool/mcp_server.py"],
      "env": {
        "SPECULA_ROOT": "/path/to/Specula"
      }
    }
  }
}
```

## MCP Tools

### 1. `get_tlc_summary`

Get a high-level overview of TLC model checking results.

**Input:**
```json
{
  "file_path": "/path/to/nohup.out"
}
```

**Output:**
```json
{
  "success": true,
  "violation_type": "invariant",
  "violation_name": "QuorumLogInv",
  "trace_length": 76,
  "actions": ["MCInit", "MCRestart(s1)", ...],
  "action_frequency": {"MCNextAsync": 49, "MCNextDynamic": 19, ...},
  "statistics": {"states_generated": 148265621, ...},
  "variables": ["currentTerm", "state", "log", ...]
}
```

### 2. `get_tlc_state`

Get state information from a TLC error trace.

**Examples:**

```json
// Get last state
{"file_path": "nohup.out", "index": -1}

// Get last 3 states
{"file_path": "nohup.out", "indices": "-3:"}

// Query nested value
{"file_path": "nohup.out", "index": "last", "path": "currentTerm.s1"}

// Filter to specific variables
{"file_path": "nohup.out", "index": 1, "variables": ["currentTerm", "state"]}
```

### 3. `compare_tlc_states`

Compare states or track variable changes.

**Compare mode:**
```json
{
  "file_path": "nohup.out",
  "index1": -2,
  "index2": -1
}
```

**Track mode:**
```json
{
  "file_path": "nohup.out",
  "track_variable": "currentTerm"
}
```

## Testing

```bash
# Run all tests
python -m pytest tools/inv_checking_tool/tests/ -v

# Run specific test file
python -m pytest tools/inv_checking_tool/tests/test_tlc_output_reader.py -v
python -m pytest tools/inv_checking_tool/tests/test_mcp_handlers.py -v
```

## Supported Input Formats

1. **Raw TLC output** - Starting with `@!`
2. **Wrapped output** - With script headers and ANSI color codes
3. **Simulation logs** - From `tlc -simulate`
4. **Direct trace files** - Starting with `--`

The tool automatically detects the format and preprocesses accordingly.

## Path Syntax

Nested values can be accessed using dot notation with optional array indices:

| Path | Description |
|------|-------------|
| `currentTerm` | Top-level variable |
| `currentTerm.s1` | Nested access |
| `log.s1.entries[0]` | Array index |
| `log.s1.entries[0].term` | Deep nested |

## License

Part of the Specula project.
