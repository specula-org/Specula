# TLA+ Trace Debugger - Systematic Debugging for TLA+ Trace Validation Failures

A comprehensive debugging toolkit for diagnosing TLA+ trace validation failures using the TLC debugger and Debug Adapter Protocol (DAP). This tool enables AI agents and developers to systematically identify and fix trace validation issues through breakpoint statistics, variable inspection, and expression evaluation.

## Table of Contents
- [Overview](#overview)
- [Features](#features)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Tools Reference](#tools-reference)
- [Debug Best Practices](#debug-best-practices)
- [Examples](#examples)
- [Requirements](#requirements)

## Overview

The TLA+ Trace Debugger provides a systematic approach to debugging trace validation failures. When TLC reports "N states generated" and stops, it means validation failed at TraceLog[N]. This tool helps you pinpoint exactly which condition failed and why, using breakpoint statistics and variable inspection.

**Key Capabilities:**
- Set conditional breakpoints in TLA+ specs
- Collect statistics on which breakpoints were hit (and how many times)
- Evaluate TLA+ expressions at breakpoints
- Inspect variable values during execution
- Quick syntax validation
- Trace file information retrieval

## Features

### Tools

| Tool | Description | Required Parameters | Optional Parameters | Example Request |
|------|-------------|---------------------|---------------------|-----------------|
| **run_trace_validation** | Run trace validation with breakpoints and collect hit statistics. This is the core debugging tool. | `spec_file` (string): TLA+ spec file name<br>`config_file` (string): TLC config file name<br>`trace_file` (string): Trace file path (relative or absolute)<br>`work_dir` (string): Working directory (absolute path)<br>`breakpoints` (array): List of breakpoint objects | `timeout` (integer, default: 300): Timeout in seconds<br>`tla_jar` (string): Path to tla2tools.jar<br>`community_jar` (string): Path to CommunityModules-deps.jar<br>`host` (string, default: "127.0.0.1"): DAP server host<br>`port` (integer, default: 4712): DAP server port<br>`evaluate` (object): Expression evaluation config<br>`collect_variables` (object): Variable collection config | Run validation with breakpoints at lines 522, 489, 323 with condition `TLCGet("level") = 29` to debug trace line 29 |
| **validate_spec_syntax** | Validate TLA+ spec syntax without running full trace validation. Fast syntax check. | `spec_file` (string): TLA+ spec file name<br>`config_file` (string): TLC config file name<br>`work_dir` (string): Working directory (absolute path) | `tla_jar` (string): Path to tla2tools.jar | Validate syntax of Traceetcdraft_progress.tla before running full validation |
| **get_trace_info** | Get basic information about a trace file (line count, size, first/last lines) without running TLC. | `trace_file` (string): Path to trace file (absolute or relative) | None | Check how many lines are in the trace file to understand validation scope |

### Breakpoint Object Schema

Each breakpoint in the `breakpoints` array must have:

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `line` | integer | **Yes** | Line number for the breakpoint |
| `file` | string | No | Source file name (defaults to spec_file if not specified) |
| `condition` | string | No | TLA+ expression to conditionally trigger breakpoint (e.g., `TLCGet("level") = 29`) |
| `description` | string | No | Human-readable description for reporting |

**Example breakpoint:**
```json
{
  "line": 522,
  "file": "Traceetcdraft_progress.tla",
  "condition": "TLCGet(\"level\") = 29",
  "description": "TraceNext entry point"
}
```

### Evaluate Object Schema (Optional)

Used with `run_trace_validation` to evaluate expressions when a specific breakpoint is hit:

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `breakpoint_line` | integer | **Yes** | Line number of the breakpoint where evaluation happens |
| `breakpoint_file` | string | No | File name (optional, matches any if not specified) |
| `expressions` | array of strings | **Yes** | List of TLA+ expressions to evaluate |

**Example:**
```json
{
  "breakpoint_line": 323,
  "breakpoint_file": "Traceetcdraft_progress.tla",
  "expressions": ["l", "i", "j", "logline.event.msg.type"]
}
```

### Collect Variables Object Schema (Optional)

Used with `run_trace_validation` to collect variable values when a specific breakpoint is hit:

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `breakpoint_line` | integer | **Yes** | Line number of the breakpoint where collection happens |
| `breakpoint_file` | string | No | File name (optional, matches any if not specified) |
| `variables` | array of strings | **Yes** | List of variable names or expressions to collect |
| `max_samples` | integer | No | Maximum number of samples to collect (default: 10) |

**Example:**
```json
{
  "breakpoint_line": 327,
  "variables": ["i", "j", "state[i].currentTerm", "logline.event.msg.index"],
  "max_samples": 5
}
```

### Tool Responses

#### run_trace_validation Response

```json
{
  "statistics": {
    "total_hits": 150,
    "breakpoints": [
      {
        "file": "Traceetcdraft_progress.tla",
        "line": 522,
        "description": "TraceNext entry",
        "hit_count": 100,
        "was_hit": true
      },
      {
        "file": "Traceetcdraft_progress.tla",
        "line": 327,
        "description": "AppendEntries call",
        "hit_count": 0,
        "was_hit": false
      }
    ],
    "never_hit": [
      {
        "file": "Traceetcdraft_progress.tla",
        "line": 327,
        "description": "AppendEntries call"
      }
    ]
  },
  "execution_time": 45.2,
  "evaluated_expressions": [
    {
      "expression": "l",
      "result": "29",
      "file": "Traceetcdraft_progress.tla",
      "line": 323
    }
  ],
  "collected_variables": [
    {
      "sample_index": 0,
      "file": "Traceetcdraft_progress.tla",
      "line": 327,
      "variables": {
        "i": "1",
        "j": "2",
        "state[i].currentTerm": "3"
      }
    }
  ]
}
```

#### validate_spec_syntax Response

```json
{
  "syntax_valid": false,
  "output": "Error: Unknown operator: AppendEntriesx\n...",
  "errors": [
    "Error: Unknown operator: AppendEntriesx at line 327"
  ],
  "spec_file": "Traceetcdraft_progress.tla",
  "config_file": "Traceetcdraft_progress.cfg",
  "work_dir": "/path/to/spec"
}
```

#### get_trace_info Response

```json
{
  "line_count": 100,
  "file_size_bytes": 45678,
  "first_lines": [
    "{\"event\": \"Init\", ...}",
    "{\"event\": \"SendAppendEntriesRequest\", ...}",
    "..."
  ],
  "last_lines": [
    "{\"event\": \"HandleAppendEntriesResponse\", ...}",
    "..."
  ],
  "trace_file": "/path/to/trace.ndjson"
}
```

## Debug Best Practices

The TLA+ Trace Debugger follows systematic debugging practices based on the **layered debugging methodology** (from coarse-grained to fine-grained localization). For detailed methodology, see [debugging_guide.md](docs/debugging_guide.md) and [debugging_guide_en.md](docs/debugging_guide_en.md).

### Core Debugging Methodology

#### 1. Understand the Failure Context

**Before setting any breakpoints, understand WHAT failed:**

- TLC reports "N states generated" means validation **failed at TraceLog[N]** (not N+1)
- Variable `l=N` means "currently validating TraceLog[N]"
- Use `get_trace_info` to check trace file size and content
- Read TraceLog[N] to understand what event should be validated

**Example:**
```
TLC Output: "29 states generated, 0 states left on queue"
→ This means: Failed to validate TraceLog[29]
→ Current state: l=29
→ Next step: Find which action/condition failed for this trace line
```

#### 2. Start with Entry Points (Coarse-Grained Localization)

**Set breakpoints at major branch points to identify which path the execution takes:**

- Set breakpoints at the top-level action (e.g., `TraceNext`) and all major branches
- **Always use conditional breakpoints** with `TLCGet("level") = N` to focus on the failing trace line
- Use `TLCGet("level")` instead of `l` because it works in all contexts (even in base spec files where `l` may not be in scope)
- Examine hit counts to see which branches were attempted and which succeeded

**Why use `TLCGet("level") = N` instead of `l = N`?**
- `l` is only defined in the Trace wrapper spec (e.g., `Traceetcdraft_progress.tla`)
- When breakpoints are in the base spec (e.g., `etcdraft_progress.tla`), `l` may not be in scope
- `TLCGet("level")` is a TLC built-in function, accessible everywhere
- During validation of TraceLog[N] (when l=N), `TLCGet("level") = N`

**Example:**
```json
{
  "breakpoints": [
    {
      "line": 522,
      "condition": "TLCGet(\"level\") = 29",
      "description": "TraceNext main entry"
    },
    {
      "line": 489,
      "condition": "TLCGet(\"level\") = 29",
      "description": "SendAppendEntriesRequest branch"
    },
    {
      "line": 476,
      "condition": "TLCGet(\"level\") = 29",
      "description": "HandleAppendEntriesResponse branch"
    }
  ]
}
```

**Interpreting Results:**
- Line 522 hit 100 times, Line 489 hit 18 times, Line 476 hit 0 times
- → Execution went through SendAppendEntriesRequest branch
- → Need to debug deeper inside line 489's path

#### 3. Narrow Down to Specific Conditions (Fine-Grained Localization)

**Once you know which branch failed, set breakpoints at each condition in that branch:**

- Set breakpoints at every conjunct (`/\`) in the failing action
- Use the **same condition** (`TLCGet("level") = N`) on all breakpoints
- Analyze hit count **patterns**:
  - **Decreasing hit counts** indicate short-circuit evaluation filtering
  - **First line with 0 hits** is where the failure occurs
  - **If last hit is an action call**, the action was entered but failed internally → debug inside that action

**Example:**
```json
{
  "breakpoints": [
    {
      "line": 323,
      "condition": "TLCGet(\"level\") = 29",
      "description": "LoglineIsMessageEvent check"
    },
    {
      "line": 324,
      "condition": "TLCGet(\"level\") = 29",
      "description": "Message type check"
    },
    {
      "line": 325,
      "condition": "TLCGet(\"level\") = 29",
      "description": "Range check"
    },
    {
      "line": 327,
      "condition": "TLCGet(\"level\") = 29",
      "description": "AppendEntries action call"
    }
  ]
}
```

**Hit Pattern Analysis:**
```
Line 323: 18 hits  → Tried 18 different (i,j,range) combinations
Line 324: 18 hits  → All 18 passed message event check
Line 325: 18 hits  → All 18 passed message type check
Line 327: 1 hit    → AppendEntries was called (entered)
Line 328: 0 hits   → AppendEntries returned FALSE
```

**Conclusion:** AppendEntries action was called but failed internally. Next step: Set breakpoints **inside** AppendEntries.

#### 4. Inspect Variables at Failure Point

**Use `evaluate` or `collect_variables` to understand WHY a condition failed:**

- Evaluate key variables at the last successful breakpoint
- Check if variable values match expectations
- Compare with trace file content (TraceLog[N])

**Example with evaluate:**
```json
{
  "evaluate": {
    "breakpoint_line": 327,
    "expressions": [
      "i",
      "j",
      "logline.event.msg.index",
      "state[i].log",
      "Len(state[i].log)"
    ]
  }
}
```

**Example with collect_variables:**
```json
{
  "collect_variables": {
    "breakpoint_line": 327,
    "variables": ["i", "j", "state[i].currentTerm", "state[j].currentTerm"],
    "max_samples": 5
  }
}
```

#### 5. Iterative Refinement

**Repeat the process:**
- If an action call failed, set breakpoints inside that action
- Use the same conditional breakpoint pattern (`TLCGet("level") = N`)
- Continue until you find the specific condition that evaluates to FALSE
- Verify your hypothesis by inspecting variable values

### Essential Background Knowledge

Before debugging, agents should understand these core concepts (see [background.md](docs/background.md) for details):

- **State Numbering**: TLC states start at 1, not 0
- **Variable `l` Semantics**: `l=N` means "currently validating TraceLog[N]", not "validated N lines"
- **Conjunction Evaluation**: All conditions in `/\` must be TRUE; TLC uses short-circuit evaluation (typically top to bottom)
- **Breakpoint Hit Semantics**: Hitting a breakpoint means "attempting to evaluate", not "condition is TRUE"
- **Action Calls**: Action calls count as "hit" even when they return FALSE; must check inside the action
- **TLCGet("level") Timing**: During validation of TraceLog[N] (l=N), `TLCGet("level") = N`

### Common Pitfalls to Avoid

❌ **WRONG:** Setting breakpoints without conditions → Too many hits, hard to analyze

✅ **CORRECT:** Always use `TLCGet("level") = N` to focus on specific trace line

---

❌ **WRONG:** Using `l = N` in breakpoint conditions for all files

✅ **CORRECT:** Use `TLCGet("level") = N` which works in all contexts

---

❌ **WRONG:** Assuming a breakpoint hit means the condition is TRUE

✅ **CORRECT:** Inspect variable values to verify if conditions are satisfied

---

❌ **WRONG:** Stopping analysis when an action is called (last hit)

✅ **CORRECT:** If last hit is an action call, debug inside that action to find internal failure

---

❌ **WRONG:** Misinterpreting "N states generated" as "validated N lines, failed at N+1"

✅ **CORRECT:** "N states generated" means "failed to validate TraceLog[N]"

### Systematic Debugging Checklist

Before starting:
- [ ] Understand which trace line failed (from TLC output: "N states generated" → TraceLog[N])
- [ ] Read the trace file to see what event TraceLog[N] contains
- [ ] Verify spec syntax is valid using `validate_spec_syntax`

Step 1 - Coarse localization:
- [ ] Set breakpoints at major branches with `TLCGet("level") = N`
- [ ] Run and analyze which branch was taken
- [ ] Identify the specific action that failed

Step 2 - Fine localization:
- [ ] Set breakpoints at each condition inside the failing action
- [ ] Use the same condition `TLCGet("level") = N` on all breakpoints
- [ ] Analyze hit count pattern (decreasing counts show filtering)
- [ ] Find the first line with 0 hits (the failing condition)

Step 3 - Root cause analysis:
- [ ] If last hit is an action call, repeat Step 2 inside that action
- [ ] Use `evaluate` or `collect_variables` to inspect values at failure point
- [ ] Compare variable values with trace file expectations
- [ ] Determine WHY the condition is FALSE (spec bug vs trace bug)

## Installation

### Prerequisites

- **Java 11+**: Required to run TLC
- **Python 3.8+**: Required for the debugger tool
- **TLA+ Tools**: `tla2tools.jar` and `CommunityModules-deps.jar`

### Setup

1. **Install Dependencies:**
   ```bash
   cd tools/trace_debugger
   pip install -r requirements.txt
   ```

2. **Verify TLA+ JAR Files:**
   ```bash
   # Default location: specula/lib/
   ls $SPECULA_ROOT/lib/tla2tools.jar
   ls $SPECULA_ROOT/lib/CommunityModules-deps.jar
   ```

   If not present, download from:
   - [TLA+ Tools](https://github.com/tlaplus/tlaplus/releases)
   - [CommunityModules](https://github.com/tlaplus/CommunityModules/releases)

3. **Set Environment Variable (Optional):**
   ```bash
   export SPECULA_ROOT=/path/to/specula
   ```

## Quick Start

### Example 1: Basic Debugging with Breakpoint Statistics

**Scenario:** TLC reports "29 states generated", need to find why validation failed at TraceLog[29].

```python
import asyncio
from tla_mcp.handlers.trace_validation import TraceValidationHandler

async def debug_trace_line_29():
    handler = TraceValidationHandler()

    result = await handler.execute({
        "spec_file": "Traceetcdraft_progress.tla",
        "config_file": "Traceetcdraft_progress.cfg",
        "trace_file": "../traces/confchange_disable_validation.ndjson",
        "work_dir": "/path/to/spec",
        "breakpoints": [
            {
                "line": 522,
                "condition": "TLCGet(\"level\") = 29",
                "description": "TraceNext entry"
            },
            {
                "line": 489,
                "condition": "TLCGet(\"level\") = 29",
                "description": "SendAppendEntriesRequest branch"
            },
            {
                "line": 323,
                "condition": "TLCGet(\"level\") = 29",
                "description": "AppendEntriesIfLogged entry"
            }
        ],
        "timeout": 120
    })

    # Analyze results
    stats = result["statistics"]
    print(f"Total hits: {stats['total_hits']}")
    for bp in stats["breakpoints"]:
        print(f"Line {bp['line']}: {bp['hit_count']} hits - {bp['description']}")

asyncio.run(debug_trace_line_29())
```

### Example 2: Variable Inspection

**Scenario:** Need to understand why AppendEntries fails by inspecting variable values.

```python
result = await handler.execute({
    "spec_file": "Traceetcdraft_progress.tla",
    "config_file": "Traceetcdraft_progress.cfg",
    "trace_file": "../traces/confchange_disable_validation.ndjson",
    "work_dir": "/path/to/spec",
    "breakpoints": [
        {
            "line": 327,
            "condition": "TLCGet(\"level\") = 29",
            "description": "AppendEntries call"
        }
    ],
    "collect_variables": {
        "breakpoint_line": 327,
        "variables": ["i", "j", "state[i].currentTerm", "state[j].currentTerm"],
        "max_samples": 3
    },
    "timeout": 120
})

# Check collected samples
for sample in result["collected_variables"]:
    print(f"Sample {sample['sample_index']}:")
    for var, value in sample["variables"].items():
        print(f"  {var} = {value}")
```

### Example 3: Expression Evaluation

**Scenario:** Evaluate complex expressions to understand state.

```python
result = await handler.execute({
    "spec_file": "Traceetcdraft_progress.tla",
    "config_file": "Traceetcdraft_progress.cfg",
    "trace_file": "../traces/confchange_disable_validation.ndjson",
    "work_dir": "/path/to/spec",
    "breakpoints": [
        {
            "line": 323,
            "condition": "TLCGet(\"level\") = 29",
            "description": "Check point"
        }
    ],
    "evaluate": {
        "breakpoint_line": 323,
        "expressions": [
            "l",
            "logline.event.msg.type",
            "Len(state[i].log)",
            "state[i].log[Len(state[i].log)]"
        ]
    },
    "timeout": 120
})

# Check evaluation results
for eval_result in result["evaluated_expressions"]:
    print(f"{eval_result['expression']} = {eval_result['result']}")
```

## Examples

The `examples/demo/` directory contains complete demonstrations:

1. **coarse_grained_localization.py**: Shows how to identify which major branch failed
2. **fine_grained_localization.py**: Shows how to narrow down to specific failing condition
3. **variable_inspection.py**: Shows how to inspect variables and evaluate expressions

## Requirements

### System Requirements

- **Operating System**: Linux, macOS, Windows (with WSL recommended)
- **Memory**: 4GB+ RAM (for TLC model checking)
- **Disk Space**: 1GB for tools and temporary files

### Software Requirements

- **Java**: JDK 11 or higher
- **Python**: 3.8 or higher
- **TLA+ Tools**: tla2tools.jar (version 1.7.1+)
- **CommunityModules**: CommunityModules-deps.jar (for JSON support)

### Python Dependencies

See `requirements.txt`:
```
# Core dependencies are minimal - mainly for MCP server integration
```

## Documentation

- **[debugging_guide.md](docs/debugging_guide.md)**: Comprehensive debugging methodology (Chinese)
- **[debugging_guide_en.md](docs/debugging_guide_en.md)**: Comprehensive debugging methodology (English)
- **[background.md](docs/background.md)**: Essential background knowledge on TLA+ trace validation, TLCGet("level"), and debugger semantics

## Architecture

The trace debugger consists of three main components:

1. **TLC Executor** (`executor/tlc_process.py`): Manages TLC process with debugger enabled
2. **DAP Client** (`client/dap_client.py`): Implements Debug Adapter Protocol client
3. **Debug Session** (`debugger/session.py`): High-level API for debugging sessions
4. **MCP Handlers** (`tla_mcp/handlers/`): Tool handlers for MCP server integration

## Troubleshooting

### Issue: "Failed to connect DAP client"

**Symptoms:** Debugger cannot connect to TLC

**Solutions:**
- Verify TLC started with debugger enabled (check for "Debugger is listening" message)
- Ensure port 4712 (default) is not in use
- Check firewall settings

### Issue: "Breakpoint never hit"

**Symptoms:** All breakpoints show 0 hits

**Solutions:**
- Verify the condition is correct (e.g., `TLCGet("level") = 29` matches the failing trace line)
- Check if the line number is correct (corresponds to actual TLA+ code, not comments)
- Ensure the file name matches (use `TLCGet("level")` instead of `l` to avoid scope issues)

### Issue: "Timeout after 300 seconds"

**Symptoms:** Validation times out before completion

**Solutions:**
- Increase timeout parameter
- Reduce number of breakpoints
- Use conditional breakpoints to limit hits
- Check if TLC is stuck (memory issues)


## Contributing

Contributions are welcome! Please see the main repository's contributing guidelines.
