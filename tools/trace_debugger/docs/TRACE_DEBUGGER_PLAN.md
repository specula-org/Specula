# TLA+ Trace Validation Debugger Implementation Plan

## Overview

This tool provides a systematic debugging framework for TLA+ trace validation failures. It supports **agent-driven, layered debugging** where the agent decides where to place breakpoints based on findings at each layer.

## Design Principles

1. **Agent-Driven, Tool-Assisted**
   - Agent decides where to set breakpoints (based on current findings)
   - Tool executes and collects information
   - No automatic "next step" decisions

2. **Layered Debugging Support**
   - Agent can run multiple sessions (one per layer)
   - Each session is independent
   - Tool does not maintain "debugging history" (agent tracks it)

3. **Information Density First**
   - One run collects as much information as possible (breakpoint statistics)
   - Avoid requiring multiple runs for basic information

4. **Simple and Flexible**
   - Core interface is simple (DebugSession)
   - Advanced features are optional
   - Agent can compose features as needed

## Core Components

### 1. DebugSession Class (Core Session Management)

**Responsibilities:**
- Launch TLC debugger process
- Manage DAP connection
- Provide basic DAP operations (set breakpoints, continue, inspect variables)

**Interface:**
```python
class DebugSession:
    def __init__(self, spec_file, config_file, trace_file, work_dir,
                 tla_jar=None, community_jar=None):
        """Initialize debug session

        Args:
            spec_file: TLA+ spec file name (e.g., "Traceetcdraft_progress.tla")
            config_file: TLC config file name
            trace_file: Path to trace file (relative to work_dir)
            work_dir: Working directory (absolute path)
            tla_jar: Path to tla2tools.jar (optional, uses default if None)
            community_jar: Path to CommunityModules-deps.jar (optional)
        """

    def start(self):
        """Start TLC debugger and establish connection

        Returns:
            bool: True if successful, False otherwise
        """

    def set_breakpoints(self, breakpoints: List[Breakpoint]):
        """Set breakpoints

        Args:
            breakpoints: List of breakpoints, each containing:
                - file: File name (optional, defaults to spec_file)
                - line: Line number
                - condition: Condition (optional, TLA+ expression)
                - description: Description (for reporting)
        """

    def run_until_done(self, max_hits: int = None,
                       timeout: int = None) -> BreakpointStatistics:
        """Run until termination or limit reached

        Args:
            max_hits: Maximum breakpoint hits (None = unlimited)
            timeout: Timeout in seconds (None = no timeout)

        Returns:
            BreakpointStatistics: Collected statistics
        """

    def evaluate_at_breakpoint(self, expression: str,
                               frame_id: int = 0) -> str:
        """Evaluate expression at current breakpoint

        Called when breakpoint is hit. Evaluates a TLA+ expression.

        Args:
            expression: TLA+ expression to evaluate
            frame_id: Stack frame ID (default 0 = top frame)

        Returns:
            str: Evaluation result, or None if failed
        """

    def get_variables_at_breakpoint(self, var_names: List[str],
                                    frame_id: int = 0) -> Dict[str, str]:
        """Get variable values at current breakpoint

        Args:
            var_names: List of variable names
            frame_id: Stack frame ID

        Returns:
            Dict mapping variable names to values
        """

    def close(self):
        """Close connection and terminate TLC process"""
```

### 2. Breakpoint Data Class

```python
@dataclass
class Breakpoint:
    line: int
    file: str = None  # None = use default spec file
    condition: str = None  # TLA+ expression
    description: str = ""
```

### 3. BreakpointStatistics Data Class

```python
@dataclass
class BreakpointHit:
    file: str
    line: int
    description: str
    hit_count: int

@dataclass
class BreakpointStatistics:
    hits: List[BreakpointHit]
    total_hits: int

    def get_hit_count(self, line: int, file: str = None) -> int:
        """Get hit count for a specific breakpoint"""

    def get_never_hit(self) -> List[BreakpointHit]:
        """Get breakpoints that were never hit"""

    def print_summary(self):
        """Print statistics summary with ✅/❌ indicators"""
```

### 4. Advanced Utility Functions (Optional)

#### 4.1 Condition Checker
```python
def check_conditions_at_breakpoint(
    session: DebugSession,
    conditions: Dict[str, str]
) -> Dict[str, Any]:
    """Check multiple conditions at current breakpoint

    Args:
        session: Debug session (must be at a stopped state)
        conditions: {"description": "TLA+ expression"}

    Returns:
        {"description": evaluation_result}
    """
```

#### 4.2 Variable Value Collector
```python
def collect_variable_values(
    session: DebugSession,
    breakpoint_line: int,
    condition: str,
    variables: List[str],
    max_samples: int = 10
) -> List[Dict[str, Any]]:
    """Collect variable values across multiple breakpoint hits

    Args:
        session: Debug session
        breakpoint_line: Line number for breakpoint
        condition: Breakpoint condition
        variables: Variables to collect
        max_samples: Maximum samples to collect

    Returns:
        List of dicts, each containing variable values for one hit
    """
```

## Usage Examples

### Example 1: Coarse-Grained Localization (Phase 2)

```python
from trace_debugger import DebugSession, Breakpoint

session = DebugSession(
    spec_file="Traceetcdraft_progress.tla",
    config_file="Traceetcdraft_progress.cfg",
    trace_file="../traces/confchange_disable_validation.ndjson",
    work_dir="/path/to/spec"
)

# Agent decides where to place breakpoints (coarse-grained)
breakpoints = [
    Breakpoint(line=522, condition="l = 29", description="TraceNext entry"),
    Breakpoint(line=489, condition="l = 29", description="SendAppendEntriesRequest"),
    Breakpoint(line=487, condition="l = 29", description="Commit branch"),
]

session.start()
session.set_breakpoints(breakpoints)

# Run and collect statistics
stats = session.run_until_done(max_hits=50)

# Analyze results
stats.print_summary()
# Output:
#   ✅ Line 522: 1 hit  - TraceNext entry
#   ✅ Line 489: 1 hit  - SendAppendEntriesRequest
#   ❌ Line 487: 0 hits - Commit branch

# Agent decides next step based on results: dive into Line 489
session.close()
```

### Example 2: Fine-Grained Localization (Phase 3)

```python
# Agent dives into AppendEntriesIfLogged based on Phase 2 findings
session = DebugSession(...)

breakpoints = [
    Breakpoint(line=323, condition="l = 29", description="AppendEntriesIfLogged entry"),
    Breakpoint(line=327, condition="l = 29", description="AppendEntries call"),
    Breakpoint(line=328, condition="l = 29", description="ValidateAfterAppendEntries"),
]

session.start()
session.set_breakpoints(breakpoints)
stats = session.run_until_done(max_hits=50)

stats.print_summary()
# Output:
#   ✅ Line 323: 18 hits - AppendEntriesIfLogged entry
#   ❌ Line 327: 0 hits  - AppendEntries call
#   ❌ Line 328: 0 hits  - ValidateAfterAppendEntries

# Agent discovers Line 327 never executed, decides to dive deeper
session.close()
```

### Example 3: Deep Dive into Function (Phase 4)

```python
# Agent dives into AppendEntriesInRangeToPeer (different file)
session = DebugSession(...)

breakpoints = [
    Breakpoint(line=436, file="etcdraft_progress.tla", condition="l = 29",
               description="i /= j"),
    Breakpoint(line=437, file="etcdraft_progress.tla", condition="l = 29",
               description="range[1] <= range[2]"),
    Breakpoint(line=438, file="etcdraft_progress.tla", condition="l = 29",
               description="state[i] = Leader"),
    Breakpoint(line=439, file="etcdraft_progress.tla", condition="l = 29",
               description="j in Config/Learners"),
]

session.start()
session.set_breakpoints(breakpoints)
stats = session.run_until_done(max_hits=50)

stats.print_summary()
# Output:
#   ✅ Line 436: 10 hits - i /= j
#   ✅ Line 437: 5 hits  - range[1] <= range[2]
#   ✅ Line 438: 3 hits  - state[i] = Leader
#   ❌ Line 439: 0 hits  - j in Config/Learners  ← First failure

# Agent discovers Line 439 never hit, decides to inspect variables
session.close()
```

### Example 4: Variable Inspection (Phase 5)

```python
from trace_debugger import DebugSession, Breakpoint, collect_variable_values

session = DebugSession(...)

# Agent collects variable values at Line 438 (before Line 439)
values = collect_variable_values(
    session,
    breakpoint_line=438,
    condition="l = 29",
    variables=["i", "j", "GetConfig(i)", "GetLearners(i)"],
    max_samples=10
)

# Analyze results
for v in values:
    print(f"i={v['i']}, j={v['j']}")
    print(f"  GetConfig({v['i']}) = {v['GetConfig(i)']}")
    j_in_set = v['j'] in parse_set(v['GetConfig(i)'])
    print(f"  j in GetConfig? {j_in_set}")

# Output:
#   i=1, j=2
#     GetConfig(1) = {"1"}
#     j in GetConfig? False  ← Root cause found!
```

## Implementation Priority

### P0 (Must Have - Core Functionality)
1. DebugSession basic features (start, connect, breakpoints, run, close)
2. Breakpoint data class
3. BreakpointStatistics and collection
4. Multi-file breakpoint support

### P1 (Important - Variable Inspection)
5. Variable value evaluation (evaluate_at_breakpoint)
6. Variable value collector (collect_variable_values)
7. Statistics report generation (print_summary)

### P2 (Optional - Advanced Features)
8. Condition checker (check_conditions_at_breakpoint)
9. Richer report formats (JSON, Markdown)
10. Error handling and recovery

## File Organization

```
tools/trace_debugger/
├── src/
│   ├── debugger/
│   │   ├── __init__.py
│   │   ├── session.py          # DebugSession class
│   │   ├── breakpoint.py       # Breakpoint, BreakpointStatistics
│   │   ├── utils.py            # Utility functions
│   │   └── ...
│   ├── client/
│   │   └── dap_client.py       # DAP protocol client (existing)
│   └── ...
├── docs/
│   ├── background.md
│   ├── debugging_guide.md
│   └── TRACE_DEBUGGER_PLAN.md  # This file
└── examples/
    ├── phase2_coarse_grain.py  # Example using DebugSession
    ├── phase3_fine_grain.py
    └── phase4_deep_dive.py
```

## Design Rationale

### Why Not Automatic Layering?

We deliberately **do not** implement automatic breakpoint placement or automatic decision-making because:

1. **Context-Dependent**: The right next step depends on understanding the spec, which varies per project
2. **Agent Intelligence**: Let the agent use its understanding of TLA+ and the spec to make decisions
3. **Flexibility**: Different debugging scenarios may require different strategies
4. **Transparency**: Agent's decision-making is explicit in the code it writes

### Why Breakpoint Statistics?

Breakpoint hit statistics provide a **high information density** view:
- One run shows which code paths were taken
- Quickly identifies "last successful" and "first failed" locations
- Much faster than single-stepping through thousands of evaluations

### Why Session-Based?

Each debugging layer is a separate session because:
- Clean separation of concerns
- Easy to parallelize or retry
- No complex state management
- Agent can easily script multiple sessions

## Extension Points

Future enhancements (not in current scope):

1. **Trace replay**: Step through trace execution line by line
2. **State diff**: Compare states between successful and failed l values
3. **Automated diagnosis**: Suggest likely root causes based on patterns
4. **Interactive mode**: REPL-like interface for ad-hoc queries
5. **Performance profiling**: Measure time spent in different spec sections
