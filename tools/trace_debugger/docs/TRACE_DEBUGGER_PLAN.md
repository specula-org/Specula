# TLA+ Trace Validation Debugger Implementation Plan

## 1. Overview
The goal is to create a robust, automated debugging tool for TLA+ Trace Validation. This tool will allow an AI Agent (or human user) to interactively debug a TLA+ specification against a JSON trace log, identifying exactly where and why the validation fails.

The system is inspired by the **DebugMCP** project, adopting a similar architecture of **Executor** (managing the process) and **Handler** (exposing high-level capabilities), but implemented in Python to interface directly with the TLC Debugger Adapter Protocol (DAP).

## 2. Architecture

### 2.1 Core Components
1.  **TLCDebuggerClient (DAP Client)**: 
    *   Handles low-level TCP/IP communication with TLC.
    *   Implements DAP protocol (Request/Response/Event).
    *   Manages message buffering and event queues.
2.  **TraceDebuggingExecutor (Controller)**:
    *   Manages the lifecycle of the `tla2tools.jar` process.
    *   Handles "Output Draining" (preventing stdout buffer blocking).
    *   Maintains current debugging state (Connected, Stopped, Terminated).
3.  **Tool Interface (API)**:
    *   High-level functions exposed to the Agent (e.g., `debug_trace`, `step`, `inspect`).

## 3. Required Features & API Design

The following functions will be implemented as tools for the Agent:

### 3.1 Session Management
*   **`start_trace_debugging(spec_file, trace_file, config_file)`**
    *   Starts TLC process with `-debugger` flag.
    *   Sets up stdout monitoring.
    *   Connects DAP client.
    *   Initializes the session (`initialize` request).

*   **`stop_debugging()`**
    *   Disconnects and kills the TLC process.

### 3.2 Breakpoint Control
*   **`add_breakpoint(line, condition=None)`**
    *   Adds a source breakpoint.
    *   Essential for "Hit-based" debugging (e.g., `TLCGet("level") = 29`).
*   **`set_exception_breakpoints(unsatisfied=True, invariant=True)`**
    *   Enables/Disables stopping on Deadlock (Unsatisfied) or Invariant Violation.

### 3.3 Execution Control
*   **`continue_execution()`**
    *   Resumes TLC.
*   **`step_in()`**
    *   Steps into the current action/predicate.
*   **`step_over()`**
    *   Steps over the current action.

### 3.4 State Inspection
*   **`get_stack_trace()`**
    *   Returns current frames (Line numbers, Source files).
*   **`get_variables(scope='all')`**
    *   Returns variables from 'State', 'Action', 'Trace', and 'Constants' scopes.
    *   **Crucial Feature**: Automatically extracts `TraceLog[current_level]` from Constants to allow comparison.
*   **`evaluate(expression)`**
    *   Evaluates a TLA+ expression in the current context.

### 3.5 Automated Diagnosis (Smart Feature)
*   **`diagnose_step(current_level)`**
    *   A composite function that:
        1.  Fetches current State variables.
        2.  Fetches expected Trace Log for the next step.
        3.  Performs a heuristic "Diff" to highlight mismatches (e.g., "Expected term=2, but State has term=1").

## 4. Implementation Roadmap

### Phase 1: Robust Core (Python)
*   Refactor `Phase2_Debugger.py` into a proper class structure (`TLCDebuggerClient`).
*   Implement robust socket handling (timeout retries, buffer management).
*   Implement event listener loop (handling `stopped`, `output`, `terminated` asynchronously).

### Phase 2: Action Primitives
*   Implement `add_breakpoint`, `step_in`, `get_variables`.
*   Verify `step_in` works reliably (as proven in PoC).
*   Ensure `get_variables` can traverse all DAP scopes (`scopes` -> `variables`).

### Phase 3: The "Diagnose" Logic
*   Implement logic to extract `OriginTraceLog` from Constants.
*   Implement logic to extract `l` (current level) from State/Action.
*   Implement the comparison logic.

## 5. Usage Example (for Agent)

```python
# 1. Start
debugger = TraceDebugger()
debugger.start("Spec.tla", "trace.ndjson")

# 2. Fast Forward to failure
debugger.add_breakpoint(line=522, condition='TLCGet("level") = 29')
debugger.continue_execution()

# 3. Inspect
state = debugger.get_variables()
print(f"Current State: {state['term']}")

# 4. Step & Probe
debugger.step_in()
debugger.evaluate("TraceLog[30]")
```

## 6. References
*   `DebugMCP/src/debuggingHandler.ts`: Reference for handling high-level debug commands.
*   `tlc2.debug.TLCDebugger`: Java implementation details of TLC's DAP server.
