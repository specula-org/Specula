# Trace Debugger Logging Improvement Plan

Based on the recent debugging session, we identified critical issues where logging to `stdout` corrupted the MCP JSON-RPC protocol. To prevent this in the future and improve observability, we propose the following improvements to the logging module.

## 1. Objectives
- **Protocol Safety**: Guarantee that no debug logs ever touch `stdout`.
- **Persistency**: Ensure logs are saved to files for post-mortem analysis.
- **Manageability**: Prevent log files from consuming infinite disk space.
- **Context**: Provide clear correlation between MCP requests and backend operations.

## 2. Implementation Plan

### A. Centralized Configuration (`src/tla_mcp/utils/logger.py`)
Refactor the current simple logger into a robust configuration module:
- **`setup_logging(name, log_dir, level)` function**:
  - Configures the root logger.
  - Clears existing handlers to prevent duplication.
  - Sets up `RotatingFileHandler` (e.g., 10MB limit, keep 5 backups).
  - Sets up `StreamHandler` pointing strictly to `sys.stderr`.
  - Defines a standard format: `[Timestamp] [Level] [Logger] [Thread] Message`.

### B. Structured / Contextual Logging
- **Request ID Tracking**: 
  - If possible, extract a Request ID from MCP calls and pass it to the logger.
  - Alternatively, use `threading.local()` to store context (Session ID) and include it in the log format.
  - Helps distinguish between parallel tool executions (though currently mostly sequential).

### C. Safety Mechanisms
- **Stdout Guard**: 
  - Consider monkey-patching `sys.stdout` in the entry point to throw an error or redirect to logger if code tries to `print()` directly (except for the actual MCP response writer).
  - Or, strictly enforce `print` removal via linter rules (e.g., `flake8-print`).

### D. Error Handling
- **Global Exception Handler**:
  - Catch unhandled exceptions at the top level (MCP server loop).
  - Log full stack traces to the file.
  - Return a clean, sanitized error message to the MCP client.

## 3. Directory Structure
- Logs should default to `~/.specula/logs/trace_debugger/` or a project-relative `.logs/` directory, rather than `/tmp`, to ensure they persist across reboots if needed (but cleanable).

## 4. Next Steps
1. Create a task to refactor `logger.py`.
2. Update all modules (`tlc_process.py`, `dap_client.py`, `session.py`) to import the new logger.
3. Add a pre-commit check or linter rule to forbid `print()` calls in the source code.
