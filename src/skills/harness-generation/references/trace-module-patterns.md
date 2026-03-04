# Trace Module Patterns

Language-specific patterns for the trace emission library. Adapt to your target system.

## Common Pattern

Every trace module needs:
1. **Global writer** — initialized once, thread-safe
2. **Server mapping** — implementation node IDs → TLA+ names (s1, s2, s3)
3. **Emit function** — captures timestamp, event name, node state, optional message fields
4. **NDJSON output** — one JSON object per line, flushed immediately

## Examples by Language

| Language | Case Study | Trace Module | Key Files |
|----------|-----------|--------------|-----------|
| Rust | aptosbft | `case-studies/aptosbft/harness/src/tla_trace.rs` | trace module + test scenario + apply.sh + run.sh |
| Go | cometbft | `case-studies/cometbft/artifact/cometbft/` (instrumented in-place) | harness/run.sh + harness/preprocess_trace.py |
| C++ | braft | `case-studies/braft/artifact/braft/` (trace_logger.cpp) | instrumented in artifact source |

**Start by reading the example closest to your target language**, then adapt the pattern to your system.
