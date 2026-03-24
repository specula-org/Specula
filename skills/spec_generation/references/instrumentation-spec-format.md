# Instrumentation Spec Format

The instrumentation spec captures the mapping between TLA+ spec actions and source code locations. It serves as a "context handoff" — the spec generation agent's knowledge distilled into a document that an instrumentation agent (or human) can use to generate the actual code patches.

> **Note**: Adapt to your target system. See `case-studies/hashicorp-raft/scenarios/base/patches/instrumentation.patch` for a complete real-world example.

## Document Structure

The instrumentation spec has three sections:

### Section 1: Trace Event Schema

Define the common event envelope and fields:
- **Event envelope** — event name, node ID, state snapshot, message fields (if applicable)
- **State fields** — mapping from implementation getter/field to TLA+ variable (captured at every event)
- **Message fields** — mapping from implementation message fields to TLA+ message fields (event-specific)

### Section 2: Action-to-Code Mapping

One entry per spec action, each specifying:
1. **Spec action name** — what the trace spec expects
2. **Code location** — `file:line` where to insert instrumentation (list all locations if a spec action maps to multiple code paths)
3. **Trigger point** — "before X" or "after Y" (state snapshot timing matters for pre/post-action correctness)
4. **Trace event name** — the string used in trace JSON
5. **Fields** — which state/message fields to capture for this event
6. **Notes** — non-obvious details (e.g., self-vote handling, atomic vs non-atomic variant choice)

### Section 3: Special Considerations

Document implementation-specific details that affect instrumentation:
- State that's hard to access for tracing (e.g., values in stable store that need shadow fields)
- Concurrent threads/goroutines whose events may interleave
- Bootstrap/initial state differences from the base spec
- Serialization quirks (e.g., zero-value field omission)

## Principles

1. **Instrumentation must match spec granularity.** Every spec action needs exactly one trace event type; every trace event type must correspond to exactly one spec action. Read the base spec and trace spec to ensure 1:1 correspondence — mismatched granularity causes trace validation failures.
2. **One entry per spec action.** List all code locations if a spec action maps to multiple places.
3. **Trigger point precision matters.** Pre-action vs post-action snapshot timing determines correctness.
4. **Document the non-obvious.** Edge cases in instrumentation cause most trace validation failures.
5. **Match field names between trace and spec.** This document is the single source of truth for the mapping.
