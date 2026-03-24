# Base Spec Methodology

How to write a TLA+ base spec from a Modeling Brief.

> **Note**: Examples reference Raft (hashicorp/raft) as an illustrative case study. Adapt to your target system.

## Principle: Bug-Family Driven, Code-Faithful

The spec's **scope** is driven by Bug Families — what variables to add, how to split actions, what invariants to check. But the **logic** within each action must faithfully follow the implementation's actual control flow. For the code paths we model, the spec must match the implementation's conditions, branches, and state updates precisely.

**Every logic block within an action must be annotated with source code line references.**

## Variable Design

Start from standard protocol variables, then add **extension variables** from Bug Families. Every extension variable must cite which Bug Family motivates it and what code it models.

Group variables for UNCHANGED clauses (e.g., `serverVars`, `logVars`, `leaderVars`).

## Action Design

### Naming

Name actions after implementation functions (e.g., `HandleRequestVoteRequest`, not `HandleRV`).

### When to Split

Split a single implementation function into multiple spec actions when:
1. **Different code paths have different checks** — e.g., one response path checks `resp.Term` while another skips it
2. **Non-atomic operations have crash windows** — e.g., persistence writes term then votedFor separately
3. **Independent threads/goroutines have different properties** — e.g., heartbeat runs without disk access while replicate requires disk

### Action Structure

Each action follows this pattern:
- Action-level comment cites the overall function (`file:line-range`)
- Every logic block inside (branches, LET bindings, conditions) cites specific source lines
- Each case in a disjunction has a descriptive comment

### Message Types

Use descriptive constants. Include a `msubtype` field when the same RPC type has different code paths (e.g., "heartbeat" vs "replicate" for AppendEntries).

## Invariant Design

Three categories:
1. **Standard protocol invariants** — fundamental safety properties
2. **Extension invariants** — target specific Bug Families (primary bug-detection tools)
3. **Structural invariants** — sanity checks that hold in all correct states

## Helpers

Common patterns: log entry records with type fields, message bags (Send/Discard/Reply using Bags module), configuration helpers for dual-config modeling.

## Fault Injection

Beyond standard faults (crash, message loss, network partition), the analysis report may reveal **system-specific fault injection** opportunities. Examples: disk IO blocking (heartbeat continues while replicate stalls), non-atomic persistence (crash between two disk writes), configuration change mid-election. Design fault-injection actions based on what the Bug Families identify, not just common fault categories.

## Crash and Recovery

For non-atomic persistence: after crash, in-memory state reverts to persisted state (which may differ if a non-atomic persist was interrupted).

## Example

See `case-studies/hashicorp-raft/scenarios/base/spec/hashiraft.tla` for a complete base spec with 5 extensions, full source line annotations, and action splitting.
