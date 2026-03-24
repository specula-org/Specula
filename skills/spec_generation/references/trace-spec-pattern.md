# Trace Spec Pattern

Template and methodology for writing trace validation specs.

> **Note**: Examples reference Raft (hashicorp/raft) as an illustrative case study. Adapt event names, state fields, and action wrappers to your target system.

## Purpose

The trace spec drives TLC through a recorded execution trace from the real implementation, verifying that the base spec can reproduce every observed state transition.

**The trace spec validates ALL base spec logic.** Do not skip or weaken action logic unless the skipped logic has zero value for bug detection. Every action wrapper should call the full base spec action and validate the complete post-state. Skipping checks defeats the purpose of trace validation — finding where the spec and implementation disagree.

## Structure

1. **Trace loading** — `ndJsonDeserialize` from JSON file, filter by tag
2. **Cursor variable** `l` — walks through trace events; `logline == TraceLog[l]`
3. **Role/type mapping** — implementation strings to spec constants
4. **Server extraction** — derive Server set from trace
5. **Event predicates** — `IsEvent(name)`, `IsNodeEvent(name, i)`, `IsMsgEvent(name, from, to)`
6. **Post-state validation** — verify spec state matches trace after each action
7. **Action wrappers** — match event → call base action → validate → `l' = l + 1`
8. **Silent actions** — fire base actions without consuming a trace event
9. **TraceNext** — all wrappers + silent actions
10. **TraceMatched** — temporal property checking entire trace was consumed

## Trace.cfg Must Include TraceMatched

`Trace.cfg` must have `PROPERTIES TraceMatched` (uncommented). Without it, TLC reports "no errors" even when `l` never advances — trace validation becomes a false positive. Define `TraceMatched == <>(l > Len(TraceLog))` in `Trace.tla` and include `PROPERTIES TraceMatched` in `Trace.cfg`.

## Silent Actions

Silent actions handle impl state changes without trace events (e.g., leader noop append, concurrent timeouts). **Unconstrained silent actions cause state space explosion.** Always add preconditions:
- Check `l <= Len(TraceLog)`
- Match against the *next* trace event that would require this silent action
- Restrict to specific nodes/states

## Post-State Validation

**Strong validation**: check term, role, commitIndex, lastLogIndex, lastLogTerm — for actions where trace records full state.

**Weak validation**: check only term + role — for async actions where trace may not capture full state.

## Bootstrap State

TraceInit must match the implementation's initial state, which may differ from the base spec's Init (e.g., initial term, bootstrap log entries).

## Common Issues

| Issue | Solution |
|-------|----------|
| TraceMatched violated at line N | Event N cannot match any base spec action |
| Deadlock at line N | No enabled action for event N |
| TLC never finishes | Unconstrained silent action causing infinite branching |
| State mismatch after action | Post-state validation failed — spec and impl disagree |
| Message not found in bag | Already consumed by silent action or prior event |

## Example

See `case-studies/hashicorp-raft/scenarios/base/spec/Tracehashiraft.tla` and `Tracehashiraft.cfg` for a complete trace spec with 11 action wrappers, 3 silent actions, bootstrap state, and strong/weak validation.
