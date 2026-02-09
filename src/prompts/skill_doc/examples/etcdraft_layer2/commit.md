# Module: Commit

## Responsibility

Advance commit index when entries are replicated to a quorum. Ensure safety: only commit entries from current term.

## Actions

### AdvanceCommitIndex

**Responsibility**: Leader calculates and advances commit index

**Trigger**: After matchIndex updates (usually part of HandleAppendResponse)

**Behavior**:
1. Find the highest index N such that:
   - N > commitIndex
   - Majority of matchIndex[i] >= N
   - log[N].term == currentTerm (Figure 8 safety)
2. If such N exists, set commitIndex = N
3. Broadcast AppendEntries to propagate new commitIndex

**Code Reference**: `maybeCommit()` → `raftLog.maybeCommit()`

---

## Action Boundaries

| Spec Action | Code Functions | Notes |
|-------------|----------------|-------|
| `AdvanceCommitIndex` | `maybeCommit` | Usually combined with HandleAppendResponse |

## Quorum Calculation

For simple config:
- Quorum = majority of voters

For joint consensus:
- Quorum = majority of incoming voters AND majority of outgoing voters
- Both conditions must be satisfied

**Code Reference**: `tracker.Committed()` → `quorum.JointConfig.CommittedIndex()`

## Design Decision

`AdvanceCommitIndex` is typically not a separate spec action. It's combined with `HandleAppendResponse` because:
1. They always happen together in code
2. Separating them would create intermediate invalid states
3. The combined action is still atomic
