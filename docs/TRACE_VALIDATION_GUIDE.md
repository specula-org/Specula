# Agent Guide: Performing Trace Validation

Trace validation is a rigorous process of verifying that a system's execution trace (logged events) conforms to its formal specification (TLA+). This guide outlines the methodology, common challenges, and best practices for an AI agent performing this task.

## 1. Core Methodology

The validation process involves iteratively aligning the formal specification with the trace data. The goal is to reach the end of the trace without deadlocks (no enabled actions) or property violations (invariant failures).

### Phase 1: Context & Setup
*   **Understand the Spec:** Analyze the TLA+ specification (`.tla`) to understand the state variables, actions, and invariants. Identify the "Trace Spec" (e.g., `Traceetcdraft_progress.tla`) which maps trace events to spec actions.
*   **Analyze the Trace:** Read the trace file (e.g., `.ndjson`) to understand the event types, data structure, and sequence of operations.
*   **Establish a Baseline:** Run the initial validation to identify the first point of failure (line number).

### Phase 2: Iterative Debugging (The Loop)
1.  **Identify Failure Point:** Use `PrintT` debugging or analyze Trace/State logs to pinpoint the exact trace line `l` where the validation stops or fails.
2.  **Hypothesize Cause:**
    *   **Deadlock:** No spec action guards evaluate to TRUE for the current trace event. (e.g., `state` mismatch, missing message).
    *   **Property Violation:** An action executed, but the resulting state violated an invariant (e.g., `ValidatePostStates` found a discrepancy between Spec state and Trace state).
3.  **Investigate Discrepancy:** Compare the Trace event data (payload, state dump) with the Spec's internal state. Look for:
    *   **Granularity Mismatch:** Does one Trace event map to multiple Spec actions, or vice-versa?
    *   **Hidden State:** Does the code have implicit side effects (e.g., sending a message immediately after logging) that the Spec misses?
    *   **Feature Gaps:** Does the Trace use features (e.g., Joint Consensus) not implemented in the Spec?
4.  **Implement Fix:** Modify the Spec (Trace Spec or Base Spec) to align logic.
5.  **Verify:** Rerun TLC. Ensure the fix resolves the specific error and extends the validated depth.

## 2. Common Challenges & Patterns

### 2.1. Atomicity Mismatches
*   **Problem:** Real-world code often groups operations (e.g., "Change Config" + "Send Response" + "Update Term") into atomic steps or logs them as a single event. TLA+ specs often model these as fine-grained, separate actions.
*   **Pattern:** Trace has 1 event, Spec needs 3 actions.
*   **Solution:**
    *   Create **Composite Actions** in the Spec (e.g., `UpdateTermAndHandleRequestVote`) to match the granularity of the Trace event.
    *   Use **Implicit Actions** (e.g., `ImplicitReplicateAndSend`) when the Trace completely skips a logically required step (like a missing `Replicate` log line).

### 2.2. Out-of-Order Events (Distributed Systems)
*   **Problem:** Trace logs are collected from distributed nodes or asynchronous threads. Timestamps may drift, or logical order may appear violated (e.g., `Receive` logged before sender's `Ready/Send`).
*   **Solution:** Relax strict causality checks where safe.
    *   Allow consuming messages from `pendingMessages` (sent but not flushed) if the Trace implies they must have been received.
    *   Implement robust `ConsumeMessage` helpers that check both network and pending buffers.

### 2.3. Feature Gaps (The "Joint Consensus" Example)
*   **Problem:** The implementation (e.g., `etcd/raft`) supports advanced features (Joint Consensus, ConfChangeV2) that older or simplified Specs (`etcdraft.tla`) do not.
*   **Solution:** You must upgrade the Spec to support the feature.
    *   **State Expansion:** Add missing state variables (e.g., `oldconf`, `enterJoint`).
    *   **Logic Update:** Update core algorithms (e.g., Quorum checks in `AdvanceCommitIndex` must check *both* majorities in Joint Consensus).

### 2.4. Data Mapping Issues
*   **Problem:** The mapping between JSON fields and TLA+ records is brittle.
*   **Solution:** verify `LoglineIsEvent` definitions. Ensure Type Aliases (e.g., `RaftMsgType`) map string tags correctly. Ensure variable types (Int vs String) match.

## 3. Best Practices for Agents

*   **Trust the Trace (Mostly):** If the Trace says an event happened, the Spec must accommodate it. Real execution is the ground truth.
*   **Verify, Don't Guess:** Use `PrintT` to dump variables at the point of failure. Don't assume `matchIndex` is correct; verify it.
*   **Fix the Root Cause:** If a `Commit` fails validation, look upstream. Did the `Receive` happen? Did `matchIndex` update? Did the message exist?
*   **Respect the Spec Structure:** When modifying the Base Spec, try to keep it general. When modifying the Trace Spec, keep it focused on mapping.
*   **Cleanup:** Remove debug prints and temporary hacks after solving a blockage to keep performance high and logs clean.

## 4. Case Study: The `leader_transfer` Deadlock

In the validation of `leader_transfer.ndjson`, we encountered and solved:
1.  **Compound Config Changes:** Trace merged `Remove` and `Add` into one. We added `FoldSeq` to compute the result.
2.  **Missing Messages:** `raft.go` auto-sends responses. We updated Spec actions (`ChangeConf`, `ClientRequest`) to auto-send `MsgAppResp`.
3.  **Joint Consensus:** The Spec assumed Simple Config. We rewrote `RequestVote`, `AppendEntries`, and `Commit` logic to support Joint Quorums.
4.  **Implicit Events:** The Trace missed `Replicate` events for config changes. We detected this via Log Length mismatch and triggered `ImplicitReplicate`.
5.  **Ghost Messages:** We incorrectly added `Send` to actions that already had separate Trace events, causing duplicate messages. We fixed this by strictly aligning actions to events.

### 2.5. Backward Compatibility & Regressions
*   **Problem:** Fixing a complex trace (e.g., `leader_transfer` with Joint Consensus) might break simpler traces (e.g., `confchange_add_remove` with Simple Config).
*   **Solution:** Use robust heuristics.
    *   **Example:** Instead of forcing `enterJoint = TRUE`, check `Len(changes) > 1` to distinguish between atomic simple changes and composite joint changes.
    *   **Regression Testing:** Always verify against the full suite of traces after a major Spec change.

### 2.6. Missing Events (Implicit Actions)
*   **Problem:** The Trace might miss crucial logical steps (e.g., a `Replicate` event for a configuration change, or `ChangeConf` event).
*   **Solution:** Use **Implicit Actions** triggered by state discrepancies.
    *   **Example:** If `Len(log) < TraceLog[l].log`, trigger an `ImplicitReplicate` action to catch up the Spec state before processing the current event.

Trace validation is detective work. It requires bridging the gap between abstract theory (TLA+) and messy reality (Go implementation).
