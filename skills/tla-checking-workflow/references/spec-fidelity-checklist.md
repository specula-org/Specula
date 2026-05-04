# Spec Fidelity Checklist

Use this checklist before classifying a counterexample as Case C (real bug). The most common false-positive shape in formal verification is a counterexample whose preconditions look implausible in the real system — usually because the spec under-models a guard or suppression mechanism the implementation has.

## When to use

Run this checklist when, after reading the counterexample, you find yourself thinking *"this couldn't actually happen because…"*. That instinct is a flag: either the spec is missing a mechanism, or the bug is so subtle the implementation seems immune to it. The checklist helps you tell which.

## Procedure

### Step 1. Extract the preconditions

Read the counterexample and write down the set of conditions the violating state requires. Be specific — "node A had property X *while* receiving message Y from B" is a precondition; "node A misbehaved" is not.

### Step 2. For each precondition, ask "what stops this in the real system?"

For every precondition, search the implementation for any guard, gate, check, or reactive update that prevents that condition. Look for:

| Mechanism category | What it looks like in code |
|---|---|
| **Reactive suppression** | Receiving X resets/clears state Y (e.g., a message resets a timer, a successful response clears a flag) |
| **Conditional acceptance** | An incoming message is only acted on if a field passes a check (term, view, sequence number, signature) |
| **Mutual exclusion / leases** | State X locks out action Y for a duration or until a condition holds |
| **Reentrancy / in-progress guards** | Action only fires if a "not currently doing this" flag holds |
| **Authentication / quorum proofs** | Message only acted on if signed / certified / quorum-attested |
| **Rate limits / counters / budgets** | Action only fires within a finite budget that the system tracks |

The implementation's choice to put a guard somewhere is itself information. If the developers wrote `if !x { return }` at the top of a function, they believed `x` could happen — and the spec should let it happen too, while modeling the guard.

### Step 3. Compare to the spec

For each guard you found in the implementation, check whether the spec models it:

- **Spec models the guard with the same precondition** → guard is faithful, move on.
- **Spec models the guard with a weaker precondition** → spec lets behavior through that the impl blocks. This is **Case B**.
- **Spec doesn't model the guard at all** → spec explores states the impl can't reach. This is **Case B**.
- **Impl has no guard for this precondition** → the precondition really can occur. The counterexample is Case C-eligible. Continue verification.

### Step 4. Re-run with the spec fix

If you found Case B, fix the spec (add the guard, tighten the precondition, model the reactive update) and re-run TLC. If the violation persists, repeat from Step 1 — there may be a second under-modeled mechanism. If the violation disappears, the original counterexample was a fidelity gap, not a bug.

## What to write down

When you classify a counterexample as Case B via this procedure, record in `changelog.md`:

- The precondition that looked implausible
- The implementation guard you found, with `file:line`
- The spec change made to model it

This trail matters for two reasons. First, it documents that you didn't dismiss the counterexample arbitrarily. Second, if the same precondition shows up in a later counterexample, you'll know whether you're seeing the same gap or a new one.

## Heuristic: if you can name the bug class, double-check fidelity

Bug classes that have a known fidelity trap:

- **Heartbeat-driven leader election** — does the spec model heartbeats *suppressing* the follower's election timer, not just resetting a leader-side counter?
- **Lease-based reads / Byzantine fast paths** — does the spec model the lease/ticket condition that gates the fast path, or does it allow the fast path unconditionally?
- **View / term advancement** — does the spec require the same evidence (quorum certificate, signed timeout, etc.) to advance that the impl requires, or can it advance freely?
- **Garbage collection / reclamation** — does the spec model the same hazard-pointer / epoch / reference-count check that the impl uses to decide reclaim safety?

A spec that models the action but not the *condition under which the action is allowed* will report violations that aren't in the real system.

## See also

- `case-studies/` contains worked examples where this checklist's pattern applied. Search for `retracted` in `bug-report.md` files to find counterexamples that were ultimately classified as fidelity gaps after this kind of analysis.
- `tla-checking-workflow/guide.md` Step 3 — this checklist is the detailed version of "Cross-Reference with Implementation".
