# Phase 2: Counterfactual Fix Check (system-property findings, advisory)

## What this phase does, in one line

Apply the proposed fix to the spec, re-run TLC, and check whether the violated property still violates. If it still violates, the original counterexample was *one* path to the bad state but not the *only* path — the bug class is mis-framed (typically: a "security/availability defense" claim is actually hygiene, because the bad outcome is reachable cheaply via other paths the model didn't show in the original trace).

## The shape this catches, walked through

Suppose TLC finds: *"attacker sends KEY_EXCHANGE and never sends FINISH; the session sits in HANDSHAKING with no watchdog; slot is held forever; eventually slots are exhausted."* The natural reading is *"missing watchdog → DoS → adding a watchdog fixes the DoS."* This phase tests that reading: add the watchdog to the spec, re-run TLC, and check if "session slots exhausted" is still reachable. If a separate path also reaches exhaustion at comparable attacker cost (e.g., attacker completes the handshake legitimately and uses HEARTBEAT keep-alive forever), the watchdog was never the principal defense. The finding is real, but its bug class is hygiene, not DoS prevention. Reading the original counterexample alone could not surface this.

## When to apply

The violated property is **system-wide** — quantifies over time, peers, or message orderings. Examples:

- *"Some session can never be closed."*
- *"The server can run out of session slots."*
- *"Two peers can disagree on the committed value."*
- *"A message can be successfully replayed."*
- *"A queue can grow without bound."*

## When NOT to apply

The violated property is **local** — a specific function returns the wrong value, a specific check is missing on a specific code path, a specific transcript is not reset on a specific error. Re-running TLC contributes nothing in these cases: there is no broader bad-outcome class to search alternative paths to; the bug *is* the missing check on that specific path. Examples:

- An OOB read, missing null check, or wrong return value in a single function.
- A specific message field unvalidated under a specific path.
- A specific transcript not reset on a specific error return.

If you are uncertain which category a finding belongs to, ask: *"Could the same bad outcome be reached by a completely different protocol path I haven't considered?"* If the answer is plausibly yes, treat as system-wide and apply this phase. If the bad outcome only manifests at exactly this code site, treat as local and skip.

## Procedure (apply only when the property is system-wide)

1. **Identify the buggy action(s) in the spec.** Read the counterexample trace and isolate the transition(s) that introduce the violation.
2. **Construct a one-line "fix" in the spec.** Typically: add an enabling guard that mirrors the proposed code fix, remove a transition the spec should not have allowed, or strengthen a precondition. Keep the edit minimal — change only what the proposed code-level fix would change.
3. **Re-run TLC with the same MC config.** Use the exact hunting cfg that found the original violation. Wrap with `timeout` and respect Batch Mode Constraints (see `../guide.md`).
4. **Inspect the result.** Two possible outcomes, each with caveats — see "Interpreting the result" below before drawing a conclusion.
5. **Record what you ran and what you saw**, in the structured form below.

## Interpreting the result — the verdict is advisory, not authoritative

This step's output is a *signal*, not a proof. State-space exploration is incomplete in several common ways, and the agent must reason about TLC's coverage before treating the result as conclusive:

- *State space not exhausted under the same config.* The hunting cfg that found the original violation may not exhaust the reachable space in the patched spec — TLC may stop after a state limit, depth limit, or wall-clock timeout without ever reaching the alternative path. A "no violation found" report from a partial run is consistent with the alternative path existing but unvisited.
- *Simulation mode (random walk).* If the original counterexample came from simulation rather than BFS, repeating the simulation under the patched spec is a sample, not an exhaustive search. The trial may simply have missed the alternative path.
- *Symmetry / abstraction artifacts.* A small spec edit can change which states TLC considers symmetric, which can hide alternative paths behind a "duplicate state" classification. Conversely, the patch can introduce spurious violations that disappear under closer modeling.
- *Property too narrow.* The proposed fix may close the original path while leaving a subtly different bad state that the violated invariant does not catch. Re-check that the invariant being verified actually captures the system-wide property you care about, not just the specific state shape from the original counterexample.

So:

- *Property still violates after fix, with a clear alternative-path counterexample* → strong signal that the original framing is wrong. Inspect the alternative path, compare attacker cost (privilege required, message count, additional crypto/authentication needed). If comparable to the original path, reframe as hygiene and downgrade the Report Tier; if higher, the original framing is partially correct — note that "fix X reduces but does not eliminate Y; full mitigation also requires Z."
- *Property holds after fix, within the explored state space* → **moderate** signal that the original framing is corroborated, qualified by the limits of what TLC actually explored. Record the result with explicit scope (`MC config X, depth limit Y, wall-clock Z`), not as proof. If the original counterexample was small (under ~30 states) and the patched run is also small and converges, the signal is stronger; if either run was large or state-limited, treat with corresponding caution.
- *Property holds, but TLC could not exhaust the space and the original counterexample is large* → no useful signal. Note the inconclusive result and rely on Phase 1 Step 4's prerequisite verification + judgment to decide whether the original framing stands.

## Recording

Write a structured block in the per-bug output:

```
Counterfactual fix check:
- Applied edit: <one-line description, e.g. "added Watchdog action that aborts HANDSHAKING after timeout">
- MC config re-run: <cfg file used>
- Coverage: <states explored, depth, wall-clock; whether TLC exhausted the space>
- Result: PROPERTY HOLDS (within explored space) / PROPERTY STILL VIOLATES / INCONCLUSIVE (state limit hit before convergence)
- If still violates: alternative path = <one-line description>; attacker cost vs. original = COMPARABLE / HIGHER / LOWER
- Conclusion: <original framing corroborated / reframed as hygiene / reframed as partial mitigation / inconclusive — using prerequisite check from Phase 1 Step 4 to decide>
```

## Why this matters even with the caveats

A state-machine path reaching a bad outcome is *necessary* but not *sufficient* evidence of a real security/availability bug. The counterfactual check converts the bug claim from "*we found a path to the bad state and assume closing it is the defense*" into "*we tried closing it and observed what TLC could find*." Even a partially-explored re-run, when it does find an alternative path, is direct evidence of mis-framing. When it doesn't find one, the corroboration is partial — combine with the Phase 1 Step 4 prerequisite check rather than relying on TLC alone.
