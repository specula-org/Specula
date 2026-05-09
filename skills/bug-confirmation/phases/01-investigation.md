# Phase 1: Investigation

Confirm whether the finding is a real bug, what the bug claim depends on, and why the code or specification supports or refutes the claim. Activities are ordered cheap-first so obviously-weak findings exit early — but **bias toward continuing investigation when in doubt**. Wrongly stopping at Step 1 on a finding whose harm needs a few lines of reasoning to articulate is far more costly than running the cheap subsequent steps on a finding that turns out to be a path deviation.

The five steps are: triage filters → code audit → developer intent investigation → prerequisite verification → precedent re-check. Move through them in order. Each step's output feeds the next; the last two are the deepest and most expensive.

## Step 1: Triage filters

Two cheap filters. Apply in order. If a filter clearly rejects, stop and record as path deviation. If you are uncertain whether a filter rejects — for example, you suspect the harm exists but cannot articulate it in one sentence yet — **do not stop**. Fall through to Step 2 and revisit the filter after reading the code.

1. **Path ≠ bug.** "The function deviates from its inferred contract" or "an unexpected execution path is reachable" is not a bug on its own. Internal helpers commonly assume preconditions their callers already enforce; a violation of an LLM-inferred postcondition that no test exercises is not a contract violation. Ask: does this deviation produce a *system-level consequence* — crash, deadlock, data corruption, safety/liveness violation, or wrong reply to a client? If the worst case is "an internal value is unexpected, but the surrounding code already validates / clamps / re-checks before any external effect", stop. Path deviation, not bug.

2. **Name the observable harm.** Write one sentence describing what a user, operator, or other system component would see go wrong. "Returns Err in a branch that's never taken" is not harm. "Two replicas commit different values for the same slot" is harm.

### What Step 1 is NOT for

The filters above reject findings with **no consequence at all**. They are not for findings whose consequence requires reasoning to articulate. Common shapes that look like Step 1 rejections but are not:

- *Stale buffer / dirty state that "looks internal."* If any downstream consumer reads the buffer for any externally-visible effect (transcript hash, signature, message dispatch), the stale state is observable. Trace consumers before rejecting.
- *Consequences that take multiple steps to articulate.* "I can't name the harm in one sentence yet" is a signal to investigate, not to stop. Many real protocol bugs require chaining 2-3 logical steps from the buggy code to the visible effect.
- *Path deviations that "look defensive" but the caller doesn't validate.* The filter assumes callers enforce preconditions. If the call chain doesn't actually enforce them, the deviation is real harm. Verify the call chain at Step 2 before deciding the deviation is benign.
- *Findings whose harm is conditional on a spec interpretation.* "If the protocol mandates X, then this is severe" is not a Step 1 rejection — it's a Step 4 question. Park the harm question and proceed.

When in doubt, fall through. The cost of running Steps 2-5 on a finding that turns out to be a path deviation is small; the cost of wrongly rejecting a real bug at Step 1 is large.

If a finding is rejected at Step 1, record it as a path deviation in the report — note which filter rejected it and why. **Do not silently drop the finding**; the rejection itself is information for evaluating the bug-finding pipeline.

## Step 2: Code audit

Confirm the bug's validity by reading the source code.

1. **Locate the relevant code.** Find the specific functions and lines mentioned in the bug report. Read these functions in full and understand their context.
2. **Trace the call chain.** Starting from public APIs or entry points, trace the path to the buggy code. Confirm whether this path is reachable during normal usage.
3. **Check for existing safeguards.** Check whether callers already have precondition checks, lock guards, or other mechanisms that prevent this bug from being triggered in practice. If they do, the bug is a false positive — report it and stop.
4. **Construct a trigger scenario.** Describe in words a concrete sequence of events that could naturally occur at the user/system level and would reach the buggy code path. If you cannot construct one, the bug is likely a false positive.

If Step 1 was deferred ("uncertain about harm"), revisit Step 1's filters now with the full code context. Apply them again with all the information you now have.

## Step 3: Developer intent investigation

A bug is defined by the developers' own requirements and expectations — not by the researcher's intuition about what should be correct, and not by what an internally-consistent TLA+ model says. Investigate what the developers themselves believe about this behavior.

### What to investigate

1. **Issue tracker.** Search for open and closed issues, PRs, and discussions mentioning the relevant code, function names, or the behavior in question. Developers may have already discussed this exact scenario.
2. **Commit messages and PR discussions.** Use `git log` and `git blame` on the affected code. Read the commit messages and linked PRs to understand why the code was written this way. Look for statements of intent ("this is a trade-off", "we accept this because...", "this should be safe even if...").
3. **Code comments and documentation.** Look for comments near the code (TODOs, FIXMEs, "known issue", "by design", "trade-off"), as well as design documents, RFCs, or architecture docs in the repository.
4. **Test cases.** Check what the existing tests assert. Tests encode developer expectations — if a test explicitly sets up the scenario you found and asserts the current behavior, the developers likely consider it correct.

### How to use what you find

- **Developer says "we know about this, it's a deliberate trade-off"** → Classify as NOT a bug unless you can show their trade-off analysis is flawed (e.g., they accepted a liveness cost but didn't realize it also affects safety).
- **Developer says "this should be safe even under condition X"** → If your counterexample shows it is NOT safe under condition X, this IS a bug — the developers' own stated requirement is violated.
- **No developer commentary found** → Fall back to code quality analysis: assess whether the behavior constitutes a bug based on established engineering standards (e.g., violating API contracts, ignoring error returns, TOCTOU races, missing atomicity). These are bugs by any reasonable standard regardless of developer intent. Note the absence of developer evidence in your report and explain which engineering principle the code violates.

The two symmetric cases above are the key insight: developer intent can both *dismiss* a finding that looks like a bug to a researcher, and *validate* a finding that a researcher would have dismissed. Always let the evidence speak.

**Report what you find.** Whether the investigation confirms or refutes the bug, include a brief summary of the developer evidence in your final report.

## Step 4: Prerequisite verification

Before relying on the model's verdict, write down explicitly the propositions that must be true for this finding to be a real bug. Distinguish:

- **Code-level prerequisites** — verifiable by reading source: e.g., "this function is reachable from public API path P with attacker-controlled input," "the buggy field is not overwritten before any externally observable effect."
- **Protocol-semantic prerequisites** — verifiable only against the protocol specification text or design document: e.g., "field F is supposed to be validated by this party," "messages M1 and M2 are required to be observed atomically," "the resource being exhausted has no other equally-cheap holder path," "this state must time out on its own."

Any finding that *implicitly* makes a claim about what the protocol *should* do — even when the surface argument is "the code is structurally inconsistent" — has at least one protocol-semantic prerequisite. Common shapes that look code-structural but carry hidden protocol-semantic claims:

- *"Missing validation / subset check / negotiation enforcement"* — silently assumes the field is meant to be validated/negotiated by the verifying party. Verify: does the verifying party even advertise an offered set, or does the spec define the field as unilaterally chosen?
- *"Race / TOCTOU between two operations"* — silently assumes the operations are required to be atomic from a peer's perspective. Verify: does the spec mandate atomicity, or is per-step observability acceptable?
- *"DoS via path P leading to resource pinning"* — silently assumes path P is the unique or cheapest way to pin the resource. Verify: enumerate alternative paths (post-handshake keep-alives, idle-session policies, etc.) and compare attacker cost.
- *"Missing atomicity / rollback in operation O"* — silently assumes O is required to be transactional from the spec's perspective. Verify: does the spec describe O as a single commit point?
- *"Missing transcript binding / signature on message M"* — silently assumes M is meant to be in the transcript. Verify: does the spec mandate M's inclusion, exclude it explicitly, or remain silent?

**For each protocol-semantic prerequisite**, fetch the relevant section of the protocol specification (PDF, RFC, IETF draft, internal design doc) and quote the passage that resolves it. Three outcomes:

- *Spec confirms the prerequisite* — the finding stands; record the spec citation in the per-bug output as supporting evidence.
- *Spec contradicts the prerequisite* — the finding is invalid in its current framing; withdraw or substantially reframe before continuing. Record the contradicting passage as the reason for downgrade.
- *Spec is silent* — the finding is reframed from "spec violation" to "defense-in-depth / hygiene improvement." It can still be reported, but the framing must reflect the absence of a normative requirement, not its presence.

### Output

Record the prerequisite check as a structured block in the per-bug output:

```
Prerequisites:
- [code] Function reachable from public API: VERIFIED — call chain X→Y→Z, file:line
- [spec] Field F is validated by Requester: VERIFIED — spec §A.B ¶N: "..."
- [spec] Resource R has no equivalent post-handshake holder: NOT VERIFIED — spec §C ¶M permits HEARTBEAT keep-alive at comparable cost
```

A finding with at least one **NOT VERIFIED** spec-level prerequisite must have its framing re-examined before reaching Phase 2 — see the Tier section in `../guide.md` for how spec-contradicted prerequisites map to tier downgrade.

## Step 5: Precedent prerequisite re-check

If the finding cites a precedent — an upstream-accepted issue, a prior-round acceptance, a similar pattern in a sister project — the precedent endorses *the pattern under its prerequisites*, not the pattern's applicability to a new field, message, or protocol step. Re-verify each of the precedent's prerequisites at the new site explicitly. Do not treat *"this is the same shape as accepted bug X"* as sufficient: the same shape on a different field can be a real bug, an artifact of spec asymmetry, or by design — only the per-site prerequisite check distinguishes these.

If the finding does not cite a precedent, skip this step.

---

Only proceed to Phase 2 (Counterfactual Fix Check, for system-property findings only) or directly to Phase 3 (Reproduction, for new bugs) after completing all applicable steps and being confident the bug stands or has been firmly invalidated.
