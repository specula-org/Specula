# Phase 1: Investigation (evidence only — no verdict)

Gather the evidence needed to decide the finding's verdict later: what the code
actually does, whether the buggy path is reachable, and what the developers know
about it. **Phase 1 records; it does not judge.** With ONE exception (the
code-review × known drop in Step 3), you do NOT decide here whether it is a bug —
that verdict is chosen *after* Phase 2 (reproduction), from the full evidence. Do
not prejudge; investigate every finding.

**Write everything to `investigation.md` in this finding's work directory** — the
cited code, call chain, reachability, safeguards, developer evidence, and
known-status. Phase 2 and the final verdict read this file; it is the evidence
record, not a verdict.

The three steps are: code audit → developer-knowledge search → known-status / precedent.

## Step 1: Code audit (record facts, do not conclude)

Read the source to establish what the code does — not whether it is a bug.

1. **Locate the relevant code.** Find the specific functions and lines the finding cites. Read them in full, in context.
2. **Trace the call chain.** From public APIs / entry points, trace the path to the cited code, and record whether that path is reachable during normal usage.
3. **Construct a trigger scenario.** Describe a concrete sequence of events that could naturally occur and would reach the code. Note any caller-side safeguards (precondition checks, lock guards, downstream sync/resend) that might prevent or mask it — **record them; do not dismiss on a spotted safeguard, Phase 2 proves whether it fires.** If you cannot construct a trigger after genuine effort, record that (it may still be real but hard to reach; Phase 2 will surface it).

Record: cited `file:line`(s), the call chain, the reachability assessment, safeguards encountered, and the trigger scenario.

## Step 2: Developer-knowledge search (record evidence, do not classify)

Search what the developers themselves know and believe about this behavior — as
**evidence** the later verdict weighs, never a verdict now.

1. **Issue tracker.** Open/closed issues, PRs, discussions naming the code, the function, or the behavior.
2. **Commits / blame.** `git log` / `git blame` on the site; read messages and linked PRs for stated intent ("trade-off", "we accept this", "should be safe even if…").
3. **Comments / docs.** Comments near the code (TODO, FIXME, "known issue", "by design"), plus design docs / RFCs.
4. **Tests.** What existing tests assert — a test that sets up this exact scenario and asserts the current behavior is evidence the developers consider it correct.

Record what you find, verbatim, with cites. **Do NOT classify it bug/not-bug here.** Developer intent is one input the verdict weighs later; it is admissible only as *evidence about whether a consequence exists* (e.g. "downstream is built to tolerate this" is evidence of no consequence). A reachable behavior with a real consequence is a bug regardless of intent; a consequence-free inconsistency is not, regardless of how wrong it looks. WIP status / an open TODO is not evidence either way. Just record.

## Step 3: Known-status / precedent — the ONE allowed drop

Determine whether this finding merely **duplicates an already-reported bug**. It
counts as *known* **only** if an existing **issue / PR / CVE / advisory (or a prior
Specula dataset entry) has already reported THIS exact defect** — the SAME
mechanism at the SAME site — as a filed bug. The bar is about *a report already
existing in the tracker*, **not** about developer awareness. So the following do
**NOT** count as known — KEEP the finding and let Phase 2 decide it, because
finding-and-confirming an unreported problem is a real bug even if someone
suspected it:

- a developer merely being **aware** it might be a problem — a comment / `TODO` / `FIXME` / "this might be unsafe" / "could be racy" / "we don't handle X yet". Suspicion is not a filed report; if we find and confirm it, it is our bug.
- a "known limitation" note about a *different* aspect;
- a same-shape precedent applied to a **different** field/message/step — re-verify EACH of the precedent's prerequisites at the new site; a matching shape alone is not the same bug;
- you spotting the gap yourself.

Then apply the single pre-filter:

- **Code-review-sourced AND an existing issue/PR/CVE has already reported this exact defect** → **DROP** now: a code-review reproduction of an already-reported bug is a duplicate, not a new bug. Record `Status: DROPPED (code-review × known, cite: <URL/dataset-id>)` and write no `repro/` test.
- **Otherwise** (MC-found with an actual counterexample — new or known; or any finding not already reported) → proceed to Phase 2. Do not drop; the verdict is decided after reproduction.

---

Proceed to Phase 2 with the evidence recorded in `investigation.md`. Decide the verdict AFTER reproduction — except the code-review × known drop above.
