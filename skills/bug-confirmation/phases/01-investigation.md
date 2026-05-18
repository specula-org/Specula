# Phase 1: Investigation

Confirm whether the finding is a real bug, what the bug claim depends on, and why the code supports or refutes the claim. Investigate every finding the input lists — do not prejudge or pre-filter. Each step's output feeds the next.

The three steps are: code audit → developer intent investigation → precedent re-check.

## Step 1: Code audit

Confirm the bug's validity by reading the source code.

1. **Locate the relevant code.** Find the specific functions and lines mentioned in the bug report. Read these functions in full and understand their context.
2. **Trace the call chain.** Starting from public APIs or entry points, trace the path to the buggy code. Confirm whether this path is reachable during normal usage.
3. **Check for existing safeguards.** Check whether callers already have precondition checks, lock guards, or other mechanisms that prevent this bug from being triggered in practice. If they do, report the finding as a false positive with the safeguard cited and stop.
4. **Construct a trigger scenario.** Describe in words a concrete sequence of events that could naturally occur at the user/system level and would reach the buggy code path. If you cannot construct one after genuine effort, note that explicitly — the bug may still be real but unreachable, in which case Phase 2 reproduction will likely fail and surface that.

Record what you found: the cited file:line(s), the call chain, any safeguards encountered, and the constructed trigger scenario.

## Step 2: Developer intent investigation

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

## Step 3: Precedent prerequisite re-check

If the finding cites a precedent — an upstream-accepted issue, a prior-round acceptance, a similar pattern in a sister project — the precedent endorses *the pattern under its prerequisites*, not the pattern's applicability to a new field, message, or protocol step. Re-verify each of the precedent's prerequisites at the new site explicitly. Do not treat *"this is the same shape as accepted bug X"* as sufficient: the same shape on a different field can be a real bug, an artifact of spec asymmetry, or by design — only the per-site prerequisite check distinguishes these.

If the finding does not cite a precedent, skip this step.

---

After completing the steps and being confident the bug stands (or has been firmly invalidated), proceed to Phase 2 (Reproduction).
