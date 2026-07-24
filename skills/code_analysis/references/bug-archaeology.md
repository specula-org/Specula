# Bug Archaeology Methodology

Detailed guide for Phase 2 of Code Analysis: mining historical bugs and grouping them into Scenarios.

---

## 1. Git History Mining

### 1.1 Bug-Fix Commit Search

Search for bug-fix commits in core files using `git log --oneline --all --grep="<keyword>" -- <core_files>` with keywords like: fix, bug, race, deadlock, panic, safety, correctness. Examine interesting commits with `git show`.

### 1.2 Bug Hotspot Analysis

Count which files appear most frequently in bug-fix PRs/commits to identify the most error-prone areas.

### 1.3 Classify Each Bug Fix

For each bug fix commit, record:

| Field | Description |
|-------|-------------|
| Commit/PR | Reference for tracing back |
| Summary | One-line description |
| Root cause | What was wrong (logic error, race, missing check, etc.) |
| Component | Which subsystem (election, replication, config, persistence, etc.) |
| Severity | Critical (safety violation) / High (data loss, cluster down) / Medium / Low |

---

### 1.4 Already-Fixed Bugs Are Reference, Not Targets

If a historical bug is already fixed in mainline, reproducing it adds value only if the reproduction itself produces something the upstream fix did not — e.g., a deeper mechanism explanation the original PR missed, a generalization to other sites the upstream did not audit, or a regression test the project does not have.

**Re-deriving the bug via formal methods is not new value.** TLA+ and Miri both recovering "this fix is necessary" is equivalent to `git revert <commit> && cargo test` — useful as methodology demonstration, but contributes zero information about the system itself.

When a historical fix has no such added value, record it as **reference context** in the brief (under "Reference Pointers" or as evidence for a bug-prone mechanism) — not as a Model-Checkable Finding or as a modeling target. A modeling-brief entry of the form "MC1: recreate pre-`<commit>` state of #<issue>" is target painting and should be rewritten as either (a) an unaudited-site question of the same mechanism, or (b) demoted to reference.

**Value-driven containment**: a historical fix's citation flows from § 2 Evidence (as bug-prone-mechanism evidence) and stays in § 7 Reference Pointers. It must **not** propagate into § 4 Proposed Extensions, § 5 Proposed Invariants, or § 6.1 Model-Checkable Findings — including when the propagation is rationalized as "defense-confirmation target", "defense audit", "X-style attack probe", "boundary test at the threshold", "test the brief's MC-N hypothesis", or "verify the fix is load-bearing". Each of these framings predictably produces a Phase 4 writeup that admits the finding is "hardening / no externally observable consequence / deliberate developer intent / documented design choice" — zero information beyond the existing PR. Specula's compute and agent effort are spent to produce information the user does not already have; observed cost of generating predictable zero-value findings is ~$100 per case in the BFT corpus. Stop the propagation at § 2.

**Scope: § 6.1 only.** Value-driven containment applies to Model-Checkable Findings (§ 6.1) because each MC hunt-cfg costs $30-80 in observed runs. § 6.3 (Code-Review-Only) candidates are NOT subject to this principle — they cost only brief-space to enumerate, and the "predict the Phase 4 verdict" heuristic is unreliable enough that pre-pruning reliably drops real bugs (helper-layer one-liners, code patterns whose effects only become clear after reading the call chain). Send every § 6.3 candidate through Phase 4 audit; let Phase 4 decide.

---

## 2. GitHub Issue/PR Verification

### 2.1 Issue Collection

Use `gh issue list -R <owner/repo>` to search by bug label and by relevant keywords (e.g., race condition, data loss, election, correctness, etc.).

### 2.2 Issue Verification (CRITICAL)

**Do NOT trust issue titles.** For every potentially interesting issue, read the full discussion:

```bash
gh issue view -R <owner/repo> <number> --comments
```

Classify each issue:

| Classification | Criteria |
|---------------|----------|
| **Confirmed bug** | Has reproduction, multiple confirmations, or maintainer acknowledgment |
| **Design defect** | Architectural limitation acknowledged by maintainers |
| **Disputed/False** | Discussed and determined to be invalid |
| **User error** | Reported as bug but actually misconfiguration |
| **Uncertain** | Insufficient evidence to determine |

For confirmed bugs, also determine:
- Is it fixed? What commit/PR fixed it?
- If unfixed, how long has it been open?
- What is the root cause?
- Which code component is affected?

### 2.3 Open PR Review

Check open PRs — they often contain bug fixes waiting for review or discussions revealing known limitations.

### 2.4 Parallelization

Use multiple Task subagents to verify issues in parallel (5-10 issues per subagent).

---

## 3. Scenario Grouping

This is the most analytically important step. Transform a flat list of bugs into grouped scenarios.

### 3.1 Grouping Strategy

Start with the raw list of confirmed bugs (from git history + issues). For each bug, ask:

1. **What mechanism failed?** (not "what file was changed")
2. **Is there another bug with the same mechanism?**
3. **Could this mechanism fail in a different place?**

### 3.2 Common Scenario Patterns

| Pattern | Description | Example |
|---------|-------------|---------|
| **Path inconsistency** | N code paths should behave identically but M < N do | 3 AppendEntries reply paths, only 2 check resp.Term |
| **State interaction** | Two features interact in unexpected ways | Config change + election, snapshot + replication |
| **Architectural side effect** | A design decision has unintended consequences | Independent heartbeat goroutine bypasses term checking |
| **Non-atomic operation** | Multi-step operation with crash window | Write term, then write votedFor (crash between = inconsistent) |
| **Missing invariant** | A property that should hold but isn't checked | Leader doesn't verify its own health before serving |
| **Copy-paste divergence** | Code copied and modified, with some paths missing updates | PreVote copied from RequestVote, metrics label not updated |

### 3.3 Scenario Template

For each Scenario:

```markdown
### Scenario N: <Descriptive Name>

**Mechanism**: One sentence describing the shared root cause.

**Evidence**:
- Historical: <list of commits/issues with one-line summaries>
- Code analysis: <file:line references, if any new findings>

**Affected code paths**: <specific functions/handlers>

**Assessment**:
- How many bugs in this scenario? (historical + new potential)
- How severe? (production impact?)
- How suitable for TLA+ modeling?

**Priority**: High / Medium / Low
```

### 3.4 Priority Ranking

Rank scenarios by combined score:

| Factor | Weight | Meaning |
|--------|--------|---------|
| Historical bug count | High | More past bugs = more likely to have undiscovered ones |
| Severity of past bugs | High | Production-impact bugs indicate dangerous areas |
| Number of new potential findings | Medium | More suspects = richer modeling target |
| TLA+ suitability | High | Protocol logic > implementation details |
| Unfixed known bugs | High | Confirms the area is still problematic |

---

## 4. Cross-Implementation Comparison (Optional)

When multiple implementations of the same algorithm exist:

### 4.1 What to Compare

- **Architectural decisions**: How each implementation handles the same concern differently
- **Bug history overlap**: Bugs fixed in one implementation that may exist in another
- **Feature scope**: What features one has that others don't (PreVote, Pipeline, LeaderLease, etc.)

### 4.2 How to Compare

Focus on the Scenarios identified above. For each Scenario:
- Does the other implementation have the same mechanism?
- Did they solve the same problem differently?
- Did they have similar bugs?

### 4.3 Value of Comparison

Cross-implementation comparison is valuable because:
- A bug fixed in implementation A might exist in implementation B
- Different design choices for the same problem reveal edge cases
- A reference implementation provides a "known good" baseline for the spec
