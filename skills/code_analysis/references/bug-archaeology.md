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

Historical fixes explain current guards, failure paths, and correctness contracts. They can support baseline modeling, regression validation, and investigation of related sites or interactions.

**Reproducing a historical defect is not a new discovery.** Label any historical or regression experiment separately from findings about the current implementation, and preserve the current fix in the reference model.

Record historical defects as reference context or explicitly labeled regression targets. A new Model-Checkable Finding must identify an unresolved question about current behavior rather than merely recreate a pre-fix state.

**Separate historical evidence from new findings.** Historical fixes can explain current guards, state transitions, and properties in the baseline model and its extensions. Preserve that behavior when it is part of the requested scope. Do not list re-creating an already-fixed defect as a new § 6.1 Model-Checkable Finding or remove its fix from the model to obtain a violation. A current interaction or generalization needs its own source-grounded question and a clear distinction from the historical result.

**Use evidence for finding triage.** Do not discard unresolved candidates based on predicted confirmation outcomes or assumed verification cost. Record the open mechanism question, evidence still needed, and the appropriate verification route; keep baseline coverage independent of candidate novelty.

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

Use multiple Task subagents to verify independent discussions in parallel when available. Size assignments to their complexity and record which discussions were actually read.

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
