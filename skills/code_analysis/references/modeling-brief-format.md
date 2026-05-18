# Modeling Brief Format Specification

The **Modeling Brief** is the standard handoff document from Code Analysis to Spec Generation.

Code Analysis finds bugs — some directly confirmable, others suspected but impossible to prove by manual reasoning alone. The Modeling Brief captures these suspected-but-unproven findings and plans how TLA+ model checking can verify them. It is a concise, actionable document that a spec author can use to make design decisions without re-reading the entire codebase.

---

## Required Sections

### 1. System Overview

Brief description (5-10 lines max):

- System name, language, scale (LOC of core logic)
- System category: **Category A (Distributed / Message-Passing)** or **Category B (Concurrent / Lock-Free)**, with one-sentence justification
- What protocol/algorithm it implements
- Key architectural choices that deviate from the reference algorithm
- Concurrency model (single-threaded event loop, goroutines, async, etc.)

### 2. Bug Families

The core of the document. Group findings by **mechanism/pattern**, not by file or component.

Each Bug Family entry:

```markdown
### Family N: <Name>

**Mechanism**: One-sentence description of the shared root cause pattern.

**Evidence**:
- Historical: <commit/issue references with one-line summary>
- Code analysis: <file:line references with one-line description>

**Affected code paths**: List the specific functions/handlers involved.

**Suggested modeling approach**:
- Variables: what new state variables are needed
- Actions: what actions need to be modeled differently from the reference spec
- Granularity: should this be one action or split into multiple steps

**Priority**: High / Medium / Low
**Rationale**: Why this priority (bug density, severity, TLA+ suitability)
```

Grouping criteria for Bug Families:
- Bugs that share the same **mechanism** (e.g., "multiple code paths that should behave identically but don't")
- Bugs that affect the same **interaction pattern** (e.g., "config change + election interleaving")
- Bugs that stem from the same **architectural decision** (e.g., "independent heartbeat goroutine")

### 3. Modeling Recommendations

Two sub-sections:

#### 3.1 Model (with rationale)

For each item, state:
- **What**: the behavior or mechanism to model
- **Why**: reference specific Bug Family evidence
- **How**: brief note on modeling approach (extension variable, split action, etc.)

#### 3.2 Do Not Model (with rationale)

For each excluded item, state:
- **What**: the behavior or mechanism NOT to model
- **Why**: why TLA+ is not the right tool (e.g., copy-paste error, metrics issue, pure performance concern)

### 4. Proposed Extensions

Concrete list of spec extensions beyond the reference algorithm:

```markdown
| Extension | Variables | Purpose | Bug Family |
|-----------|-----------|---------|------------|
| <name>    | var1, var2 | <what it captures> | Family N |
```

### 5. Proposed Invariants

Properties to check, derived from Bug Families:

```markdown
| Invariant | Type | Description | Targets |
|-----------|------|-------------|---------|
| <name>    | Safety / Liveness | <what it checks> | Family N, finding X |
```

Include both:
- Standard algorithm invariants (ElectionSafety, LogMatching, etc.)
- Implementation-specific invariants derived from the analysis

### 6. Findings Pending Verification

Findings from Code Analysis that need further work, split by verification method:

#### 6.1 Model-Checkable

Findings that TLA+ model checking should be able to confirm or refute. These directly feed into the spec's invariants and error injection strategy.

```markdown
| ID | Description | Expected invariant violation | Bug Family |
|----|-------------|----------------------------|------------|
```

**Each MC finding should be a forward-looking question about unaudited behavior**, not a reproduction of a closed historical issue.

- ✅ *"If FastConfirmLoad's SC label is downgraded, can a stale snapshot reach the writer?"* — mechanism question, lets MC explore something whose answer isn't already known.
- ❌ *"MC1: recreate pre-`d5dd00c` state of #198"* — the answer is in the closed PR; the fix already passed review.

We don't value findings whose punchline reduces to "we reproduced a bug that's already fixed upstream." Re-deriving via TLA+ + Miri produces no information beyond `git revert <commit> && cargo test`. If a candidate finding's only honest description is "recreate #N" or "regression of PR #M", **demote it to § 7 Reference Pointers** — keep the issue as context for the bug family in § 2, but don't list it as a modeling target. See `bug-archaeology.md` § 1.4.

**Output-value litmus** (apply before adding any candidate to § 6.1): write the one-sentence Phase 4 writeup conclusion you predict for the finding. If the only honest conclusion is one of "hardening / defense-in-depth / no externally observable consequence / deliberate developer intent / documented design choice", **drop the finding from § 6.1 entirely** — the Phase 2-onward MC effort it would consume (~$30-80 per hunt-cfg pass in observed BFT runs) yields zero information beyond the existing fix. The Phase 2 hunt-cfg author is the same agent writing § 6.1, so the predicted Phase 4 verdict is fully accessible at brief-writing time; if you can foresee the verdict, the work is not worth generating. Rewrite the finding as a genuinely open mechanism question, or demote to § 7 Reference Pointers.

**Litmus scope: § 6.1 only.** This pre-filter applies to Model-Checkable Findings because each MC hunt-cfg consumes real compute ($30-80 per run). § 6.3 (Code-Review-Only) candidates skip this gate — Phase 4 audit is cheap compared to MC, and the predicted-verdict heuristic has been observed to reliably miss real helper-layer bugs (e.g., braft's `AppendEntriesCache(_, version)` initializer that writes `_cache_version(0)` ignoring the parameter — a one-line bug that looks "trivial" at brief-writing time but is a real defect). All § 6.3 candidates flow to Phase 4 without predicted-verdict filtering.

#### 6.2 Test-Verifiable

Findings better verified by writing unit/integration tests. Not suitable for TLA+ (too low-level, implementation-specific, or performance-related).

```markdown
| ID | Description | Suggested test approach |
|----|-------------|----------------------|
```

#### 6.3 Code-Review-Only

Findings that require human judgment (design decisions, copy-paste errors, defensive programming gaps).

```markdown
| ID | Description | Suggested action |
|----|-------------|-----------------|
```

### 7. Reference Pointers

Links to detailed evidence for the spec author to consult:
- Full analysis report path
- Key source files with line ranges
- Relevant GitHub issues/PRs
- Reference spec/paper (if any)

---

## Principles

1. **Concise over comprehensive**. The modeling brief should be 100-200 lines, not 800. The full analysis report exists for details.

2. **Actionable over descriptive**. Every section should directly inform a spec design decision.

3. **Evidence-based**. Every claim references a commit, issue, or file:line.

4. **Bug Families are the organizing principle**. Don't list findings flat. Group by mechanism so the spec author can design targeted extensions.

5. **Explicit exclusions**. Stating what NOT to model is as valuable as stating what to model. It prevents the spec author from wasting effort.
6. **Category must carry forward.** Later phases should be able to read the brief and immediately know whether to use distributed-style or concurrent-style modeling and trace validation.
7. **Put category-specific detail in the right place.** The brief should record the category and chosen bug families, but the reusable playbooks live in `distributed-analysis.md` and `concurrent-analysis.md`, with `bft-analysis.md` as a BFT overlay on top of distributed.
8. **Closed bugs are reference, not target.** Historical bugs that the upstream has already fixed belong in § 2 Evidence (as evidence for the mechanism's bug-proneness) and § 7 Reference Pointers (as context for the spec author). They do **not** belong in § 6.1 as model-checkable findings. Reproducing a closed bug via formal methods produces no information beyond what the original PR already has. We don't value such results. See `bug-archaeology.md` § 1.4 and § 6.1 above.
