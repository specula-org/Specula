# Modeling Brief Format Specification

The **Modeling Brief** is the standard handoff document from Code Analysis to Spec Generation.

The Modeling Brief describes the behavior, contracts, and abstractions needed to model the requested scope, together with suspected findings and plans for verifying them. Give the spec author enough source-grounded detail to construct a connected model and identify where further source reading is needed. Its length and number of Scenarios depend on the system and scope.

---

## Required Sections

### 1. System Overview

Describe the system at the level needed to understand the modeling scope:

- System name, language, scale (LOC of core logic)
- System category: **Category A (Distributed / Message-Passing)** or **Category B (Concurrent / Lock-Free)**, with one-sentence justification
- What protocol/algorithm it implements
- Key architectural choices that deviate from the reference algorithm
- Concurrency model (single-threaded event loop, goroutines, async, etc.)

### 2. Scenarios

Group related findings into evidence-backed Scenarios by
**mechanism/pattern**, not by file or component. A Scenario may encompass multiple
findings and yield multiple concrete bugs. Baseline behavior and contracts belong
in the overview and modeling recommendations even when they have no associated finding.

Each Scenario entry:

```markdown
### Scenario N: <Name>

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

Grouping criteria for Scenarios:
- Bugs that share the same **mechanism** (e.g., "multiple code paths that should behave identically but don't")
- Bugs that affect the same **interaction pattern** (e.g., "config change + election interleaving")
- Bugs that stem from the same **architectural decision** (e.g., "independent heartbeat goroutine")

### 3. Modeling Recommendations

Two sub-sections:

#### 3.1 Model (with rationale)

For each item, state:
- **What**: the behavior or mechanism to model
- **Why**: connect it to the requested scope, a system contract, or Scenario evidence
- **How**: explain the state, transitions, interfaces, and abstraction decisions needed to represent it

For a scope spanning multiple components, explain their execution contexts and ownership, identity relationships, state transitions and atomicity boundaries, interface outcomes, and supported configuration differences. Connect normal execution with error, cancellation, cleanup, and recovery paths. For abstracted internals, state the retained effects, assumptions, source evidence, and unresolved questions. Use tables, diagrams, or linked companion documents when helpful; the brief must index any companion material required for spec generation.

#### 3.2 Do Not Model (with rationale)

For each excluded item, state:
- **What**: the behavior or mechanism NOT to model
- **Why**: why TLA+ is not the right tool (e.g., copy-paste error, metrics issue, pure performance concern)

### 4. Proposed Extensions

Concrete list of spec extensions beyond the reference algorithm:

```markdown
| Extension | Variables | Purpose | Scope / Contract / Scenario |
|-----------|-----------|---------|------------|
| <name>    | var1, var2 | <what it captures> | <source-grounded motivation> |
```

### 5. Proposed Invariants

Properties to check, derived from system contracts, the requested scope, and Scenarios:

```markdown
| Invariant | Type | Description | Targets |
|-----------|------|-------------|---------|
| <name>    | Safety / Liveness | <what it checks> | Scenario N, finding X |
```

Include both:
- Standard algorithm invariants (ElectionSafety, LogMatching, etc.)
- Implementation-specific invariants derived from the analysis

### 6. Findings Pending Verification

Findings from Code Analysis that need further work, split by verification method:

#### 6.1 Model-Checkable

Findings that TLA+ model checking should be able to confirm or refute. These directly feed into the spec's invariants and error injection strategy.

```markdown
| ID | Description | Expected invariant violation | Scenario |
|----|-------------|----------------------------|------------|
```

**Each MC finding should be a forward-looking question about unaudited behavior**, not a reproduction of a closed historical issue.

- ✅ *"Can cancellation after publication let cleanup reclaim data still owned by a reader?"* — an unresolved mechanism question grounded in current code.
- ❌ *"MC1: recreate pre-`d5dd00c` state of #198"* — the answer is in the closed PR; the fix already passed review.

Record an already-fixed defect in § 7 Reference Pointers or as an explicitly labeled regression target. Its guards and associated behavior can still belong in the current model. Do not remove a fix to manufacture a new finding. See `bug-archaeology.md` § 1.4.

**Evidence-based triage.** For each candidate, identify the reachable behavior in question, possible observable consequence, and remaining uncertainty. Resolve exclusions with source or historical evidence rather than predicting the eventual confirmation verdict. Priorities and estimated cost can guide investigation order within the user's budget; they do not establish that a candidate is false or remove an in-scope contract from modeling.

Keep candidates routed to testing or code review visible in § 6.2 / § 6.3. An uncertain classification is a question for further analysis, not a reason to omit the candidate.

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

1. **Scale detail with scope.** There is no fixed line, word, or Scenario count. Preserve the behavioral detail needed for modeling; organize large handoffs into linked sections or companion documents rather than compressing away necessary information. The analysis report retains the investigation evidence.

2. **Actionable over descriptive**. Every section should directly inform a spec design decision.

3. **Evidence-based**. Every claim references a commit, issue, or file:line.

4. **Connect the baseline and the Scenarios.** Group findings by mechanism and explain how they interact with the system behavior being modeled. A component does not need a suspected bug to belong in the requested model.

5. **Explicit exclusions**. Stating what NOT to model is as valuable as stating what to model. It prevents the spec author from wasting effort.
6. **Category must carry forward.** Later phases should be able to read the brief and immediately know whether to use distributed-style or concurrent-style modeling and trace validation.
7. **Put category-specific detail in the right place.** The brief should record the category and chosen scenarios, but the reusable playbooks live in `distributed-analysis.md` and `concurrent-analysis.md`, with `bft-analysis.md` as a BFT overlay on top of distributed.
8. **Distinguish historical and current results.** Preserve current fixes and use their history to explain modeled behavior and properties. Label historical or regression checks explicitly; only unresolved questions about current behavior belong among new model-checkable candidates. See `bug-archaeology.md` § 1.4 and § 6.1 above.
