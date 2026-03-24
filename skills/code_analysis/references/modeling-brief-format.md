# Modeling Brief Format Specification

The **Modeling Brief** is the standard handoff document from Code Analysis to Spec Generation.

Code Analysis finds bugs — some directly confirmable, others suspected but impossible to prove by manual reasoning alone. The Modeling Brief captures these suspected-but-unproven findings and plans how TLA+ model checking can verify them. It is a concise, actionable document that a spec author can use to make design decisions without re-reading the entire codebase.

---

## Required Sections

### 1. System Overview

Brief description (5-10 lines max):

- System name, language, scale (LOC of core logic)
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
