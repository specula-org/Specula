# Code Analysis for Formal Verification

Investigate a system implementation to establish the requested modeling scope and find bugs. Some bugs can be confirmed directly (copy-paste errors, data races). Protocol safety questions may need TLA+ model checking to resolve. The **Modeling Brief** describes the system behavior to model, its contracts and abstractions, and findings that need verification.

When a candidate defect appears, follow [Persistent Findings](../bug-confirmation/references/persistent-findings.md) for a lightweight history match before deeper analysis or reproduction.

## Input / Output

**Input**: Repository path + reference algorithm/paper (optional) + GitHub URL (optional)

**Output**: `modeling-brief.md` (handoff to Spec Generation) + `analysis-report.md` (optional audit trail)

**The user drives each phase.** You provide methodology and execute on their direction.

---

## Step 0: Classify System Category

Before archaeology or deep analysis, classify the target as one of:

- **Category A (Distributed / Message-Passing)** — network RPC, disk I/O, cluster membership, protocol state machines
- **Category B (Concurrent / Lock-Free / Runtime)** — CAS loops, atomics, thread handoff, memory reclamation, ownership transfer, async cancellation

Record the category and a brief justification in `modeling-brief.md`.

After classifying:

- read `references/deep-analysis.md` for the shared methodology
- read `references/distributed-analysis.md` for **Category A**
- if Category A uses BFT consensus (Byzantine threat model — PBFT, HotStuff, Tendermint, DiemBFT, IBFT/QBFT, etc.), **also** read `references/bft-analysis.md`
- read `references/concurrent-analysis.md` for **Category B**

---

## Phase 1: Reconnaissance

**Goal**: Build a structural map — core modules, scale, concurrency model, and atomicity boundaries.

---

## Phase 2: Bug Archaeology

**Goal**: Map historical bugs to identify error-prone areas and recurring patterns. This phase requires **thorough** coverage — the quality of the entire analysis depends on the evidence gathered here.

### Steps

1. **Git history mining** by keyword (fix, bug, race, panic, deadlock, correctness, crash, corrupt, leak, inconsistent, wrong). Analyze **all** significant bug-fix commits, not just a sample.
2. **Issue/PR verification** — read full discussions, not just titles. Use `gh issue list` with multiple keyword searches and label filters to maximize coverage.
3. **Scenario grouping** — group by shared **mechanism**, not by file.
4. **Reference comparison** (if applicable) — find deviations from paper/other implementations.

### Depth Requirements

- **Git commits**: Analyze all bug-fix commits touching core files. Report the total count.
- **GitHub issues**: Read the full discussion thread (including all comments) for every issue you plan to reference. Select relevant discussions across the requested components and mechanisms; a fixed issue count does not establish sufficient coverage. Report: total issues collected, total deeply read, total confirmed, total excluded with reasons, and unresolved review work.
- **Open PRs**: Review all open PRs with bug-fix intent — they often contain fixes waiting for review and reveal known-but-unfixed problems.
- **Parallelization**: Use multiple Task subagents for independent issue verification when available. Size assignments by the discussion depth and component relationships, keeping a shared record of reviewed and pending evidence.

**Read `references/bug-archaeology.md`** for detailed methodology.

---

## Phase 3: Deep Analysis

**Goal**: Find new issues through systematic code reading, guided by Phase 2 — code path inconsistencies, non-atomic operations, missing guards, reference deviations.

### Parallelization Strategy

Deep Analysis is the most time-consuming phase. **Use parallel Task subagents aggressively**:

- Divide work by coherent components, mechanisms, or source files, including the callers and consumers needed to understand them
- Each subagent reads its assigned core files completely and applies the relevant analysis patterns
- After all subagents return, cross-reference findings in the main context

Choose parallelism according to the scope, dependencies, host capabilities, and available resources. The coordinating agent remains responsible for cross-component contracts and unresolved coverage.

### Verification

Every finding MUST be verified: re-read exact code lines, check for compensating mechanisms, trace execution path, check if it's an acknowledged design decision.

**Read `references/deep-analysis.md`** for the full methodology.

---

## Phase 4: Modeling Brief

**Goal**: Produce an actionable handoff for the requested modeling scope — describe the baseline behavior and component interactions, organize findings into Scenarios, propose spec extensions, explain exclusions, and classify findings by verification method. Priorities determine investigation order; they do not cap the number of Scenarios or replace the requested scope with a shortlist.

When target-specific guidance is provided, treat its priorities and scope as required investigative intent. Make their handling visible in the Modeling Brief through the relevant Scenarios, findings, exclusions, or unresolved questions, without imposing a separate format. Guidance determines what must be investigated, not what the evidence must conclude, and it remains a coverage floor rather than a ceiling on code-driven exploration. Respect explicit boundaries, while reading adjacent code when needed to establish in-scope behavior.

**Read `references/modeling-brief-format.md`** for the format specification.
**See `examples/hashicorp-raft-modeling-brief.md`** for a complete example.

Examples record the scope and choices of earlier investigations; their length, Scenario counts, and exclusions do not constrain a new target.

---

## Critical Rules

1. **VERIFY before reporting.** Re-read the code. Check for compensating mechanisms. No unverified suspicions.
2. **Read issue discussions, not just titles.** For every issue you reference, read the full comment thread via `gh issue view --comments`. Confirm it hasn't been debunked.
3. **Do NOT hallucinate code logic.** If unsure, READ IT. Cite `file:line` for every claim.
4. **Exclude false positives explicitly.** Explain WHY each exclusion was made.
5. **Use parallel subagents aggressively.** Launch multiple Task subagents for concurrent issue verification, concurrent file analysis, and concurrent commit review. This is essential for both depth AND coverage.
6. **Evidence-based claims only.** Show code, git commits, issue discussions, or code path inconsistencies.
7. **Group findings by mechanism.** Use as many Scenarios as the evidence and scope require. Document baseline behavior and cross-component contracts even when no candidate defect has been identified.
8. **Thoroughness is non-negotiable.** Do not skip issues, truncate commit analysis, or sample instead of scanning. The analysis report should document coverage statistics (total commits analyzed, issues deeply read, false positives excluded).
9. **Classify Category A vs B explicitly.** Carry that decision into the Modeling Brief. Later phases should not have to rediscover it.

---

## Reference Files

- **`references/bug-archaeology.md`** — Git mining and issue verification methodology
- **`references/deep-analysis.md`** — Shared deep-analysis methodology
- **`references/distributed-analysis.md`** — Category A (distributed / message-passing) analysis patterns
- **`references/bft-analysis.md`** — BFT overlay (Byzantine adversary categories), read in addition to distributed-analysis.md when Category A is BFT
- **`references/concurrent-analysis.md`** — Category B (concurrent / lock-free / runtime) analysis patterns
- **`references/modeling-brief-format.md`** — Standard format for the handoff document
- **`examples/hashicorp-raft-modeling-brief.md`** — Complete real-world example

## Related Skills

- **spec-generation** — Next phase: produces TLA+ specs from the Modeling Brief
- **tla-trace-workflow** — Validates the trace spec against real traces

## Additional References

For additional examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
