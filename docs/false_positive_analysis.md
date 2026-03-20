# Bug False Positive Analysis (Comprehensive)

**Date**: 2026-03-20

## Data Sources

- **Initial candidates**: `modeling-brief.md` (MC-N and CR-N tables) + `analysis-report.md` findings
- **Bugs claimed found**: `bug-report.md`, `bug-confirmation.md`, `bug-inventory.md`, etc.
- **Confirmed (ground truth)**: Google Sheet tracker — **112 bugs** (98 new + 14 known)

## Tracker Summary (Ground Truth)

### By Original Discovery Method (as recorded)

| | MC-BFS | MC-Simulation | Code Review | By-product | Total |
|---|--------|---------------|-------------|------------|-------|
| New | 38 | 1 | 51 | 8 | **98** |
| Known | 9 | 1 | 4 | 0 | **14** |
| **Total** | **47** | **2** | **55** | **8** | **112** |

### Reclassified by MC-Discoverability

Many CR/BP bugs are **protocol-level** issues (missing guards, persistence ordering, election safety, etc.) that TLA+ can model and TLC can detect. Only **16** bugs are purely code-level (copy-paste, format string, resource leak, bounds check) that MC cannot find.

| Category | Criteria | Count | % |
|----------|---------|-------|---|
| **MC-confirmed** | Found directly by TLC (MC-BFS / MC-Simulation) | 49 | 43.8% |
| **MC-discoverable CR/BP** | Protocol-level bug, TLA+ can model: persistence, election, membership, view change, message guards, snapshot lifecycle, etc. | 47 | 42.0% |
| **MC pipeline subtotal** | | **96** | **85.7%** |
| **Pure CR** | Code-level only: copy-paste (3), runtime exception (2), error handling (3), resource leak (1), bounds check (1), buffer calc (1), concurrency/impl (3), debug gaps (1), off-by-one (1) | **16** | **14.3%** |
| **Total** | | **112** | **100%** |

MC-discoverable CR/BP breakdown by family:
- Message Acceptance Guards (5), View Change Safety (4), Non-Atomic Persistence (4)
- Pre-Vote Protocol Deviation (3), Membership/Config Change (5), Election Safety (4)
- Snapshot/Persistence (5), Leadership Transfer (1), Broadcast Starvation (1)
- Monotonicity Violation (1), Joint Consensus Quorum (1), others (13)

---

## Stage 1: Initial Candidates (Modeling Briefs + Analysis Reports)

Each case study produces a `modeling-brief.md` with MC-N (model checking) and CR-N (code review) hypotheses, plus an `analysis-report.md` with detailed findings.

| # | Case Study | MB MC | MB CR | AR Findings | Total Initial | Confirmed | Not Confirmed |
|---|-----------|-------|-------|-------------|---------------|-----------|---------------|
| 1 | Aeron | 10 | 4 | 0 | 14 | 0 | 14 |
| 2 | AptosBFT | 6 | 4 | 18 | 28 | — | — |
| 3 | arc-swap | 7 | 2 | 0 | 9 | 1 | 8 |
| 4 | async-raft | 8 | 5 | 2 | 15 | 8 | 7 |
| 5 | Autobahn | — | — | 2 | 2* | 16 | — |
| 6 | Besu QBFT | 6 | 4 | 8 | 18 | 1 | 17 |
| 7 | braft | 9 | 5 | 0 | 14 | 5 | 9 |
| 8 | CometBFT | 10 | 5 | 1 | 16 | 2 | 14 |
| 9 | crossbeam-epoch | 7 | 4 | 0 | 11 | 2 | 9 |
| 10 | dotNext | 6 | 3 | 1 | 10 | 5 | 5 |
| 11 | dpdk-ring | 7 | 5 | 0 | 12 | 0 | 12 |
| 12 | Dragonboat | 5 | 5 | 0 | 10 | 3 | 7 |
| 13 | eliben-raft | — | — | 7 | 7 | 4 | 3 |
| 14 | Epaxos | 5 | 2 | 0 | 7 | 3 | 4 |
| 15 | etcd/raft | 8 | 6 | 1 | 15 | 2 | 13 |
| 16 | goraft | 6 | 4 | 0 | 10 | 5 | 5 |
| 17 | HashiCorp Raft | — | — | 0 | —* | 2 | — |
| 18 | hazelcast | 7 | 3 | 2 | 12 | 0 | 12 |
| 19 | kudu | 8 | 4 | 13 | 25 | 0 | 25 |
| 20 | libgomp (GCC) | 5 | 3 | 7 | 15 | 3 | 12 |
| 21 | LLVM libomp | 7 | 5 | 1 | 13 | 1 | 12 |
| 22 | logcabin | 8 | 5 | 0 | 13 | 0 | 13 |
| 23 | N2Paxos | 3 | 3 | 0 | 6 | 3 | 3 |
| 24 | nebula | — | — | 0 | —* | 2 | — |
| 25 | NuRaft | 8 | 4 | 0 | 12 | 3 | 9 |
| 26 | openraft | 7 | 3 | 1 | 11 | 1 | 10 |
| 27 | rabbitmq/ra | 10 | 3 | 0 | 13 | 7 | 6 |
| 28 | raft-java | 7 | 4 | 0 | 11 | 5 | 6 |
| 29 | ratis | 10 | 4 | 0 | 14 | 0 | 14 |
| 30 | RedisRaft | 7 | 5 | 0 | 12 | 2 | 10 |
| 31 | RethinkDB | 7 | 3 | 35 | 45 | 3 | 42 |
| 32 | scc | 8 | 3 | 0 | 11 | 0 | 11 |
| 33 | ScyllaDB | 6 | 3 | 0 | 9 | 1 | 8 |
| 34 | sofa-jraft | 6 | 5 | 21 | 32 | 9 | 23 |
| 35 | Substrate GRANDPA | 8 | 5 | 0 | 13 | 1 | 12 |
| 36 | SwiftPaxos | — | — | — | —* | 2 | — |
| 37 | tarantool | — | — | 11 | 11 | 1 | 10 |
| 38 | tikv/raft-rs | 10 | 3 | 0 | 13 | 4 | 9 |
| 39 | willemt/raft | 9 | 5 | 1 | 15 | 5 | 10 |
| | **Total** | **241** | **131** | **132** | **~504** | **112** | **~392** |

\* Autobahn, HashiCorp Raft, nebula, SwiftPaxos use older pipeline format without standard modeling-brief tables. Autobahn has 17 bugs documented directly in bug-report.md; HashiCorp has 5 families in modeling-brief without MC-N/CR-N table format.

**Notes**:
- MB MC = Model Checking hypotheses in modeling brief
- MB CR = Code Review hypotheses in modeling brief
- AR Findings = Additional findings in analysis report (some overlap with MB)
- "Total Initial" may overcount where AR overlaps with MB
- RethinkDB AR=35 includes bug archaeology (27 historical commits + 8 new findings)

---

## Stage 2: Bugs Claimed Found (Bug Reports)

After MC hunting and code analysis, bugs are documented in bug reports. This is the "claimed found" stage.

| # | Case Study | MC Bugs Claimed | CR/BP Bugs Claimed | Total Claimed | Confirmed | FP |
|---|-----------|----------------|-------------------|---------------|-----------|-----|
| 1 | Aeron | 1 | 0 | 1 | 0 | 1 |
| 2 | arc-swap | 1 | 0 | 1 | 1 | 0 |
| 3 | async-raft | 5 | 3 | 8 | 8 | 0 |
| 4 | Autobahn | 3 (incl 1 retracted) | 14 | 17 | 16 | 1 |
| 5 | Besu QBFT | 2 (incl 1 reclassified) | 0 | 2 | 1 | 1 |
| 6 | braft | 1 | 4 | 5 | 5 | 0 |
| 7 | CometBFT | 2 | 0 | 2 | 2 | 0 |
| 8 | crossbeam-epoch | 2 (known repro) | 0 | 2 | 2 | 0 |
| 9 | dotNext | 0 | 5 | 5 | 5 | 0 |
| 10 | dpdk-ring | 0 | 0 | 0 | 0 | 0 |
| 11 | Dragonboat | 2 | 17 (10CR+6quality+1spec) | 19 | 3 | 16 |
| 12 | eliben-raft | 5 | 2 (design concern+deviation) | 7 | 4 | 3 |
| 13 | Epaxos | 2 | 1 | 3 | 3 | 0 |
| 14 | etcd/raft | 2 | 0 | 2 | 2 | 0 |
| 15 | goraft | 3 | 2 | 5 | 5 | 0 |
| 16 | HashiCorp Raft | 2 (retracted) | 2 | 4 | 2 | 2 |
| 17 | hazelcast | 0 | 0 | 0 | 0 | 0 |
| 18 | kudu | 0 | 0 | 0 | 0 | 0 |
| 19 | libgomp (GCC) | 2 | 0 | 2 | 3 | 0* |
| 20 | LLVM libomp | 1 | 0 | 1 | 1 | 0 |
| 21 | logcabin | 0 | 0 | 0 | 0 | 0 |
| 22 | N2Paxos | 4 | 0 | 4 | 3 | 1 |
| 23 | nebula | 4 | 1 | 5 | 2 | 3 |
| 24 | NuRaft | 2 | 2 | 4 | 3 | 1 |
| 25 | openraft | 0 | 3 (1 confirmed+2 dismissed) | 3 | 1 | 2 |
| 26 | rabbitmq/ra | 0 | 7 | 7 | 7 | 0 |
| 27 | raft-java | 2 | 3 | 5 | 5 | 0 |
| 28 | ratis | 0 | 0 | 0 | 0 | 0 |
| 29 | RedisRaft | 2 | 2 | 4 | 2 | 2 |
| 30 | RethinkDB | 1 | 10 (1 DA-1 + 8 AR + 1 known) | 11 | 3 | 8 |
| 31 | scc | 0 | 0 | 0 | 0 | 0 |
| 32 | ScyllaDB | 0 | 1 | 1 | 1 | 0 |
| 33 | sofa-jraft | 2 | 23 (19 new + 4 known in confirmation) | 25 | 9 | 16 |
| 34 | Substrate GRANDPA | 4 | 0 | 4 | 1 | 3* |
| 35 | SwiftPaxos | 3 | 0 | 3 | 2 | 1 |
| 36 | tarantool | 2 (incl 1 retracted) | 9 (AR findings) | 11 | 1 | 10 |
| 37 | tikv/raft-rs | 0 | 4 | 4 | 4 | 0 |
| 38 | willemt/raft | 0 | 5 | 5 | 5 | 0 |
| | **Total** | **~63** | **~115** | **~178** | **112** | **~66** |

\* libgomp: 3rd bug found after report. Substrate: MC-1/MC-2 are real but not yet in tracker.

---

## Summary: Three-Stage Funnel

```
Stage 1: Modeling Brief Hypotheses    ~504 candidates (241 MC + 131 CR + 132 AR)
            ↓ MC hunting + Code Review
Stage 2: Bugs Claimed Found           ~178 bugs claimed
            ↓ Expert review + Bug confirmation
Stage 3: Confirmed in Tracker          112 bugs confirmed
```

### Conversion Rates

| Metric | Value |
|--------|-------|
| **Stage 1 → Stage 3** (hypothesis → confirmed) | 112 / ~504 = **~22%** |
| **Stage 1 → Stage 2** (hypothesis → claimed) | ~178 / ~504 = **~35%** |
| **Stage 2 → Stage 3** (claimed → confirmed) | 112 / ~178 = **~63%** |
| **Stage 2 FP rate** (claimed → not confirmed) | ~66 / ~178 = **~37%** |

### By Original Discovery Method

| Method | Hypotheses (Stage 1) | Claimed (Stage 2) | Confirmed (Stage 3) | Claim FP Rate |
|--------|---------------------|-------------------|--------------------|----|
| Model Checking | 241 | 63 | 49 | 22.2% (14/63) |
| Code Review | 131 + 132 AR | ~115 | 63 | 45.2% (52/115) |

### Reclassified: MC Pipeline vs Pure CR

Of the 112 confirmed bugs, **96 (85.7%)** are in the MC pipeline (either directly found by TLC or are protocol-level bugs that MC could discover). Only **16 (14.3%)** are pure code-level issues that only CR can find.

| Method | Hypotheses (Stage 1) | Claimed (Stage 2) | Confirmed (Stage 3) | Claim FP Rate |
|--------|---------------------|-------------------|--------------------|----|
| MC pipeline (MC + MC-discoverable CR) | 241 + ~131 | ~178 | **96** | — |
| Pure CR (code-level only) | ~132 AR | — | **16** | — |

### MC Pipeline Detail

| Metric | Value |
|--------|-------|
| MC hypotheses tested (modeling briefs) | 241 |
| MC bugs claimed found (by TLC directly) | 63 |
| MC bugs confirmed (by TLC directly) | 49 |
| MC-discoverable CR/BP bugs confirmed | +47 |
| **MC pipeline total confirmed** | **96** |
| MC direct precision (confirmed / claimed) | **77.8%** |
| MC direct FP rate | **22.2%** |

### Pure CR Detail

| Metric | Value |
|--------|-------|
| Pure CR bugs confirmed | 16 |
| Bug families | Copy-paste (3), Runtime exception (2), Error handling (3), Resource leak (1), Bounds check (1), Buffer calc (1), Concurrency/impl (3), Debug gaps (1), Off-by-one (1) |

### CR Overall Detail (before reclassification)

| Metric | Value |
|--------|-------|
| CR hypotheses (MB + AR) | ~263 |
| CR bugs claimed found | ~115 |
| CR bugs confirmed | 63 |
| CR yield (claimed / hypotheses) | ~43.7% |
| CR precision (confirmed / claimed) | **54.8%** |
| CR FP rate | **45.2%** |

Top CR FP contributors:
- Dragonboat: 17 claimed → 1 confirmed (16 FP) — deliberately inclusive inventory
- sofa-jraft: 23 claimed → 9 confirmed (14 FP) — comprehensive confirmation doc (25 items incl known)
- RethinkDB: 10 claimed → 3 confirmed (7 FP) — 35-item bug archaeology
- tarantool: 9 claimed → 1 confirmed (8 FP) — 11 analysis-report findings

---

## Per-Case False Positives (Stage 2 → Stage 3)

| Case | Claimed | Confirmed | FP | FP Rate | Key FP Reasons |
|------|---------|-----------|-----|---------|---------------|
| Dragonboat | 19 | 3 | 16 | 84.2% | Intentional design, low severity, backward compat |
| sofa-jraft | 25 | 9 | 16 | 64.0% | Pending review, duplicates, non-safety issues |
| tarantool | 11 | 1 | 10 | 90.9% | AR findings mostly informational |
| RethinkDB | 11 | 3 | 8 | 72.7% | Bug archaeology (historical), informational findings |
| nebula | 5 | 2 | 3 | 60.0% | NB-1/NB-3 not independently confirmed |
| eliben-raft | 7 | 4 | 3 | 42.9% | Design concern, paper deviation |
| Substrate | 4 | 1 | 3 | 75.0% | MC-1/MC-2 real but not yet tracked |
| HashiCorp Raft | 4 | 2 | 2 | 50.0% | Spec infidelity (election timeout) |
| openraft | 3 | 1 | 2 | 66.7% | Dismissed (documented behavior) |
| RedisRaft | 4 | 2 | 2 | 50.0% | MC bugs not confirmed, different CR confirmed |
| Autobahn | 17 | 16 | 1 | 5.9% | DA-28 retracted (spec infidelity) |
| Besu QBFT | 2 | 1 | 1 | 50.0% | MC-5 reclassified |
| N2Paxos | 4 | 3 | 1 | 25.0% | 1 family not confirmed |
| NuRaft | 4 | 3 | 1 | 25.0% | 1 MC not confirmed |
| SwiftPaxos | 3 | 2 | 1 | 33.3% | 1 not confirmed |
| Aeron | 1 | 0 | 1 | 100% | MC bug not in tracker |
| 22 other cases | 62 | 62 | 0 | 0% | |
| **Total** | **~178** | **112** | **~66** | **~37%** | |

---

## Key Takeaways

1. **Total pipeline: ~504 initial hypotheses → 112 confirmed bugs** (22% overall yield)

2. **85.7% of confirmed bugs are MC pipeline**: 96 of 112 bugs are either directly found by TLC model checking (49) or are protocol-level bugs discoverable by MC (47). Only 16 bugs (14.3%) are pure code-level issues that require human code review.

3. **MC direct precision is 77.8%**: Of 63 bugs claimed found by TLC, 49 were confirmed. The 14 FP are due to spec infidelity (3), overly-strong invariants (2), and unconfirmed findings (9).

4. **CR false positives concentrate in comprehensive inventories**: Dragonboat (16 FP), sofa-jraft (16 FP), tarantool (10 FP), RethinkDB (8 FP) account for 50/66 = 76% of all FP. These cases used deliberately inclusive documentation that was then filtered.

5. **22 out of 38 cases have 0 false positives**: When bugs are claimed, they are confirmed. The FP problem is concentrated in ~10 cases with extensive inventories.

6. **MC-discoverable CR families**: The 47 CR/BP bugs attributable to the MC pipeline span protocol-level families — Message Acceptance Guards (5), View Change Safety (4), Non-Atomic Persistence (4), Pre-Vote Deviation (3), Membership/Config Change (5), Election Safety (4), Snapshot/Persistence (5), etc. These are bugs in **state machine logic** that TLA+ specifications naturally model.
