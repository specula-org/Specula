# Splits

Two properties were split. Each keeps its original name, now defined as the conjunction of its parts, so every `.cfg` still works. Clause text was copied character for character. Splitting `\A x \in S : C1 /\ C2 /\ C3` into `(\A x \in S : C1) /\ (\A x \in S : C2) /\ ...` does not change the meaning.

## 1. AckPreservation

Original (`spec-original/base.tla:1184-1187`):

```tla
AckPreservation == \A a\in history.acks:
    /\ a.before=a.after
    /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
    /\ (a.cursor#0 => a.applied=a.cursor)
```

Parts (`spec-annotated/base.tla`):

```tla
AckPreservation_LogUnchanged == \A a\in history.acks:
    /\ a.before=a.after
AckPreservation_SnapshotRetained == \A a\in history.acks:
    /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
AckPreservation_AppliedCursor == \A a\in history.acks:
    /\ (a.cursor#0 => a.applied=a.cursor)
AckPreservation == AckPreservation_LogUnchanged /\ AckPreservation_SnapshotRetained /\ AckPreservation_AppliedCursor
```

Why the clauses have different origins:

| Part | Status | Origin |
|---|---|---|
| `_LogUnchanged` | requirement | Commit ee0757a9b ("raft: stableTo checks term matching") states the rule: "raft must verify the (index,term) of stableTo, before marking the entries as stable." The comment at log_unstable.go:82-84 restates it, and test TestStableTo (log_test.go:481, "bad term") checks it. |
| `_SnapshotRetained` | unknown | Only the code supports it: `stableSnapTo` clears the unstable snapshot only when its index equals the acknowledged one (log_unstable.go:111-115). The guard was added in 516891c49 ("raft: set snapshot to nil when it is saved") with no stated reason. Later commits (83245f7fe, 4b3a7ff35, 09d237400) only moved the code. No test calls `stableSnapTo`. |
| `_AppliedCursor` | requirement | The doc comments on `appliedCursor` (node.go:112-114), `commitReady` (rawnode.go:52-55) and `Advance` (node.go:149) say so. The regression test comment at rawnode_test.go:465-467 calls a cursor that is off by one a lost write. |

## 2. LogStructure

Original (`spec-original/base.tla:1243-1247`):

```tla
LogStructure == \A n\in Server:
    /\ raft[n].applied<=raft[n].commit
    /\ raft[n].commit<=Last(raft[n])
    /\ \A k\in DOMAIN Hist(raft[n]):Hist(raft[n])[k].index=k
    /\ raft[n].uoff+Len(raft[n].unstable)<=Last(raft[n])+1
```

Parts:

```tla
LogStructure_CommitBounds == \A n\in Server:
    /\ raft[n].applied<=raft[n].commit
    /\ raft[n].commit<=Last(raft[n])
LogStructure_Indexing == \A n\in Server:
    /\ \A k\in DOMAIN Hist(raft[n]):Hist(raft[n])[k].index=k
    /\ raft[n].uoff+Len(raft[n].unstable)<=Last(raft[n])+1
LogStructure == LogStructure_CommitBounds /\ LogStructure_Indexing
```

Why the clauses have different origins:

| Part | Status | Origin |
|---|---|---|
| `_CommitBounds` | requirement | log.go:37 says "Invariant: applied <= committed". raft.go:513-514 says "The leader MUST NOT forward the follower's commit to an unmatched index." TestCommitTo (log_test.go:451, "commit out of range -> panic") checks the bound, and commit a90ffa34e explains the panic as possible log corruption. |
| `_Indexing` | model-internal | These clauses check that the model's own `Hist`/`unstable` representation is well formed (entry k has index k; the unstable segment ends inside the log). The only related source text is a layout comment (log_unstable.go:19). |

## Mixed-origin properties not split

These properties mix origins but are a single `LET`/`\A` body (or a helper-defined body), so the splitting shape does not apply. Each block gives a per-clause status in `\* clause` lines instead: VoteDecisionEligibility, CampaignDecisionEligibility, TransferDecisionEligibility, RequestCorrelatedConfigurationEffects, ProposalConfigurationDecisions, OutcomeSoundness (via `ExpectedDecision`), ReadBasis, NoUnexpectedFatal, and TypeOK (its per-node conjunction contains the requirement clause `voters \cap learners = {}`).
