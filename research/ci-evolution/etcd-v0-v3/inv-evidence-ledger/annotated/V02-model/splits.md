# Splits (V02 model)

Five properties mixed clauses of different origins and had the shape `P == \A x \in S : C1 /\ ... /\ Cn` or `P == C1 /\ C2`. Each was split into parts, with clause text copied unchanged. The original name is kept as the conjunction of the parts, so every `.cfg` and every `Update.tla` alias still resolves. All are in `spec-annotated/base.tla`. No `.cfg` was edited.

Mixed properties that were **not** split, because their clauses share one `LET` contract or sit inside one quantifier body: `TypeOK`, `VoteDecisionEligibility`, `CampaignDecisionEligibility`, `TransferDecisionEligibility`, `RequestCorrelatedConfigurationEffects`, `ProposalConfigurationDecisions`. Each of these has one block, with `\* clause ...` lines after `note:`.

---

## 1. AckPreservation (status of the conjunction: model-internal)

Original:

```tla
AckPreservation == \A a\in history.acks:
    /\ \/ a.before=a.after
       \/ /\ Len(a.after)=Len(a.before)+1 /\ Prefix(a.after,Len(a.before))=a.before
          /\ LET e==a.after[Len(a.after)] IN e.kind="V2" /\ e.changes= <<>>
    /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
    /\ (a.cursor#0 => a.applied=a.cursor)
    /\ a.outAfter=a.outBefore
    /\ a.readsAfter=a.readsBefore
    /\ a.ssAfter=a.ssBefore
```

Parts:

| Part | Clauses | Status | Why |
|---|---|---|---|
| `AckPreservation_LogUnchanged` | log unchanged, or one empty V2 entry appended | impl-abstraction | Describes what Advance does at V02 (it only stabilises entries and may append the auto-leave entry from 46580dcf6). No doc, comment or test says Advance must not change the log. |
| `AckPreservation_SnapshotRetained` | `oldSnap` kept unless it is the batch's snapshot | unknown | Looks like a correctness rule (Advance must not drop a snapshot it never handed out), but the only evidence is the code (`log_unstable.go:111-115`). History (`log -S'stableSnapTo'`, `show 83245f7fe`) shows only the same check being moved. |
| `AckPreservation_AppliedCursor` | `cursor#0 => applied=cursor` | requirement | `node.go:112` (appliedCursor) and `node.go:159` (Advance contract); `TestRawNodeCommitPaginationAfterRestart` (`rawnode_test.go:732`) treats a wrong applied cursor as a lost write. |
| `AckPreservation_OutputPreserved` | `outAfter=outBefore`, `readsAfter=readsBefore`, `ssAfter=ssBefore` | requirement | Commit 5fa684b47 calls dropping messages at Advance a bug; `TestRawNodeConsumeReady` (`rawnode_test.go:954`) asserts that Advance does not drop a later message. Read states and SoftState follow the same accept-at-Ready rule but have no test of their own. |

New definition: `AckPreservation == AckPreservation_LogUnchanged /\ AckPreservation_SnapshotRetained /\ AckPreservation_AppliedCursor /\ AckPreservation_OutputPreserved`.

`UpdateAdvanceOutputPreservation` (Update.tla) is still an alias of the whole `AckPreservation`.

---

## 2. ReadyAccounting (conjunction: model-internal)

Original:

```tla
ReadyAccounting ==
    /\ history.lostReads={}
    /\ \A b\in history.readyChecks:
        /\ b.cursor<=b.commit
        /\ IF b.entries= <<>> THEN b.cursor=b.snapshot ELSE
             /\ Head(b.entries).index=Max(b.from+1,b.first)
             /\ b.cursor=b.entries[Len(b.entries)].index
             /\ \A k\in DOMAIN b.entries:b.entries[k].index=Head(b.entries).index+k-1
```

| Part | Clauses | Status | Why |
|---|---|---|---|
| `ReadyAccounting_NoLostReads` | `history.lostReads={}` | model-internal | A ghost set that no action ever writes, so the clause is vacuous (see concerns). |
| `ReadyAccounting_CommittedPage` | the `\A b` paging clause | requirement | `TestRawNodeCommitPaginationAfterRestart` (`rawnode_test.go:785`, "leaving a gap"), `log.go:149`, `node.go:77`, `node.go:112`. |

New definition: `ReadyAccounting == ReadyAccounting_NoLostReads /\ ReadyAccounting_CommittedPage`.

---

## 3. ReadyOwnership (conjunction: model-internal)

Original:

```tla
ReadyOwnership == \A b\in history.readyChecks:
    /\ b.quotaAfter=b.quotaBefore
    /\ b.outAfter=EmptyBag /\ b.readsAfter= <<>>
```

| Part | Clauses | Status | Why |
|---|---|---|---|
| `ReadyOwnership_QuotaUntouched` | `quotaAfter=quotaBefore` | impl-abstraction | At V02 the quota is released in `advance` (`raft.go:585`). Nothing says Ready must leave it alone, and history (`log -S'reduceUncommittedSize'`) only shows the release point moving. |
| `ReadyOwnership_OutputAccepted` | `outAfter=EmptyBag /\ readsAfter= <<>>` | requirement | `rawnode.go:121` ("*must* be handled"), `TestRawNodeConsumeReady` (`rawnode_test.go:945`), commit 5fa684b47. |

New definition: `ReadyOwnership == ReadyOwnership_QuotaUntouched /\ ReadyOwnership_OutputAccepted`. `UpdateReadyOwnership` is still an alias of the whole.

---

## 4. ReadCorrelation (conjunction: model-internal)

Original:

```tla
ReadCorrelation == \A x\in history.readResults:
    x.rd.id=x.context /\ x.rd.rid=x.id /\ requests[x.id].handoff
```

| Part | Clauses | Status | Why |
|---|---|---|---|
| `ReadCorrelation_Context` | `x.rd.id=x.context` | requirement | `rawnode.go:236` ("same rctx attached"), `read_only.go:21`, `TestReadOnlyOptionSafe` (`raft_test.go:2212`). |
| `ReadCorrelation_Ghost` | `x.rd.rid=x.id /\ requests[x.id].handoff` | model-internal | `rid` and `handoff` exist only in the model (`ReadRecord`, `ProtocolReadIndex`). |

New definition: `ReadCorrelation == ReadCorrelation_Context /\ ReadCorrelation_Ghost`.

---

## 5. LogStructure (conjunction: model-internal)

Original:

```tla
LogStructure == \A n\in Server:
    /\ raft[n].applied<=raft[n].commit
    /\ raft[n].commit<=Last(raft[n])
    /\ \A k\in DOMAIN Hist(raft[n]):Hist(raft[n])[k].index=k
    /\ raft[n].uoff+Len(raft[n].unstable)<=Last(raft[n])+1
```

| Part | Clauses | Status | Why |
|---|---|---|---|
| `LogStructure_CommitBounds` | `applied<=commit`, `commit<=Last` | requirement | `log.go:37` ("Invariant: applied <= committed"), `log.go:32`; `TestCommitTo` (`log_test.go:451`) expects a panic when commit is out of range. |
| `LogStructure_LogShape` | `Hist[k].index=k`, `uoff+Len(unstable)<=Last+1` | model-internal | Well-formedness of the model's ghost log encoding. It mirrors the code's representation comments (`log_unstable.go:19`, `storage.go:82`) but checks only the model. |

New definition: `LogStructure == LogStructure_CommitBounds /\ LogStructure_LogShape`.
