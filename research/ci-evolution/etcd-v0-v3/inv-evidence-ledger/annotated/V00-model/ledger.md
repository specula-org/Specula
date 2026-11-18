# Requirement-evidence ledger — etcd raft V00 (d58d5d159ae1a1f644a10003f2d8b3b807cd0b3a)

Scope: every operator named after `INVARIANT(S)` / `PROPERTY(IES)` in any `spec-original/*.cfg` (including commented-out lines), 36 distinct names. `Update.tla` does not exist. 29 of the 36 names are defined in `spec-original/base.tla`. The other 7 are not defined anywhere in the workspace (see the second table), so they could not be annotated. No property is an alias (`A == B`), and none is a reachability canary.

After splitting two properties (AckPreservation into 3 parts, LogStructure into 2 parts), `spec-annotated/base.tla` holds **34 REQ-EVIDENCE blocks**.

## Annotated properties

| # | Property | Status | Evidence types | Split from | Intent |
|---|---|---|---|---|---|
| 1 | `VoteDecisionEligibility` | requirement | comment, test, impl | — | every observed MsgVote/MsgPreVote step answers exactly as the vote rules prescribe (lease suppression, stale-term handling, learner silence, term reset, single-vote and up-to-date grant, response term). |
| 2 | `CampaignDecisionEligibility` | requirement | history, test, comment, doc, impl | — | every observed Hup or tick starts a (pre-)campaign exactly when the node is a due, non-leader voter with no unapplied committed configuration change, sending one vote request per other voter for term+1 with its last index and term. |
| 3 | `TransferDecisionEligibility` | requirement | comment, test, impl | — | every observed MsgTransferLeader at a leader ignores unknown, learner and already-pending targets, aborts on self, otherwise records the target with a reset election timer, and sends MsgTimeoutNow exactly when the target is caught up. |
| 4 | `RequestCorrelatedConfigurationEffects` | requirement | doc, comment, test, impl | — | applying a committed configuration entry changes the voter/learner sets exactly as its kind says (no change when cancelled via NodeID zero, AddLearner of a voter ignored), and every applied non-bootstrap change comes from a handed-off request with the same kind and target. |
| 5 | `ProposalConfigurationDecisions` | impl-abstraction | comment, doc, test, impl | — | every observed proposal step reaches the decision predicted from the pre-state and, when accepted, appends exactly the proposed entries, with configuration changes turned into no-ops while another change is pending or earlier in the same batch. |
| 6 | `ElectionSafety` | requirement | protocol, test, impl | — | at most one node ever wins an election in any given term. |
| 7 | `LogMatching` | requirement | protocol, test, impl | — | if two nodes' logs hold an entry with the same index and the same nonzero term, the logs are identical up to that index. |
| 8 | `LeaderCompleteness` | requirement | protocol, test, comment, impl | — | every leader elected in a term later than a commitment's term holds that committed prefix in its log when elected. |
| 9 | `CommittedHistory` | requirement | protocol, comment, test, impl | — | a live node never loses entries it has committed, and all observed commitments and every live node's committed prefix lie on one common history. |
| 10 | `AppliedAgreement` | requirement | protocol, doc, test, impl | — | any two state-machine histories ever applied, at any nodes, are prefix-compatible. |
| 11 | `VoteRecovery` | requirement | comment, doc, test, impl | — | after a restart a node's term is never below its persisted term, and in the persisted term it keeps its persisted vote. |
| 12 | `RecoveryBacking` | requirement | doc, comment, impl | — | on restart the recovered commit index is backed by durable log entries without gaps, and the recovered application state is a prefix of the durable log. |
| 13 | `PromiseBacking` | requirement | doc, comment, impl | — | every message or write acknowledgement released to the outside is backed by durable state (term, granted vote, acknowledged log prefix, announced commit prefix). |
| 14 | `ConfigurationOrigin` | requirement | doc, comment, impl | — | every live node's configuration is exactly the result of the configuration entries in a committed prefix of its own log (bootstrap, applied entries or restored snapshot). |
| 15 | `ConfigurationTransitionSafety` | requirement | doc, comment, test, impl | — | every non-bootstrap configuration entry is committed under exactly the voter set produced by all entries before it (one change at a time, committed under the old membership). |
| 16 | `LearnerEligibility` | requirement | comment, test, impl | — | a node never grants a (pre-)vote and never starts a campaign while it is a learner. |
| 17 | `QuorumAccounting` | requirement | protocol, test, impl | — | every election win and every commit decision is backed by a majority of a nonempty voter set. |
| 18 | `ReplicationEvidence` | requirement | doc, comment, protocol, impl | — | whenever a leader records Match m>0 for a peer, that peer actually acknowledged a log whose first m entries are still a prefix of the leader's log. |
| 19 | `SnapshotBacking` | requirement | comment, test, impl | — | every snapshot created by the caller, held as unstable snapshot, or persisted carries index, term and ConfState consistent with the log prefix it captures. |
| 20 | `AckPreservation_LogUnchanged` | requirement | history, comment, test, doc, impl | AckPreservation | acknowledging a Ready with Advance never changes the node's logical log. |
| 21 | `AckPreservation_SnapshotRetained` | unknown | impl, history | AckPreservation | Advance never discards an unstable snapshot other than the one carried by the acknowledged Ready. |
| 22 | `AckPreservation_AppliedCursor` | requirement | comment, test, impl | AckPreservation | after Advance a node's applied index equals the applied cursor of the acknowledged Ready (last committed entry, else snapshot index). |
| 23 | `AckPreservation` | model-internal | — | (conjunction of parts) | conjunction of the parts below; kept so existing configs and references still work |
| 24 | `ReadyAccounting` | requirement | comment, test, impl | — | no ReadState produced for the application is dropped before delivery, and every Ready's committed-entry page starts right after max(applied, snapshot), is contiguous, ends at the cursor and never passes the commit index. |
| 25 | `QuotaIntegrity` | requirement | comment, doc, test, impl | — | the uncommitted-size quota is nonnegative and, at a leader, never exceeds the payload of its unapplied log tail, and every progress holds at most MaxInflight in-flight append indexes in strictly increasing order. |
| 26 | `OutcomeSoundness` | impl-abstraction | comment, doc, test, impl | — | every proposal handed to raft gets exactly the drop/accept/forward decision predicted from role, membership, known leader, forwarding flag, pending transfer and uncommitted quota. |
| 27 | `ReadBasis` | requirement | comment, history, test, doc, impl | — | every completed read used a read index confirmed in the leader's own term by a quorum of a legitimate voter configuration containing the leader, after the leader committed an entry of its term (unless singleton), and its state at that index includes every write completed before the read was invoked. |
| 28 | `ReadApplication` | requirement | comment | — | a read completes only once the reader's applied state contains the read's log prefix and has reached the read index. |
| 29 | `ReadCorrelation` | requirement | comment, test, impl | — | a completed read uses a ReadState that carries the request's own context and was produced for that very request, and the request was actually handed to raft. |
| 30 | `NoUnexpectedFatal` | unknown | comment, impl | — | no node ever reaches one of the modelled panic/fatal paths. |
| 31 | `TypeOK` | model-internal | comment, impl | — | all state variables have their expected shapes and value ranges. |
| 32 | `LogStructure_CommitBounds` | requirement | comment, test, history, impl | LogStructure | on every node the applied index never exceeds the commit index, which never exceeds the last log index. |
| 33 | `LogStructure_Indexing` | model-internal | comment | LogStructure | every log entry sits at the position equal to its index, and the unstable segment ends within the log. |
| 34 | `LogStructure` | model-internal | — | (conjunction of parts) | conjunction of the parts below; kept so existing configs and references still work |

### Counts by status (34 blocks)

| status | count |
|---|---|
| requirement | 26 |
| impl-abstraction | 2 (`ProposalConfigurationDecisions`, `OutcomeSoundness`) |
| unknown | 2 (`AckPreservation_SnapshotRetained`, `NoUnexpectedFatal`) |
| model-internal | 4 (`TypeOK`, `LogStructure_Indexing`, and the two split conjunctions `AckPreservation`, `LogStructure`) |

If you count only the 29 original definitions and record each split property under its parts, the totals are the same. The two conjunction blocks are `model-internal` as the task template requires.

Properties with mixed origins that cannot be split because they are one `LET`/`\A` body with shared local definitions. Each has per-clause `\* clause` lines in its block: `VoteDecisionEligibility`, `CampaignDecisionEligibility`, `TransferDecisionEligibility`, `RequestCorrelatedConfigurationEffects`, `ProposalConfigurationDecisions`, `OutcomeSoundness`, `ReadBasis`, `NoUnexpectedFatal`, `TypeOK`.

## In-scope names with no definition in the workspace (not annotated)

| Property | Referenced by | Status | Reason |
|---|---|---|---|
| `MCTypeOK` | MC.cfg, MC_hunt_*.cfg (`INVARIANTS`) | not annotated | defined in no workspace file; `MC.tla` is absent (the cfgs also need `MCSpec`, `StateConstraint`, `Symmetry`) |
| `TraceMatched` | Trace.cfg (`PROPERTIES`) | not annotated | `Trace.tla` is absent (also `TraceSpec` and the `Trace*` constants) |
| `ElectionProgress` | MC*.cfg (`\* PROPERTY`, commented out) | not annotated | not defined in base.tla; presumably in the absent MC.tla |
| `CatchupProgress` | MC*.cfg (`\* PROPERTY`) | not annotated | same |
| `ManagementProgress` | MC*.cfg (`\* PROPERTY`) | not annotated | same |
| `TransferSettlement` | MC*.cfg (`\* PROPERTY`) | not annotated | same |
| `ReadProgress` | MC*.cfg (`\* PROPERTY`) | not annotated | same |

These are also listed in `out/concerns.md`.
