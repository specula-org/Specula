# Requirement-evidence ledger (V02 model, etcd raft 3ea6503e)

One row per annotated definition (56 in-scope properties plus 12 split parts). Evidence types are listed strongest first as they appear in the block.

| # | Property | Module | Status | Evidence types | Split from | Intent |
|---|---|---|---|---|---|---|
| 1 | VoteDecisionEligibility | base.tla | requirement | comment, history, test, doc, impl | - | Every vote or pre-vote request a node handles is answered exactly as the voting rules prescribe (lease suppression, stale-term handling, term adoption, one vote per term, log freshness, pre-vote for a future term), learners included. |
| 2 | CampaignDecisionEligibility | base.tla | requirement | history, test, doc, impl | - | Every Hup or election tick produces exactly the prescribed campaign: only a due, promotable voter with no pending unapplied configuration change campaigns; pre-vote keeps the term and a real campaign increments it; requests go to every other voter with the candidate's last index and term. |
| 3 | TransferDecisionEligibility | base.tla | requirement | comment, test, history, impl | - | Every leader-transfer request is handled as prescribed: unknown, learner, or already-pending targets are ignored; a self target aborts any transfer; another voter becomes the transferee with the election timer reset; MsgTimeoutNow is sent at once only if the target is caught up. |
| 4 | RequestCorrelatedConfigurationEffects | base.tla | requirement | doc, comment, test, impl | - | Applying a committed configuration entry changes the node's configuration exactly as that change prescribes (or not at all if it is invalid or cancelled), and every applied configuration entry is committed and comes from bootstrap, auto-leave, or a handed-off request with the same content. |
| 5 | ProposalConfigurationDecisions | base.tla | requirement | doc, comment, test, impl | - | For every proposal reaching a node, the decision follows the drop/accept/forward rules, and an accepted proposal extends the log by exactly the proposed entries, with configuration entries replaced by empty normal entries while another configuration change is pending or earlier in the batch; otherwise the log is unchanged. |
| 6 | ElectionSafety | base.tla | requirement | protocol, test, comment, impl | - | In any term, at most one node ever wins an election and becomes leader. |
| 7 | LogMatching | base.tla | requirement | protocol, test, comment, impl | - | If two nodes' logs hold an entry with the same index and the same nonzero term, the logs are identical up to that index. |
| 8 | LeaderCompleteness | base.tla | requirement | protocol, test, comment, impl | - | Every leader elected in a term later than a recorded commitment's term has that committed history as a prefix of its log. |
| 9 | CommittedHistory | base.tla | requirement | protocol, comment, test, impl | - | Committed history never diverges: a live node never loses its own committed prefix, all recorded commitments are pairwise compatible, and every live node's committed prefix is compatible with them. |
| 10 | AppliedAgreement | base.tla | requirement | protocol, test, comment, doc | - | Any two application histories ever applied, on any nodes, are prefix-compatible. |
| 11 | VoteRecovery | base.tla | requirement | comment, doc, impl | - | After a restart a node's term is at least its durably saved term, and while still in that term it keeps the durably saved vote. |
| 12 | RecoveryBacking | base.tla | requirement | doc, comment, test, impl | - | On restart the loaded commit index refers only to locally persisted, non-missing entries, and the recovered application state is a prefix of the persisted log. |
| 13 | PromiseBacking | base.tla | requirement | doc, comment, impl | - | Every message or write result a node publishes is backed by durable state: its term and granted vote are persisted, and acknowledged entries and advertised commit prefixes are on disk. |
| 14 | ConfigurationOrigin | base.tla | requirement | doc, proto, comment, impl | - | A live node's active configuration is exactly the result of the configuration entries in a history that is a prefix of its log and lies within its committed prefix. |
| 15 | ConfigurationTransitionSafety | base.tla | requirement | doc, comment, test, impl | - | Whenever a leader newly commits a request-originated configuration entry, it counts that commit under the configuration produced by all entries before it. |
| 16 | LearnerEligibility | base.tla | requirement | test, history, comment, impl | - | A node that is a learner in its own configuration never starts a (pre-)campaign. |
| 17 | QuorumAccounting | base.tla | requirement | comment, proto, test, impl | - | Every election win and every commit decision is backed by a majority of each half of a non-empty (joint) voter configuration, counting only voters. |
| 18 | ReplicationEvidence | base.tla | requirement | doc, comment, impl | - | For every peer whose Match a live leader records as positive, that peer acknowledged a log whose prefix up to Match equals the leader's own log prefix. |
| 19 | SnapshotBacking | base.tla | requirement | comment, impl | - | Every snapshot created, held as unstable, or persisted describes exactly the history up to its index: its last term and configuration agree with that history. |
| 20 | AckPreservation_LogUnchanged | base.tla | impl-abstraction | comment, impl | AckPreservation | Advance leaves the log history unchanged, except that it may append exactly one empty ConfChangeV2 (auto-leave) entry. |
| 21 | AckPreservation_SnapshotRetained | base.tla | unknown | impl | AckPreservation | Advance does not discard a pending unstable snapshot other than the one handed out in the acknowledged Ready. |
| 22 | AckPreservation_AppliedCursor | base.tla | requirement | comment, test, impl | AckPreservation | When the acknowledged Ready carried committed entries or a snapshot, Advance sets the applied index to exactly that Ready's cursor. |
| 23 | AckPreservation_OutputPreserved | base.tla | requirement | history, test, comment, impl | AckPreservation | Advance never drops or alters outgoing messages, read states, or the accepted SoftState that were produced after the Ready was accepted. |
| 24 | AckPreservation | base.tla | model-internal | - | - | conjunction of the parts below; kept so existing configs and references still work (conjunction of AckPreservation_LogUnchanged, AckPreservation_SnapshotRetained, AckPreservation_AppliedCursor, AckPreservation_OutputPreserved) |
| 25 | ReadyAccounting_NoLostReads | base.tla | model-internal | - | ReadyAccounting | The ghost set of lost read states stays empty. |
| 26 | ReadyAccounting_CommittedPage | base.tla | requirement | test, comment, impl | ReadyAccounting | Each Ready's committed-entry page starts right after the applied index (or at the first available index), is contiguous, ends at the Ready's cursor and never passes the commit index; a Ready without entries uses the snapshot index as cursor. |
| 27 | ReadyAccounting | base.tla | model-internal | - | - | conjunction of the parts below; kept so existing configs and references still work (conjunction of ReadyAccounting_NoLostReads, ReadyAccounting_CommittedPage) |
| 28 | ReadyOwnership_QuotaUntouched | base.tla | impl-abstraction | comment, impl | ReadyOwnership | Producing and accepting a Ready never changes the leader's uncommitted-size quota. |
| 29 | ReadyOwnership_OutputAccepted | base.tla | requirement | comment, test, history, impl | ReadyOwnership | Once a Ready is accepted (returned by RawNode.Ready or delivered by Node), its messages and read states are removed from the node's pending output. |
| 30 | ReadyOwnership | base.tla | model-internal | - | - | conjunction of the parts below; kept so existing configs and references still work (conjunction of ReadyOwnership_QuotaUntouched, ReadyOwnership_OutputAccepted) |
| 31 | AutoLeaveAdvance | base.tla | requirement | proto, comment, test, impl | - | Whenever Advance runs on a leader in an auto-leave joint configuration whose pending change has been applied, it appends the empty leave-joint entry or, if the quota drops it, sets the pending index to its last index to retry. |
| 32 | JointConfigurationShape | base.tla | requirement | comment, proto, test, impl | - | Every node's configuration is empty or well formed: non-empty incoming voters, learners disjoint from both voter halves, staged learners only among outgoing voters and disjoint from incoming voters and learners, and no staged learners or auto-leave outside a joint state. |
| 33 | JointSnapshotRecovery | base.tla | requirement | history, test, comment, impl | - | A joint configuration (outgoing voters, staged learners, auto-leave) survives intact both when a node restarts from a persisted ConfState and in the live configuration derived from its configuration history. |
| 34 | JointSnapshotMemberAcceptance | base.tla | requirement | comment, proto, history, impl | - | A follower that belongs to a fresh snapshot's (joint) configuration, including as an outgoing-only voter, and does not already match it, must install it, taking its index as commit and its configuration. |
| 35 | QuotaIntegrity | base.tla | requirement | comment, history, test, impl | - | The leader's uncommitted-size quota is non-negative and never exceeds the payload size of its unapplied log tail, and every peer's in-flight window holds at most MaxInflight strictly increasing indexes. |
| 36 | OutcomeSoundness | base.tla | requirement | comment, test, doc, impl | - | Every proposal handed to the core gets the decision prescribed by the node state: a removed leader, a pending transfer, a quota overflow, no leader, or disabled forwarding drop it; otherwise a leader accepts it and a follower forwards it. |
| 37 | ReadBasis | base.tla | requirement | doc, comment, test, impl | - | Every completed read was served at an index confirmed by a joint quorum of the serving leader's configuration in its own term, after that leader committed an entry of its term (or as a singleton), and reflects every write completed before the read was invoked. |
| 38 | ReadApplication | base.tla | requirement | comment, test | - | A read completes only after the reader's applied history covers the read state's committed prefix and reaches its read index. |
| 39 | ReadCorrelation_Context | base.tla | requirement | comment, test, impl | ReadCorrelation | A completed read uses a read state whose request context equals the context of the request it completes. |
| 40 | ReadCorrelation_Ghost | base.tla | model-internal | - | ReadCorrelation | The ghost request id carried by the read state is the completed request's id, and that request was actually handed to the core. |
| 41 | ReadCorrelation | base.tla | model-internal | - | - | conjunction of the parts below; kept so existing configs and references still work (conjunction of ReadCorrelation_Context, ReadCorrelation_Ghost) |
| 42 | NoUnexpectedFatal | base.tla | requirement | comment, impl | - | No node ever reaches a state that the implementation treats as fatal (a panic path). |
| 43 | TypeOK | base.tla | model-internal | - | - | Model variables have the expected domains and value shapes. |
| 44 | LogStructure_CommitBounds | base.tla | requirement | comment, test, impl | LogStructure | On every node the applied index never exceeds the commit index, which never exceeds the last log index. |
| 45 | LogStructure_LogShape | base.tla | model-internal | - | LogStructure | Each entry of a node's ghost history sits at the position named by its index, and the unstable suffix ends within the log. |
| 46 | LogStructure | base.tla | model-internal | - | - | conjunction of the parts below; kept so existing configs and references still work (conjunction of LogStructure_CommitBounds, LogStructure_LogShape) |
| 47 | MCTypeOK | MC.tla | model-internal | - | - | TypeOK holds and every fault-budget counter is a natural number within its configured limit. |
| 48 | ElectionProgress | MC.tla | requirement | test, doc, impl | - | Under stable services, an eventually common configuration, a fair caller and network, and some promotable node that gets quiet campaign windows and campaigns strongly fairly, a leader eventually exists. |
| 49 | CatchupProgress | MC.tla | requirement | test, comment, doc, impl | - | With a stable leader n, a stable member p, stable services and fair execution, every index committed at n is eventually applied by p. |
| 50 | ManagementProgress | MC.tla | requirement | doc, comment, impl | - | Under stable services and a fair caller, every configuration entry committed at a node is eventually applied by that node's application. |
| 51 | TransferSettlement | MC.tla | requirement | comment, test, impl | - | A leader with a pending leadership transfer whose ticks are fair, and whose transferee is not repeatedly replaced, eventually clears the transfer or stops being leader. |
| 52 | ReadProgress | MC.tla | model-internal | - | - | Under stable services, a fair caller and a strongly fair CompleteRead, a read whose completion becomes enabled is eventually completed. |
| 53 | TraceMatched | Trace.tla | model-internal | - | - | Trace replay eventually consumes every line of the recorded trace. |
| 54 | UpdateLearnerVoteContract | Update.tla | alias | - | - | alias of VoteDecisionEligibility |
| 55 | UpdateLearnerCampaignEligibility | Update.tla | alias | - | - | alias of LearnerEligibility |
| 56 | UpdateReadyOwnership | Update.tla | alias | - | - | alias of ReadyOwnership |
| 57 | UpdateAdvanceOutputPreservation | Update.tla | alias | - | - | alias of AckPreservation |
| 58 | UpdateJointConfigurationShape | Update.tla | alias | - | - | alias of JointConfigurationShape |
| 59 | UpdateJointSnapshotRecovery | Update.tla | alias | - | - | alias of JointSnapshotRecovery |
| 60 | UpdateJointSnapshotMemberAcceptance | Update.tla | alias | - | - | alias of JointSnapshotMemberAcceptance |
| 61 | UpdateAutoLeaveAdvance | Update.tla | alias | - | - | alias of AutoLeaveAdvance |
| 62 | UpdateQuorumAccounting | Update.tla | alias | - | - | alias of QuorumAccounting |
| 63 | LearnerGrantNotReached | Update.tla | model-internal | - | - | Reachability canary (expected to be violated): no learner ever grants a vote; a violation shows the learner-vote path ran. |
| 64 | PostReadyOutputNotReached | Update.tla | model-internal | - | - | Reachability canary (expected to be violated): no Advance ever sees messages or read states produced after Ready acceptance. |
| 65 | OutgoingSnapshotRestoreNotReached | Update.tla | model-internal | - | - | Reachability canary (expected to be violated): no fresh, nonmatching snapshot ever reaches a follower that is only an outgoing joint voter. |
| 66 | JointRecoveryNotReached | Update.tla | model-internal | - | - | Reachability canary (expected to be violated): no restart ever restores a joint configuration correctly. |
| 67 | JointNotReached | Update.tla | model-internal | - | - | Reachability canary (expected to be violated): no node ever holds a joint configuration. |
| 68 | AutoLeaveNotAppended | Update.tla | model-internal | - | - | Reachability canary (expected to be violated): no log ever contains an auto-leave (empty, id 0) ConfChangeV2 entry. |

## Counts by status

| Status | Count |
|---|---|
| requirement | 38 |
| impl-abstraction | 2 |
| unknown | 1 |
| model-internal | 18 |
| alias | 9 |
| **total blocks** | 68 |

Counting only the 56 original in-scope properties (split conjunctions counted as model-internal, aliases separately): requirement 32, impl-abstraction 0, unknown 0, model-internal 15, alias 9.

Counting the 12 split parts alone: requirement 6, impl-abstraction 2, unknown 1, model-internal 3.

Aliases (Update.tla) carry a one-line pointer block; their evidence is in the target's block. Reachability canaries and split conjunctions are model-internal.
