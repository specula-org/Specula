# Review decisions, one row per REQ-EVIDENCE block

All 68 blocks were reviewed. On every non-`impl` evidence line I kept, I added the required `-> <part supported>` suffix. The annotator had added it to none of them. Adding a suffix alone does not count as a change; such a block is marked `ok`.

Abbreviations: req = requirement, impl-abs = impl-abstraction, mi = model-internal, unk = unknown.

| # | Property (module) | Old status | New status | Intent changed | Evidence retyped / removed / added | Reason (one line) |
|---|---|---|---|---|---|---|
| 1 | VoteDecisionEligibility (base) | req | req | yes | retyped raft.go:925 comment→impl; removed test raft_paper_test.go:77; added test raft_paper_test.go:234, comment log.go:275, doc doc.go:248 | "answered exactly" covered the response multiset, which is impl-abstraction. The stale-term test steps an MsgApp, not a vote. doc.go:247 contradicts the expected silence on a stale MsgVote. |
| 2 | CampaignDecisionEligibility (base) | req | req | no | corrected history location (cd227fb83^:node.go:141, a removed line, not the commit message); added doc doc.go:209 | The quote is a deleted comment line. The added line backs the existing "due" clause. |
| 3 | TransferDecisionEligibility (base) | req | req | yes | added tests raft_test.go:3604 TestLeaderTransferBack and :3624 TestLeaderTransferSecondTransferToAnotherNode | "MsgTimeoutNow at once iff caught up" is impl only; the cited tests assert eventual transfer. A clause line cited the unrelated raft.go:1083. |
| 4 | RequestCorrelatedConfigurationEffects (base) | req | req | yes | none | The intent included the model-internal origin clause and an "invalid ⇒ no-op" case that has no non-impl evidence (the library panics). Both moved to clause lines. |
| 5 | ProposalConfigurationDecisions (base) | req | req | yes | none | Narrowed to the content and drop rules. Precedence and the removed-leader drop are impl only or unknown (clause line). |
| 6 | ElectionSafety (base) | req | req | no | retyped raft.go:925 comment→impl | The comment narrates the canVote expression. |
| 7 | LogMatching (base) | req | req | no | — | ok |
| 8 | LeaderCompleteness (base) | req | req | no | — | ok |
| 9 | CommittedHistory (base) | req | req | no | removed test node_test.go:968 | The test asserts commit non-regression across a restart; liveOK is checked within one live incarnation. |
| 10 | AppliedAgreement (base) | req | req | no | — | ok |
| 11 | VoteRecovery (base) | req | req | no | — | ok |
| 12 | RecoveryBacking (base) | req | req | yes | removed comment raft.go:147 and test node_test.go:968 | Covers(diskHist,app) relates the caller model's recovered application to the disk log (model-internal). The two removed lines support no clause. |
| 13 | PromiseBacking (base) | req | req | yes | none | No non-impl source says a completed application write is on the local disk (README.md:114 allows parallel steps). The WriteResult clause is now unknown. |
| 14 | ConfigurationOrigin (base) | req | req | no | — | ok |
| 15 | ConfigurationTransitionSafety (base) | req | req | no | — | ok |
| 16 | LearnerEligibility (base) | req | req | no | — | ok |
| 17 | QuorumAccounting (base) | req | req | no | added history 60429a913, test confchange/testdata/simple_safety.txt:4 | The non-empty-voters clause had only impl evidence. The history search found the rule ("prevent the use of empty commit quorums"). |
| 18 | ReplicationEvidence (base) | req | req | no | — | ok |
| 19 | SnapshotBacking (base) | req | req | no | none | The ghost condition s.index=Len(s.hist) was covered by the single status without a clause line; it is now a model-internal clause. |
| 20 | AckPreservation_LogUnchanged (base) | impl-abs | impl-abs | no | retyped raft.go:565 comment→impl | Narrating comment ("initiate that now"). |
| 21 | AckPreservation_SnapshotRetained (base) | unk | unk | no | — | ok (my own hist search found nothing more) |
| 22 | AckPreservation_AppliedCursor (base) | req | req | no | — | ok |
| 23 | AckPreservation_OutputPreserved (base) | req | req | yes | none | The commit message and the test say only "Advance does not drop later messages". Equality on messages and SoftState is impl-abstraction; read states are unknown. |
| 24 | AckPreservation (base, split conjunction) | mi | mi | no | — | Note updated to mention the clause lines in part 23. |
| 25 | ReadyAccounting_NoLostReads (base) | mi | mi | no | — | ok |
| 26 | ReadyAccounting_CommittedPage (base) | req | req | no | — | ok |
| 27 | ReadyAccounting (base, split conjunction) | mi | mi | no | — | ok |
| 28 | ReadyOwnership_QuotaUntouched (base) | impl-abs | impl-abs | no | retyped raft.go:289 comment→impl | The field comment says nothing about Ready leaving the quota alone. |
| 29 | ReadyOwnership_OutputAccepted (base) | req | req | no | — | ok |
| 30 | ReadyOwnership (base, split conjunction) | mi | mi | no | — | ok |
| 31 | AutoLeaveAdvance (base) | req | req | yes | retyped raft.go:565 and raft.go:575 comment→impl | Both comments narrate (575 is the task's own example). The per-Advance timing and the quota-retry branch are impl-abstraction clauses. |
| 32 | JointConfigurationShape (base) | req | req | no | added history 60429a913, proto raft.proto:112 | Non-empty voters and "no auto-leave outside joint" lacked non-impl support. The note called the first impl-only. |
| 33 | JointSnapshotRecovery (base) | req | req | no | added proto raft.proto:148 | No line supported the live-configuration clause. |
| 34 | JointSnapshotMemberAcceptance (base) | req | req | yes | none | "Taking its index as commit" is impl only (clause line). The rest rests on a two-step reading of raft.go:1398 and raft.proto:105. |
| 35 | QuotaIntegrity (base) | req | req | yes | none | The sources ask for a "monotonic sequence" / "in order", not strict increase. Strictness is an impl-abstraction clause. |
| 36 | OutcomeSoundness (base) | req | req | yes | retyped raft.go:1018 comment→impl | Narrating comment. The removed-leader drop becomes unknown; the no-leader drop, precedence and default acceptance are impl-abstraction clauses. |
| 37 | ReadBasis (base) | req | req | no | retyped raft.go:1051 comment→impl | Narrating comment (TestReadOnlyForNewLeader carries that clause). The leader-membership and ghost config-matching conjuncts are recorded as clauses. |
| 38 | ReadApplication (base) | req | req | no | — | ok |
| 39 | ReadCorrelation_Context (base) | req | req | no | — | ok |
| 40 | ReadCorrelation_Ghost (base) | mi | mi | no | — | ok |
| 41 | ReadCorrelation (base, split conjunction) | mi | mi | no | — | ok |
| 42 | NoUnexpectedFatal (base) | req | unk | no | retyped raft.go:704 TODO→impl; removed raft.go:1388 | raft.go:1441 covers a restore panic that is not a modeled Fatal reason. 1388 is not a panic. No source states that the modeled panics are unreachable. |
| 43 | TypeOK (base) | mi | mi | no | — | ok |
| 44 | LogStructure_CommitBounds (base) | req | req | no | — | ok |
| 45 | LogStructure_LogShape (base) | mi | mi | no | — | ok |
| 46 | LogStructure (base, split conjunction) | mi | mi | no | — | ok |
| 47 | MCTypeOK (MC) | mi | mi | no | — | ok |
| 48 | ElectionProgress (MC) | req | req | no | — | ok |
| 49 | CatchupProgress (MC) | req | req | no | — | ok |
| 50 | ManagementProgress (MC) | req | req | no | — | ok |
| 51 | TransferSettlement (MC) | req | req | no | retyped raft.go:678 comment→impl; added comment raft.go:1227 | Narrating comment. The two tests still support the intent. |
| 52 | ReadProgress (MC) | mi | mi | no | — | ok |
| 53 | TraceMatched (Trace) | mi | mi | no | — | ok |
| 54 | UpdateLearnerVoteContract (Update, alias) | alias | alias | no | — | ok |
| 55 | UpdateLearnerCampaignEligibility (Update, alias) | alias | alias | no | — | ok |
| 56 | UpdateReadyOwnership (Update, alias) | alias | alias | no | — | ok |
| 57 | UpdateAdvanceOutputPreservation (Update, alias) | alias | alias | no | — | ok |
| 58 | UpdateJointConfigurationShape (Update, alias) | alias | alias | no | — | ok |
| 59 | UpdateJointSnapshotRecovery (Update, alias) | alias | alias | no | — | ok |
| 60 | UpdateJointSnapshotMemberAcceptance (Update, alias) | alias | alias | no | — | ok |
| 61 | UpdateAutoLeaveAdvance (Update, alias) | alias | alias | no | — | ok |
| 62 | UpdateQuorumAccounting (Update, alias) | alias | alias | no | — | ok |
| 63 | LearnerGrantNotReached (Update, canary) | mi | mi | no | — | ok |
| 64 | PostReadyOutputNotReached (Update, canary) | mi | mi | no | — | ok |
| 65 | OutgoingSnapshotRestoreNotReached (Update, canary) | mi | mi | no | — | ok |
| 66 | JointRecoveryNotReached (Update, canary) | mi | mi | no | — | ok |
| 67 | JointNotReached (Update, canary) | mi | mi | no | — | ok |
| 68 | AutoLeaveNotAppended (Update, canary) | mi | mi | no | — | ok |

Classification rule applied the same way to every block. A code comment is `comment` when it states a rule, invariant, contract or reason: "must", "never", "should … so", "Invariant:", a definitional doc comment, or a quoted thesis rule. It is `impl` when it narrates the next statement(s) inside a function body: "initiate that now", "bump the pending conf index", "drop any new proposals", "Reject read only request …", "it becomes leader again", "We can vote if …", or a TODO.
