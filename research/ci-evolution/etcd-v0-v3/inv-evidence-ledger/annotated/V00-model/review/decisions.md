# Review decisions (one row per REQ-EVIDENCE block)

All 34 blocks are in `spec-reviewed/base.tla`. On every block, each non-`impl` evidence line that was kept now ends with the required `-> <part supported>` suffix. None of the annotated blocks had these suffixes. Adding them alone does not count as a change ("ok").

Abbreviations: req = requirement, impl-abs = impl-abstraction, mi = model-internal.

| # | Property | Old status | New status | Intent changed | Evidence retyped / removed / added | Reason |
|---|---|---|---|---|---|---|
| 1 | VoteDecisionEligibility | req | req | yes | retyped `raft.go:892` comment→impl | The comment narrates the canVote expression. The intent claimed every rule, but stale-term handling, the PreVote future-term grant and the rejection term are code-only, so the intent is narrowed and those parts are recorded as clauses. |
| 2 | CampaignDecisionEligibility | req | req | yes | retyped `raft.go:683`, `raft.go:751` comment→impl | Both comments narrate becomePreCandidate and the single-node branch. The tick arithmetic is impl-only and now sits outside the intent. The pre-vote and singleton clauses are re-sourced to doc.go:255-263. |
| 3 | TransferDecisionEligibility | req | req | yes | none | The intent included the learner-target exclusion, but its own clause marks that part impl-abstraction. It is now only in the clause. |
| 4 | RequestCorrelatedConfigurationEffects | req | req | yes | retyped `raft.go:1412` comment→impl | "Can only change Learner to Voter." is followed by "TODO(tbg): why?", so it states no rule. The AddLearner-of-a-voter no-op is now only in an impl-abstraction clause. |
| 5 | ProposalConfigurationDecisions | impl-abs | req | yes | retyped `raft.go:969` comment→impl; added history `db2dbe524`; re-quoted `README.md:170` | Following the granularity rule, the intent is narrowed to the documented clauses (drop cases, conf→no-op, content kept). Precedence and mandatory acceptance stay impl-abstraction clauses. The old README:170 quote ("no guarantee…") supported no part of the intent. |
| 6 | ElectionSafety | req | req | no | none | ok |
| 7 | LogMatching | req | req | no | none | ok |
| 8 | LeaderCompleteness | req | req | no | none | ok |
| 9 | CommittedHistory | req | req | no | none | ok |
| 10 | AppliedAgreement | req | req | no | none | ok |
| 11 | VoteRecovery | req | req | no | none | ok |
| 12 | RecoveryBacking | req | req | no | none | ok |
| 13 | PromiseBacking | req | req | no | added comment `node.go:77` | No cited non-impl line covered the write-acknowledgement part of the intent. node.go:77 says committed entries are already in stable storage. |
| 14 | ConfigurationOrigin | req | req | no | none | ok |
| 15 | ConfigurationTransitionSafety | req | req | no | none | ok |
| 16 | LearnerEligibility | req | req | no | none | ok |
| 17 | QuorumAccounting | req | req | yes | none | No evidence supports a nonempty voter set, and quorum/majority.go:172 states the opposite convention. That part is now an `unknown` clause. The subset check is a model-internal clause. |
| 18 | ReplicationEvidence | req | req | no | none | ok |
| 19 | SnapshotBacking | req | req | no | none | ok |
| 20 | AckPreservation_LogUnchanged | req | req | yes | retyped `log_unstable.go:83` comment→impl; removed `README.md:124` | "Never changes the log" claims more than ee0757a9b supports (do not mark truncated entries stable). The intent is narrowed and full equality is now an impl-abstraction clause. README:124 says nothing about Advance. |
| 21 | AckPreservation_SnapshotRetained | unknown | unknown | no | removed history `516891c49` | The commit message only narrates the code change ("set snapshot to nil when it is saved"). A history re-search found no rationale. |
| 22 | AckPreservation_AppliedCursor | req | req | no | retyped `rawnode.go:52` comment→impl | The comment narrates the next lines. node.go:112 and node.go:149 and the test still support the intent. |
| 23 | AckPreservation | mi | mi | no | none | ok (conjunction alias) |
| 24 | ReadyAccounting | req | req | no | none | ok |
| 25 | QuotaIntegrity | req | req | yes | none | The formula checks strictly increasing indexes, but the comments say only "monotonic" / "in order". The intent now says "increasing", and strictness is an impl-abstraction clause. |
| 26 | OutcomeSoundness | impl-abs | req | yes | retyped `raft.go:969` comment→impl; added history `db2dbe524`; removed `README.md:170` | The intent is narrowed to the documented drop cases plus forwarding (TestDisableProposalForwarding asserts both directions). Precedence and Accepted-otherwise stay impl-abstraction clauses. README:170 supports no part of the intent. |
| 27 | ReadBasis | req | req | yes | retyped `raft.go:1000` comment→impl; re-quoted history `f9382a4d7` to its commit message | The comment narrates the check. The singleton exemption is now explicit in the intent. "Leader in voters" and "nonempty set" have no evidence and are now an `unknown` clause. |
| 28 | ReadApplication | req | req | no | removed `read_only.go:20` | That comment says to call ReadIndex first. It says nothing about when a read may complete. |
| 29 | ReadCorrelation | req | req | no | none | ok |
| 30 | NoUnexpectedFatal | unknown | req | yes | removed `storage.go:214`, `raft.go:665` | The intent is narrowed to the fatal paths whose triggers are documented as forbidden, and the rest are unknown clauses. storage.go:214 is about Compact beyond applied, which is not a modelled fatal. raft.go:665 is a TODO, not a rule. |
| 31 | TypeOK | mi | mi | no | none | ok (the clause lines already separate the one requirement clause) |
| 32 | LogStructure_CommitBounds | req | req | no | removed history `a90ffa34e` | The commit message only explains a better panic message and states no rule. |
| 33 | LogStructure_Indexing | mi | mi | no | none | ok |
| 34 | LogStructure | mi | mi | no | none | ok (conjunction alias) |
