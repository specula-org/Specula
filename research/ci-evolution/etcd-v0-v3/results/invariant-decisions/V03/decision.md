The suite needs targeted changes and additions. Preserve the consensus, durability, full joint-membership, learner-vote, Ready, and replication safety requirements. No correctness property should be removed.

This is an independent static assessment of `old/source`, `new/source`, `update.patch`, and `old/spec`. No tests, TLC, source execution, browsing, other agents, or experiment history were used. Code and specs were not changed. All witnesses in [decision.json](decision.json) are proposed, not validated.

| Decision | Property or obligation | Reason |
| --- | --- | --- |
| Modify | `AutoLeaveAdvance` / `UpdateAutoLeaveAdvance` | Require the applied cursor to cross the pending index, exactly one zero-payload leave, and pending index advancement on success. Remove quota-retry acceptance; forbid a leave when the crossing condition is false. |
| Modify | `OutcomeSoundness` | An otherwise admissible zero-payload batch must succeed even above the quota cap. Positive payload remains limited. |
| Modify | `ProposalConfigurationDecisions` | Check joint-state admission, empty-normal rewriting, sequential batch decisions, effective payload, and pending cursor. Observe the full configuration. Retain the documented `LeaveJoint()` classification. |
| Modify: old property repair | `CampaignDecisionEligibility` | A joint `{1} && {1}` configuration can self-elect. Use the actual self-quorum condition; retain blocking on all unapplied configuration kinds. Sorted output does not change eligibility. |
| Modify: old coverage repair | `ConfigurationTransitionSafety` | Exempt actual bootstrap entries, not every configuration entry with `id=0`; automatic leaves also require their predecessor configuration. |
| Modify: observer repair | `JointSnapshotMemberAcceptance` / alias | Observe actual restore dispatch, so stale-term messages do not falsely require acceptance. Keep outgoing-only voters and staged learners covered. |
| Migrate representation | Automatic-leave payload/size; new-peer and live-restore progress | Nil Data has payload 0 but a positive entry size. Changer starts Next at LastIndex; reset still uses LastIndex+1. Live snapshot self-progress also changes. |
| Add | Configuration-triggered transfer cancellation | Existing transfer observers run only on transfer requests. A demoted target must be canceled on leaving joint; a staged outgoing voter remains eligible. |
| Add | Immediate configuration probing | Catchup eventually is weaker than probing an eligible new peer during the configuration callback. Preserve pause, size and compacted-log exceptions. |
| Add | Automatic-leave completion under fair service | Preserve eventual automatic exit, including any allowed early-Advance order; a crossing-only predicate is insufficient. |
| Add | Exact Advance quota release; snapshot AppResp recovery | Existing quota/evidence predicates cannot detect every missed release or a caught-up snapshot peer stuck in Probe. |
| Add at source boundaries | Changer error/result integrity, campaign emission order, operation-string round trip, harness snapshot application and RNG serialization | These obligations are absent from the old abstract observers. They do not justify restricting network delivery schedules. |

The decisive witnesses include:

- **Duplicate auto-leave:** applied=5, pending=6, last=8; Advance to 6 appends leave 9 but leaves pending=6. The old property passes. Advancing through ordinary entries 7–8 can append leave 10 and pass again. The strengthened predicate rejects both cursor failure and duplication.
- **Quota:** quota=5, cap=3, one zero-payload normal entry. Correct new acceptance violates the old outcome oracle. A positive-payload proposal in the same state must still be rejected.
- **Batch admission:** in joint state with no pending change, `[AddVoter(3), empty Auto V2]` must become `[normal no-op, leave]`. Rejecting the first must not make the second pending-conf blocked.
- **Demotion:** transfer to 3 survives while 3 is in outgoing voters/learnersNext; after leave-joint makes 3 only a learner, the transfer must immediately clear. Eventual timeout and request-time eligibility do not prove this.
- **Observer repair:** a stale-term snapshot at a fresh index may be ignored. A term-current snapshot for an outgoing-only member must still be accepted.

Several important behaviors are already covered. `VoteContract` checks ordinary vote/log/term rules for learners, while `LearnerEligibility` prohibits their campaigns. `QuorumAccounting` requires both joint majorities. `EffectContract`, `ConfigOf`, and the joint recovery predicates retain every ConfState field. `AckPreservation` already permits one empty-change V2 extension and preserves output generated after Ready; it needs the stronger auto-leave predicate alongside it. `ReplicationEvidence` checks acknowledgment-backed Match independently of optimistic Next. None of these should be weakened.

Implementation concerns must remain visible:

- Proposal admission tests only `len(Changes)==0`, but `LeaveJoint()` also requires zero Transition. Empty `JointExplicit` is wrongly treated as leave intent; inside joint it can be admitted and then panic when applied.
- The unchanged snapshot membership guard omits outgoing voters, and `numOfPendingConf` omits V2 entries. Retain the requirements that expose these failures.
- The new interaction harness appends before installing a snapshot, does not incorporate that snapshot into application History, and drops `ProcessReady` errors in `Stabilize`. It cannot be assumed to be a faithful validation adapter.
- The new shared `rand.Rand` is accessed after releasing the network mutex while senders run concurrently.
- The comment “Configuration changes are never refused” is broader than the implemented and tested zero-payload exemption. Do not silently exempt all configuration payloads.

Validation still needs reachable old/new witnesses, mixed-entry proposal and demotion workloads, concrete size/progress mappings, and configurations that actually enable the retained/new predicates. Early Advance before a configuration callback, self-demoted leaders, and pending cursors after quota rejection need separate resolution. Finite safety exploration will not establish eventual automatic exit or other liveness targets. The JSON records each retained property, alias, diagnostic canary, negative control, and outstanding obligation explicitly.
