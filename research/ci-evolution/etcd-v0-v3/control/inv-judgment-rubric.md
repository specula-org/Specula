# Pre-assessment rubric for invariant maintenance

Written before independent invariant-judgment calls. This file is coordinator-only and is not included in evaluated input packets. These are obligations to adjudicate with executable witnesses, not an exhaustive inventory or an assumption that every retained invariant is correct.

Evaluate each adjacent update separately. Give the model only old properties, old/new implementation, their diff, and necessary state mapping. Exclude new-version reports, revised properties, gold labels, this rubric, and feedback from previous attempts. Freeze the initial answer before generating validation feedback. First try judgment/targeted edits; try blind regeneration only if observed omissions or incorrect edits justify it.

| Update | Obligation | Expected disposition and evidence boundary |
|---|---|---|
| V00→V01 | Advance may append an automatic leave-joint entry | Revise the old exact-log-equality clause of AckPreservation. Require preservation of the old prefix and legitimate append context. A candidate that allows arbitrary log changes is wrong. |
| V00→V01 | Quorums become joint | Preserve the safety intent and adapt the predicate/observations to require both voter halves. Merely satisfying incoming majority must not be accepted. Record representation changes separately from changed requirements. |
| V00→V01 | Newly introduced configuration type enters existing election scan | Preserve the requirement forbidding campaigns with pending committed configuration changes. A model-fidelity failure or implementation bug is not permission to exclude V2 from the correctness requirement. |
| V00→V01 | ElectionSafety and durable vote recovery | Preserve their normative meaning. An implementation fix changes violations, not the requirement. |
| V01→V02 | Learners may grant votes but may not campaign | Revise LearnerEligibility and the learner restriction in VoteContract. Keep campaign exclusion and decision-side quorum restrictions. Source rationale and changed TestLearnerCanVote provide requirement evidence. |
| V01→V02 | RawNode.Ready now accepts messages/read states/SoftState | Revise ReadyOwnership; the previous raw-vs-Node distinction is stale. |
| V01→V02 | Advance must preserve output generated after Ready | Strengthen the relevant ownership/preservation checks or show an existing property already covers it. Old AckPreservation checks log/snapshot/applied state and does not by itself constrain later output. The added TestRawNodeConsumeReady is a source-side requirement witness. |
| V01→V02 | Restored joint configuration now retains its outgoing voters | Keep JointSnapshotRecovery's normative obligation; repairing the implementation is not a reason to weaken it. |
| V02→V03 | Advance autoleave changes to crossing-based emission | Revise the old per-Advance effect assertion and retain the broader obligation that automatic transitions make progress. Do not identify the buggy crossing guard with the entire intended progress requirement. Separate local effect checking from temporal progress. |
| V02→V03 | Invalid configuration proposals are normalized/rejected based on current joint phase | Strengthen/adapt ProposalContract or demonstrate equivalent existing coverage. Include joint+nonempty and nonjoint+empty cases. Checking only new-system reachable states can conceal the missing old-invariant constraint. |
| V02→V03 | Zero-payload entries are always admissible under quota | Adapt ExpectedDecision/OutcomeSoundness and any relevant observation helper. Do not drop unrelated quota rules for nonempty data. |
| V02→V03 | Transfer target demotion now cancels transfer | Preserve or add a check of the configuration-change side effect; ordinary TransferLeader request checking alone may not observe it. Determine actual old coverage before labeling an omission. |

For every proposed semantic modification record a separating observation: old predicate value, candidate predicate value, old/new model behavior, old/new code behavior, and the requirement evidence. Preserve forbidden old behaviors in the comparison domain. Add an invalid nearby observation when needed to check that a legitimate relaxation has not erased detection ability. If an observer lacks the necessary pre-state fields, report and test observer evolution rather than silently treating an unavailable fact as false.

Score correct retention, required change detected, missed change, incorrect change, unsupported extra change, and unresolved. Candidate grammar failure and adapter/setup failure are separate from a wrong maintenance decision. Three version transitions are developmental evidence; success here does not establish general judgment reliability.
