# Branching from the 11 V02 recordings

## Matrix

| Version | Run | Events | Replayed | Points | Result | Seconds | Runs | Branch step | Action |
|---|---|---:|---:|---|---|---:|---:|---:|---|
| V01 | joint-autoleave | 414 | 414 | all | none | 300.1 | 4 |  |  |
| V01 | joint-explicit | 446 | 446 | all | RevisedCampaignDecisionEligibility | 293.6 | 5 | 416 | MCCampaign |
| V01 | joint-snapshot-recovery | 398 | 238 | all | none | 300.1 | 5 |  |  |
| V01 | learner-vote | 560 | 444 | all | none | 300.1 | 5 |  |  |
| V01 | membership-snapshots | 1574 | 1574 | all | none | 300.0 | 2 |  |  |
| V01 | node-lifecycle | 100 | 100 | all | NoUnexpectedFatal | 92.5 | 121 | 57 | MCInvokeV2 |
| V01 | outgoing-snapshot-restore | 298 | 298 | all | RevisedCampaignDecisionEligibility | 186.9 | 3 | 193 | MCCampaign |
| V01 | partition-batching | 733 | 733 | all | none | 300.0 | 2 |  |  |
| V01 | raw-elections-reads-recovery | 761 | 761 | all | none | 300.1 | 4 |  |  |
| V01 | ready-intervening-output | 131 | 119 | all | none | 300.0 | 59 |  |  |
| V01 | same-batch-replay | 352 | 352 | all | PromiseBacking | 112.1 | 7 | 148 | MCInvokeV2 |
| V02 | joint-autoleave | 414 | 414 | all | none | 300.0 | 4 |  |  |
| V02 | joint-explicit | 446 | 446 | all | none | 300.0 | 3 |  |  |
| V02 | joint-snapshot-recovery | 398 | 398 | all | none | 300.1 | 2 |  |  |
| V02 | learner-vote | 560 | 560 | all | none | 300.0 | 6 |  |  |
| V02 | membership-snapshots | 1574 | 1574 | all | none | 300.1 | 2 |  |  |
| V02 | node-lifecycle | 100 | 100 | all | NoUnexpectedFatal | 28.8 | 23 | 49 | MCInvokeV2 |
| V02 | outgoing-snapshot-restore | 298 | 298 | all | RevisedCampaignDecisionEligibility | 59.2 | 4 | 193 | MCCampaign |
| V02 | partition-batching | 733 | 733 | all | none | 300.1 | 2 |  |  |
| V02 | raw-elections-reads-recovery | 761 | 761 | all | none | 300.0 | 4 |  |  |
| V02 | ready-intervening-output | 131 | 131 | all | NoUnexpectedFatal | 115.0 | 22 | 125 | MCInvokeV2 |
| V02 | same-batch-replay | 352 | 352 | all | PromiseBacking | 84.7 | 5 | 113 | MCInvokeV2 |
| V03 | joint-autoleave | 414 | 205 | all | RevisedCampaignDecisionEligibility | 93.7 | 3 | 213 | MCCampaign |
| V03 | joint-explicit | 446 | 236 | all | none | 300.0 | 3 |  |  |
| V03 | joint-snapshot-recovery | 398 | 398 | all | none | 300.1 | 2 |  |  |
| V03 | learner-vote | 560 | 234 | all | none | 300.0 | 4 |  |  |
| V03 | membership-snapshots | 1574 | 264 | all | none | 300.0 | 2 |  |  |
| V03 | node-lifecycle | 100 | 100 | all | RevisedProposalConfigurationDecisions | 23.4 | 10 | 85 | MCInvokeV2 |
| V03 | outgoing-snapshot-restore | 298 | 215 | all | none | 300.0 | 3 |  |  |
| V03 | partition-batching | 733 | 733 | all | none | 300.0 | 2 |  |  |
| V03 | raw-elections-reads-recovery | 761 | 761 | all | none | 300.0 | 4 |  |  |
| V03 | ready-intervening-output | 131 | 131 | all | RevisedProposalConfigurationDecisions | 138.9 | 24 | 231 | MCInvokeV2 |
| V03 | same-batch-replay | 352 | 352 | all | PromiseBacking | 125.1 | 7 | 148 | MCInvokeV2 |

## Triage

| Run | Alarm | Triage |
|---|---|---|
| V01/joint-explicit | RevisedCampaignDecisionEligibility | no previous version to compare |
| V01/node-lifecycle | NoUnexpectedFatal | no previous version to compare |
| V01/outgoing-snapshot-restore | RevisedCampaignDecisionEligibility | no previous version to compare |
| V01/same-batch-replay | PromiseBacking | no previous version to compare |
| V02/node-lifecycle | NoUnexpectedFatal | also found on the previous version |
| V02/outgoing-snapshot-restore | RevisedCampaignDecisionEligibility | also found on the previous version |
| V02/ready-intervening-output | NoUnexpectedFatal | also found on the previous version |
| V02/same-batch-replay | PromiseBacking | also found on the previous version |
| V03/joint-autoleave | RevisedCampaignDecisionEligibility | also found on the previous version |
| V03/node-lifecycle | RevisedProposalConfigurationDecisions | property not in the previous version |
| V03/ready-intervening-output | RevisedProposalConfigurationDecisions | property not in the previous version |
| V03/same-batch-replay | PromiseBacking | also found on the previous version |

## Skipped checks

- V01: AckPreservation: replaced by RevisedAckPreservation
- V01: CampaignDecisionEligibility: replaced by RevisedCampaignDecisionEligibility
- V01: ConfigurationTransitionSafety: replaced by RevisedConfigurationTransitionSafety
- V01: WitnessCheck: its module Witnesses extends Checks
- V02: AckPreservation: replaced by RevisedAckPreservation
- V02: CampaignDecisionEligibility: replaced by RevisedCampaignDecisionEligibility
- V02: ConfigurationTransitionSafety: replaced by RevisedConfigurationTransitionSafety
- V02: ReadyAccounting: replaced by RevisedReadyAccounting
- V02: ReadyOwnership: replaced by RevisedReadyOwnership
- V02: WitnessCheck: its module Witnesses extends Checks
- V03: AckPreservation: replaced by RevisedAckPreservation
- V03: CampaignDecisionEligibility: replaced by RevisedCampaignDecisionEligibility
- V03: ConfigurationTransitionSafety: replaced by RevisedConfigurationTransitionSafety
- V03: OutcomeSoundness: replaced by RevisedOutcomeSoundness
- V03: ProposalConfigurationDecisions: replaced by RevisedProposalConfigurationDecisions
- V03: ReadyAccounting: replaced by RevisedReadyAccounting
- V03: ReadyOwnership: replaced by RevisedReadyOwnership
- V03: WitnessCheck: its module Witnesses extends Checks
