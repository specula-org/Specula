# Branching from the 11 V02 recordings

## Matrix

| Version | Run | Events | Replayed | Points | Result | Seconds | Runs | Branch step | Action |
|---|---|---:|---:|---|---|---:|---:|---:|---|
| V01 | joint-autoleave | 414 | 414 | all | none | 300.1 | 4 |  |  |
| V01 | joint-explicit | 446 | 446 | all | RevisedCampaignDecisionEligibility | 286.6 | 5 | 416 | MCCampaign |
| V01 | joint-snapshot-recovery | 398 | 238 | all | none | 300.1 | 6 |  |  |
| V01 | learner-vote | 560 | 444 | all | none | 300.1 | 5 |  |  |
| V01 | membership-snapshots | 1574 | 1574 | all | none | 300.1 | 2 |  |  |
| V01 | node-lifecycle | 100 | 100 | all | RevisedConfigurationTransitionSafety | 108.8 | 128 | 26 | MCInvokeV2 |
| V01 | outgoing-snapshot-restore | 298 | 298 | all | RevisedCampaignDecisionEligibility | 171.6 | 3 | 193 | MCCampaign |
| V01 | partition-batching | 733 | 733 | all | none | 300.1 | 2 |  |  |
| V01 | raw-elections-reads-recovery | 761 | 761 | all | none | 300.1 | 4 |  |  |
| V01 | ready-intervening-output | 131 | 119 | all | none | 300.1 | 66 |  |  |
| V01 | same-batch-replay | 352 | 352 | all | none | 300.1 | 11 |  |  |
| V02 | joint-autoleave | 414 | 414 | all | RevisedCampaignDecisionEligibility | 145.7 | 6 | 355 | MCCampaign |
| V02 | joint-explicit | 446 | 446 | all | RevisedCampaignDecisionEligibility | 294.9 | 5 | 416 | MCCampaign |
| V02 | joint-snapshot-recovery | 398 | 398 | all | none | 300.1 | 3 |  |  |
| V02 | learner-vote | 560 | 560 | all | none | 300.1 | 4 |  |  |
| V02 | membership-snapshots | 1574 | 1574 | all | none | 300.1 | 2 |  |  |
| V02 | node-lifecycle | 100 | 100 | all | ReadBasis | 65.7 | 48 | 50 | MCInvokeV2 |
| V02 | outgoing-snapshot-restore | 298 | 298 | all | RevisedCampaignDecisionEligibility | 52.9 | 3 | 193 | MCCampaign |
| V02 | partition-batching | 733 | 733 | all | none | 300.1 | 2 |  |  |
| V02 | raw-elections-reads-recovery | 761 | 761 | all | none | 300.1 | 4 |  |  |
| V02 | ready-intervening-output | 131 | 131 | all | none | 300.1 | 57 |  |  |
| V02 | same-batch-replay | 352 | 352 | all | none | 300.1 | 13 |  |  |
| V03 | joint-autoleave | 414 | 205 | all | RevisedCampaignDecisionEligibility | 73.1 | 3 | 213 | MCCampaign |
| V03 | joint-explicit | 446 | 236 | all | none | 300.1 | 2 |  |  |
| V03 | joint-snapshot-recovery | 398 | 398 | all | none | 300.1 | 2 |  |  |
| V03 | learner-vote | 560 | 234 | all | none | 300.1 | 6 |  |  |
| V03 | membership-snapshots | 1574 | 264 | all | none | 300.0 | 2 |  |  |
| V03 | node-lifecycle | 100 | 100 | all | RevisedProposalConfigurationDecisions | 25.2 | 10 | 85 | MCInvokeV2 |
| V03 | outgoing-snapshot-restore | 298 | 215 | all | none | 300.0 | 4 |  |  |
| V03 | partition-batching | 733 | 733 | all | none | 300.1 | 2 |  |  |
| V03 | raw-elections-reads-recovery | 761 | 761 | all | none | 300.1 | 4 |  |  |
| V03 | ready-intervening-output | 131 | 131 | all | RevisedProposalConfigurationDecisions | 124.2 | 24 | 231 | MCInvokeV2 |
| V03 | same-batch-replay | 352 | 352 | all | RevisedProposalConfigurationDecisions | 136.8 | 10 | 279 | MCInvokeV2 |

## Triage

| Run | Alarm | Triage |
|---|---|---|
| V01/joint-explicit | RevisedCampaignDecisionEligibility | no previous version to compare |
| V01/node-lifecycle | RevisedConfigurationTransitionSafety | no previous version to compare |
| V01/outgoing-snapshot-restore | RevisedCampaignDecisionEligibility | no previous version to compare |
| V02/joint-autoleave | RevisedCampaignDecisionEligibility | also found on the previous version |
| V02/joint-explicit | RevisedCampaignDecisionEligibility | also found on the previous version |
| V02/node-lifecycle | ReadBasis | also found on the previous version |
| V02/outgoing-snapshot-restore | RevisedCampaignDecisionEligibility | also found on the previous version |
| V03/joint-autoleave | RevisedCampaignDecisionEligibility | also found on the previous version |
| V03/node-lifecycle | RevisedProposalConfigurationDecisions | property not in the previous version |
| V03/ready-intervening-output | RevisedProposalConfigurationDecisions | property not in the previous version |
| V03/same-batch-replay | RevisedProposalConfigurationDecisions | property not in the previous version |

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
- V03: ReadyAccounting: replaced by RevisedReadyAccounting
- V03: ReadyOwnership: replaced by RevisedReadyOwnership
- V03: WitnessCheck: its module Witnesses extends Checks
