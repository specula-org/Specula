# Qian's verdicts, rerun

| Case | Qian's verdict | Version | Recording | What the tool reports now |
|---|---|---|---|---|
| workload | noise | V01 | node-lifecycle | found (no previous version to compare), but it is the fixed-upstream case; without the guard: found |
| workload | noise | V02 | node-lifecycle | found (also found on the previous version), but it is the fixed-upstream case; without the guard: found |
| workload | noise | V03 | node-lifecycle | found (also found on the previous version), but it is the duplicate-leave case; without the guard: found |
| fixed-upstream | real, not from the update | V01 | ready-intervening-output | found (no previous version to compare) |
| fixed-upstream | real, not from the update | V02 | ready-intervening-output | found (also found on the previous version) |
| fixed-upstream | real, not from the update | V03 | ready-intervening-output | not found in the budget |
| old-model-gap | noise | V01 | same-batch-replay | found (no previous version to compare) |
| old-model-gap | noise | V02 | same-batch-replay | found (also found on the previous version) |
| old-model-gap | noise | V03 | same-batch-replay | found (also found on the previous version) |
| in-recording | noise | V01 | joint-snapshot-recovery | broken by the recording itself, not reported as an alarm |
| replaced | noise | V03 | joint-explicit | skipped: replaced by RevisedProposalConfigurationDecisions |
| replaced | noise | V03 | outgoing-snapshot-restore | skipped: replaced by RevisedProposalConfigurationDecisions |
| replaced | noise | V03 | ready-intervening-output | skipped: replaced by RevisedProposalConfigurationDecisions |
| bug-a | real, from the update | V01 | joint-autoleave | found (no previous version to compare) |
| bug-a | real, from the update | V01 | joint-explicit | found (no previous version to compare) |
| bug-a | real, from the update | V01 | joint-snapshot-recovery | found (no previous version to compare) |
| bug-a | real, from the update | V01 | outgoing-snapshot-restore | found (no previous version to compare) |
| bug-a | real, from the update | V02 | joint-autoleave | found (also found on the previous version) |
| bug-a | real, from the update | V02 | joint-explicit | found (also found on the previous version) |
| bug-a | real, from the update | V02 | joint-snapshot-recovery | found (also found on the previous version) |
| bug-a | real, from the update | V02 | outgoing-snapshot-restore | found (also found on the previous version) |
