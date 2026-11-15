# Simulation on the corrected V01 configs

After the coverage check, the obvious question is whether fixing the configs is enough for ordinary checking to find bug A. It is not, at least not from Init with random simulation.

Spec: `agent-runs/inv-evidence/out/revised-spec/V01`. `MC_v2.cfg` is `MC.cfg` with `"V2"` added to `WorkloadKinds`; `Update_full_cde.cfg` is `Update_full.cfg` with `CampaignDecisionEligibility` added. Each run: TLC 2026.11.03, `-simulate -seed 11 -workers 1`, 20 minutes, all of the config's invariants enabled.

| Config | Depth | Traces | States checked | Violation |
|---|---:|---:|---:|---|
| `MC_v2.cfg` | 100 | 428 | 501,987 | none |
| `MC_v2.cfg` | 300 | 113 | 461,352 | none |
| `Update_full_cde.cfg` | 100 | 1,533 | 1,575,418 | none |
| `Update_full_cde.cfg` | 300 | 497 | 1,653,899 | none |

The coverage reports show why: in every config, random runs from Init never deliver a message (`Receive` is never reached), so no leader is elected and the follower-campaign scenario behind bug A never arises. Qian's prefix probe reaches it in 40 s by replaying a recorded run first. Fixing the configs is necessary for the check to apply, and the prefix is what gets the search there.
