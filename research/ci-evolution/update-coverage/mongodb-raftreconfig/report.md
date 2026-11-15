# Update coverage: case-studies-mongodb-raftreconfig/spec

## Checks never run while an action happens

An action marked *never possible* was never enabled in any state visited by the configs that
enable those checks; *possible* means it was enabled there but not taken within the budget.

| Never checked while | Checks | Names |
|---|---:|---|
| 2 MCForceReconfig (never possible) | 3 | `ConfigTermValid`, `ConfigVersionNonNeg`, `LeaderInOwnConfig` |
| 6 MCRemoveNewlyAdded (never possible) | 3 | `ActiveConfigsOverlap`, `ArbiterQuorumOverlap`, `DrainModeReconfigSafety` |
| 4 MCShutDown (never possible); 6 MCRemoveNewlyAdded (never possible) | 1 | `ConfigPropagationSafety` |

## Actions

| # | Group | Action |
|---:|---|---|
| 1 | MCNext | MCWinElection |
| 2 | MCNext | MCForceReconfig |
| 3 | MCNext | MCReconfig |
| 4 | MCNext | MCShutDown |
| 5 | MCNext | MCClientRequest |
| 6 | MCNext | MCRemoveNewlyAdded |
| 7 | MCNext | MCCompleteDrain |
| 8 | MCNext | MCSendConfig |
| 9 | MCNext | MCGetEntry |
| 10 | MCNext | MCRollbackEntries |
| 11 | MCNext | MCCommitEntry |
| 12 | MCNext | MCUpdateTermsOnNodes |

## What each config reached

`x` taken, `e` enabled but not taken, `.` never enabled. Retried configs ran a second, longer pass.

| Config | Status | Traces | Seconds | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---:|---:|---|---|---|---|---|---|---|---|---|---|---|---|
| `MC.cfg` | budget used, retried | 35418 | 360.1 | x | . | x | x | x | x | x | x | x | x | x | x |
| `MC_hunt_arbiter.cfg` | budget used, retried | 8926 | 360.1 | x | x | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_drain.cfg` | budget used, retried | 9365 | 360.1 | x | x | x | . | x | . | x | x | x | . | x | x |
| `MC_hunt_drain_v2.cfg` | budget used, retried | 34776 | 360.1 | x | . | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_drain_v3.cfg` | budget used, retried | 38970 | 360.1 | x | . | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_force.cfg` | budget used, retried | 45279 | 360.1 | x | x | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_force_deep.cfg` | budget used | 15643 | 120.0 | x | x | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_force_rollback.cfg` | budget used | 15643 | 120.0 | x | x | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_force_v2.cfg` | budget used | 12713 | 120.0 | x | x | x | x | x | . | x | x | x | x | x | x |
| `MC_hunt_heartbeat.cfg` | budget used, retried | 24028 | 360.0 | x | x | x | . | x | . | x | x | x | x | x | x |
| `MC_hunt_heartbeat_v2.cfg` | budget used, retried | 24583 | 360.0 | x | . | x | . | x | . | x | x | x | x | x | x |
| `MC_hunt_newlyadded.cfg` | budget used | 8025 | 120.0 | x | x | x | . | x | x | x | x | x | x | x | x |
| `MC_hunt_newlyadded_v2.cfg` | budget used | 14209 | 120.0 | x | . | x | x | x | x | x | x | x | x | x | x |
