# What the force-reconfig gap was hiding

The MongoDB reconfiguration suite (`case-studies/systems/mongodb/modules/raftreconfig/runs/case-studies-mongodb-raftreconfig/spec`) is a full run, not an update, so the check was pointed at every action in `MCNext` (`--actions MC.tla:MCNext`). `report.md` is its output.

Its first row says `ConfigTermValid`, `ConfigVersionNonNeg` and `LeaderInOwnConfig` are enabled only in `MC.cfg`, which sets `ForceReconfigLimit = 0`, so none of them ever runs while a force reconfig happens. Every hunt that allows force reconfig leaves them off.

To see whether that matters, `MC.cfg` was run with only `ForceReconfigLimit = 1` changed: TLC 2026.11.03, `-simulate -depth 100 -seed 1 -workers 1`, all of `MC.cfg`'s invariants enabled. `LeaderInOwnConfig` failed within seconds, at state 9:

1. s1 becomes leader with config `{s1}`; s2 shuts down.
2. Follower s3 force-reconfigures to `{s2, s3}` (version 10000, configTerm -1).
3. s1 receives that config through `SendConfig`, installs it and stays leader, now outside its own config.

This does not say MongoDB has a bug. Either the real primary steps down when it installs a config without itself, and the model is missing that, or the invariant does not hold under force reconfig by design. The check's contribution is that this combination had never been checked; deciding which case it is needs the source and the suite's authors.
