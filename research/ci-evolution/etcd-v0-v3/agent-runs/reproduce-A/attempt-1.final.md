Confirmed and reproduced.

Deliverables are in place:

- `out/investigation.md`
- `out/confirmation.md`
- `out/results.json`
- executable harnesses in `out/repro/test_bugA_*`
- full run logs in `out/logs/`
- source hash manifests in `out/hashes/`

Verdict: `REPRODUCED` on V01, V02, and V03. V00 has no public V2 API, so it was run only as the requested legacy-configuration control, which blocks campaign.

Representative command:

```sh
timeout 5m env GOTOOLCHAIN=local GOCACHE=/workspace/out/gocache GOTMPDIR=/workspace/out/gotmp GOPROXY=off /workspace/out/repro/test_bugA_runner.sh V01 v2 rep1
```

Key observed consequence: node 2 campaigns over committed-but-unapplied `EntryConfChangeV2`, emits term-3 votes to old voters 1 and 3, and node 1 steps down from live leader term 2 to follower term 3. Legacy pending config control emits no votes and keeps the leader stable.

All repeated runs passed deterministically: V01/V02/V03 V2 reproduction plus legacy control, and V00 legacy control. Source snapshots under `versions/` were not modified.