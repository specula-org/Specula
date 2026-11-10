# V03 local action validation

Work from `/workspace`. The supplied sources are V02 (`old/source`) and V03 (`new/source`). Both use Voters/VotersOutgoing and `newNode(rn)`/`node.run()`; the inherited historical-path compatibility branch was removed from the Go adapter. Production sources, generic runner, protocol schema and comparator tests are unchanged.

Rebuild descriptors and run the six-way matrix in a fresh directory:

```sh
python3 out/framework/targets/etcd/build_v03.py
python3 out/framework/targets/etcd/replay.py
python3 out/framework/targets/etcd/summarize.py --run-root <printed-output-root>
```

`replay.py` accepts `--output-root` but requires a new path. The final recorded root is `out/cases/v03-final-03`. The suite has 479 source descriptors and 63 finite TLC seeds. The TLC adapter chooses 174 inputs, executes the actual original/evolved model operators, exports those descriptors and transitions, and replays them in Go. All 239 prior source cases and all 103 prior TLC inputs are retained. Both code-to-model and model-to-code routes run against the inherited model, evolved model, and V02 source/model controls. See `out/results.json` and `out/report.md` for actual outcomes.

A single run remains available through the unchanged generic runner:

```sh
python3 out/framework/runner.py --manifest out/framework/targets/etcd/manifest.json --cases out/cases/code-inputs.json --output out/cases/my-fresh-run --spec out/repaired-spec --route code-to-model
```

Use `out/cases/model-seeds.json` and `--route model-to-code` for local TLC generation. Use `manifest-old.json` and `old/spec` for V02 controls. Adapters write commands, logs, actual mapped pre/input, complete declared observations, and raw evidence into each run. Failed commands supply no successful results. Completed disabled relations retain their mapped candidates; no case is silently removed.

Go uses GOMAXPROCS=2, offline modules, workspace temp/cache paths, and a 90-second outer test timeout. TLC uses one worker, a 2 GB heap and an 80-second per-process timeout. Each runner command has a 180-second outer limit in the replay script; model adapter timeout is 178 seconds. The final matrix runs serially. This is local finite action generation, not a full protocol or invariant-checking campaign.

The target adapter calls actual package-local Raft methods, NewRawNode/Bootstrap, and the real Node goroutine/channels. LocalActions calls original `Step`, `ApplyConfCore`, `Restore`, `InitialRaft`, `RestartCore`, `ProtocolReady`, `ProtocolAdvance`, `ProtocolApplyEntry`, and `ProtocolPropose`. Bootstrap uses a parameterized instance of the original model. Preparation executes original Ready and intervening Step calls; persistence installation is explicit caller mapping. There is no Python Raft oracle.

`out/repaired-spec/assets/v02` preserves the actual entire inherited suite. Existing predicates and configuration invariant lists remain intact. `property-phase-handoff.md` explains legacy versus new observer meanings. `out/evidence/triage.json`, `run-index.json`, `disagreements.json`, and `semantic-deltas.json` preserve initial failures, mapping corrections, and behavioral differences.

`domain.py`, `domain_v02.py`, the original target `model-seeds.json`, and immutable `prior-*` files remain historical input assets. Use `build_v03.py` for this packet; do not invoke the old V02 domain rebuild, whose previous-stage seed pathname is absent here.
