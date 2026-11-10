# Investigation: Bug A Campaign Eligibility Over Pending V2 Config

This file records Phase 1 evidence only. Verdict is in `out/confirmation.md`.

## Finding And Scope

- Source: MC counterexample with 209 states, dataset `etcd-raft-ci-sequence-20260912 label A`.
- Main target: V01, then regression on V02/V03. V00 predates V2 and is limited to a legacy configuration-control run.
- Compact witness: node 2 is `Follower`, term 2, `commit=5`, `applied=4`, old voters `{1,2,3}`, `PreVote=false`, no active Ready, and log entry 5 is a committed `EntryConfChangeV2` replacement (`remove 3`, `add 4`) not yet applied. Campaign makes node 2 `Candidate` term 3 and emits `MsgVote` to 1 and 3.

## Code Audit

V01 public path:

- `RawNode.Campaign()` sends a local `MsgHup` into the raft state machine at `versions/V01/source/rawnode.go:77`.
- `Node.Campaign()` uses the same `MsgHup` path through `node.step` at `versions/V01/source/node.go:131`.
- In `raft.Step`, the `MsgHup` branch slices unapplied committed entries from `applied+1` through `committed` and blocks only if `numOfPendingConf(ents)` is nonzero: `versions/V01/source/raft.go:897`.
- `numOfPendingConf` counts only `pb.EntryConfChange`; it does not count `pb.EntryConfChangeV2`: `versions/V01/source/raft.go:1580`.
- Proposal handling already treats both `EntryConfChange` and `EntryConfChangeV2` as configuration entries: `versions/V01/source/raft.go:1014`.

V03 comparison:

- The `MsgHup` campaign gate is still the same shape: `versions/V03/source/raft.go:907`.
- `numOfPendingConf` still counts only `EntryConfChange`: `versions/V03/source/raft.go:1652`.
- V03 proposal handling decodes both legacy and V2 config entries and has extra refusal checks for pending/joint states: `versions/V03/source/raft.go:1038`. This is neighboring behavior; it does not repair the campaign scan.

V2 API evidence:

- V01 defines `EntryConfChangeV2` as a real raft log entry type: `versions/V01/source/raftpb/raft.pb.go:48`.
- V01 documents `ConfChangeV2` as the API for joint consensus and arbitrary membership changes; it also says configuration changes become active when applied, not merely appended: `versions/V01/source/raftpb/raft.pb.go:365`.
- V01 `Node.ProposeConfChange` explicitly accepts either legacy `ConfChange` or `ConfChangeV2`: `versions/V01/source/node.go:141`.
- `ApplyConfChange` must be called when config entries are observed in committed entries: `versions/V01/source/node.go:169`.

V00 API limitation:

- V00 has only `EntryNormal` and `EntryConfChange`; there is no `EntryConfChangeV2`: `versions/V00/source/raftpb/raft.pb.go:46`.
- V00's public RawNode startup API is the older `NewRawNode(config, peers)` form: `versions/V00/source/rawnode.go:72`. The V2 witness cannot be run on V00 without fabricating a nonexistent API, so V00 is only a legacy-control snapshot.

## Reachability And Trigger Scenario

The reachable scenario is a normal three-node RawNode cluster:

1. Bootstrap voters `{1,2,3}` through the public startup API and process `Ready` records with storage persistence and `ApplyConfChange`.
2. Campaign node 1 through `RawNode.Campaign`; deliver real `MsgVote` / `MsgVoteResp` messages until node 1 is leader in term 2.
3. Let node 1 replicate and commit its term-2 leader no-op at index 4 to node 2.
4. Propose a real `ConfChangeV2` on node 1 replacing voter 3 with voter 4. Replicate entry 5 to node 2 and commit it through a real `MsgAppResp`.
5. Deliver the leader's commit update to node 2, but do not poll node 2's next `Ready`. At this point node 2 has `commit=5`, `applied=4`, and no active RawNode Ready; a Ready is available but not being handled.
6. Call `RawNode.Campaign()` on node 2. This is not between `Ready()` and `Advance()`, honoring the V01 RawNode restriction at `versions/V01/source/rawnode.go:122`.

The scheduler is valid because applications may receive committed work and delay polling or applying the next Ready. The Node API also documents that `Advance` may be called while application work continues in some cases: `versions/V01/source/node.go:159`.

## Safeguards And Masks Checked

- `promotable()` still allows node 2 because its active local config is the old incoming voters `{1,2,3}`.
- `PreVote=false` in the witness and harness, so the path emits real `MsgVote`, not `MsgPreVote`.
- The legacy pending-conf safeguard does fire: with a committed but unapplied `EntryConfChange`, `numOfPendingConf` returns 1 and campaign is blocked.
- No downstream guard masks the V2 case before votes are emitted. The higher-term vote request from node 2 is accepted by node 1 and immediately causes the live term-2 leader to step down to follower term 3.

## Developer Knowledge / Local Prior Evidence

No external browsing or tracker search was performed per the experimental scope. Local source comments and tests show developer intent that V2 config changes are real public API entries and become active on application, not append. The supplied dataset identity is prior-work evidence: `etcd-raft-ci-sequence-20260912 label A`, mechanism `numOfPendingConf/Step MsgHup`. This is therefore recorded as known to the supplied dataset, not as a novelty claim.

Existing local tests exercise V2 conf changes in RawNode tests and V03 datadriven tests, but no local test was found that checks campaign eligibility while a committed `EntryConfChangeV2` is pending application. The legacy path has the intended warning/control behavior through `numOfPendingConf`.

## Harness Attempts

The source snapshots were not edited. Early harness setup attempts failed only in standalone runner plumbing:

- Disposable module initially lacked the selected snapshot's `go.sum`.
- Go does not inherit `replace go.etcd.io/etcd/pkg` from the replaced raft module, so the runner had to add the local replacement explicitly.
- V00 required a separate legacy-only harness because it uses `NewRawNode(config, peers)` and lacks `RawNode.Bootstrap` and V2 types.

Final harness files are under `out/repro/`; full repetition logs are under `out/logs/`.
