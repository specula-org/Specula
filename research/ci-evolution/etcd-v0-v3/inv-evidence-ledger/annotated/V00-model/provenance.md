# Provenance

## Every `tools/hist.sh` command run (in order)

All were run from `/mydata/bingzhuo/inv-evidence-ledger/ws-V00-model`. Some outputs were piped through `head`, `sed -n`, `grep` or `wc` for display; the pipes are shown.

1. `tools/hist.sh log -S'gt == t' --oneline -- log_unstable.go raft/log_unstable.go` → ee0757a9b
2. `tools/hist.sh log --oneline -- log_unstable.go | head -30`
3. `tools/hist.sh log --oneline | head -3`
4. `tools/hist.sh log --oneline | wc -l` → 917
5. `tools/hist.sh show ee0757a9b | head -80`
6. `tools/hist.sh log -S'stableSnapTo' --oneline -- log_unstable.go log.go node.go rawnode.go` → 4b3a7ff35, 83245f7fe
7. `tools/hist.sh log -S'Metadata.Index == i' --oneline -- log_unstable.go` → 83245f7fe
8. `tools/hist.sh show 83245f7fe | grep -n -B3 -A12 'stableSnapTo\|Metadata.Index == i' | head -80`
9. `tools/hist.sh log -S'stableSnapTo' --oneline | head` → 4b3a7ff35, 09d237400, 83245f7fe
10. `tools/hist.sh log -S'Metadata.Index == prevSnapi' --oneline -- node.go` → 83245f7fe, 516891c49
11. `tools/hist.sh show 516891c49 | head -60`
12. `tools/hist.sh log -S'readStates = nil' --oneline -- rawnode.go node.go raft.go` → b1eed3342, f1dae53a7
13. `tools/hist.sh blame -L 60,70 rawnode.go`
14. `tools/hist.sh show b1eed3342 | head -120`
15. `tools/hist.sh log -S'numOfPendingConf' --oneline -- raft.go` → 530b8862c, cd227fb83
16. `tools/hist.sh show cd227fb83 | head -120`
17. `tools/hist.sh log --format='%h %p %s' -1 cd227fb83 -- raft.go` (refused by hist.sh: revisions are fixed to the cutoff)
18. `tools/hist.sh show cd227fb83 | sed -n 120,200p`
19. `tools/hist.sh show 'cd227fb83^:node.go' | grep -n 'MUST apply all pending\|it MUST apply'`
20. `tools/hist.sh show 'cd227fb83^' | head -5` → parent is 9392e5d3b
21. `tools/hist.sh show 'cd227fb83^:node.go' | sed -n 136,142p`
22. `tools/hist.sh log -S'Was the raft log corrupted' --oneline -- log.go` → a90ffa34e
23. `tools/hist.sh log -S'Invariant: applied <= committed' --oneline -- log.go` → bdc5f3805
24. `tools/hist.sh log -S'never decrease commit' --oneline -- log.go` → c40563479
25. `tools/hist.sh show a90ffa34e | head -40`
26. `tools/hist.sh show c40563479 | head -30`
27. `tools/hist.sh log -S'elections on an empty config win' --oneline -- quorum/majority.go` → 0b1ee4fc5
28. `tools/hist.sh log -S'Ignored transferring leadership' --oneline -- raft.go` → 26506fa2f, a1bcec0c7
29. `tools/hist.sh log -S'do not support changing' --oneline -- raft.go` → 26506fa2f
30. `tools/hist.sh log -S'Reject read only request when this leader' --oneline -- raft.go` → f9382a4d7
31. `tools/hist.sh log -S'learner can not vote' --oneline -- raft.go` → 26506fa2f
32. `tools/hist.sh show 26506fa2f | head -30`
33. `tools/hist.sh show f9382a4d7 | head -25`
34. `tools/hist.sh show 0b1ee4fc5 | head -30`
35. `tools/hist.sh show 09d237400 | grep -n -B2 -A4 'stableSnapTo\|prevSnapi' | head -30`
36. `tools/hist.sh show 9392e5d3b:node.go | sed -n 141p`

I did not run `git` directly.

## Files read

All paths are relative to `/mydata/bingzhuo/inv-evidence-ledger/ws-V00-model`.

**Task and tools**
- `TASK.md` (full)
- `tools/hist.sh` (full, via `cat`)

**Model**
- `spec-original/base.tla` (full)
- `spec-original/MC.cfg`, `spec-original/base.cfg` (full)
- `spec-original/Trace.cfg` (full, read in two parts)
- `spec-original/MC_hunt_1_durability.cfg`, `MC_hunt_1_parallel.cfg`, `MC_hunt_1_same_batch.cfg`, `MC_hunt_2_election_transfer.cfg`, `MC_hunt_3_configuration_application.cfg`, `MC_hunt_3_node.cfg`, `MC_hunt_4_replication_snapshot.cfg`, `MC_hunt_5_reads.cfg`, `MC_hunt_5_singleton.cfg`, `MC_hunt_6_outcomes.cfg`. All were read through `grep -A30` of their INVARIANT/PROPERTY sections and `diff` against `MC.cfg`, plus `grep` for SendPolicy/PersistPolicy/ReadFence. Together this covers every line.
- Directory listing of the workspace (`find -maxdepth 3`), `wc -l` of `spec-original/*` and of the main source files.

**Source, read in full**
- `source/README.md`
- `source/design.md`
- `source/doc.go`
- `source/raftpb/raft.proto`
- `source/log.go`
- `source/log_unstable.go`
- `source/raft.go`
- `source/read_only.go` (lines 15-121, the whole file after the license header)
- `source/node.go` (lines 15-604)
- `source/rawnode.go` (lines 15-282)
- `source/storage.go` (lines 15-271)
- `source/tracker/inflights.go` (lines 15-124)
- `source/tracker/progress.go` (lines 15-237)
- `source/tracker/tracker.go` (lines 15-259)
- `source/quorum/majority.go` (lines 15-202)
- `source/quorum/quorum.go` (lines 15-58)

**Source, read in part** (excerpts and grep results)
- `source/raft_paper_test.go`: `grep '^func Test'`; `grep` of comment lines with section references (`//`, `5.x`, `section`); lines 75-77, 141-146, 186, 234, 545, 596, 694, 820, 865 seen through those greps
- `source/raft_test.go`:
  - `grep '^func Test'`
  - 4-line headers above lines 111, 179, 311, 382, 1445, 2155, 2319, 2703, 3036, 3060, 3083, 3094, 3143, 3221, 3254, 3319, 3407, 3452, 3463, 3500, 3606, 3882, 1259, 3645
  - bodies 111-125, 179-200, 1445-1470, 3500-3524, 380-394, 311-315, 3452-3471
  - `grep` for specific comment phrases; `sed -n 1,60p | grep` (no hits); line 381 via `cat -A`
- `source/node_test.go`: `grep '^func Test'`; headers above lines 165, 213, 245, 641, 680, 727, 894, 956; lines 935-956; `grep -A30` in TestNodeRestart and TestCommitPagination
- `source/rawnode_test.go`: `grep '^func Test'`; headers above lines 239, 369, 468; lines 450-468
- `source/log_test.go`: `grep '^func Test'`; lines 155-170, 171-240 (comment grep), 441-531; `grep 'panic\|recover'`
- `source/log_unstable_test.go`: `grep '^func Test'`; lines 215-240
- `source/storage_test.go`: `grep '^func Test'`; headers above lines 178 and 205; lines 178-204
- `source/raft_snap_test.go`, `source/tracker/progress_test.go`: `grep '^func Test'` only
- `source/tracker/inflights_test.go`: `grep '^func Test'`; lines 20-40
- `source/util.go`: `grep -n 'func limitSize\|func PayloadSize\|func IsResponseMsg'` only
- All `source/**/*_test.go`: `grep -rn 'stableSnapTo'` (no hits)

**Verification**
- A verification script re-read every source file cited by a `source/` evidence line, at that line ±3, after the annotations were written. These are the files listed above, plus `source/log_test.go` lines 227-233, 447-454 and 478-484.

**Files written or used as tool input**
- `spec-annotated/*`: a copy of `spec-original/*`; only `base.tla` was edited.
- `out/*.md`
- Scratchpad helper files: `blocks.txt`, `apply.py`, `check.py`, `ledger_rows.md`, `sany_before.txt`, `sany_after.txt`, `full.diff`, `before/base.tla`.

**Executed, not read**
- `/users/bingzhuo/Specula/lib/tla2tools.jar` and `CommunityModules-deps.jar`, exactly as `TASK.md` prescribes for the SANY check.

No other path on the machine was read, and no network was used.
