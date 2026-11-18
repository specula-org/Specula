# Provenance (V02 model)

I ran all commands from `/mydata/bingzhuo/inv-evidence-ledger/ws-V02-model`. I did not run `git` directly and did not use the network. Outside the workspace I touched only two things: I ran the SANY jar named in TASK.md (`/users/bingzhuo/Specula/lib/tla2tools.jar` and `CommunityModules-deps.jar`), and I used my session scratchpad for helper scripts and SANY logs.

## Every `tools/hist.sh` command run, in order

| # | Command | Result used |
|---|---|---|
| 1 | `tools/hist.sh log --oneline -40 -- raft` (piped to `head -50`) | empty output (wrong path form) |
| 2 | `tools/hist.sh log --oneline -5` | top 5 commits (3ea6503e5, 6c86b7913, e515a6751, 003eb7250, 5c931b381) |
| 3 | `tools/hist.sh log --oneline -40 -- raft/raft.go` (piped to `head`) | empty output (paths are relative to the raft dir) |
| 4 | `tools/hist.sh log --oneline -3 -- raft.go` (piped to `head`) | e515a6751, abb533c27, 2eaf0449e |
| 5 | `tools/hist.sh log --oneline -60 -- .` (piped to `head -70`) | list of the last 60 raft commits |
| 6 | `tools/hist.sh show e515a6751 --stat` | refused (usage message) |
| 7 | `tools/hist.sh show abb533c27 --stat` | refused (usage message) |
| 8 | `tools/hist.sh show 5fa684b47 --stat` | refused (usage message) |
| 9 | `tools/hist.sh show db54973bb --stat` | refused (usage message) |
| 10 | `tools/hist.sh show 46580dcf6 --stat` | refused (usage message) |
| 11 | `tools/hist.sh show 5fa684b47` (piped to `head -150`) | message and diff; evidence for AckPreservation_OutputPreserved and ReadyOwnership_OutputAccepted |
| 12 | `tools/hist.sh show abb533c27` (piped to `head -200`) | "raft: let learners vote"; evidence for VoteDecisionEligibility; also showed the old `TestLearnerCannotVote` |
| 13 | `tools/hist.sh show e515a6751` (piped to `head -250`) | "raft: fix restoring joint configurations"; evidence for JointSnapshotRecovery and JointSnapshotMemberAcceptance |
| 14 | `tools/hist.sh log -S'stableSnapTo' --oneline -- log_unstable.go log.go raft.go node.go rawnode.go` | 46580dcf6, c60f8da6b, 4b3a7ff35, 83245f7fe (AckPreservation_SnapshotRetained search) |
| 15 | `tools/hist.sh log -S'reduceUncommittedSize' --oneline -- raft.go node.go rawnode.go` | 46580dcf6, c60f8da6b, a370b6f6e, 2598fca29 (ReadyOwnership_QuotaUntouched search) |
| 16 | `tools/hist.sh show 83245f7fe` (piped to `grep -n -i -B3 -A8 stableSnapTo`) | only moves the index-equality check; no rule stated |
| 17 | `tools/hist.sh show a370b6f6e` (piped to `head -60`) | uncommitted-size bug message; evidence for QuotaIntegrity |
| 18 | `tools/hist.sh show 46580dcf6` (piped to `sed -n 1,60p`) | joint-quorum commit message |
| 19 | `tools/hist.sh show 46580dcf6` (piped to `grep -n -A30 "func (r \*raft) advance"`) | added `advance` with the auto-leave append (AckPreservation_LogUnchanged note) |
| 20 | `tools/hist.sh log -S'numOfPendingConf' --oneline -- raft.go` | 530b8862c, cd227fb83 |
| 21 | `tools/hist.sh log -S'pending configuration changes to apply' --oneline -- raft.go` | cd227fb83 |
| 22 | `tools/hist.sh show cd227fb83` (piped to `head -80`) | removed caller "MUST apply all pending configuration changes" rule; evidence for CampaignDecisionEligibility |
| 23 | `tools/hist.sh show 530b8862c` (piped to `head -30`) | pendingConfIndex tracking rationale (context only) |
| 24 | `tools/hist.sh show db54973bb` (piped to `head -40`) | "raft: prevent learners from becoming leader"; evidence for LearnerEligibility and TransferDecisionEligibility |
| 25–32 | quote-verification loop: `tools/hist.sh show <c>` piped to `grep -qF "<quote>"` for c = 5fa684b47, 5fa684b47, a370b6f6e, abb533c27, cd227fb83, db54973bb, db54973bb, e515a6751 | two quotes were not found (wrapped message lines) |
| 33 | `tools/hist.sh show 5fa684b47` (piped to `grep -n "dropped\|clear out"`) | exact message line 20 |
| 34 | `tools/hist.sh show e515a6751` (piped to `grep -n "notion\|floor"`) | exact message lines 8–9 |
| 35–42 | second quote-verification loop, same 8 `tools/hist.sh show <c>` calls as 25–32, after the fix | all found |

## Files read

**Task and tools:** `TASK.md`; `tools/hist.sh`, read with `cat` before running it.

**Model, all of `spec-original/`:**
- Every `.cfg` file, read in full with `cat`: `base.cfg`, `MC.cfg`, `MC_hunt_1_durability.cfg`, `MC_hunt_1_parallel.cfg`, `MC_hunt_1_same_batch.cfg`, `MC_hunt_2_election_transfer.cfg`, `MC_hunt_3_configuration_application.cfg`, `MC_hunt_3_node.cfg`, `MC_hunt_4_replication_snapshot.cfg`, `MC_hunt_5_reads.cfg`, `MC_hunt_5_singleton.cfg`, `MC_hunt_6_outcomes.cfg`, `Trace.cfg`, `TraceCorrespondence.cfg`, `Update_focused.cfg`, `Update_full.cfg`, `Update_hunt_autoleave.cfg`, `Update_hunt_joint.cfg`, `Update_hunt_learner_vote.cfg`, `Update_hunt_outgoing_snapshot.cfg`, `Update_hunt_ready.cfg`, `Update_hunt_recovery.cfg`. The `cat` output was saved to a tool-results file by the harness; I used the grep and sed extracts.
- `base.tla`, `MC.tla`, `Update.tla` and `Trace.tla`, all in full.

**Source, read in full:** `README.md`, `design.md`, `doc.go`, `raft.go`, `rawnode.go`, `node.go`, `log.go`, `log_unstable.go`, `storage.go`, `read_only.go`, `bootstrap.go`, `util.go`, `raftpb/raft.proto`, `raftpb/confchange.go`, `raftpb/confstate.go`, `tracker/tracker.go`, `tracker/inflights.go`, `tracker/progress.go`, `tracker/state.go`, `quorum/quorum.go`, `quorum/majority.go`, `quorum/joint.go`, `confchange/confchange.go`, `confchange/restore.go`.

**Source, read in part (line ranges or grep extracts):**
- `raft_test.go`: test-name list, plus lines 175–400, 1450–1470, 1806–1820, 2160–2220, 2322–2400, 2708–2760, 2873–2910, 3025–3092, 3288–3300, 3486–3570, 3640–3702, 3915–4020 and 3942–3946.
- `raft_paper_test.go`: test names with their comments, plus lines 15–40, 110–140, 186–190, 380–392 and 384–390.
- `rawnode_test.go`: test names with their comments, plus lines 712–800 and 928–960.
- `node_test.go`: test names with their comments, plus lines 950–1019.
- `log_test.go`: test names with their comments, plus lines 441–471.
- `confchange/restore_test.go`: lines 95–142, plus test names.
- `confchange/testdata/joint_autoleave.txt`, `confchange/testdata/joint_learners_next.txt`, `quorum/testdata/joint_commit.txt`: first 12–20 lines each.
- Test-name or comment grep only (`grep -n -B4 "^func Test"` or `grep -n "^func Test"`): `raft_snap_test.go`, `log_unstable_test.go`, `storage_test.go`, `raft_flow_control_test.go` (comment lines 23–25), `tracker/progress_test.go`, `tracker/inflights_test.go`, `quorum/quick_test.go`, `quorum/datadriven_test.go`, `confchange/quick_test.go`, `confchange/datadriven_test.go`, `raftpb/confstate_test.go`.
- Keyword greps over all `*.go`, `*.md` and `*.proto` files in `source/`: Raft paper and thesis references, plus the quote strings cited in the blocks.
- `wc -l` over all source files, and a `find` listing of the workspace.

**Not read:** `raftpb/raft.pb.go`, `logger.go`, `status.go`, `diff_test.go`, `example_test.go`, `node_bench_test.go`, `OWNERS`, `rafttest/*`, `quorum/bench_test.go`, `quorum/voteresult_string.go`, and the other testdata files. These were opened by no tool except the `wc` and `find` listings and the keyword greps above.

**My own outputs, read back for checking:** `spec-annotated/*.tla` and `out/ledger.md`.

## Outside-workspace items

- **SANY jar.** Executed only, per TASK.md.
- **Session scratchpad.** I wrote my own helper files there under `v02model_ledger_agent/`: block texts, `apply_v02.py`, `check_v02.py`, `ledger_v02.py` and the SANY logs. While I was working, a file at the scratchpad root (`apply.py`, which I had created) was overwritten by another process. The tool harness showed me its new contents in a change notice; I did not open it myself. Listing the scratchpad directory also showed file names I had not created (`1110-head.md`, `blocks.txt`, `sany_after.txt`, `ckt/`, `ucov-V02/`). I read none of them, used nothing from them, and moved my own files into the private subdirectory.
- **Raft paper.** The `protocol` evidence quotes are Figure 3 statements of the Raft paper, which `source/README.md:5` references. They come from my knowledge of that paper, not from a workspace file, and each block's `note:` says so. I used no knowledge of later etcd raft versions, commits, issues or bugs.
