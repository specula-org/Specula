# Provenance

All work was done inside /mydata/bingzhuo/inv-evidence-ledger/rws-V02-model. Scratch files are in tmp/. No network was used and `git` was not run directly.

## tools/hist.sh commands (in order)

1. `tools/hist.sh log -1 --format='%H%n%B' <c>` for abb533c27, cd227fb83, db54973bb, e515a6751, 5fa684b47 and a370b6f6e. All six were refused by the tool ("revisions are fixed to the cutoff"), so no output.
2. `tools/hist.sh show abb533c27` (raft: let learners vote) → tmp/hist/abb533c27.txt
3. `tools/hist.sh show cd227fb83` (raft: hide Campaign rules on applying all entries) → tmp/hist/cd227fb83.txt
4. `tools/hist.sh show db54973bb` (raft: prevent learners from becoming leader) → tmp/hist/db54973bb.txt
5. `tools/hist.sh show e515a6751` (raft: fix restoring joint configurations) → tmp/hist/e515a6751.txt
6. `tools/hist.sh show 5fa684b47` (raft: require app to consume result from Ready()) → tmp/hist/5fa684b47.txt
7. `tools/hist.sh show a370b6f6e` (raft: fix bug in unbounded log growth prevention mechanism) → tmp/hist/a370b6f6e.txt
8. `tools/hist.sh log -S'removed all voters' --oneline -- confchange/confchange.go` → 60429a913
9. `tools/hist.sh log -S'removed all voters' --oneline -- raft.go tracker/ quorum/` → no output
10. `tools/hist.sh show 60429a913` (raft: internally support joint consensus) → tmp/hist/60429a913.txt
11. `tools/hist.sh log -S'stableSnapTo' --oneline -- log_unstable.go raft.go log.go` → 46580dcf6, 83245f7fe
12. `tools/hist.sh show cd227fb83^:node.go` (checked lines 136-142: the removed "it MUST apply all pending configuration changes" comment at line 141)
13. `tools/hist.sh log -S'numOfPendingConf' --oneline -- raft.go` → 530b8862c, cd227fb83
14. `tools/hist.sh show 46580dcf6` (raft: allow use of joint quorums) → tmp/hist/46580dcf6.txt

## Files read

Workspace documents: TASK.md, ANNOTATION-RULES.md, tools/hist.sh.

Spec (spec-annotated/, and spec-original/ through `diff -ru spec-original spec-annotated` → tmp/annot.diff):
- base.tla: the contract definitions at lines 600-770; the formulas of every annotated property; Fatal, CommitTo and JointWon at 138-148; ConfigAfter at 551-576; SetCore and ProtocolReceive liveOK updates; PromiseOK and ProtocolPublish at 1143-1160; ProtocolCompleteWrite; EmptyHistory; and a grep of the Fatal call sites.
- MC.tla, Trace.tla and Update.tla: annotated regions, plus a grep of the definitions.
- Every .cfg file: grep of the INVARIANT/PROPERTY lines. Read in full or in part: MC.cfg, base.cfg, Trace.cfg, Update_full.cfg, Update_focused.cfg, Update_hunt_outgoing_snapshot.cfg.

Source (source/), the regions around every cited line plus the following:
- raft.go: 40-55, 120-170, 195-205, 275-295, 355-372, 545-600, 650-720, 770-965, 1005-1060, 1075-1110, 1145-1180, 1195-1245, 1255-1300, 1380-1490, 1525-1545, 1585-1610, and the grep of panic sites
- node.go: 50-200, 570-590
- README.md: 1-10, 20-32, 105-200
- doc.go: 200-265
- log.go: 28-40, 84-130, 145-160, 196-215, 270-303
- log_unstable.go: 15-25, 75-120
- storage.go: 75-85, 183-215
- tracker/tracker.go: 30-62, 170-185; tracker/progress.go: 60-75, 136-150; tracker/inflights.go: 48-60
- quorum/joint.go: 14-22; quorum/majority.go: 170-190
- raftpb/raft.proto: 95-160
- confchange/confchange.go: 150-180, 275-335; confchange/restore.go: 105-118; confchange/restore_test.go: 115-145
- confchange/testdata/joint_learners_next.txt: 1-20; confchange/testdata/simple_safety.txt: 1-12 (and grep of testdata and *_test.go for "removed all voters")
- read_only.go: 15-25; rawnode.go: 115-180, 228-240; design.md: 1-12, 36-44
- raft_paper_test.go: 70-110, 183-275, 385-480, 540-620, 765-880
- raft_test.go: 180-258, 305-330, 378-400, 2150-2216, 2322-2350, 3036-3075, 3355-3387, 3445-3467, 3495-3720, 3740-3760, 3915-3960
- rawnode_test.go: 104-118, 728-800, 925-975
- node_test.go: 210-240, 960-1050
- log_test.go: 440-480
- raft_flow_control_test.go: 15-40

Scripts and scratch files, all in tmp/: checkquotes.py, extract.py, apply.py, blocks_orig.txt, blocks_new.txt, annot.diff, review.diff, sany_*.txt, hist/*.txt.
