# Provenance

## tools/hist.sh commands (all run from the workspace root)

1. `tools/hist.sh show 9392e5d3b:node.go` (lines 130-150 viewed)
2. `tools/hist.sh show cd227fb83` (first 120 lines, then lines 120-200)
3. `tools/hist.sh show ee0757a9b`
4. `tools/hist.sh show 516891c49`
5. `tools/hist.sh show f9382a4d7`
6. `tools/hist.sh show a90ffa34e`
7. `tools/hist.sh log -S'stableSnapTo' --oneline -- log_unstable.go log.go node.go rawnode.go` -> 4b3a7ff35, 83245f7fe
8. `tools/hist.sh log -S'drop any new proposals' --oneline -- raft.go` -> db2dbe524
9. `tools/hist.sh log -S'Ignored transferring leadership' --oneline -- raft.go` -> 26506fa2f, a1bcec0c7
10. `tools/hist.sh log -S'Can only change Learner to Voter' --oneline -- raft.go` -> 518a73189
11. `tools/hist.sh log -S'monotonic sequence of indexes' --oneline -- tracker/inflights.go inflights.go` -> 1dc601a9b
12. `tools/hist.sh show db2dbe524` (first 80 lines)
13. `tools/hist.sh log -S'stableSnapTo' --oneline -- log_unstable.go log.go node.go rawnode.go raft.go` -> 4b3a7ff35, 83245f7fe
14. `tools/hist.sh log -S'monotonic sequence' --oneline -- inflights.go tracker/inflights.go` -> 1dc601a9b
15. `tools/hist.sh log -S'monotonic' --oneline -- inflights.go progress.go tracker/inflights.go` -> 1dc601a9b
16. `tools/hist.sh log -S'Metadata.Index == i' --oneline -- log_unstable.go` -> 83245f7fe
17. `tools/hist.sh log --oneline --follow -- tracker/inflights.go` -> 1dc601a9b
18. `tools/hist.sh log -S'monotonic' --oneline` -> 1dc601a9b, ec0dbbb53
19. `tools/hist.sh show 1dc601a9b` (grep for "monotonic" only)

I did not run `git` directly. I read `tools/hist.sh` itself with `cat`.

## Files read

Workspace instructions: `TASK.md`, `ANNOTATION-RULES.md`, `tools/hist.sh`.

Model:
- `spec-annotated/base.tla`: all REQ-EVIDENCE blocks and formulas (lines 640-800, 1225-1744). Also the helper and observer definitions they use: lines 117-340 via grep, 500-640, 820-910, 955-985, 1032-1140, and SetCore.
- `spec-annotated/MC.cfg` (full) and `spec-annotated/Trace.cfg` (full).
- All other `spec-annotated/*.cfg`: compared against MC.cfg with `diff`, and their property lines extracted with a script.
- `spec-original/base.tla`: only through `diff -u` against `spec-annotated/base.tla`.

Source:
- Viewed directly at or around the cited lines: `source/raft.go`, `source/raft_paper_test.go`, `source/raft_test.go`, `source/README.md` (lines 1-40 and 105-200), `source/node.go`, `source/node_test.go`, `source/doc.go`, `source/log.go`, `source/log_test.go`, `source/log_unstable.go`, `source/rawnode.go`, `source/rawnode_test.go`, `source/storage.go`, `source/storage_test.go`, `source/read_only.go`, `source/design.md` (lines 1-60), `source/tracker/progress.go`, `source/tracker/inflights.go`, `source/tracker/tracker.go` (lines 138-146), `source/quorum/majority.go` (lines 120-205).
- Read by `tmp/qcheck.py`, which checks that each cited quote appears within 3 lines of its cited line and finds the cited test function: every file cited in an evidence line, including `source/tracker/tracker.go:30,156`.

## Scratch files (tmp/)

- `tmp/qcheck.py`: quote checker
- `tmp/blocks.py`: reviewed block texts
- `tmp/apply.py`: writes `spec-reviewed/base.tla` from `spec-annotated/base.tla` by replacing only the comment lines of each block
- `tmp/sany_reviewed.txt`: SANY output
- `tmp/diff.txt`: diff output

SANY unpacks its standard modules into a JVM temp directory under /tmp by itself. I did not write any files there.
