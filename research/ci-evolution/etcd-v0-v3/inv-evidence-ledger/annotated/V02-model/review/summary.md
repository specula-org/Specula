# Review summary: REQ-EVIDENCE annotations, etcd raft V02 model

## Counts

| Item | Count |
|---|---|
| Blocks reviewed | 68 (59 full blocks + 9 alias one-liners; every in-scope property has exactly one block) |
| Kept unchanged (`review: ok`) | 44 |
| Changed | 24 |
| Intent changed | 11 |
| Status changed | 1 |
| Blocks with an evidence-type change | 9 (10 lines retyped `comment` → `impl`) |
| Evidence lines removed | 5 lines in 4 blocks (they do not support any part of the intent) |
| Evidence lines added | 12 lines in 7 blocks (sources already named in the block's clause lines, or found by a history search) |
| Evidence locations corrected | 1 (cd227fb83: the quote is a removed `node.go` line, not the commit message) |
| `->` suffixes added | to every remaining non-`impl` evidence line; the annotator had added none |
| New splits | 0 (no formula text changed) |
| Clause lines | 24 → 52. 37 written, 9 old ones replaced or reworded, net +28. 10 blocks that had no clause lines now have them. |

Status before → after (59 status-bearing blocks; the 9 aliases have no status):

| old \ new | requirement | impl-abstraction | model-internal | unknown |
|---|---|---|---|---|
| requirement (38) | 37 | 0 | 0 | 1 (NoUnexpectedFatal) |
| impl-abstraction (2) | 0 | 2 | 0 | 0 |
| model-internal (18) | 0 | 0 | 18 | 0 |
| unknown (1) | 0 | 0 | 0 | 1 |

After review: requirement 37, model-internal 18, impl-abstraction 2, unknown 2.

## Main patterns found

- **Narrating comments typed as `comment`.** Ten lines were retyped to `impl`: raft.go:565, :575, :678, :704, :925 (twice), :1018, :1051, :289. Most blocks keep their status through other evidence. NoUnexpectedFatal does not, and its status became unknown.
- **Intents broader than their evidence.** Examples: "answered exactly" (votes), "never drops or alters messages, read states, SoftState", "strictly increasing", "taking its index as commit", "message or write result", and the decision-table precedence. These were narrowed, and the remainder moved to `clause` lines.
- **Tests cited for more than they assert.** TestRejectStaleTermMessage steps a stale MsgApp, not a vote. TestLearnerCanVote's reject check is vacuous for an MsgVoteResp. TestNodeCommitPaginationAfterRestart was cited for RecoveryBacking and CommittedHistory clauses it does not check. The leader-transfer tests assert eventual transfer, not an immediate MsgTimeoutNow.
- **Impl-only clauses rescued by history.** "Non-empty voters" in QuorumAccounting and JointConfigurationShape is stated in commit 60429a913 ("prevent the use of empty commit quorums"), found with `hist.sh log -S'removed all voters'`.
- **Contradiction recorded.** doc.go:246-247 says a stale MsgVote "will be rejected", but VoteContract expects silence. That clause is impl-abstraction.

## Five blocks I was least sure about

1. **NoUnexpectedFatal** (requirement → unknown). The "conflict with committed entry" panics are arguably protocol-implied. I recorded them as a requirement-in-substance clause instead of keeping the whole block a requirement.
2. **JointSnapshotMemberAcceptance** (kept requirement). The support is a two-step reading: raft.go:1398 says a snapshot is thrown away only if the recipient is "not in the config", and raft.proto:105 says outgoing voters are part of the config. No test or document addresses outgoing-only recipients directly.
3. **AckPreservation_OutputPreserved vs ReadyOwnership_OutputAccepted.** I kept read states as a requirement for acceptance at Ready, citing rawnode.go:121 ("must be handled"). For preservation across Advance I marked them unknown, because 5fa684b47 and the test speak only of messages. This asymmetry is a judgment call.
4. **PromiseBacking.** README.md:118 allows sending messages while entries of the same batch are being persisted; node.go:81 says messages go after entries are on stable storage. I kept requirement on node.go:81, and made the WriteResult clause unknown.
5. **ElectionProgress** (kept requirement). The evidence is a regression test ("would come to a standstill") and a one-round election test. No document states election liveness under this premise set.
