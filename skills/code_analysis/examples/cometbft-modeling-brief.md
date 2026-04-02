# Modeling Brief: cometbft/cometbft

## 1. System Overview

- **System**: CometBFT (fork of Tendermint) — Go BFT consensus engine for blockchain
- **Language**: Go, ~6200 LOC consensus core (`consensus/state.go` 2671, `consensus/reactor.go` 2010, `consensus/types/` 577), ~6600 LOC supporting types (`types/vote_set.go` 725, `types/validator_set.go` 1118, `state/execution.go` 822, `evidence/` 575+)
- **Protocol**: Tendermint BFT consensus (PBFT variant) with extensions: vote extensions (ABCI++), proposer-based timestamps (PBTS), weighted round-robin proposer selection
- **Key architectural choices**:
  - **Single-writer concurrency**: Only `receiveRoutine` goroutine modifies `RoundState`; all input via channels (`peerMsgQueue`, `internalMsgQueue`, `timeoutTicker`)
  - **WAL-based crash recovery**: Internal messages (own votes) use `WriteSync` (fsync); peer messages use async `Write`; `EndHeightMessage` is the recovery boundary
  - **Snapshot-based gossip**: Per-peer goroutines (`gossipDataRoutine`, `gossipVotesRoutine`, `queryMaj23Routine`) read snapshots of reactor/peer state with inherent TOCTOU races
  - **Three validator set pipeline**: `LastValidators` / `Validators` / `NextValidators` with +2 height delay for validator changes
  - **Vote extensions**: Application-defined data attached to non-nil precommits, verified via ABCI `VerifyVoteExtension`

## 2. Bug Families

### Family 1: Vote Extension Lifecycle Defects (HIGH)

**Mechanism**: Asymmetric handling of vote extensions across code paths — proposer vs non-proposer, nil vs non-nil precommit, normal operation vs replay, creation context vs verification context.

**Evidence**:
- Historical: cometbft#5204 — Proposer doesn't self-verify its VE; other validators reject it, causing consensus deadlock (OPEN, unfixed, reported on Seda chain)
- Historical: cometbft#3570 — VE enabled flag incorrectly set for nil precommits, causing remote signer panic (fixed PR#3565)
- Historical: cometbft#2361 — Late precommits in `LastCommit` during `timeout_commit` have unverified VEs, passed to proposer via `PrepareProposal` (spec fix only, PR#2423)
- Historical: cometbft#1253 — Large VEs exceed WAL `maxMsgSize` (1MB), causing node panic on `WriteSync` (OPEN, unfixed)
- Code analysis: `ExtendVote` request includes full block context (txs, last commit, misbehavior) but `VerifyVoteExtension` only gets hash+height+address (execution.go:346-370)
- Code analysis: Extensions only delivered to proposer via `buildExtendedCommitInfoFromStore` (execution.go:528-540)

**Affected code paths**:
- `signVote` / `signAddVote` (state.go:2384-2492) — extension creation
- `addVote` VE verification (state.go:2196-2244) — extension checking
- `defaultDoPrevote` / `enterPrecommit` (state.go:1362-1578) — voting decisions
- `Commit` / `BuildExtendedCommitInfo` (execution.go:397-598) — extension propagation

**Suggested modeling approach**:
- Variables: `voteExtension[Server -> Value]`, `veVerified[Server -> SUBSET Server]`
- Actions: Split precommit into `ExtendAndSignPrecommit` (proposer creates VE) and `VerifyVoteExtension` (other validators check VE). Model the asymmetry where proposer skips self-verification.
- Key invariant: If >1/3 of voting power produces VEs that fail verification, consensus should NOT deadlock (liveness).
- Also model: late precommit arrival during `timeout_commit` with unverified extensions

**Priority**: High
**Rationale**: 4 confirmed issues (1 critical OPEN deadlock), affects production chains (Seda). The proposer self-verification gap (#5204) is an unfixed protocol-level liveness bug.

---

### Family 2: Consensus State Machine Liveness / Round Progression (HIGH)

**Mechanism**: Protocol state machine deviates from the Tendermint BFT specification in ways that prevent or delay round/height progression, particularly under message reordering, validator failures, or network conditions.

**Evidence**:
- Historical: tendermint#1745 — Receiving 2f+1 prevotes before proposal prevents termination (CRITICAL, fixed PR#2540)
- Historical: cometbft#1431 — +2/3 nil precommits don't immediately advance to next round; waits for `timeout_precommit` instead (OPEN, spec mismatch)
- Historical: tendermint#1496 — Round synchronization very slow for lagging nodes; cumulative timeout delays (partially fixed)
- Historical: cometbft#3340 — Consensus catch-up failure with short block times; block parts dropped before precommits arrive (OPEN, affects Injective/Sei/Initia)
- Historical: cometbft#3091 — Timeout ticker race: two timeouts in quick succession return wrong timeout info (fixed PR#3092)
- Historical: tendermint#3341 — Single-validator consensus loop stops if signing fails (unfixed)
- Code analysis: `enterPrecommitWait` uses `TriggeredTimeoutPrecommit` flag to prevent re-entry, but round-skip path at addVote:2372 can bypass this (state.go:1584, 2372)
- Code analysis: Guard in `enterPrevoteWait` panics if `!HasTwoThirdsAny()` (state.go:1434) — this is an assertion, not a soft check

**Affected code paths**:
- `enterNewRound` (state.go:1066-1131) — round progression
- `enterPrevoteWait` / `enterPrecommitWait` (state.go:1423-1610) — timeout scheduling
- `addVote` prevote/precommit handlers (state.go:2269-2374) — round-skip logic
- `handleTimeout` (state.go:979-1027) — timeout dispatch

**Suggested modeling approach**:
- Variables: Standard Tendermint vars + `msgReceiveOrder[Server -> Seq(Message)]` to model message ordering
- Actions: Model message delivery as nondeterministic — prevotes can arrive before proposal. Model timeout scheduling and firing.
- Key properties: (1) Liveness: consensus eventually commits if >=2/3 correct and eventually synchronous. (2) The +2/3 nil precommit path should advance without timeout (spec compliance). (3) Round-skip on +2/3 any prevotes/precommits should work correctly.

**Priority**: High
**Rationale**: tendermint#1745 was a critical liveness vulnerability; cometbft#1431 and cometbft#3340 are OPEN affecting production. Round progression is the core liveness mechanism.

---

### Family 3: Crash Recovery / WAL Consistency (HIGH)

**Mechanism**: Non-atomic operations between WAL writes, private validator signing state, and block persistence create crash windows where recovery leads to inconsistent state or equivocation.

**Evidence**:
- Historical: tendermint#8739 — Chain halt on WAL replay when PBTS timeliness check fails for replayed proposal (CRITICAL, unfixed path identified)
- Historical: tendermint#3089 — Crashed validator needs manual `priv_validator.json` edit; WAL corruption during crash leaves incomplete replay (partially fixed PR#3246)
- Historical: tendermint#573 — WAL had no checksums/fsync (fixed PR#672)
- Code analysis: Race between privval signing (state.go:2426) and WAL `WriteSync` (state.go:849) — signed vote exists in privval state but not WAL during crash window
- Code analysis: Async WAL writes (peer messages, timeouts) can be lost on crash (state.go:838, 869)
- Code analysis: WAL repair truncates at first corrupt entry, losing subsequent messages (state.go:2637-2671)
- Code analysis: Non-corruption WAL errors proceed anyway: "proceeding to start state anyway" (state.go:345-347)
- Code analysis: 6 `fail.Fail()` crash points in finalization path (state.go:862, 1744, 1761, 1784, 1804, 1812)
- Code analysis: WAL overwritten during replay catchup (wal.go:74-76, acknowledged TODO)
- Code analysis: `EndHeightMessage` is the recovery boundary — must be written after block save, before `ApplyBlock`

**Affected code paths**:
- `finalizeCommit` (state.go:1704-1827) — block finalization with crash points
- `signVote` / `signAddVote` (state.go:2384-2492) — WAL flush before signing
- `catchupReplay` (replay.go:93-170) — WAL replay on startup
- `repairWalFile` (state.go:2639-2671) — WAL repair
- ABCI Handshake (replay.go:240-470) — block replay for crash recovery

**Suggested modeling approach**:
- Variables: `walEntries[Server -> Seq(Entry)]`, `persistedState[Server -> State]`, `privvalLastSigned[Server -> (H,R,S,BlockID)]`
- Actions: `Crash` clears volatile state and potentially truncates WAL (losing last N async entries). `Recover` replays from WAL + ABCI handshake. Split `FinalizeCommit` into sub-steps: SaveBlock, WriteEndHeight, ApplyBlock, SaveState.
- Key invariants: (1) No equivocation: a recovered node never signs a conflicting vote. (2) Committed blocks are never lost. (3) Recovery reaches a consistent state.

**Priority**: High
**Rationale**: tendermint#8739 and tendermint#3089 caused production chain halts. Crash recovery is a classic TLA+ strength — the model checker can explore all crash timings.

---

### Family 4: Evidence Handling Defects (MEDIUM)

**Mechanism**: Evidence lifecycle gaps between detection, pending pool, block proposal, and commitment allow double-commitment or evidence loss.

**Evidence**:
- Historical: cometbft#4114 — Same `DuplicateVoteEvidence` committed in two consecutive blocks, creating permanently unsyncable chain (CRITICAL, closed NOT_PLANNED, also affects v1.0)
- Historical: cometbft#2353 — Evidence detection/propagation unreliable in tests (OPEN)
- Historical: tendermint#5560 — Proposer includes already-committed evidence due to clist race (fixed PR#5574)
- Code analysis: No crash injection point between `Commit` (execution.go:298) and `evpool.Update` (execution.go:304) — crash here means committed evidence not marked as committed
- Code analysis: Consensus buffer votes not verified before being added to pending pool (pool.go:461-538)
- Code analysis: Evidence can expire between detection and block inclusion (pool.go:89-98, 128-132)
- Code analysis: Evidence expiration uses AND logic — both `MaxAgeDuration` and `MaxAgeNumBlocks` must be exceeded (verify.go:309-317)

**Affected code paths**:
- `AddEvidence` / `ReportConflictingVotes` (pool.go:136-188) — evidence entry
- `CheckEvidence` (pool.go:194-232) — block validation
- `Update` / `markEvidenceAsCommitted` (pool.go:107-358) — lifecycle transitions
- `processConsensusBuffer` (pool.go:461-538) — buffered vote processing

**Suggested modeling approach**:
- Variables: `pendingEvidence[SUBSET Evidence]`, `committedEvidence[SUBSET Evidence]`
- Actions: `DetectEquivocation`, `ProposeBlockWithEvidence`, `CommitBlock`, `UpdateEvidencePool`
- Key invariant: `CommittedInvariant`: for all blocks B1, B2 where B1.height < B2.height, `B1.evidence ∩ B2.evidence = {}`
- Model the crash window between Commit and evpool.Update

**Priority**: Medium
**Rationale**: cometbft#4114 creates permanently unsyncable chains — a critical unfixed bug. The evidence lifecycle is naturally expressible in TLA+.

---

### Family 5: Locking / Unlocking Protocol Correctness (MEDIUM)

**Mechanism**: The Tendermint locking mechanism (`LockedRound`/`LockedBlock`, `ValidRound`/`ValidBlock`) has complex multi-path logic in `enterPrecommit` and `addVote` that must maintain safety invariants across all paths.

**Evidence**:
- Historical: tendermint#1551 — Miss to lock/commit on conflicting votes (design defect, unfixed)
- Historical: tendermint#9251 — Discussion of unlock-on-polka correctness
- Historical: tendermint#1047 — Livelock bug in spec with Byzantine validator (mitigated by gossip)
- Code analysis: `enterPrecommit` has 5 distinct paths (state.go:1459-1578): nil polka → precommit nil; nil-polka with lock → unlock + precommit nil; polka for locked block → relock + precommit; polka for proposal block → lock + precommit; polka for unknown block → unlock + precommit nil
- Code analysis: `addVote` prevote handler has complex unlock/relock at (state.go:2279-2324): updates `ValidBlock`/`ValidRound` and potentially unlocks if polka for different block at higher round
- Code analysis: `POLRound` not validated against `Round` in Proposal (proposal.go:59-61) — `POLRound >= Round` passes validation
- Code analysis: Proposal with `Height == 0` passes `ValidateBasic` despite votes/VoteSet rejecting height 0 (proposal.go:53 vs vote.go:283)

**Affected code paths**:
- `enterPrecommit` (state.go:1459-1578) — main locking logic
- `addVote` prevote handler (state.go:2269-2346) — ValidBlock/ValidRound updates, unlock
- `defaultDoPrevote` (state.go:1362-1420) — locked block prevoting
- `defaultSetProposal` (state.go:1920-1967) — proposal validation

**Suggested modeling approach**:
- Variables: Standard `lockedRound`, `lockedValue`, `validRound`, `validValue` per server
- Actions: Model all 5 `enterPrecommit` paths explicitly. Model the prevote handler's unlock/relock logic.
- Key invariants: (1) If a node is locked on block B at round R, it only precommits B unless it sees a polka for a different block at round > R. (2) ElectionSafety: at most one value can be committed per height.
- Explicitly model the case where `POLRound >= Round` to check if it creates a safety issue

**Priority**: Medium
**Rationale**: The locking protocol is the core safety mechanism. 5 distinct code paths in `enterPrecommit` create significant verification burden. Historical bugs confirm this area is error-prone.

---

### Family 6: Block Execution Crash Atomicity (LOW)

**Mechanism**: The `applyBlock` function in `state/execution.go` performs a multi-step sequence (FinalizeBlock → SaveResponse → Commit → evpool.Update → SaveState) with crash windows between each step. Some crash points lead to inconsistent state.

**Evidence**:
- Code analysis: Crash after Commit but before SaveState means app is committed but CometBFT state is stale (execution.go:310-312) — most dangerous partial-failure
- Code analysis: Crash between SaveFinalizeBlockResponse and Commit — app may have accumulated state not committed (execution.go:271)
- Code analysis: 4 explicit `fail.Fail()` crash injection points (execution.go:264, 271, 306, 314)
- Code analysis: ABCI Handshake handles recovery with multiple cases (replay.go:416-470)
- Code analysis: Error message "commit failed for application" used for both `updateState` and `Commit` errors (execution.go:294, 300)

**Affected code paths**:
- `applyBlock` (execution.go:230-331) — full execution sequence
- `Commit` (execution.go:397-433) — app commit with mempool lock
- ABCI Handshake `ReplayBlocks` (replay.go:240-470) — recovery paths

**Suggested modeling approach**:
- Variables: `appState[Server -> State]`, `cometState[Server -> State]`, `blockStore[Server -> Seq(Block)]`
- Actions: Split `ApplyBlock` into sub-steps with `Crash` between each
- Key invariant: After recovery, `appState` and `cometState` are consistent

**Priority**: Low (for primary spec)
**Rationale**: The ABCI Handshake recovery logic is well-documented and has crash injection testing. Lower priority than protocol-level families unless crash atomicity is a specific verification target.

## 3. Modeling Recommendations

### 3.1 Model

| What | Why | How |
|------|-----|-----|
| Vote extension asymmetry | Family 1: unfixed deadlock #5204, 4 historical bugs | Add VE creation/verification as separate actions; model proposer self-skip |
| Message ordering nondeterminism | Family 2: #1745 critical liveness fix, #1431 open | Allow prevotes/precommits to arrive before proposal |
| Round-skip on +2/3 any | Family 2: #1496 slow sync, #3340 catch-up failure | Model round advancement on +2/3 any votes |
| Crash and WAL recovery | Family 3: #8739 chain halt, #3089 manual recovery | `Crash` action + `Recover` from WAL; split finalization into steps |
| Evidence lifecycle | Family 4: #4114 critical double-commit | Track evidence through pending → committed states |
| Locking protocol (all 5 paths) | Family 5: core safety mechanism, #1551 | Model all `enterPrecommit` paths; verify lock/unlock invariants |
| Validator set rotation | Family 5/6: +2 height delay, 3-set pipeline | Track `LastValidators`/`Validators`/`NextValidators` |

### 3.2 Do Not Model

| What | Why |
|------|-----|
| Gossip protocol details (TOCTOU races) | Family 5 gossip issues are implementation-level Go concurrency bugs, not protocol logic. Model message delivery as nondeterministic instead. |
| Signature verification | Cryptographic details abstracted as `isValid(sig, pubkey)` |
| WAL file format / checksums | Below TLA+ abstraction level; model WAL as a sequence that can lose tail entries on crash |
| Mempool / transaction ordering | Not related to consensus safety |
| P2P network layer | Abstract as nondeterministic message delivery |
| Block sync mode | Separate protocol; model consensus mode only |
| PBTS timeliness checks | Not present in the analyzed codebase version; can be added later |
| ProposerPriority hash (#5609) | Implementation-level arithmetic issue, not protocol logic |

## 4. Proposed Extensions

| Extension | Variables | Purpose | Bug Family |
|-----------|-----------|---------|------------|
| Vote extensions | `voteExtension`, `veVerified` | Model VE creation/verification asymmetry | Family 1 |
| Message ordering | (encoded in action enabling) | Allow prevotes before proposal | Family 2 |
| Timeout modeling | `timeoutScheduled`, `timeoutFired` | Model timeout-based round progression | Family 2 |
| Crash recovery | `walEntries`, `persistedState`, `privvalLastSigned` | Model crash windows and recovery | Family 3 |
| Evidence lifecycle | `pendingEvidence`, `committedEvidence` | Track evidence through states | Family 4 |
| Lock/unlock paths | `lockedRound`, `lockedValue`, `validRound`, `validValue` | All 5 enterPrecommit paths | Family 5 |
| Validator rotation | `lastVals`, `curVals`, `nextVals`, `heightValsChanged` | 3-set pipeline with +2 delay | Family 5/6 |

## 5. Proposed Invariants

| Invariant | Type | Description | Targets |
|-----------|------|-------------|---------|
| ElectionSafety | Safety | At most one value committed per height | Standard, Family 5 |
| Agreement | Safety | No two correct nodes commit different values at the same height | Standard, Family 5 |
| Validity | Safety | Only proposed values can be committed | Standard |
| VELiveness | Liveness | Consensus eventually commits even if some VEs fail verification, provided <1/3 are invalid | Family 1, #5204 |
| NoPhantomVE | Safety | Extensions in `PrepareProposal` that were not verified should be identifiable | Family 1, #2361 |
| RoundProgress | Liveness | If +2/3 correct and eventually synchronous, consensus commits within bounded rounds | Family 2, #1431 |
| NilPrecommitAdvance | Liveness | After +2/3 nil precommits, next round eventually starts | Family 2, #1431 |
| CrashRecoveryConsistency | Safety | After crash and recovery, node does not equivocate | Family 3, #8739 |
| CommittedBlockDurability | Safety | A committed block is never lost | Family 3 |
| EvidenceUniqueness | Safety | Same evidence never committed in two different blocks | Family 4, #4114 |
| LockSafety | Safety | A locked node only precommits its locked value unless it sees a polka at higher round | Family 5 |
| POLRoundValidity | Safety | POLRound < Round for all proposals with POLRound >= 0 | Family 5, proposal.go:59 |

## 6. Findings Pending Verification

### 6.1 Model-Checkable

| ID | Description | Expected invariant violation | Bug Family |
|----|-------------|----------------------------|------------|
| MC-1 | Proposer VE self-verification skip causes deadlock with >1/3 invalid VEs | VELiveness violation | Family 1 |
| MC-2 | Late precommits during timeout_commit have unverified VEs | NoPhantomVE violation | Family 1 |
| MC-3 | +2/3 nil precommits: immediate advance vs timeout — safety equivalence | Verify NilPrecommitAdvance holds under both | Family 2 |
| MC-4 | Prevotes arriving before proposal under Byzantine strategy | RoundProgress violation without fix | Family 2 |
| MC-5 | Crash between privval signing and WAL WriteSync | CrashRecoveryConsistency violation | Family 3 |
| MC-6 | Crash after Commit but before evpool.Update | EvidenceUniqueness violation | Family 4 |
| MC-7 | POLRound >= Round in proposal | LockSafety or ElectionSafety violation | Family 5 |
| MC-8 | All 5 enterPrecommit paths preserve locking invariant | LockSafety | Family 5 |
| MC-9 | Crash after block save but before EndHeightMessage | CommittedBlockDurability | Family 3 |
| MC-10 | Round skip on +2/3 any precommits with concurrent height advance | ElectionSafety | Family 2/5 |

### 6.2 Test-Verifiable

| ID | Description | Suggested test approach |
|----|-------------|----------------------|
| TV-1 | Large vote extension exceeds WAL maxMsgSize | Unit test: create VE > 1MB, verify WAL behavior |
| TV-2 | VoteSetBitsMessage missing Round >= 0 validation | Unit test: send VoteSetBitsMessage with negative round |
| TV-3 | Proposal accepts Height == 0 (inconsistent with Vote/VoteSet) | Unit test: create Proposal with Height=0, verify ValidateBasic |
| TV-4 | Consensus buffer votes not verified before pending pool | Integration test: inject invalid conflicting votes into buffer |
| TV-5 | Data race when logging consensus.State during shutdown (#653) | Race detector test during Stop() with active receiveRoutine |
| TV-6 | Evidence duplicate detection O(n^2) in CheckEvidence | Benchmark with many evidence items |

### 6.3 Code-Review-Only

| ID | Description | Suggested action |
|----|-------------|-----------------|
| CR-1 | `RemovePeer` is a no-op in reactor (reactor.go:229-239) | Implement cleanup; goroutine leak window |
| CR-2 | `ExtendVote` panics instead of returning error (execution.go:359) | Consider returning error for graceful handling |
| CR-3 | Duplicate "commit failed" error message (execution.go:294, 300) | Fix error message at line 294 |
| CR-4 | WAL overwrite during replay acknowledged TODO (wal.go:74-76) | Add read/append mode separation |
| CR-5 | Non-corruption WAL errors proceed anyway (state.go:345-347) | Consider making this fatal |

## 7. Reference Pointers

- **Full analysis report**: see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) for the complete cometbft analysis
- **Key source files**:
  - `artifact/cometbft/consensus/state.go` (2671 lines) — core state machine
  - `artifact/cometbft/consensus/reactor.go` (2010 lines) — gossip and message routing
  - `artifact/cometbft/types/vote_set.go` (725 lines) — vote tracking and quorum
  - `artifact/cometbft/state/execution.go` (822 lines) — block execution
  - `artifact/cometbft/evidence/pool.go` (575 lines) — evidence lifecycle
  - `artifact/cometbft/consensus/replay.go` (563 lines) — crash recovery
  - `artifact/cometbft/consensus/wal.go` (435 lines) — write-ahead log
- **GitHub issues (CometBFT)**: #5204, #1431, #1253, #3340, #3570, #3195, #3091, #2361, #4114, #2353
- **GitHub issues (Tendermint)**: #1745, #1047, #1496, #1551, #3341, #8739, #3089, #573, #5560
- **Reference algorithm**: Tendermint BFT (Buchman, Kwon, Milosevic, 2018, arXiv:1807.04938)
- **Reference TLA+ spec**: Tendermint BFT TLA+ spec from Informal Systems (for syntax patterns)
