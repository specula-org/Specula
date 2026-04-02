# CometBFT Bug Hunting Report

## Summary

- Hypotheses tested: 10 (MC-1 through MC-10)
- Bugs found: 2
- Known bugs reproduced: 2 (B1/#5204, B6/#1431)
- Not reproduced: 8 (3 infeasible without spec extension, 5 hold within tested bounds)

### Model Checking Coverage

| Config | Mode | States | Traces | Invariants | Result |
|--------|------|--------|--------|------------|--------|
| MC_ve_ultra.cfg | BFS | 26.2M | - | ElectionSafety, Validity, VELivenessInv | **VELivenessInv violated** |
| MC_ve.cfg | BFS | 58.5M | - | ElectionSafety, Validity, VELivenessInv + structural | **VELivenessInv violated** (23 states) |
| MC_liveness.cfg | BFS | 889K | - | 16 safety + 4 temporal | **NilPrecommitAdvance violated** (15 states) |
| MC.cfg | BFS | 793M | - | 16 safety + 3 temporal (deadlock off) | All hold |
| MC.cfg | Simulation | 66K | 523 | 16 safety + 3 temporal | All hold |
| MC_safety_extended.cfg | Simulation (4 servers) | 152M | 490K | 18 safety | All hold |
| MC_hunt_crash_ve.cfg | Simulation | 1.9K | 14 | 18 safety + VE + crash recovery | All hold (deadlock = Bug #2) |
| MC_hunt_ve_crash_targeted.cfg | BFS | 366M | - | ElectionSafety, VELivenessInv, VEConsistency, CrashRecoveryConsistency + 6 | All hold |
| MC.cfg (inv_log Run#1) | Simulation | 19.6M | 246K | 16 safety + 3 temporal | All hold |

### Trace Validation Coverage

| Trace | States | Result |
|-------|--------|--------|
| basic_consensus_mapped.ndjson | 829 | Pass |
| lock_and_relock_mapped.ndjson | 1,483 | Pass |
| timeout_propose_mapped.ndjson | 27,407 | Pass |
| two_heights_mapped.ndjson | 1,676 | Pass |

---

## Bugs Found

### Bug #1: Vote Extension Deadlock (B1 / Issue #5204)

- **Hypothesis**: MC-1
- **Bug Family**: Family 1 (Vote Extensions)
- **Severity**: Critical
- **Status**: Known (issue #5204, OPEN, unfixed)
- **Invariant violated**: `VELivenessInv`
- **Counterexample**: 22 states (file: `counterexample_MC1_VEDeadlock.out`)

#### Trace Summary

The counterexample demonstrates a consensus deadlock caused by the proposer skipping vote extension self-verification:

| State | Action | Key Change |
|-------|--------|------------|
| 1 | Initial | s2 has `InvalidVE` (pre-injected) |
| 2-3 | s2 enters round 0, proposes v1 | s2 is proposer for (h=1, r=0) |
| 4 | s2 prevotes v1 | s2 sends prevotes |
| 5-9 | s1, s3 enter round, receive proposal + prevotes | All servers have proposal for v1 |
| 10-13 | s1, s3 prevote v1, deliver prevotes | All see 3/3 prevotes for v1 (polka) |
| 14-15 | s3, s1 precommit v1 (NewLockPolka) | s1, s3 lock on v1, send precommits with `ValidVE` |
| 16-19 | s2 receives s3's precommit (ValidVE, accepted); s2 precommits v1 with `InvalidVE` | s2 sends precommits with `InvalidVE` to s1, s3 |
| 20-21 | s2 receives s1's precommit (ValidVE, accepted) | s2 now has 3/3 precommits: self(no VE check) + s1(ValidVE) + s3(ValidVE) |
| **22** | **s2 commits v1** | **`decision[s2][1] = v1`, but s1 and s3 still have only 1/3 precommits** |

#### Violation State (State 22)

```
decision = (s1 :> <<Nil, Nil>> @@ s2 :> <<v1, Nil>> @@ s3 :> <<Nil, Nil>>)
precommits[s1][0] = (s1 :> v1 @@ s2 :> Nil @@ s3 :> Nil)   \* 1/3 - NOT quorum
precommits[s2][0] = (s1 :> v1 @@ s2 :> v1 @@ s3 :> v1)     \* 3/3 - quorum (self-skip!)
precommits[s3][0] = (s1 :> Nil @@ s2 :> Nil @@ s3 :> v1)    \* 1/3 - NOT quorum
```

- s2 committed because it counted its own precommit (proposer self-verification skip) plus 2 valid precommits from s1, s3
- s1 and s3 will **never** reach quorum: s2's precommits carry `InvalidVE` and are **dropped** by the VE verification check in `ReceivePrecommit` (state.go:2331-2333)
- Even in subsequent rounds, s2 has advanced to height 2 and its height-1 messages are ignored

#### Root Cause

**Implementation code**: `state.go:2196-2244` (vote extension verification)

The proposer skips `VerifyVoteExtension` on its own precommit vote. When the proposer has an invalid vote extension:

1. **Proposer's view** (`state.go:2413-2423`): Signs precommit with its VE. Self-vote is always accepted (no VE check). Receives others' precommits with `ValidVE` → counts them. Reaches 3/3 → commits.

2. **Others' view** (`state.go:2196-2244`, `state.go:2331-2333`): Receive proposer's precommit, run `VerifyVoteExtension`. VE is invalid → `tryAddVote` returns false → vote is NOT added to vote set. Only see 2/3 precommits → below quorum threshold (need >2/3) → cannot commit.

3. **Permanent deadlock**: Proposer advances to next height. Non-proposer servers are stuck at the old height forever, unable to reach quorum because the proposer's votes are always invalid.

#### Affected Code

- `state.go:2196-2244`: `VerifyVoteExtension` — proposer self-verification skip
- `state.go:2331-2333`: `tryAddVote` — drops votes with invalid VEs
- `state.go:2413-2423`: `signAddVote` — signs precommit with VE (no self-check)
- `execution.go:364-384`: `VerifyVoteExtension` RPC — only receives hash+height+address, not full block context

#### Recommendation

Remove the proposer self-verification skip. All precommit votes, including the proposer's own, should pass `VerifyVoteExtension`. Alternatively, ensure the proposer's VE is always valid before signing.

---

### Bug #2: Nil Precommit Advance Requires Timeout (B6 / Issue #1431)

- **Hypothesis**: MC-3
- **Bug Family**: Family 2 (Liveness / Round Progression)
- **Severity**: High
- **Status**: Known (issue #1431, OPEN)
- **Property violated**: `NilPrecommitAdvance` (temporal, leads-to)
- **Counterexample**: 16 states (file: `counterexample_MC3_NilPrecommitAdvance.out`)

#### Trace Summary

The counterexample demonstrates that after +2/3 nil precommits, the system cannot advance without an explicit timeout:

| State | Action | Key Change |
|-------|--------|------------|
| 1 | Initial | All servers at StepNewHeight, no VE faults |
| 2-5 | s1: EnterNewRound → EnterPropose → EnterPrevote (NilVote) → EnterPrecommitNoPolka (NilVote) | s1 prevotes nil (no proposal received), precommits nil (no polka) |
| 6-8 | s2: EnterNewRound → EnterPrevote (NilVote) → EnterPrecommitNoPolka (NilVote) | s2 also prevotes and precommits nil |
| 9-13 | Message delivery, s3: EnterNewRound → EnterPrevote (NilVote) → EnterPrecommitNoPolka (NilVote) | s3 also prevotes and precommits nil |
| 14-15 | Message delivery | s1 sees 3/3 nil precommits: `{s1:NilVote, s2:NilVote, s3:NilVote}` |
| **16** | **Stuttering** | **System halts — no further progress without timeout** |

#### Violation State (State 15)

```
step = (s1 :> "StepPrecommit" @@ s2 :> "StepPrecommit" @@ s3 :> "StepPrecommit")
precommits[s1][0] = (s1 :> NilVote @@ s2 :> NilVote @@ s3 :> NilVote)  \* 3/3 nil
timeoutScheduled[s1] = {"propose"}  \* Only propose timeout, no precommitWait
```

- `HasPrecommitQuorum(s1, 0, NilVote) = TRUE` — s1 sees +2/3 nil precommits
- But `NilPrecommitAdvance` requires `round[s1] > 0 \/ decision[s1][1] /= Nil` to eventually hold
- The system **stutters**: without a `precommitWait` timeout firing, there is no mechanism to advance to round 1
- The spec correctly models the implementation: advancement requires `EnterPrecommitWait` → `HandleTimeoutPrecommit`

#### Root Cause

**Implementation code**: `state.go:1584-1610` (`enterPrecommitWait`) and `state.go:1018-1022` (precommit timeout handler)

The Tendermint/CometBFT implementation does NOT detect +2/3 nil precommits as a special case for immediate round advancement. Instead, it follows the general path:

1. `enterPrecommitWait` (`state.go:1593-1598`): Requires `HasTwoThirdsAny` to schedule `timeout_precommit`
2. `handleTimeout` (`state.go:1018-1022`): Only fires after `timeout_precommit` expires
3. `enterNewRound` (`state.go:1066`): Advances to next round

The correct behavior (per Tendermint paper) would be to immediately advance to the next round when +2/3 nil precommits are observed, without waiting for the timeout. This adds unnecessary latency to rounds where no block can be committed.

#### Affected Code

- `state.go:1584-1610`: `enterPrecommitWait` — schedules timeout instead of immediate advance
- `state.go:1018-1022`: `handleTimeout` — waits for timeout_precommit to expire
- `state.go:2348-2374`: `addVote` precommit handler — checks `HasTwoThirdsAny` but doesn't check for nil quorum specifically

#### Recommendation

Add a fast path: when +2/3 nil precommits are observed (not just +2/3 "any"), immediately call `enterNewRound(height, round+1)` without scheduling `timeout_precommit`. This preserves the timeout path as a fallback while enabling faster round progression in the common nil-precommit case.

---

## Spec Fixes Applied During Bug Hunting

### Fix 1: NilVote Encoding (Case B — Spec Bug)

**Problem**: The spec used `Nil` for both "not yet voted" and "voted nil" in the prevote/precommit arrays. This made `HasPrecommitTwoThirdsAny` (which checks `/= Nil`) unable to detect nil precommits, causing spurious deadlocks unrelated to the VE bug.

**Fix**: Added `CONSTANT NilVote` to distinguish "voted nil" from "not voted yet":
- `prevotes[i][r][j] = Nil` → server j has not prevoted (from i's perspective)
- `prevotes[i][r][j] = NilVote` → server j prevoted nil
- `precommits[i][r][j] = NilVote` → server j precommitted nil

Updated all nil-vote assignments in: `EnterPrevote`, `HandleTimeoutPropose`, `EnterPrecommitNoPolka`, `EnterPrecommitNilPolka`, `EnterPrecommitUnknownPolka`, quorum checks, temporal properties, and all `.cfg` files.

### Fix 2: ReceivePrecommit VE Verification (Case B — Spec Modeling)

**Problem**: The original spec's `ReceivePrecommit` always added precommit votes regardless of VE verification result. The real implementation drops votes with invalid VEs (`state.go:2331-2333`).

**Fix**: Updated `ReceivePrecommit` to drop precommits when `m.ve /= ValidVE` (for non-self, non-nil precommits). This accurately models the implementation's `tryAddVote` behavior and is required for the VE deadlock (MC-1) to manifest.

### Fix 3: VEConsistency Invariant (Enhancement)

Replaced the placeholder `TRUE` body of `VEConsistency` with a meaningful check: every non-self precommit in a quorum must have been VE-verified as valid. This invariant holds because Fix 2 ensures only valid-VE votes are added.

### Fix 4: CrashRecoveryConsistency Invariant (Case A — Invariant Bug)

**Problem**: The invariant used `\A v \in Values \cup {Nil} : prevotes[s][r][s] = v \/ v = Nil` which requires the prevote to equal ALL values simultaneously — unsatisfiable when `|Values| > 1`. Also did not account for `NilVote` constant.

**Fix**: Rewrote to check that all cast prevotes and precommits are legitimate values (`\in Values \cup {NilVote}`). Verified with 366M states (BFS, MC_hunt_ve_crash_targeted.cfg) — invariant holds.

---

## Not Reproduced

| ID | Hypothesis | States Checked | Notes |
|----|-----------|----------------|-------|
| MC-2 | Late precommits during timeout_commit have unverified VEs | N/A | **Not testable**: Spec does not model `timeout_commit` or `LastCommit` reuse across heights. Would require extending the spec with a cross-height vote propagation model. Corresponds to B15/#2361. |
| MC-4 | Prevotes arriving before proposal under Byzantine strategy | 152M (4-server sim) + 66K (3-server sim) | No specific invariant violation. The spec already handles async message delivery correctly. Prevotes before proposals simply result in nil prevotes (timeout path), which is the expected behavior. |
| MC-5 | Crash between privval signing and WAL WriteSync | N/A | **Not testable**: Spec's `signAddVote` is atomic (sign + WAL write + send in one action). Reproducing this requires splitting into sub-steps with crash points between them. |
| MC-6 | Crash after Commit but before evpool.Update | N/A | **Not testable**: Evidence lifecycle in the spec is trivial (single-step add/commit). The real implementation's multi-step evidence processing is not modeled. |
| MC-7 | POLRound >= Round in proposal | 152M + 66K + 19.6M | `POLRoundValidity` holds. The spec's `EnterPropose` correctly sets `polRound < round` (from `validRound`). All 5 enterPrecommit paths preserve locking invariant. |
| MC-8 | All 5 enterPrecommit paths preserve locking invariant | 152M + 66K + 19.6M | `LockSafety` holds across all configurations including 4-server, MaxRound=3. The 5 precommit paths (NoPolka, NilPolka, RelockPolka, NewLockPolka, UnknownPolka) correctly maintain lock consistency. |
| MC-9 | Crash after block save but before EndHeightMessage | N/A | **Not testable**: Same as MC-5 — `FinalizeCommit` is atomic in the spec. Would need sub-step crash modeling. |
| MC-10 | Round skip on +2/3 any precommits with concurrent height advance | 152M + 66K + 19.6M | `ElectionSafety` holds. The round-skip mechanism (`RoundSkipPrecommit`) correctly handles concurrent height advances. No safety violation found even with 4 servers and MaxRound=3. |
