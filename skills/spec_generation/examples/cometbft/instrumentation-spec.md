# Instrumentation Spec: CometBFT Consensus

Maps TLA+ spec actions to source code locations for trace generation.

## Section 1: Trace Event Schema

### Event Envelope

```json
{
  "tag": "trace",
  "timestamp": "<ISO8601>",
  "event": {
    "name": "<action_name>",
    "nid": "<server_id>",
    "state": {
      "height": <int>,
      "round": <int>,
      "step": "<StepName>",
      "lockedRound": <int>,
      "lockedValue": "<value_or_nil>",
      "validRound": <int>,
      "validValue": "<value_or_nil>"
    },
    "msg": {  // optional, for message events
      "source": "<sender_id>",
      "dest": "<receiver_id>",
      "type": "<msg_type>",
      "value": "<value_or_nil>",
      "round": <int>,
      "ve": "<vote_extension_value>"
    }
  }
}
```

### State Fields

| Implementation Field | TLA+ Variable | Access Method |
|---------------------|---------------|---------------|
| `cs.Height` | `height` | `RoundState.Height` |
| `cs.Round` | `round` | `RoundState.Round` |
| `cs.Step` | `step` | `RoundState.Step.String()` |
| `cs.LockedRound` | `lockedRound` | `RoundState.LockedRound` |
| `cs.LockedBlock.Hash()` | `lockedValue` | `RoundState.LockedBlock.Hash().String()` or `"nil"` |
| `cs.ValidRound` | `validRound` | `RoundState.ValidRound` |
| `cs.ValidBlock.Hash()` | `validValue` | `RoundState.ValidBlock.Hash().String()` or `"nil"` |

### Message Fields

| Implementation Field | TLA+ Field | Notes |
|---------------------|------------|-------|
| `vote.ValidatorAddress` | `msg.source` | Hex-encoded address |
| `proposal.Signature signer` | `msg.source` | Proposer address |
| Receiving node | `msg.dest` | Node emitting the event |
| `vote.BlockID.Hash` | `msg.value` | Hex or `"nil"` for nil votes |
| `vote.Round` | `msg.round` | Vote round |
| `vote.Extension` | `msg.ve` | Base64 or `"NoVE"` for nil precommits |

## Section 2: Action-to-Code Mapping

### 1. EnterNewRound

- **Spec action**: `EnterNewRound(i, r)`
- **Code location**: `consensus/state.go:1066-1131`
- **Trigger point**: After step transition at line 1114 (`cs.Step = RoundStepNewRound`)
- **Trace event name**: `"EnterNewRound"`
- **Fields**: State snapshot (height, round, step)
- **Notes**: Fires after validators updated (line 1084-1088). Round 0 may be delayed by `CreateEmptyBlocksInterval`.

### 2. EnterPropose

- **Spec action**: `EnterPropose(i)`
- **Code location**: `consensus/state.go:1157-1214`
- **Trigger point**: After step transition at line 1172 (`cs.Step = RoundStepPropose`)
- **Trace event name**: `"EnterPropose"`
- **Fields**: State snapshot
- **Notes**: If proposer, `defaultDecideProposal` (line 1209) creates proposal before this event. Capture after step set but before proposal broadcast.

### 3. ReceiveProposal

- **Spec action**: `ReceiveProposal(i, m)`
- **Code location**: `consensus/state.go:1920-1967` (`defaultSetProposal`)
- **Trigger point**: After proposal accepted at line 1957 (`cs.Proposal = proposal`)
- **Trace event name**: `"ReceiveProposal"`
- **Fields**: State snapshot + msg (source=proposer, value=proposal block hash, round=proposal.Round, polRound=proposal.POLRound)
- **Notes**: Proposals rejected by validation (lines 1932-1953) should NOT emit events. Only emit on successful acceptance.

### 4. EnterPrevote

- **Spec action**: `EnterPrevote(i)`
- **Code location**: `consensus/state.go:1334-1360` (enterPrevote) + `1362-1420` (defaultDoPrevote)
- **Trigger point**: After step transition at line 1345 (`cs.Step = RoundStepPrevote`), after `signAddVote` returns
- **Trace event name**: `"EnterPrevote"`
- **Fields**: State snapshot + msg (source=self, value=prevoted block hash or nil)
- **Notes**: The vote value depends on which of the 5 paths in `defaultDoPrevote` was taken. Capture the actual vote sent.

### 5. ReceivePrevote

- **Spec action**: `ReceivePrevote(i, m)`
- **Code location**: `consensus/state.go:2269-2346` (addVote prevote handler)
- **Trigger point**: After vote added at line 2246 (`cs.Votes.AddVote`)
- **Trace event name**: `"ReceivePrevote"`
- **Fields**: State snapshot + msg (source=vote sender, dest=self, value=vote value, round=vote round)
- **Notes**: Must capture lock/unlock changes. If unlock occurs (lines 2279-2290), the state snapshot will show updated lockedRound/lockedValue. If ValidBlock updated (lines 2299-2310), show updated validRound/validValue.

### 6. EnterPrevoteWait

- **Spec action**: `EnterPrevoteWait(i)`
- **Code location**: `consensus/state.go:1423-1440`
- **Trigger point**: After step transition at line 1445 (`cs.Step = RoundStepPrevoteWait`)
- **Trace event name**: `"EnterPrevoteWait"`
- **Fields**: State snapshot
- **Notes**: Only entered when `HasTwoThirdsAny()` prevotes. Panic at line 1434 if precondition fails.

### 7. EnterPrecommit (5 paths)

- **Spec actions**: `EnterPrecommitNoPolka`, `EnterPrecommitNilPolka`, `EnterPrecommitRelockPolka`, `EnterPrecommitNewLockPolka`, `EnterPrecommitUnknownPolka`
- **Code location**: `consensus/state.go:1459-1578`
- **Trigger point**: After step transition and precommit vote sent
- **Trace event name**: `"EnterPrecommit"`
- **Fields**: State snapshot (including updated lock state) + msg (source=self, value=precommit value, ve=vote extension)
- **Notes**:
  - All 5 paths emit the same event name. The trace spec disambiguates by checking post-state lock values.
  - Path 1 (no polka, line 1479): lockedRound unchanged, precommit nil
  - Path 2 (nil polka, line 1505): lockedRound=-1, lockedValue=nil, precommit nil
  - Path 3 (relock, line 1525): lockedRound=current round, lockedValue=same block, precommit block
  - Path 4 (new lock, line 1538): lockedRound=current round, lockedValue=NEW block, precommit block
  - Path 5 (unknown, line 1559): lockedRound=-1, lockedValue=nil, precommit nil
  - Vote extensions attached only for non-nil precommits (state.go:2413-2423, Family 1)

### 8. ReceivePrecommit

- **Spec action**: `ReceivePrecommit(i, m)`
- **Code location**: `consensus/state.go:2348-2374` (addVote precommit handler)
- **Trigger point**: After vote added at line 2246
- **Trace event name**: `"ReceivePrecommit"`
- **Fields**: State snapshot + msg (source=vote sender, dest=self, value=vote value, round=vote round, ve=vote extension)
- **Notes**: VE verification happens at lines 2196-2244 BEFORE vote addition. Capture `veVerified` status in event. Proposer skips self-verification (Bug #5204).

### 9. EnterPrecommitWait

- **Spec action**: `EnterPrecommitWait(i)`
- **Code location**: `consensus/state.go:1584-1610`
- **Trigger point**: After `TriggeredTimeoutPrecommit = true` at line 1604
- **Trace event name**: `"EnterPrecommitWait"`
- **Fields**: State snapshot
- **Notes**: Precondition: `HasTwoThirdsAny()` precommits (line 1593). Only fires once per round due to `TriggeredTimeoutPrecommit` flag.

### 10. HandleTimeoutPropose

- **Spec action**: `HandleTimeoutPropose(i)`
- **Code location**: `consensus/state.go:1003-1009` (handleTimeout, RoundStepPropose case)
- **Trigger point**: After timeout handler fires, after prevote sent
- **Trace event name**: `"HandleTimeoutPropose"`
- **Fields**: State snapshot
- **Notes**: Triggers `enterPrevote(height, round)` which prevotes nil.

### 11. HandleTimeoutPrevote

- **Spec action**: `HandleTimeoutPrevote(i)`
- **Code location**: `consensus/state.go:1011-1016` (handleTimeout, RoundStepPrevoteWait case)
- **Trigger point**: After timeout handler fires
- **Trace event name**: `"HandleTimeoutPrevote"`
- **Fields**: State snapshot
- **Notes**: Triggers `enterPrecommit(height, round)`.

### 12. HandleTimeoutPrecommit

- **Spec action**: `HandleTimeoutPrecommit(i)`
- **Code location**: `consensus/state.go:1018-1022` (handleTimeout, RoundStepPrecommitWait case)
- **Trigger point**: After timeout handler fires, after entering new round
- **Trace event name**: `"HandleTimeoutPrecommit"`
- **Fields**: State snapshot (new round/step after advancement)
- **Notes**: Triggers `enterNewRound(height, round+1)`. Family 2: Bug #1431 — +2/3 nil precommits should advance immediately but implementation waits for this timeout.

### 13. EnterCommit

- **Spec action**: `EnterCommit(i)`
- **Code location**: `consensus/state.go:1620-1673`
- **Trigger point**: After step transition at line 1629 (`cs.Step = RoundStepCommit`)
- **Trace event name**: `"EnterCommit"`
- **Fields**: State snapshot + decision value
- **Notes**: `CommitRound` set at line 1630. Block may not be available yet (lines 1652-1671).

### 14. FinalizeCommit

- **Spec action**: `FinalizeCommit(i)`
- **Code location**: `consensus/state.go:1704-1827`
- **Trigger point**: After `updateToState` at line 1800 (height incremented)
- **Trace event name**: `"FinalizeCommit"`
- **Fields**: State snapshot (new height, round=0, step=NewHeight)
- **Notes**:
  - 4 crash points: lines 1744, 1761, 1784, 1812 (Family 3)
  - Evidence in block marked as committed during `blockExec.ApplyVerifiedBlock` (Family 4)
  - EndHeightMessage written to WAL at line 1776 (Family 3)

### 15. RoundSkip

- **Spec actions**: `RoundSkipPrevote(i)`, `RoundSkipPrecommit(i)`
- **Code locations**:
  - Prevote: `consensus/state.go:2329-2331` (addVote prevote handler, +2/3 any)
  - Precommit: `consensus/state.go:2371-2373` (addVote precommit handler, +2/3 any)
- **Trigger point**: After `enterNewRound` called from addVote
- **Trace event name**: `"RoundSkip"`
- **Fields**: State snapshot (new round)
- **Notes**: Family 2: round synchronization mechanism. May be triggered by either prevote or precommit +2/3 any detection.

### 16. Crash

- **Spec action**: `Crash(i)`
- **Code location**: N/A (external event — process kill or panic)
- **Trigger point**: Detected by peer via connection loss, or injected via `fail.Fail()` points
- **Trace event name**: `"Crash"`
- **Fields**: Node ID only
- **Notes**: Family 3. WAL may lose last async entry. 6 crash injection points in `finalizeCommit` (state.go:862, 1744, 1761, 1784, 1804, 1812) and 4 in `applyBlock` (execution.go:264, 271, 306, 314).

### 17. Recover

- **Spec action**: `Recover(i)`
- **Code location**: `consensus/replay.go:93-170` (catchupReplay) + `replay.go:240-470` (ReplayBlocks)
- **Trigger point**: After WAL replay completes and consensus restarts
- **Trace event name**: `"Recover"`
- **Fields**: State snapshot (recovered height, round=0)
- **Notes**: Family 3. Recovery uses EndHeightMessage as boundary. ABCI Handshake determines recovery strategy (replay.go:416-470).

## Section 3: Special Considerations

### 3.1 Vote Extensions (Family 1)

- **ExtendVote** is called inside `signVote` (state.go:2413-2423) only for precommit + non-nil block
- **VerifyVoteExtension** is called inside `addVote` (state.go:2196-2244) for remote precommits on non-nil blocks
- The asymmetry: `ExtendVote` receives full block context (txs, last commit, misbehavior) but `VerifyVoteExtension` only gets hash+height+address
- **Bug #5204**: Proposer does NOT call `VerifyVoteExtension` on its own VE. If >1/3 produce invalid VEs, other validators reject them but proposer counts its own, potentially causing deadlock.
- Instrumentation should capture both the VE value attached and the verification result.

### 3.2 Concurrent Goroutines

- Only `receiveRoutine` modifies `RoundState` (single-writer design)
- All input arrives via channels: `peerMsgQueue`, `internalMsgQueue`, `timeoutTicker`
- Trace events should be emitted from within `receiveRoutine` to maintain causal ordering
- Gossip goroutines (`gossipDataRoutine`, `gossipVotesRoutine`) read snapshots with TOCTOU races — do NOT instrument these for trace events

### 3.3 WAL Interaction (Family 3)

- `WriteSync` (fsync) used for own votes: state.go:849
- `Write` (async) used for peer messages and timeouts: state.go:838, 869
- On crash, async writes may be lost but sync writes survive
- Instrumentation should NOT emit trace events for WAL writes themselves — WAL state is modeled implicitly

### 3.4 Evidence Pool (Family 4)

- `ReportConflictingVotes` buffers evidence until next `Update` call (pool.go:181-188)
- `processConsensusBuffer` runs during `Update` (pool.go:461-538), not during consensus
- Evidence detection events should be emitted from `processConsensusBuffer`, not `ReportConflictingVotes`
- `CheckEvidence` (pool.go:194-232) validates evidence in proposed blocks — emit event for evidence verification failures

### 3.5 Bootstrap / Initial State

- Consensus starts at `height = state.LastBlockHeight + 1`
- Initial `round = 0`, `step = NewHeight`
- `lockedRound = -1`, `validRound = -1`
- All vote maps empty
- If recovering from state sync, initial height may differ from 1

### 3.6 Serialization Quirks

- Block hashes are hex-encoded strings; use consistent encoding
- Nil votes: `BlockID.Hash` is empty bytes, serialize as `"nil"` or `""`
- Vote extensions: base64-encode the raw bytes; `"NoVE"` for nil precommits
- Proposal `POLRound`: -1 when no POL, serialize as integer
- Server IDs: use validator address (hex) as the node identifier for trace events
