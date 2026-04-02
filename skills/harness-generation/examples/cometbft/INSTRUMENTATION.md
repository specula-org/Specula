# CometBFT Consensus Instrumentation Guide

Guide for adjusting instrumentation during trace validation (Phase 3).

## Instrumented Files

All instrumentation is in the CometBFT consensus package:

| File | Description |
|------|-------------|
| `consensus/trace_emit.go` | Trace module: `TraceLogger`, `TraceEvent`, `captureState()` |
| `consensus/state.go` | 15 emit points inserted into the consensus state machine |
| `consensus/scenario_trace_test.go` | Test scenarios that generate traces |

## Trace Module (`trace_emit.go`)

- **`TraceLogger`**: Thread-safe NDJSON writer with `Emit(*TraceEvent)` method
- **`captureState()`**: Snapshots `height`, `round`, `step`, `lockedRound`, `lockedValue`, `validRound`, `validValue` from `cs.RoundState`
- **`traceNodeID()`**: Returns hex-encoded validator address
- **`stepString()`**: Maps `RoundStepType` to TLA+ step names (`"NewHeight"`, `"Propose"`, etc.)
- **`blockHashStr()`**: Hex-encodes block hash, returns `"nil"` for empty

The logger is set on `cs.traceLogger` (field at `state.go:141`) via `cs.SetTraceLogger(tl)` (line 229).

## Instrumentation Points in `state.go`

| Line | Event Name | Trigger |
|------|-----------|---------|
| 1016 | `HandleTimeoutPropose` | After timeout handler, RoundStepPropose case |
| 1030 | `HandleTimeoutPrevote` | After timeout handler, RoundStepPrevoteWait case |
| 1044 | `HandleTimeoutPrecommit` | After timeout handler, RoundStepPrecommitWait case |
| 1148 | `EnterNewRound` | After `cs.Step = RoundStepNewRound` |
| 1213 | `EnterPropose` | After `cs.Step = RoundStepPropose` |
| 1397 | `EnterPrevote` | After step transition + `signAddVote` |
| 1500 | `EnterPrecommit` | After step transition + precommit vote sent |
| 1536 | `EnterPrecommit` | (alternate path — nil polka) |
| 1673 | `EnterPrecommitWait` | After `TriggeredTimeoutPrecommit = true` |
| 1707 | `EnterCommit` | After `cs.Step = RoundStepCommit` |
| 1908 | `FinalizeCommit` | After `updateToState` (height incremented) |
| 2054 | `ReceiveProposal` | After `cs.Proposal = proposal` accepted |
| 2371 | `ReceivePrevote` | After `cs.Votes.AddVote` for prevote |
| 2383 | `ReceivePrecommit` | After `cs.Votes.AddVote` for precommit |

## Post-Processing

Traces require post-processing before TLA+ validation:

```bash
python3 harness/preprocess_trace.py < traces/raw.ndjson > traces/mapped.ndjson
```

The script (`preprocess_trace.py`):
- Maps hex validator addresses → `s1`, `s2`, `s3`
- Maps hex block hashes → `v1`, `v2`, ...
- Preserves event structure

## How to Add a New Field

1. Add field to `TraceStateSnap` or `TraceMsgFields` struct in `trace_emit.go`
2. Populate it in `captureState()` or at the emit call site in `state.go`
3. Rebuild: `cd artifact/cometbft && go build ./consensus/...`

## How to Add a New Event

1. Find the code location in `instrumentation-spec.md`
2. Add `cs.traceLogger.Emit(&TraceEvent{...})` with `captureState()` call
3. Rebuild and re-run tests

## How to Move a Capture Point

All events capture state via `cs.captureState()` which reads from `cs.RoundState`. Moving an emit call before/after a state mutation changes what the snapshot contains. Key state mutations:
- `cs.Step = ...` (step transitions)
- `cs.LockedRound = ...` / `cs.LockedBlock = ...` (lock changes in enterPrecommit)
- `cs.ValidRound = ...` / `cs.ValidBlock = ...` (valid block updates in addVote)

## Rebuild and Re-run

```bash
cd artifact/cometbft
go test -v -run "TestScenario(BasicConsensus|TimeoutPropose|LockAndRelock|TwoHeights)" \
  -timeout 120s ./consensus/
```

Then post-process:
```bash
python3 harness/preprocess_trace.py < traces/basic_consensus.ndjson > traces/basic_consensus_mapped.ndjson
```
