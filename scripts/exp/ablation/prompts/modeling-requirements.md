# Modeling Requirements

These are the mandatory core actions that must be modeled for each system.
This ensures fair comparison across different agent configurations.

## etcd-raft

**Mandatory core actions:**
- Leader election (Timeout, RequestVote, BecomeLeader)
- Log replication (AppendEntries, commit advancement)
- Heartbeat protocol (SendHeartbeat, HandleHeartbeat)
- ReadIndex / linearizable reads
- Crash and recovery

**Actions that may be excluded:**
- Snapshot / log compaction
- Membership changes (joint consensus)

## autobahn

**Mandatory core actions:**
- 3-phase consensus: Prepare, Confirm, Commit
- Fast path (3f+1 unanimous PrepareQC skips Confirm)
- View change via Timeout Certificate (TC)
- Byzantine fault actions (at least: Byzantine Prepare, Byzantine Commit)
- Message loss

**Actions that may be excluded:**
- Parallel slot management (K concurrent slots)
- Garbage collection

## libgomp

**Mandatory core actions:**
- Barrier phases: arrive (secondary + primary), release, exit
- Task scheduling: CreateTask, ExecuteTask
- Task lock acquire/release (HandleTasks_AcquireLock, HandleTasks_ReleaseLock)
- Cancellation (BAR_CANCELLED flag)
- BAR_TASK_PENDING and BAR_WAITING_FOR_TASK flags
- EnsureLast (primary check)

**Actions that may be excluded:**
- Memory ordering details (acquire/release semantics)
- Multiple barrier types (centralized vs flat)
