---------- MODULE MC ----------
\* Model Checking Spec for brpc/braft.
\*
\* Wraps the base spec with counter-bounded actions for
\* exhaustive state-space exploration via TLC.
\*
\* Scenarios covered:
\*   - PreVote + real election with two-sided lease (Bug Family 1)
\*   - Snapshot response without term check (Bug Family 2)
\*   - Crash / recovery with RPCs-before-persist (Bug Family 3)
\*   - Joint consensus configuration changes (Bug Family 4)
\*   - Unreliable network (message loss)

EXTENDS base

\* Access original (un-overridden) operator definitions.
B == INSTANCE base

\* ============================================================================
\* CONSTRAINT CONSTANTS
\* ============================================================================

CONSTANT MaxTermLimit
ASSUME MaxTermLimit \in Nat

CONSTANT MaxPreVoteLimit
ASSUME MaxPreVoteLimit \in Nat

CONSTANT MaxTimeoutLimit
ASSUME MaxTimeoutLimit \in Nat

CONSTANT RequestLimit
ASSUME RequestLimit \in Nat

CONSTANT CrashLimit
ASSUME CrashLimit \in Nat

CONSTANT LoseLimit
ASSUME LoseLimit \in Nat

CONSTANT HeartbeatLimit
ASSUME HeartbeatLimit \in Nat

CONSTANT SnapshotLimit
ASSUME SnapshotLimit \in Nat

CONSTANT ConfigChangeLimit
ASSUME ConfigChangeLimit \in Nat

CONSTANT LeaseExpireLimit
ASSUME LeaseExpireLimit \in Nat

CONSTANT MaxMsgBufferLimit
ASSUME MaxMsgBufferLimit \in Nat

\* ============================================================================
\* CONSTRAINT VARIABLES
\* ============================================================================

VARIABLE constraintCounters

faultVars == <<constraintCounters>>

\* ============================================================================
\* MODEL CHECKING CONSTRAINED ACTIONS
\* ============================================================================

\* --- PreVote Constraints (Bug Family 1) ---
MCPreVote(i) ==
    /\ constraintCounters.preVote < MaxPreVoteLimit
    /\ B!PreVote(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.preVote = @ + 1]

\* --- Election Constraints ---
MCElectSelf(i) ==
    /\ currentTerm[i] < MaxTermLimit
    /\ constraintCounters.timeout < MaxTimeoutLimit
    /\ B!ElectSelf(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.timeout = @ + 1]

\* --- Client Request Constraints ---
MCClientRequest(i) ==
    /\ constraintCounters.request < RequestLimit
    /\ B!ClientRequest(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.request = @ + 1]

\* --- Crash Constraints ---
MCCrash(i) ==
    /\ constraintCounters.crash < CrashLimit
    /\ B!Crash(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.crash = @ + 1]

\* --- Message Loss Constraints ---
MCLoseMessage(m) ==
    /\ constraintCounters.lose < LoseLimit
    /\ B!LoseMessage(m)
    /\ constraintCounters' = [constraintCounters EXCEPT !.lose = @ + 1]

\* --- Heartbeat Constraints ---
MCSendHeartbeat(i, j) ==
    /\ constraintCounters.heartbeat < HeartbeatLimit
    /\ B!SendHeartbeat(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.heartbeat = @ + 1]

\* --- Snapshot Constraints (Bug Family 2) ---
MCSendInstallSnapshot(i, j) ==
    /\ constraintCounters.snapshot < SnapshotLimit
    /\ B!SendInstallSnapshot(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.snapshot = @ + 1]

\* --- Config Change Constraints (Bug Family 4) ---
MCProposeConfigChange(i, s) ==
    /\ constraintCounters.configChange < ConfigChangeLimit
    /\ B!ProposeConfigChange(i, s)
    /\ constraintCounters' = [constraintCounters EXCEPT !.configChange = @ + 1]

\* --- Follower Lease Expire Constraints (Bug Family 1) ---
MCFollowerLeaseExpire(i) ==
    /\ constraintCounters.leaseExpire < LeaseExpireLimit
    /\ B!FollowerLeaseExpire(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.leaseExpire = @ + 1]

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

MCInit ==
    /\ Init
    /\ constraintCounters = [
         preVote      |-> 0,
         timeout      |-> 0,
         request      |-> 0,
         crash        |-> 0,
         lose         |-> 0,
         heartbeat    |-> 0,
         snapshot     |-> 0,
         configChange |-> 0,
         leaseExpire  |-> 0]

\* ============================================================================
\* NEXT STATE RELATIONS
\* ============================================================================

MCNextAsync(i) ==
    \* --- PreVote (Bug Family 1) ---
    \/ MCPreVote(i)
    \* --- Elections ---
    \/ MCElectSelf(i)
    \/ /\ B!CompletePersistElectSelf(i)
       /\ UNCHANGED faultVars
    \/ /\ B!BecomeLeader(i)
       /\ UNCHANGED faultVars
    \* --- Client requests ---
    \/ MCClientRequest(i)
    \* --- Leader lease ---
    \/ /\ B!CheckLeaderLease(i)
       /\ UNCHANGED faultVars
    \/ MCFollowerLeaseExpire(i)
    \* --- Commit advancement ---
    \/ /\ B!AdvanceCommitIndex(i)
       /\ UNCHANGED faultVars
    \* --- Log replication ---
    \/ /\ \E j \in Server : B!ReplicateEntries(i, j)
       /\ UNCHANGED faultVars
    \* --- Heartbeats ---
    \/ \E j \in Server : MCSendHeartbeat(i, j)
    \* --- Snapshots (Bug Family 2) ---
    \/ \E j \in Server : MCSendInstallSnapshot(i, j)

MCNextMsg ==
    \E m \in DOMAIN messages :
        /\ m.mdest \in Server
        /\ \/ /\ B!HandlePreVoteRequest(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandlePreVoteResponse(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleRequestVoteRequest(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleRequestVoteResponse(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleAppendEntriesRequest(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleReplicateResponse(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleHeartbeatResponse(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleInstallSnapshotRequest(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!HandleInstallSnapshotResponse(m.mdest, m)
              /\ UNCHANGED faultVars
           \/ /\ B!DropStaleMessage(m)
              /\ UNCHANGED faultVars

MCNextCrash == \E i \in Server : MCCrash(i)

MCNextUnreliable ==
    \E m \in DOMAIN messages : MCLoseMessage(m)

MCNextConfigChange ==
    \E i, s \in Server : MCProposeConfigChange(i, s)

\* --- Combined Next variants ---

\* Base: no config changes
MCNext ==
    \/ \E i \in Server :
        \/ MCPreVote(i)
        \/ MCElectSelf(i)
        \/ /\ B!CompletePersistElectSelf(i)
           /\ UNCHANGED faultVars
        \/ /\ B!BecomeLeader(i)
           /\ UNCHANGED faultVars
        \/ MCClientRequest(i)
        \/ /\ B!CheckLeaderLease(i)
           /\ UNCHANGED faultVars
        \/ MCFollowerLeaseExpire(i)
        \/ /\ B!AdvanceCommitIndex(i)
           /\ UNCHANGED faultVars
        \/ /\ \E j \in Server : B!ReplicateEntries(i, j)
           /\ UNCHANGED faultVars
        \/ \E j \in Server : MCSendHeartbeat(i, j)
        \/ \E j \in Server : MCSendInstallSnapshot(i, j)
    \/ MCNextMsg
    \/ MCNextCrash
    \/ MCNextUnreliable

\* Dynamic: with config changes
MCNextDynamic ==
    \/ MCNext
    \/ MCNextConfigChange

\* ============================================================================
\* SPECIFICATIONS
\* ============================================================================

mc_vars == <<vars, faultVars>>

MCSpec ==
    /\ MCInit
    /\ [][MCNext]_mc_vars

MCSpecDynamic ==
    /\ MCInit
    /\ [][MCNextDynamic]_mc_vars

\* ============================================================================
\* SYMMETRY AND VIEW DEFINITIONS
\* ============================================================================

Symmetry == Permutations(Server)

ModelView == <<vars>>

\* ============================================================================
\* STATE SPACE PRUNING CONSTRAINTS
\* ============================================================================

MsgBufferConstraint ==
    \/ MaxMsgBufferLimit = 0
    \/ BagCardinality(messages) <= MaxMsgBufferLimit

\* ============================================================================
\* SAFETY INVARIANTS
\* ============================================================================

\* Persisted term is always <= in-memory term.
PersistedTermConsistencyInv ==
    \A i \in Server : persistedTerm[i] <= currentTerm[i]

\* Commit index never exceeds log length.
CommitIndexBoundInv ==
    \A i \in Server : commitIndex[i] <= LastLogIndex(i)

\* Candidates always voted for themselves.
CandidateVotedForSelfInv ==
    \A i \in Server : state[i] = Candidate => votedFor[i] = i

\* Leaders always have a positive term.
LeaderTermPositiveInv ==
    \A i \in Server : state[i] = Leader => currentTerm[i] > 0

\* Pending persist only exists for candidates.
PendingPersistStateInv ==
    \A i \in Server : pendingPersist[i] = TRUE => state[i] = Candidate

\* Config is always a non-empty subset of Server.
ConfigValidInv ==
    \A i \in Server :
        /\ config[i] /= {}
        /\ config[i] \subseteq Server

\* A leader's log contains all committed entries from all servers.
LeaderLogCompleteness ==
    \A s1, s2 \in Server :
        (state[s1] = Leader /\ commitIndex[s2] > 0) =>
            \A idx \in 1..commitIndex[s2] :
                /\ idx <= LastLogIndex(s1)
                /\ log[s1][idx] = log[s2][idx]

\* ============================================================================
\* BUG FAMILY 3: PERSIST WINDOW DETECTION
\* ============================================================================

\* Detect orphaned election RPCs: a RequestVoteRequest is in flight from
\* server i at term T, but i's currentTerm < T (crashed after ElectSelf
\* before persist completed).
NoOrphanedElectionRPCs ==
    \A m \in DOMAIN messages :
        m.mtype = RequestVoteRequest =>
            currentTerm[m.msource] >= m.mterm

\* Stronger: detect when a crashed-and-recovered node has voted for
\* a DIFFERENT candidate at the same term as its orphaned RPCs.
\* This is the "double vote" that Bug Family 3 enables.
NoDualVoteFromCrash ==
    \A m \in DOMAIN messages :
        /\ m.mtype = RequestVoteRequest
        /\ currentTerm[m.msource] = m.mterm
        => votedFor[m.msource] = m.msource

\* ============================================================================
\* TEMPORAL PROPERTIES
\* ============================================================================

\* Commit index never decreases (except after Crash).
MonotonicCommitIndexProp ==
    [][(~\E i \in Server : B!Crash(i)) =>
        \A i \in Server : commitIndex'[i] >= commitIndex[i]]_mc_vars

\* Term never decreases (except after Crash).
MonotonicTermProp ==
    [][(~\E i \in Server : B!Crash(i)) =>
        \A i \in Server : currentTerm'[i] >= currentTerm[i]]_mc_vars

\* Leader only appends to its log, never truncates.
LeaderAppendOnlyProp ==
    [][
        \A i \in Server :
            (state[i] = Leader /\ state'[i] = Leader) =>
                /\ Len(log'[i]) >= Len(log[i])
                /\ SubSeq(log'[i], 1, Len(log[i])) =
                   SubSeq(log[i], 1, Len(log[i]))
    ]_mc_vars

\* Leader only commits entries from its current term.
LeaderCommitCurrentTermLogsProp ==
    [][
        \A i \in Server :
            (state'[i] = Leader /\ commitIndex[i] /= commitIndex'[i]) =>
                log'[i][commitIndex'[i]].term = currentTerm'[i]
    ]_mc_vars

=============================================================================
