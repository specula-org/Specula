---------- MODULE MCetcdraft ----------
\* Model Checking Spec for etcdraft with combined scenarios:
\* - Error scenarios (crashes, unreliable network)
\* - Snapshots and log compaction
\* - Configuration changes

EXTENDS etcdraft

\* ============================================================================
\* CONSTRAINT CONSTANTS
\* ============================================================================

\* Model value for client requests
CONSTANT Value

\* Config change limits
CONSTANT ReconfigurationLimit
ASSUME ReconfigurationLimit \in Nat

\* Term limits (prevents infinite state space from repeated elections)
CONSTANT MaxTermLimit
ASSUME MaxTermLimit \in Nat

\* Client request limits
CONSTANT RequestLimit
ASSUME RequestLimit \in Nat

\* Fault injection limits
CONSTANT RestartLimit
ASSUME RestartLimit \in Nat

CONSTANT DropLimit
ASSUME DropLimit \in Nat

CONSTANT DuplicateLimit
ASSUME DuplicateLimit \in Nat

CONSTANT StepDownLimit
ASSUME StepDownLimit \in Nat

CONSTANT HeartbeatLimit
ASSUME HeartbeatLimit \in Nat

CONSTANT MaxTimeoutLimit
ASSUME MaxTimeoutLimit \in Nat

\* Snapshot-specific limits
CONSTANT SnapshotLimit
ASSUME SnapshotLimit \in Nat

CONSTANT CompactLimit
ASSUME CompactLimit \in Nat

\* Config change limits (for ChangeConf/ChangeConfAndSend)
CONSTANT ConfChangeLimit
ASSUME ConfChangeLimit \in Nat

\* ReportUnreachable limit
CONSTANT ReportUnreachableLimit
ASSUME ReportUnreachableLimit \in Nat

\* Message buffer limit for state space pruning
CONSTANT MaxMsgBufferLimit
ASSUME MaxMsgBufferLimit \in Nat

\* Pending messages buffer limit for state space pruning
CONSTANT MaxPendingMsgLimit
ASSUME MaxPendingMsgLimit \in Nat

\* Network partition limits
CONSTANT PartitionLimit  \* Maximum number of partition/heal cycles
ASSUME PartitionLimit \in Nat

\* ============================================================================
\* CONSTRAINT VARIABLES
\* ============================================================================

\* Counters for fault injection events (aggregated in a record for easier View definition)
VARIABLE constraintCounters

faultVars == <<constraintCounters>>

etcd == INSTANCE etcdraft

\* ============================================================================
\* ETCD BOOTSTRAP INITIALIZATION
\* ============================================================================

\* Application uses Node (instead of RawNode) will have multiple ConfigEntry entries appended to log in bootstrapping.
BootstrapLog ==
    LET prevConf(y) == IF Len(y) = 0 THEN {} ELSE y[Len(y)].value.newconf
    IN FoldSeq(LAMBDA x, y: Append(y, [ term  |-> 1, type |-> ConfigEntry, value |-> [ newconf |-> prevConf(y) \union {x}, learners |-> {} ] ]), <<>>, SetToSeq(InitServer))

\* etcd is bootstrapped in two ways.
\* 1. bootstrap a cluster for the first time: server vars are initialized with term 1 and pre-inserted log entries for initial configuration.
\* 2. adding a new member: server vars are initialized with all state 0
\* 3. restarting an existing member: all states are loaded from durable storage
etcdInitServerVars == /\ currentTerm = [i \in Server |-> IF i \in InitServer THEN 1 ELSE 0]
                      /\ state       = [i \in Server |-> Follower]
                      /\ votedFor    = [i \in Server |-> Nil]

\* Adapted for offset-based log with historyLog
etcdInitLogVars == /\ log = [i \in Server |-> IF i \in InitServer
                                              THEN [offset |-> 1, entries |-> BootstrapLog, snapshotIndex |-> 0, snapshotTerm |-> 0]
                                              ELSE [offset |-> 1, entries |-> <<>>, snapshotIndex |-> 0, snapshotTerm |-> 0]]
                   /\ historyLog = [i \in Server |-> IF i \in InitServer THEN BootstrapLog ELSE <<>>]
                   /\ commitIndex = [i \in Server |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0]
                   /\ applied = [i \in Server |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0]

etcdInitConfigVars == /\ config = [i \in Server |-> [ jointConfig |-> IF i \in InitServer THEN <<InitServer, {}>> ELSE <<{}, {}>>, learners |-> {}, autoLeave |-> FALSE]]
                      /\ reconfigCount = 0 \* the bootstrap configurations are not counted
                      \* Bootstrap config entries are already applied (committed at Cardinality(InitServer))
                      /\ appliedConfigIndex = [i \in Server |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0]

\* Bootstrap durable state: log length must match the actual bootstrap log
etcdInitDurableState ==
    durableState = [ i \in Server |-> [
        currentTerm |-> IF i \in InitServer THEN 1 ELSE 0,
        votedFor |-> Nil,
        log |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0,
        entries |-> IF i \in InitServer THEN BootstrapLog ELSE <<>>,  \* Persisted log entries
        snapshotIndex |-> 0,
        snapshotTerm |-> 0,
        snapshotHistory |-> <<>>,  \* History covered by snapshot (initially empty)
        commitIndex |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0,
        config |-> [ jointConfig |-> IF i \in InitServer THEN <<InitServer, {}>> ELSE <<{}, {}>>, learners |-> {}, autoLeave |-> FALSE]
    ]]

\* ============================================================================
\* MODEL CHECKING CONSTRAINED ACTIONS
\* ============================================================================

\* --- Config Change Constraints ---
MCAddNewServer(i, j) ==
    /\ reconfigCount < ReconfigurationLimit
    /\ etcd!AddNewServer(i, j)

MCDeleteServer(i, j) ==
    /\ reconfigCount < ReconfigurationLimit
    /\ etcd!DeleteServer(i, j)

MCAddLearner(i, j) ==
    /\ reconfigCount < ReconfigurationLimit
    /\ etcd!AddLearner(i, j)

\* --- Election/Term Constraints ---
\* Limit the terms that can be reached. Needs to be set to at least 3 to
\* evaluate all relevant states. If set to only 2, the candidate_quorum
\* constraint below is too restrictive.
MCTimeout(i) ==
    \* Limit the term of each server to reduce state space
    /\ currentTerm[i] < MaxTermLimit
    \* Limit total number of timeouts
    /\ constraintCounters.timeout < MaxTimeoutLimit
    /\ etcd!Timeout(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.timeout = @ + 1]

\* --- Client Request Constraints ---
\* Limit number of requests (new entries) that can be made
MCClientRequest(i, v) ==
    /\ constraintCounters.request < RequestLimit
    /\ etcd!ClientRequest(i, v)
    /\ constraintCounters' = [constraintCounters EXCEPT !.request = @ + 1]

\* --- Fault Injection Constraints ---
\* Limit node restarts/crashes to reduce state space explosion
MCRestart(i) ==
    /\ constraintCounters.restart < RestartLimit
    /\ etcd!Restart(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.restart = @ + 1]

\* Limit message drops to reduce state space explosion
MCDropMessage(m) ==
    /\ constraintCounters.drop < DropLimit
    /\ etcd!DropMessage(m)
    /\ constraintCounters' = [constraintCounters EXCEPT !.drop = @ + 1]

\* Limit message duplicates to reduce state space explosion
MCDuplicateMessage(m) ==
    /\ constraintCounters.duplicate < DuplicateLimit
    /\ etcd!DuplicateMessage(m)
    /\ constraintCounters' = [constraintCounters EXCEPT !.duplicate = @ + 1]

\* Limit heartbeats
MCHeartbeat(i, j) ==
    /\ constraintCounters.heartbeat < HeartbeatLimit
    /\ etcd!Heartbeat(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.heartbeat = @ + 1]

\* Limit step downs
MCStepDown(i) ==
    /\ constraintCounters.stepDown < StepDownLimit
    /\ etcd!StepDownToFollower(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.stepDown = @ + 1]

\* --- Snapshot Constraints ---
\* Limit snapshot operations to reduce state space
MCSendSnapshot(i, j) ==
    /\ constraintCounters.snapshot < SnapshotLimit
    /\ etcd!SendSnapshot(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.snapshot = @ + 1]

\* Limit log compaction operations
MCCompactLog(i, newStart) ==
    /\ constraintCounters.compact < CompactLimit
    /\ etcd!CompactLog(i, newStart)
    /\ constraintCounters' = [constraintCounters EXCEPT !.compact = @ + 1]

\* --- Additional Snapshot Constraints ---
\* ManualSendSnapshot with snapshot limit
MCManualSendSnapshot(i, j) ==
    /\ constraintCounters.snapshot < SnapshotLimit
    /\ etcd!ManualSendSnapshot(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.snapshot = @ + 1]

\* SendSnapshotWithCompaction with snapshot limit
MCSendSnapshotWithCompaction(i, j, idx) ==
    /\ constraintCounters.snapshot < SnapshotLimit
    /\ etcd!SendSnapshotWithCompaction(i, j, idx)
    /\ constraintCounters' = [constraintCounters EXCEPT !.snapshot = @ + 1]

\* --- Config Change Constraints ---
\* ChangeConf with confChange limit
MCChangeConf(i) ==
    /\ constraintCounters.confChange < ConfChangeLimit
    /\ etcd!ChangeConf(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.confChange = @ + 1]

\* ChangeConfAndSend with confChange limit
MCChangeConfAndSend(i) ==
    /\ constraintCounters.confChange < ConfChangeLimit
    /\ etcd!ChangeConfAndSend(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.confChange = @ + 1]

\* --- Client Request Constraints ---
\* ClientRequestAndSend with request limit (same as ClientRequest)
MCClientRequestAndSend(i, v) ==
    /\ constraintCounters.request < RequestLimit
    /\ etcd!ClientRequestAndSend(i, v)
    /\ constraintCounters' = [constraintCounters EXCEPT !.request = @ + 1]

\* --- ReportUnreachable Constraint ---
MCReportUnreachable(i, j) ==
    /\ constraintCounters.reportUnreachable < ReportUnreachableLimit
    /\ etcd!ReportUnreachable(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.reportUnreachable = @ + 1]

\* --- Message Deduplication ---
\* Limit how many identical append entries messages each node can send to another
\* Limit number of duplicate messages sent to the same server
MCSend(msg) ==
    \* One AppendEntriesRequest per node-pair at a time:
    \* a) No AppendEntries request from i to j.
    /\ ~ \E n \in DOMAIN messages \union DOMAIN pendingMessages:
        /\ n.mdest = msg.mdest
        /\ n.msource = msg.msource
        /\ n.mterm = msg.mterm
        /\ n.mtype = AppendEntriesRequest
        /\ msg.mtype = AppendEntriesRequest
    \* b) No (corresponding) AppendEntries response from j to i.
    /\ ~ \E n \in DOMAIN messages \union DOMAIN pendingMessages:
        /\ n.mdest = msg.msource
        /\ n.msource = msg.mdest
        /\ n.mterm = msg.mterm
        /\ n.mtype = AppendEntriesResponse
        /\ msg.mtype = AppendEntriesRequest
    /\ etcd!Send(msg)

\* ============================================================================
\* NETWORK PARTITION ACTIONS
\* ============================================================================

\* Create a simple two-way partition: servers in group1 vs servers not in group1
MCCreatePartition(group1) ==
    /\ constraintCounters.partition < PartitionLimit
    /\ LET partitionAssignment == [i \in Server |-> IF i \in group1 THEN 1 ELSE 2]
       IN etcd!CreatePartition(partitionAssignment)
    /\ constraintCounters' = [constraintCounters EXCEPT !.partition = @ + 1]

\* Heal the network partition
MCHealPartition ==
    /\ etcd!HealPartition
    /\ UNCHANGED constraintCounters

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

MCInit ==
    /\ etcd!Init
    /\ constraintCounters = [restart |-> 0, drop |-> 0, duplicate |-> 0, stepDown |-> 0, heartbeat |-> 0, snapshot |-> 0, compact |-> 0, confChange |-> 0, reportUnreachable |-> 0, timeout |-> 0, request |-> 0, partition |-> 0]

\* ============================================================================
\* NEXT STATE RELATIONS
\* ============================================================================

\* MCNextAsync(i) - All async actions for a single server i
\* This allows external quantification: \E i \in Server : MCNextAsync(i)
MCNextAsync(i) ==
    \/ /\ \E j \in Server : etcd!RequestVote(i, j)
       /\ UNCHANGED faultVars
    \/ /\ etcd!BecomeLeader(i)
       /\ UNCHANGED faultVars
    \/ \E v \in Value: MCClientRequest(i, v)
    \* \/ \E v \in Value: MCClientRequestAndSend(i, v)
    \/ /\ etcd!AdvanceCommitIndex(i)
       /\ UNCHANGED faultVars
    \* NOTE: Entries must be sent starting from nextIndex (per raft.go:638)
    \* Implementation always sends from pr.Next, not from arbitrary positions
    \* BUG DETECTION MODE: Removed constraint "nextIndex[i][j] >= log[i].offset"
    \* This allows exploring scenarios like bug 76f1249 where leader sends MsgApp
    \* with prevLogTerm=0 after log truncation (instead of sending snapshot).
    \* The correct behavior is enforced by invariants, not by action constraints.
    \/ /\ \E j \in Server :
           \* REMOVED: /\ nextIndex[i][j] >= log[i].offset  \* Allow bug scenario exploration
           /\ \E e \in nextIndex[i][j]..LastIndex(log[i])+1 : etcd!AppendEntries(i, j, <<nextIndex[i][j], e>>)
       /\ UNCHANGED faultVars
    \/ /\ etcd!AppendEntriesToSelf(i)
       /\ UNCHANGED faultVars
    \/ /\ \E j \in Server : MCHeartbeat(i, j)
    \/ /\ \E j \in Server : MCSendSnapshot(i, j)
    \* ManualSendSnapshot: Test harness sends snapshot without modifying progress state
    \/ /\ \E j \in Server : MCManualSendSnapshot(i, j)
    \* SendSnapshotWithCompaction: Snapshot with custom index
    \/ /\ \E j \in Server : \E idx \in 1..commitIndex[i] :
           /\ idx > 0
           /\ MCSendSnapshotWithCompaction(i, j, idx)
    \* ReportUnreachable: Leader detects follower unreachable, transitions Replicate->Probe
    \/ /\ \E j \in Server : MCReportUnreachable(i, j)
    \* ReplicateImplicitEntry: For joint config, leader creates implicit entry
    \/ /\ etcd!ReplicateImplicitEntry(i)
       /\ UNCHANGED faultVars
    \* NOTE: FollowerAdvanceCommitIndex removed - it allows invalid states where
    \* a follower advances commitIndex beyond what has been quorum-committed.
    \* In real Raft, followers only advance commitIndex based on leader messages.
    \* Optimization: Only allow compacting to the commitIndex to reduce state space explosion.
    \* This provides the most aggressive compaction scenario for testing Snapshots.
    \/ /\ log[i].offset < commitIndex[i]
       /\ MCCompactLog(i, commitIndex[i])
    \/ MCTimeout(i)
    \* Ready is handled separately via composition with MCReady
    \* \/ /\ etcd!Ready(i)
    \*    /\ UNCHANGED faultVars
    \/ MCStepDown(i)
    \* Message receive: only receive messages destined for server i
    \/ /\ \E m \in DOMAIN messages : 
           /\ m.mdest = i
           /\ etcd!Receive(m)
       /\ UNCHANGED faultVars

\* MCReady(i) - Ready action for server i, used for composition
\* Implements: IF ENABLED Ready(i) THEN Ready(i) ELSE UNCHANGED vars
MCReady(i) ==
    IF ENABLED etcd!Ready(i)
    THEN /\ etcd!Ready(i)
         /\ UNCHANGED faultVars
    ELSE UNCHANGED <<vars, faultVars>>

\* Combined action: MCNextAsync(i) followed by MCReady(i)
\* This reduces state space by atomically combining async action with Ready
MCNextAsyncWithReady(i) ==
    MCNextAsync(i) \cdot MCReady(i)

\* MCNextAsync for all servers (uses external quantification)
\* Includes Ready as a separate disjunct for non-composed version
MCNextAsyncAll ==
    \/ \E i \in Server : MCNextAsync(i)
    \/ \E i \in Server : 
       /\ etcd!Ready(i)
       /\ UNCHANGED faultVars

\* MCNextAsync with Ready composition for all servers
MCNextAsyncWithReadyAll ==
    \E i \in Server : MCNextAsyncWithReady(i)

MCNextCrash == \E i \in Server : MCRestart(i)

MCNextUnreliable ==
    \* Only duplicate once
    \/ \E m \in DOMAIN messages :
        /\ messages[m] = 1
        /\ MCDuplicateMessage(m)
    \* Only drop if it makes a difference
    \/ \E m \in DOMAIN messages :
        /\ messages[m] = 1
        /\ MCDropMessage(m)

\* Network partition actions
MCNextPartition ==
    \* Create a partition by splitting servers into two groups
    \* We enumerate possible non-empty subsets as partition group 1
    \/ \E group1 \in SUBSET(Server) :
        /\ group1 /= {}
        /\ group1 /= Server  \* Must have servers in both groups
        /\ MCCreatePartition(group1)
    \* Heal an existing partition
    \/ MCHealPartition

MCNext ==
    \/ MCNextAsyncAll
    \/ MCNextCrash
    \/ MCNextUnreliable
    \/ MCNextPartition

\* MCNext with Ready composition - reduces state space
MCNextWithReady ==
    \/ MCNextAsyncWithReadyAll
    \/ MCNextCrash
    \/ MCNextUnreliable
    \/ MCNextPartition

\* Note: MCAddNewServer, MCAddLearner, MCDeleteServer removed - they bypass ChangeConf constraints
\* Dynamic config change actions (shared by MCNextDynamic and MCNextDynamicWithReady)
MCDynamicConfigActions ==
    \/ /\ \E i \in Server : MCChangeConf(i)
    \* \/ /\ \E i \in Server : MCChangeConfAndSend(i)
    \/ /\ \E i \in Server : etcd!ApplySimpleConfChange(i)
       /\ UNCHANGED faultVars
    \* ProposeLeaveJoint: Leader proposes empty ConfChangeV2 to leave joint config
    \* Reference: raft.go:745-760 - AutoLeave mechanism requires log entry commitment
    \/ /\ \E i \in Server : etcd!ProposeLeaveJoint(i)
       /\ UNCHANGED faultVars

MCNextDynamic ==
    \/ MCNext
    \/ MCDynamicConfigActions

\* MCNextDynamic with Ready composition - reduces state space
MCNextDynamicWithReady ==
    \/ MCNextWithReady
    \/ MCDynamicConfigActions

mc_vars == <<vars, faultVars>>

mc_etcdSpec ==
    /\ MCInit
    /\ [][MCNextDynamic]_mc_vars

\* Spec with Ready composition for reduced state space
mc_etcdSpecWithReady ==
    /\ MCInit
    /\ [][MCNextDynamicWithReady]_mc_vars

mc_etcdSpec_no_conf_change ==
    /\ MCInit
    /\ [][MCNext]_mc_vars

\* Spec with Ready composition for reduced state space
mc_etcdSpecWithReady_no_conf_change ==
    /\ MCInit
    /\ [][MCNextWithReady]_mc_vars

\* ============================================================================
\* SYMMETRY AND VIEW DEFINITIONS
\* ============================================================================

\* Symmetry set over possible servers. May dangerous and is only enabled
\* via the Symmetry option in cfg file.
Symmetry == Permutations(Server) \union Permutations(Value)

\* View used for state space reduction.
\* It excludes 'constraintCounters' so that states differing only in counters are considered identical.
ModelView == << view_vars >>

\* ============================================================================
\* STATE SPACE PRUNING CONSTRAINTS
\* ============================================================================

\* Constraint to limit network messages buffer size for state space pruning
\* Returns FALSE when message count exceeds limit, causing TLC to prune that state
\* If MaxMsgBufferLimit = 0, no limit is applied (always returns TRUE)
MsgBufferConstraint ==
    \/ MaxMsgBufferLimit = 0
    \/ BagCardinality(messages) <= MaxMsgBufferLimit

\* Constraint to limit pending messages buffer size for state space pruning
\* Returns FALSE when pending message count exceeds limit, causing TLC to prune that state
\* If MaxPendingMsgLimit = 0, no limit is applied (always returns TRUE)
PendingMsgBufferConstraint ==
    \/ MaxPendingMsgLimit = 0
    \/ BagCardinality(pendingMessages) <= MaxPendingMsgLimit

\* Combined constraint for convenience (can use either or both in cfg)
AllMsgBufferConstraint ==
    /\ MsgBufferConstraint
    /\ PendingMsgBufferConstraint

\* ============================================================================
\* MONOTONICITY PROPERTIES
\* ============================================================================

\* Each server's commit index is monotonically increasing
\* This is weaker form of CommittedLogAppendOnlyProp so it is not checked by default
\* Note: Excludes Restart action since nodes recover from durableState,
\*       which may have an older commitIndex if not yet persisted before crash
MonotonicCommitIndexProp ==
    [][(~\E i \in Server: Restart(i)) =>
        \A i \in Server : commitIndex'[i] >= commitIndex[i]]_mc_vars

\* Each server's term is monotonically increasing
\* Note: Excludes Restart action since nodes recover from durableState,
\*       which may have an older term if not yet persisted before crash
MonotonicTermProp ==
    [][(~\E i \in Server: Restart(i)) =>
        \A i \in Server : currentTerm'[i] >= currentTerm[i]]_mc_vars

\* Match index never decrements unless the current action is a node becoming leader
\* or a node restarting (crash/recovery).
\* Figure 2, page 4 in the raft paper:
\* "Volatile state on leaders, reinitialized after election. For each server,
\*  index of the highest log entry known to be replicated on server. Initialized
\*  to 0, increases monotonically".  In other words, matchIndex never decrements
\* unless the current action is a node becoming leader or restarting.
\*
\* Additional exceptions:
\* 1. When a node is re-added to the config after being removed,
\*    its matchIndex is reset to 0. This is correct behavior per confchange.go:
\*    - remove() deletes Progress when node leaves config (line 242)
\*    - makeLearner()/makeVoter() calls initProgress with Match=0 for new nodes (line 262)
\*    Reference: confchange/confchange.go:231-243 (remove), 246-270 (initProgress)
\* 2. When a node restarts, all volatile state including matchIndex is lost.
\*    The node must rebuild this knowledge after recovery.
\*    Reference: etcdraft.tla Restart(i) - matchIndex reset to 0 for all peers
MonotonicMatchIndexProp ==
    [][(~ \E i \in Server: etcd!BecomeLeader(i) \/ etcd!Restart(i)) =>
            (\A i,j \in Server :
                LET
                    \* Pre-state: nodes tracked by leader i
                    preConfig == config[i].jointConfig[1] \cup config[i].jointConfig[2] \cup config[i].learners
                    \* Post-state: nodes tracked by leader i after transition
                    postConfig == config'[i].jointConfig[1] \cup config'[i].jointConfig[2] \cup config'[i].learners
                IN
                \* Only check monotonicity for nodes that are continuously tracked
                \* (in config in both pre and post states)
                (j \in preConfig /\ j \in postConfig) => matchIndex'[i][j] >= matchIndex[i][j])]_mc_vars

\* Leader can only commit entries from its current term
\* Reference: Raft paper §5.4.2 - "Raft never commits log entries from previous terms by counting replicas"
\* This prevents the Figure 8 safety issue where a leader might incorrectly commit entries from previous terms
LeaderCommitCurrentTermLogsProp ==
    [][
        \A i \in Server :
            (state'[i] = Leader /\ commitIndex[i] /= commitIndex'[i]) =>
                historyLog'[i][commitIndex'[i]].term = currentTerm'[i]
    ]_mc_vars

\* ============================================================================
\* RAFT PAPER CORE PROPERTIES
\* ============================================================================

\* Leader Append-Only Property (Raft Paper Figure 3, Property 2)
\* "A leader never overwrites or deletes entries in its log; it only appends new entries."
\* Reference: Raft paper §5.3 - Leaders only append, never modify existing entries
\* 
\* This property verifies:
\* 1. Log length never decreases for a leader
\* 2. Existing entries are never modified (using historyLog for full history)
\*
\* Note: We require state'[i] = Leader to exclude Restart action, since a leader
\* that crashes loses leadership and becomes Follower (state'[i] = Follower).
LeaderAppendOnlyProp ==
    [][
        \A i \in Server :
            (state[i] = Leader /\ state'[i] = Leader) =>
                \* Log only grows (or stays same)
                /\ LastIndex(log'[i]) >= LastIndex(log[i])
                \* All existing entries remain unchanged (prefix comparison)
                \* Using SubSeq equality is more efficient than \A idx check
                /\ SubSeq(historyLog'[i], 1, LastIndex(log[i])) = 
                   SubSeq(historyLog[i], 1, LastIndex(log[i]))
    ]_mc_vars

\* Committed Entries Are Never Truncated Property
\* "Once an entry is committed, it will never be removed from any server's log."
\* Reference: This is a consequence of Log Matching + Leader Completeness properties
\*
\* This property explicitly verifies that committed entries persist across all transitions.
\* It's stronger than MonotonicCommitIndexProp (which only checks index, not content).
\*
\* Note: We exclude Restart action because:
\* 1. After restart, committed entries are restored from durableState
\* 2. The historyLog ghost variable is not modified by Restart
\* 3. What matters is that durableState preserves committed entries
CommittedEntriesPersistProp ==
    [][(~\E i \in Server: etcd!Restart(i)) =>
        \A i \in Server :
            \* All entries up to commitIndex remain unchanged (prefix comparison)
            \* Using SubSeq equality is more efficient than \A idx check
            SubSeq(historyLog'[i], 1, commitIndex[i]) = 
            SubSeq(historyLog[i], 1, commitIndex[i])
    ]_mc_vars

=============================================================================
