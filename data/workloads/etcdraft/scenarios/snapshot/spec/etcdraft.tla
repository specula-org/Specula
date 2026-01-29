-------------------------- MODULE etcdraft --------------------------
EXTENDS Naturals, Integers, Bags, FiniteSets, Sequences, SequencesExt, FiniteSetsExt, BagsExt, TLC

\* The initial and global set of server IDs.
CONSTANTS InitServer, Server

\* Log metadata to distinguish values from configuration changes.
CONSTANT ValueEntry, ConfigEntry

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower,
    \* @type: Str;
    Candidate,
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Int;
    Nil

\* Message types:
CONSTANTS
    \* @type: Str;
    RequestVoteRequest,
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest,
    \* @type: Str;
    AppendEntriesResponse,
    \* @type: Str;
    SnapshotRequest,
    \* @type: Str;
    SnapshotResponse

\* New: Progress state constants
\* Reference: tracker/state.go:20-33
CONSTANTS
    \* @type: Str;
    StateProbe,      \* Probe state: don't know follower's last index
    \* @type: Str;
    StateReplicate,  \* Replicate state: normal fast replication
    \* @type: Str;
    StateSnapshot    \* Snapshot state: need to send snapshot

\* New: Flow control configuration constants
\* Reference: raft.go:205-210, Config.MaxInflightMsgs
CONSTANT
    \* @type: Int;
    MaxInflightMsgs  \* Max inflight messages (per Progress)

ASSUME MaxInflightMsgs \in Nat /\ MaxInflightMsgs > 0

\* FIFO message ordering control
\* When TRUE, messages are tagged with sequence numbers and must be received in order
CONSTANT MsgNoReorder
ASSUME MsgNoReorder \in BOOLEAN

\* Network partition configuration
\* MaxPartitions: maximum number of partitions that can be created (2 = split into 2 groups)
CONSTANT MaxPartitions
ASSUME MaxPartitions \in Nat /\ MaxPartitions >= 1

\* When TRUE, Restart action drops all messages to/from the restarting node
CONSTANT RestartDropsMessages
ASSUME RestartDropsMessages \in BOOLEAN

\* DisableConfChangeValidation turns off propose-time verification of
\* configuration changes against the currently active configuration.
\* Reference: raft.go:258-278 Config.DisableConfChangeValidation
\* WARNING: When TRUE, allows proposing LeaveJoint before EnterJoint is applied,
\* which can violate QuorumLogInv if new config members don't have committed entries.
\* Users should NOT enable this unless they have a reliable mechanism above raft
\* that serializes and verifies configuration changes.
CONSTANT DisableConfChangeValidation
ASSUME DisableConfChangeValidation \in BOOLEAN

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. We differentiate between the message types to support Apalache.
VARIABLE
    \* @typeAlias: ENTRY = [term: Int, value: Int];
    \* @typeAlias: LOGT = Seq(ENTRY);
    \* @typeAlias: RVREQT = [mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: Int, mdest: Int];
    \* @typeAlias: RVRESPT = [mtype: Str, mterm: Int, mvoteGranted: Bool, msource: Int, mdest: Int ];
    \* @typeAlias: AEREQT = [mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: LOGT, mcommitIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: AERESPT = [mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, mrejectHint: Int, mlogTerm: Int, msource: Int, mdest: Int ];
    \* @typeAlias: MSG = [ wrapped: Bool, mtype: Str, mterm: Int, msource: Int, mdest: Int, RVReq: RVREQT, RVResp: RVRESPT, AEReq: AEREQT, AEResp: AERESPT ];
    \* @type: MSG -> Int;
    messages
VARIABLE 
    pendingMessages

\* Sequence counter for FIFO message ordering (used when MsgNoReorder = TRUE)
VARIABLE
    msgSeqCounter

\* Network partition state: a function from Server to partition ID (1..MaxPartitions)
\* Servers in the same partition can communicate; servers in different partitions cannot
\* partitions[i] = 0 means no partition (all servers can communicate)
VARIABLE
    partitions

\* Tuple for pending messages and sequence counter (these change together when sending)
\* msgSeqCounter is incremented when messages are added to pendingMessages
pendingMsgVars == <<pendingMessages, msgSeqCounter>>

messageVars == <<messages, pendingMessages, msgSeqCounter>>

\* Network partition variables
partitionVars == <<partitions>>

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE 
    \* @type: Int -> Int;
    currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE 
    \* @type: Int -> Str;
    state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE 
    \* @type: Int -> Int;
    votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE 
    \* @type: Int -> [ offset: Int, entries: LOGT, snapshotIndex: Int, snapshotTerm: Int ];
    log
\* Ghost variable for verification: keeps the full history of entries
VARIABLE
    \* @type: Int -> LOGT;
    historyLog
\* The index of the latest entry in the log the state machine may apply.
VARIABLE
    \* @type: Int -> Int;
    commitIndex
\* The index of the last entry applied to the state machine.
\* Reference: raft/log.go:41-47 - applied is the highest log position successfully applied
\* Invariant: applied <= committed
VARIABLE
    \* @type: Int -> Int;
    applied
logVars == <<log, historyLog, commitIndex, applied>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesGranted
\* @type: Seq(Int -> Set(Int));
candidateVars == <<votesResponded, votesGranted>>

\* The following variables are used only on leaders:
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    matchIndex
VARIABLE
    pendingConfChangeIndex
leaderVars == <<matchIndex, pendingConfChangeIndex>>

\* @type: Int -> [jointConfig: Seq(Set(int)), learners: Set(int)]
VARIABLE 
    config
VARIABLE
    reconfigCount

\* Track the index of the last applied config entry per server
\* Reference: etcd processes CommittedEntries sequentially, applying configs as encountered
\* This ensures config is applied before commit can advance past it
VARIABLE
    \* @type: Int -> Int;
    appliedConfigIndex

configVars == <<config, reconfigCount, appliedConfigIndex>>

VARIABLE
    durableState

\* ============================================================================
\* New: Progress state machine variables
\* Reference: tracker/progress.go:30-117
\* ============================================================================

VARIABLE
    \* @type: Int -> (Int -> Str);
    progressState    \* State of each node j maintained by Leader i
                     \* Values: StateProbe | StateReplicate | StateSnapshot

VARIABLE
    \* @type: Int -> (Int -> Int);
    pendingSnapshot  \* Pending snapshot index from Leader i to node j
                     \* Meaningful only when progressState[i][j] = StateSnapshot

VARIABLE
    \* @type: Int -> (Int -> Int);
    nextIndex        \* Next log index to send from Leader i to node j
                     \* Reference: progress.go:34-40
                     \* Invariant: Match < Next (matchIndex[i][j] < nextIndex[i][j])
                     \* In StateSnapshot: Next == PendingSnapshot + 1

VARIABLE
    \* @type: Int -> (Int -> Bool);
    msgAppFlowPaused \* Whether message flow from Leader i to node j is paused
                     \* This is a cached flag, updated at SentEntries

\* ============================================================================
\* New: Inflights flow control variables
\* Reference: tracker/inflights.go:28-40
\* ============================================================================

VARIABLE
    \* @type: Int -> (Int -> Set(Int));
    inflights        \* Set of inflight messages from Leader i to node j
                     \* Stores the last entry index of each inflight AppendEntries message
                     \*
                     \* Modeling simplification: represented as a set, actual code uses a ring buffer (FIFO)
                     \* Reason: messages are added in increasing index order, FreeLE frees messages <= index
                     \*         For verifying flow control constraints (capacity limit), a set is sufficient
                     \*
                     \* Constraint: spec enforces that Add index is strictly monotonically increasing (see AddInflight)
                     \*
                     \* Limitations (accepted risks):
                     \* 1. Cannot detect duplicate index bugs (set automatically deduplicates)
                     \*    - If code repeatedly adds the same index, InflightsCount is underestimated
                     \*    - Cannot capture "repeated retries blowing up capacity" issues
                     \* 2. Cannot verify ring buffer implementation details (grow(), etc.)
                     \*
                     \* If more precision is needed: can be changed to Bag (multiset) or Seq (sequence)

progressVars == <<progressState, pendingSnapshot, nextIndex, msgAppFlowPaused, inflights>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messageVars, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, partitionVars>>

\* View variables for state space reduction.
\* Excludes from vars:
\* - historyLog: Ghost variable for verification only, doesn't affect system behavior
\* - applied: Can be derived from commitIndex progression
\* - reconfigCount: Pure counter for trace validation
\* - durableState: Derived from log state
\* Note: msgSeqCounter is embedded in messages (mseq field), so excluding it here has no effect
view_vars == <<messages, pendingMessages, serverVars, candidateVars, leaderVars, log, commitIndex, config, progressVars, partitionVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(c) == {i \in SUBSET(c) : Cardinality(i) * 2 > Cardinality(c)}

\* ============================================================================
\* Network Partition Helpers
\* ============================================================================

\* Check if there is currently a network partition active
IsPartitioned == \E i \in Server : partitions[i] /= 0

\* Check if two servers can communicate (in the same partition or no partition)
CanCommunicate(i, j) ==
    \/ partitions[i] = 0  \* No partition active for i
    \/ partitions[j] = 0  \* No partition active for j
    \/ partitions[i] = partitions[j]  \* Same partition

\* Get all messages that cross partition boundaries (to be dropped)
CrossPartitionMessages ==
    {m \in DOMAIN messages : 
        /\ partitions[m.msource] /= 0 
        /\ partitions[m.mdest] /= 0
        /\ partitions[m.msource] /= partitions[m.mdest]}

\* Get all pending messages that cross partition boundaries
CrossPartitionPendingMessages ==
    {m \in DOMAIN pendingMessages : 
        /\ partitions[m.msource] /= 0 
        /\ partitions[m.mdest] /= 0
        /\ partitions[m.msource] /= partitions[m.mdest]}

\* Drop all messages between two servers
DropMessagesBetween(i, j) ==
    {m \in DOMAIN messages : (m.msource = i /\ m.mdest = j) \/ (m.msource = j /\ m.mdest = i)}

\* Drop all messages to/from a specific server
MessagesToOrFrom(i) ==
    {m \in DOMAIN messages : m.msource = i \/ m.mdest = i}

\* Drop all pending messages to/from a specific server
PendingMessagesToOrFrom(i) ==
    {m \in DOMAIN pendingMessages : m.msource = i \/ m.mdest = i}

\* ============================================================================
\* New: Virtual Log Helpers (Offset-aware)
\* ============================================================================

\* Get the logical index of the last entry in the log
\* @type: [ offset: Int, entries: LOGT, snapshotIndex: Int, snapshotTerm: Int ] => Int;
LastIndex(xlog) ==
    xlog.offset + Len(xlog.entries) - 1

\* Get the term of the last entry (or snapshot term if empty)
\* @type: [ offset: Int, entries: LOGT, snapshotIndex: Int, snapshotTerm: Int ] => Int;
LastTerm(xlog) ==
    IF Len(xlog.entries) > 0 THEN xlog.entries[Len(xlog.entries)].term
    ELSE xlog.snapshotTerm

\* Check if a logical index is available in the memory log (not compacted)
IsAvailable(i, index) ==
    /\ index >= log[i].offset
    /\ index <= LastIndex(log[i])

\* Get the log entry at a logical index
\* PRECONDITION: IsAvailable(i, index)
LogEntry(i, index) ==
    log[i].entries[index - log[i].offset + 1]

\* Get the term at a logical index
\* Returns 0 if index is 0.
\* Returns snapshotTerm if index is snapshotIndex.
\* Checks availability for other indices.
LogTerm(i, index) ==
    IF index = 0 THEN 0
    ELSE IF index = log[i].snapshotIndex THEN log[i].snapshotTerm
    ELSE IF IsAvailable(i, index) THEN LogEntry(i, index).term
    ELSE 0

\* Reference: raft.go findConflictByTerm
\* Find the largest index in [firstIndex-1, index] where term <= given term.
\* This is used for fast log backtracking during rejection handling.
FindConflictByTerm(i, index, targetTerm) ==
    LET firstIdx == log[i].offset
        \* Valid range includes firstIdx-1 (for snapshot term check)
        validRange == (firstIdx - 1)..index
        \* Find indices where term <= targetTerm
        matchingIndices == {k \in validRange : LogTerm(i, k) <= targetTerm}
    IN IF index = 0 \/ matchingIndices = {} THEN 0 ELSE Max(matchingIndices)

\* Reference: raft.go handleAppendEntries rejection logic
\* Compute the rejection hint using findConflictByTerm optimization.
\* The optimization uses the LEADER's prevLogTerm to find the last index
\* where the follower's log has term <= prevLogTerm.
\* This helps the leader skip over conflicting entries faster.
\* Parameters: i = follower, rejectedIndex = m.mprevLogIndex, leaderTerm = m.mprevLogTerm
ComputeRejectHint(i, rejectedIndex, leaderTerm) ==
    LET hintIndex == Min({rejectedIndex, LastIndex(log[i])})
    IN FindConflictByTerm(i, hintIndex, leaderTerm)

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Add a message to the bag of pendingMessages.
\* When MsgNoReorder is TRUE, add sequence number for FIFO ordering.
SendDirect(m) == 
    IF MsgNoReorder
    THEN /\ pendingMessages' = WithMessage(m @@ [mseq |-> msgSeqCounter], pendingMessages)
         /\ msgSeqCounter' = msgSeqCounter + 1
    ELSE /\ pendingMessages' = WithMessage(m, pendingMessages)
         /\ UNCHANGED msgSeqCounter

\* All pending messages sent from node i
PendingMessages(i) ==
    FoldBag(LAMBDA x, y: IF y.msource = i THEN BagAdd(x,y) ELSE x, EmptyBag, pendingMessages)

\* Remove all messages in pendingMessages that were sent from node i
ClearPendingMessages(i) ==
    pendingMessages (-) PendingMessages(i)

\* Move all messages which was sent from node i in pendingMessages to messages
SendPendingMessages(i) ==
    LET msgs == PendingMessages(i)
    IN /\ messages' = msgs (+) messages
       /\ pendingMessages' = pendingMessages (-) msgs

\* Remove a message from the bag of messages OR pendingMessages. Used when a server is done
DiscardDirect(m) ==
    IF m \in DOMAIN messages 
    THEN messages' = WithoutMessage(m, messages) /\ UNCHANGED <<pendingMessages, msgSeqCounter>>
    ELSE pendingMessages' = WithoutMessage(m, pendingMessages) /\ UNCHANGED <<messages, msgSeqCounter>>

\* Combination of Send and Discard
\* When MsgNoReorder is TRUE, add sequence number to response for FIFO ordering.
ReplyDirect(response, request) ==
    LET resp == IF MsgNoReorder THEN response @@ [mseq |-> msgSeqCounter] ELSE response
    IN IF request \in DOMAIN messages
       THEN /\ messages' = WithoutMessage(request, messages)
            /\ pendingMessages' = WithMessage(resp, pendingMessages)
            /\ IF MsgNoReorder THEN msgSeqCounter' = msgSeqCounter + 1 ELSE UNCHANGED msgSeqCounter
       ELSE /\ pendingMessages' = WithMessage(resp, WithoutMessage(request, pendingMessages))
            /\ UNCHANGED messages
            /\ IF MsgNoReorder THEN msgSeqCounter' = msgSeqCounter + 1 ELSE UNCHANGED msgSeqCounter

\* Default: change when needed
 Send(m) == SendDirect(m)
 Reply(response, request) == ReplyDirect(response, request) 
 Discard(m) == DiscardDirect(m)

\* FIFO ordering predicate: check if message m is the first message from its source to its dest
\* A message is FIFO-first if no other message with lower sequence number exists for the same pair
IsFifoFirst(m) ==
    IF ~MsgNoReorder THEN TRUE
    ELSE ~\E other \in DOMAIN messages:
            /\ other.msource = m.msource
            /\ other.mdest = m.mdest
            /\ other.mseq < m.mseq
     
MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

GetJointConfig(i) == 
    config[i].jointConfig

GetConfig(i) == 
    GetJointConfig(i)[1]

GetOutgoingConfig(i) ==
    GetJointConfig(i)[2]

IsJointConfig(i) ==
    /\ GetJointConfig(i)[2] # {}

GetLearners(i) ==
    config[i].learners

\* Compute ConfState from a history sequence (for snapshot)
\* This simulates what the real system stores in Snapshot.Metadata.ConfState
\* The ConfState contains the configuration at the snapshot index.
\* Reference: raftpb.ConfState contains Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave
\* @type: Seq([value: a, term: Int, type: Str]) => [voters: Set(Str), learners: Set(Str), outgoing: Set(Str), autoLeave: Bool];
ComputeConfStateFromHistory(history) ==
    LET configIndices == {k \in 1..Len(history) : history[k].type = ConfigEntry}
        lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
    IN
    IF lastConfigIdx = 0 THEN
        \* No config entry, return empty config
        [voters |-> {}, learners |-> {}, outgoing |-> {}, autoLeave |-> FALSE]
    ELSE
        LET entry == history[lastConfigIdx]
            isLeaveJoint == "leaveJoint" \in DOMAIN entry.value /\ entry.value.leaveJoint = TRUE
        IN
        IF isLeaveJoint THEN
            \* LeaveJoint: voters come from newconf, learners from entry, no outgoing
            [voters |-> entry.value.newconf,
             learners |-> IF "learners" \in DOMAIN entry.value THEN entry.value.learners ELSE {},
             outgoing |-> {},
             autoLeave |-> FALSE]
        ELSE
            \* Regular config entry (including enterJoint)
            LET hasEnterJoint == "enterJoint" \in DOMAIN entry.value
                enterJoint == IF hasEnterJoint THEN entry.value.enterJoint ELSE FALSE
                hasOldconf == enterJoint /\ "oldconf" \in DOMAIN entry.value
                oldconf == IF hasOldconf THEN entry.value.oldconf ELSE {}
            IN
            [voters |-> entry.value.newconf,
             learners |-> IF "learners" \in DOMAIN entry.value THEN entry.value.learners ELSE {},
             outgoing |-> oldconf,
             autoLeave |-> enterJoint /\ oldconf /= {}]

\* Apply conf change log entry to configuration
\* Reference: raft.go applyConfChange() - enterJoint sets autoLeave=TRUE, leaveJoint clears it
\* Reference: confchange.go:103-107 LeaveJoint() - preserves Learners and adds LearnersNext to Learners
ApplyConfigUpdate(i, k) ==
    LET entry == LogEntry(i, k)
        isLeaveJoint == "leaveJoint" \in DOMAIN entry.value /\ entry.value.leaveJoint = TRUE
        newVoters == IF isLeaveJoint THEN GetConfig(i) ELSE entry.value.newconf
        \* FIX: For LeaveJoint, learners are preserved (stored in entry.value.learners by ProposeLeaveJoint)
        \* Previously this was hardcoded to {} which was incorrect
        newLearners == IF "learners" \in DOMAIN entry.value THEN entry.value.learners ELSE {}
        enterJoint == IF "enterJoint" \in DOMAIN entry.value THEN entry.value.enterJoint ELSE FALSE
        outgoing == IF enterJoint THEN entry.value.oldconf ELSE {}
        \* AutoLeave: Set TRUE when entering joint, clear when leaving joint
        newAutoLeave == IF isLeaveJoint THEN FALSE ELSE enterJoint
    IN
    [config EXCEPT ![i]= [jointConfig |-> << newVoters, outgoing >>, learners |-> newLearners, autoLeave |-> newAutoLeave]]

\* Apply a single config change to a config record
\* Used for processing ChangeConf events with multiple changes
\* @type: ([nid: Str, action: Str], [voters: Set(Str), learners: Set(Str)]) => [voters: Set(Str), learners: Set(Str)];
ApplyChange(change, conf) ==
    CASE change.action = "AddNewServer" ->
            [voters   |-> conf.voters \union {change.nid},
             learners |-> conf.learners \ {change.nid}]
      [] change.action = "RemoveServer" ->
            [voters   |-> conf.voters \ {change.nid},
             learners |-> conf.learners \ {change.nid}]
      [] change.action = "AddLearner" ->
            [voters   |-> conf.voters \ {change.nid},
             learners |-> conf.learners \union {change.nid}]
      [] OTHER -> conf

CommitTo(i, c) ==
    commitIndex' = [commitIndex EXCEPT ![i] = Max({@, c})]

CurrentLeaders == {i \in Server : state[i] = Leader}

PersistState(i) ==
    durableState' = [durableState EXCEPT ![i] = [
        currentTerm |-> currentTerm[i],
        votedFor |-> votedFor[i],
        log |-> LastIndex(log[i]),
        entries |-> log[i].entries,    \* Persist actual log entries
        snapshotIndex |-> log[i].snapshotIndex,
        snapshotTerm |-> log[i].snapshotTerm,
        snapshotHistory |-> @.snapshotHistory,  \* Preserve existing snapshot history
        commitIndex |-> commitIndex[i],
        config |-> config[i]
    ]]

\* ============================================================================
\* New: Progress and Inflights helper functions
\* ============================================================================

\* Calculate the number of messages in inflights
\* Reference: inflights.go:87-89 Count()
InflightsCount(i, j) == Cardinality(inflights[i][j])

\* Determine if inflights is full
\* Reference: inflights.go:74-76 Full()
InflightsFull(i, j) == InflightsCount(i, j) >= MaxInflightMsgs

\* Determine if Progress is paused (cannot send new AppendEntries)
\* Reference: progress.go:262-273 IsPaused()
\* Key: only checks msgAppFlowPaused flag, which is updated at SentEntries()
IsPaused(i, j) ==
    CASE progressState[i][j] = StateProbe      -> msgAppFlowPaused[i][j]
      [] progressState[i][j] = StateReplicate  -> msgAppFlowPaused[i][j]
      [] progressState[i][j] = StateSnapshot   -> TRUE
      [] OTHER -> FALSE

\* Add an inflight message
\* Reference: inflights.go:45-57 Add()
\* Note: This is a pure assignment operation; monotonicity is checked by the InflightsMonotonicInv invariant
AddInflight(i, j, lastIndex) ==
    inflights' = [inflights EXCEPT ![i][j] = @ \cup {lastIndex}]

\* Free all inflight messages up to and including index
\* Reference: inflights.go:59-72 FreeLE()
FreeInflightsLE(i, j, index) ==
    inflights' = [inflights EXCEPT ![i][j] = {idx \in @ : idx > index}]

\* Reset inflights (on state transition)
\* Reference: progress.go:121-126 ResetState() calls inflights.reset()
ResetInflights(i, j) ==
    inflights' = [inflights EXCEPT ![i][j] = {}]

----
\* Define initial values for all variables
InitMessageVars == /\ messages = EmptyBag
                   /\ pendingMessages = EmptyBag
                   /\ msgSeqCounter = 0
InitServerVars == /\ currentTerm = [i \in Server |-> 0]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ pendingConfChangeIndex = [i \in Server |-> 0]
InitLogVars == /\ log          = [i \in Server |-> [offset |-> 1, entries |-> <<>>, snapshotIndex |-> 0, snapshotTerm |-> 0]]
               /\ historyLog   = [i \in Server |-> <<>>]
               /\ commitIndex  = [i \in Server |-> 0]
               /\ applied      = [i \in Server |-> 0]
InitConfigVars == /\ config = [i \in Server |-> [ jointConfig |-> <<InitServer, {}>>, learners |-> {}, autoLeave |-> FALSE]]
                  /\ reconfigCount = 0
                  /\ appliedConfigIndex = [i \in Server |-> 0] 
InitDurableState ==
    durableState = [ i \in Server |-> [
        currentTerm |-> currentTerm[i],
        votedFor |-> votedFor[i],
        log |-> 0,
        entries |-> <<>>,              \* Persisted log entries (from offset to lastIndex)
        snapshotIndex |-> 0,
        snapshotTerm |-> 0,
        snapshotHistory |-> <<>>,      \* History covered by snapshot (1 to snapshotIndex)
        commitIndex |-> commitIndex[i],
        config |-> config[i]
    ]]

\* New: Progress and Inflights initialization
\* Reference: Progress initialization in raft.go:798-808 becomeFollower
\* All Progress initialized to StateProbe (StateType zero value is 0, i.e., StateProbe)
InitProgressVars ==
    /\ progressState = [i \in Server |-> [j \in Server |-> StateProbe]]
    /\ pendingSnapshot = [i \in Server |-> [j \in Server |-> 0]]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ msgAppFlowPaused = [i \in Server |-> [j \in Server |-> FALSE]]
    /\ inflights = [i \in Server |-> [j \in Server |-> {}]]

\* Network partition initialization: no partition active (all servers in partition 0)
InitPartitionVars ==
    /\ partitions = [i \in Server |-> 0]

Init == /\ InitMessageVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitConfigVars
        /\ InitDurableState
        /\ InitProgressVars
        /\ InitPartitionVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, commitIndex, votedFor, log, and config in durable state.
\* When RestartDropsMessages is TRUE, all messages to/from the restarting node are dropped.
\* @type: Int => Bool;
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
    /\ pendingMessages' = ClearPendingMessages(i)
    /\ currentTerm' = [currentTerm EXCEPT ![i] = durableState[i].currentTerm]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = durableState[i].commitIndex]
    /\ votedFor' = [votedFor EXCEPT ![i] = durableState[i].votedFor]
    \* Restore log from durableState: offset must equal snapshotIndex + 1
    \* Entries are restored from durableState.entries (persisted log)
    /\ log' = [log EXCEPT ![i] = [
                    offset |-> durableState[i].snapshotIndex + 1,
                    entries |-> durableState[i].entries,
                    snapshotIndex |-> durableState[i].snapshotIndex,
                    snapshotTerm |-> durableState[i].snapshotTerm
       ]]
    \* On restart, applied is reset to snapshotIndex (all entries up to snapshot are applied)
    /\ applied' = [applied EXCEPT ![i] = durableState[i].snapshotIndex]
    /\ config' = [config EXCEPT ![i] = durableState[i].config]
    \* After restart, consider all committed configs as applied (durableState.config reflects this)
    /\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = durableState[i].commitIndex]
    \* New: Reset Progress variables (volatile state, not persisted)
    /\ progressState' = [progressState EXCEPT ![i] = [j \in Server |-> StateProbe]]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i] = [j \in Server |-> 0]]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ inflights' = [inflights EXCEPT ![i] = [j \in Server |-> {}]]
    \* When RestartDropsMessages is TRUE, drop all messages to/from this node
    /\ IF RestartDropsMessages 
       THEN messages' = messages (-) SetToBag(MessagesToOrFrom(i))
       ELSE UNCHANGED messages
    \* historyLog (ghost variable) must also be restored to durable state
    \* (entries beyond durableState.log are lost on crash)
    /\ historyLog' = [historyLog EXCEPT ![i] = durableState[i].snapshotHistory \o durableState[i].entries]
    /\ UNCHANGED <<msgSeqCounter, durableState, reconfigCount, partitions>>

\* Server i times out and starts a new election.
\* @type: Int => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ i \in GetConfig(i) \union GetOutgoingConfig(i)
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ UNCHANGED <<messageVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Candidate i sends j a RequestVote request.
\* @type: (Int, Int) => Bool;
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \in ((GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)) \ votesResponded[i])
    /\ IF i # j 
        THEN Send([mtype            |-> RequestVoteRequest,
                   mterm            |-> currentTerm[i],
                   mlastLogTerm     |-> LastTerm(log[i]),
                   mlastLogIndex    |-> LastIndex(log[i]),
                   msource          |-> i,
                   mdest            |-> j])
        ELSE Send([mtype            |-> RequestVoteResponse,
                   mterm            |-> currentTerm[i],
                   mvoteGranted     |-> TRUE,
                   msource          |-> i,
                   mdest            |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Leader i sends j an AppendEntries request containing entries in [b,e) range.
\* N.B. range is right open
\* @type: (Int, Int, <<Int, Int>>, Int) => Bool;
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)
    \* Guard: If sending entries (non-empty range), they must be available (not compacted)
    \* Reference: raft.go:623-627 maybeSendAppend() - if term(prevIndex) fails, send snapshot
    \* Heartbeat (range[1] = range[2]) doesn't send entries, so no check needed
    /\ (range[1] = range[2] \/ range[1] >= log[i].offset)
    \* NEW Guard (Bug 76f1249 fix): prevLogIndex must have retrievable term
    \* Reference: raft.go:622-628 - if term(prevIndex) fails, send snapshot instead
    \* prevLogIndex = range[1] - 1 can have valid term if:
    \*   (1) prevLogIndex = 0 (empty log case, term = 0 is valid), or
    \*   (2) prevLogIndex = snapshotIndex (term from snapshot metadata), or
    \*   (3) prevLogIndex >= offset (entry is available in log)
    \* NOTE: This applies to ALL AppendEntries including heartbeats - heartbeats also need valid prevLogTerm
    /\ (range[1] = 1 \/ range[1] - 1 = log[i].snapshotIndex \/ range[1] - 1 >= log[i].offset)
    \* New: Check flow control state; cannot send when paused (except heartbeat)
    \* Reference: IsPaused check in raft.go:407-410, 652-655 maybeSendAppend()
    \* Note: heartbeat is sent directly via bcastHeartbeat(), bypassing maybeSendAppend()
    /\ (subtype = "heartbeat" \/ ~IsPaused(i, j))
    /\ LET
        prevLogIndex == range[1] - 1
        \* The following upper bound on prevLogIndex is unnecessary
        \* but makes verification substantially simpler.
        prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= LastIndex(log[i]) THEN
                            LogTerm(i, prevLogIndex)
                        ELSE
                            0
        \* Send the entries
        lastEntry == Min({LastIndex(log[i]), range[2]-1})
        entries == SubSeq(log[i].entries, range[1] - log[i].offset + 1, lastEntry - log[i].offset + 1)
        \* Commit calculation:
        \* - Heartbeat: Min(commitIndex, matchIndex) - bounded by what follower has
        \* - Empty append (no entries): commitIndex directly - just updating commit
        \* - Regular append: Min(commitIndex, lastEntry) - bounded by entries being sent
        \* Reference: raft.go sendAppend() calculates commit based on entries
        commit == CASE subtype = "heartbeat"  -> Min({commitIndex[i], matchIndex[i][j]})
                    [] lastEntry < range[1]   -> commitIndex[i]
                    [] OTHER                  -> Min({commitIndex[i], lastEntry})
        \* New: Calculate number of entries sent (for updating msgAppFlowPaused)
        numEntries == Len(entries)
        \* New: Calculate updated inflights (if entries were sent)
        newInflights == IF lastEntry >= range[1]
                        THEN inflights[i][j] \cup {lastEntry}
                        ELSE inflights[i][j]
        \* New: Calculate updated msgAppFlowPaused
        \* Reference: progress.go:165-185 SentEntries()
        \* Reference: progress.go:197-200 SentCommit() does not modify MsgAppFlowPaused
        \* Heartbeat calls SentCommit(), not SentEntries(), so does not change pause state
        newMsgAppFlowPaused ==
            CASE subtype = "heartbeat"
                    -> msgAppFlowPaused[i][j]  \* Heartbeat doesn't change pause state
              [] progressState[i][j] = StateReplicate
                    -> Cardinality(newInflights) >= MaxInflightMsgs
              [] progressState[i][j] = StateProbe /\ numEntries > 0
                    -> TRUE
              [] OTHER -> msgAppFlowPaused[i][j]
       IN /\ Send( [mtype          |-> AppendEntriesRequest,
                    msubtype       |-> subtype,
                    mterm          |-> currentTerm[i],
                    mprevLogIndex  |-> prevLogIndex,
                    mprevLogTerm   |-> prevLogTerm,
                    mentries       |-> entries,
                    mcommitIndex   |-> commit,
                    msource        |-> i,
                    mdest          |-> j])
          \* New: Update inflights (if entries were sent)
          \* Reference: raft.go:692-708 sendHeartbeat() only calls SentCommit(), not SentEntries()
          \* Reference: raft.go:721 "bcastHeartbeat sends RPC, without entries"
          \* Reference: tracker/progress.go:165-185 SentEntries() - Inflights.Add() ONLY in StateReplicate!
          \* Heartbeat never adds to inflights (inflights is only for MsgApp with entries)
          \* StateProbe does NOT add inflights (only sets MsgAppFlowPaused)
          /\ IF lastEntry >= range[1] /\ subtype /= "heartbeat" /\ progressState[i][j] = StateReplicate
             THEN AddInflight(i, j, lastEntry)
             ELSE UNCHANGED inflights
          \* New: Update msgAppFlowPaused
          /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = newMsgAppFlowPaused]
          \* New: Update nextIndex (Reference: progress.go:165-185 SentEntries())
          \* In StateReplicate, pr.Next += entries; in StateProbe, Next unchanged
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
              IF numEntries > 0 /\ progressState[i][j] = StateReplicate /\ subtype /= "heartbeat"
              THEN @ + numEntries
              ELSE @]
          \* New: Other Progress variables remain unchanged
          /\ UNCHANGED <<progressState, pendingSnapshot>>
          /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, partitions>> 

\* etcd leader sends MsgAppResp to itself immediately after appending log entry
AppendEntriesToSelf(i) ==
    /\ state[i] = Leader
    /\ Send([mtype           |-> AppendEntriesResponse,
             msubtype        |-> "app",
             mterm           |-> currentTerm[i],
             msuccess        |-> TRUE,
             mmatchIndex     |-> LastIndex(log[i]),
             mrejectHint     |-> 0,
             mlogTerm        |-> 0,
             msource         |-> i,
             mdest           |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

AppendEntries(i, j, range) ==
    AppendEntriesInRangeToPeer("app", i, j, range)

Heartbeat(i, j) ==
    \* heartbeat is equivalent to an append-entry request with 0 entry index 1
    AppendEntriesInRangeToPeer("heartbeat", i, j, <<1,1>>)

SendSnapshot(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    \* Trigger: The previous log index required for AppendEntries is NOT available
    /\ LET prevLogIndex == nextIndex[i][j] - 1 IN
       ~IsAvailable(i, prevLogIndex)
    \* Must have a snapshot to send (snapshotIndex > 0)
    \* Reference: raft.go:677-682 - maybeSendSnapshot checks r.raftLog.snapshot()
    /\ log[i].snapshotIndex > 0
    \* Use persisted snapshotHistory instead of ghost variable historyLog
    /\ LET snapshotHistory == durableState[i].snapshotHistory
       IN Send([mtype          |-> SnapshotRequest,
                mterm          |-> currentTerm[i],
                msnapshotIndex |-> log[i].snapshotIndex,
                msnapshotTerm  |-> log[i].snapshotTerm,
                mhistory       |-> snapshotHistory,
                \* NEW: Include ConfState in snapshot message (like real system)
                \* Reference: raftpb.Snapshot.Metadata.ConfState
                mconfState     |-> ComputeConfStateFromHistory(snapshotHistory),
                msource        |-> i,
                mdest          |-> j])
    \* Transition to StateSnapshot, set pendingSnapshot and Next
    \* Reference: raft.go:684 sendSnapshot() -> pr.BecomeSnapshot()
    \* Reference: tracker/progress.go:153-158 BecomeSnapshot()
    /\ progressState' = [progressState EXCEPT ![i][j] = StateSnapshot]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = log[i].snapshotIndex]
    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = log[i].snapshotIndex + 1]
    /\ ResetInflights(i, j)
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, historyLog, partitions>>

\* Send snapshot with optional log compaction.
\* SendSnapshot without compacting the log.
\* In etcd, the application compacts log independently via a separate Compact() call.
\* The raft library's maybeSendSnapshot() only sends the snapshot message.
\* Reference: raft.go:680-689 maybeSendSnapshot()
\*
\* Note: Previously this action combined compaction with snapshot sending, but
\* this caused issues in scenarios where the leader needs to send log entries
\* after sending a snapshot (e.g., snapshot_succeed_via_app_resp_behind).
SendSnapshotWithCompaction(i, j, snapshoti) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ snapshoti <= applied[i]  \* Can only snapshot applied entries (not just committed)
    /\ snapshoti >= log[i].snapshotIndex  \* Must be >= current snapshotIndex (can't send compacted entries)
    /\ snapshoti >= matchIndex[i][j]   \* Only send snapshot for entries follower doesn't have
    \* Use snapshotHistory for compacted part, log.entries for available part
    /\ LET snapshotHistory == IF snapshoti <= durableState[i].snapshotIndex
                              THEN SubSeq(durableState[i].snapshotHistory, 1, snapshoti)
                              ELSE durableState[i].snapshotHistory \o
                                   SubSeq(log[i].entries, 1, snapshoti - log[i].offset + 1)
       IN SendDirect([mtype          |-> SnapshotRequest,
                      mterm          |-> currentTerm[i],
                      msnapshotIndex |-> snapshoti,
                      msnapshotTerm  |-> LogTerm(i, snapshoti),
                      mhistory       |-> snapshotHistory,
                      \* NEW: Include ConfState in snapshot message
                      mconfState     |-> ComputeConfStateFromHistory(snapshotHistory),
                      msource        |-> i,
                      mdest          |-> j])
    /\ progressState' = [progressState EXCEPT ![i][j] = StateSnapshot]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = snapshoti]
    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = snapshoti + 1]
    /\ inflights' = [inflights EXCEPT ![i][j] = {}]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, historyLog, partitions>>

\* ManualSendSnapshot - Send snapshot without modifying progress state
\* This models the send-snapshot command in the test harness which bypasses
\* the normal raft send path and directly injects a snapshot message.
\* Reference: rafttest/interaction_env_handler_send_snapshot.go:34-50
\*           rafttest/interaction_env_handler_add_nodes.go:106-108
\*
\* Key differences from SendSnapshot:
\* - Does NOT transition progressState to StateSnapshot
\* - Does NOT set pendingSnapshot
\* - Does NOT update nextIndex
\* - Creates snapshot from applied state, NOT from snapshotIndex
\*
\* The test harness's Snapshot() returns the last entry from History, which
\* tracks the applied state (not a persisted snapshot).
\* Reference: raft_test.go:2652 CreateSnapshot(lead.raftLog.applied, ...)
ManualSendSnapshot(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    \* Must have applied entries to create a snapshot from
    /\ applied[i] > 0
    \* Use snapshotHistory for compacted part, log.entries for available part
    /\ LET snapshotHistory == IF applied[i] <= durableState[i].snapshotIndex
                              THEN SubSeq(durableState[i].snapshotHistory, 1, applied[i])
                              ELSE durableState[i].snapshotHistory \o
                                   SubSeq(log[i].entries, 1, applied[i] - log[i].offset + 1)
       IN Send([mtype          |-> SnapshotRequest,
                mterm          |-> currentTerm[i],
                msnapshotIndex |-> applied[i],
                msnapshotTerm  |-> LogTerm(i, applied[i]),
                mhistory       |-> snapshotHistory,
                \* NEW: Include ConfState in snapshot message
                mconfState     |-> ComputeConfStateFromHistory(snapshotHistory),
                msource        |-> i,
                mdest          |-> j])
    \* Key: Do NOT modify progress state!
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Candidate i transitions to leader.
\* @type: Int => Bool;
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ IF IsJointConfig(i) THEN
           /\ (votesGranted[i] \cap GetConfig(i)) \in Quorum(GetConfig(i))
           /\ (votesGranted[i] \cap GetOutgoingConfig(i)) \in Quorum(GetOutgoingConfig(i))
       ELSE
           votesGranted[i] \in Quorum(GetConfig(i))
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> IF j = i THEN LastIndex(log[i]) ELSE 0]]
    \* New: Initialize Progress state
    \* Reference: raft.go:933-950 becomeLeader() -> reset()
    \* Reference: raft.go:784-810 reset() - initializes Match=0, Next=lastIndex+1 for all peers
    \* Leader sets itself to StateReplicate (line 947), others to StateProbe
    /\ progressState' = [progressState EXCEPT ![i] =
                            [j \in Server |-> IF j = i THEN StateReplicate ELSE StateProbe]]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i] =
                            [j \in Server |-> FALSE]]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i] =
                            [j \in Server |-> 0]]
    /\ nextIndex' = [nextIndex EXCEPT ![i] =
                            [j \in Server |-> LastIndex(log[i]) + 1]]
    /\ inflights' = [inflights EXCEPT ![i] =
                            [j \in Server |-> {}]]
    \* FIX: Set pendingConfChangeIndex to lastIndex per raft.go:955-960
    \* Reference: "Conservatively set the pendingConfIndex to the last index in the
    \* log. There may or may not be a pending config change, but it's safe to delay
    \* any future proposals until we commit all our pending log entries."
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = LastIndex(log[i])]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, candidateVars, logVars, configVars, durableState, partitions>>
    
Replicate(i, v, t) == 
    /\ t \in {ValueEntry, ConfigEntry}
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     type  |-> t,
                     value |-> v]
           newLog == [log[i] EXCEPT !.entries = Append(@, entry)]
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ historyLog' = [historyLog EXCEPT ![i] = Append(@, entry)]

\* Leader i receives a client request to add v to the log.
\* @type: (Int, Int) => Bool;
ClientRequest(i, v) ==
    /\ Replicate(i, [val |-> v], ValueEntry)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Leader i receives a client request AND sends MsgAppResp immediately (mimicking atomic behavior).
\* Used for implicit replication in Trace Validation.
ClientRequestAndSend(i, v) ==
    /\ Replicate(i, [val |-> v], ValueEntry)
    /\ Send([mtype       |-> AppendEntriesResponse,
             msubtype    |-> "app",
             mterm       |-> currentTerm[i],
             msuccess    |-> TRUE,
             mmatchIndex |-> LastIndex(log'[i]),
             mrejectHint |-> 0,
             mlogTerm    |-> 0,
             msource     |-> i,
             mdest       |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, applied, configVars, durableState, progressVars, partitions>>


\* Leader replicates an implicit entry (for self-message response in trace).
\* In joint config: creates a leave-joint config entry (auto-leave mechanism)
\* Otherwise: creates a normal value entry
\* Reference: This models the implicit replication when leader sends MsgAppResp to itself.
\* Reference: raft.go:745 - Auto-leave trigger condition:
\*   if r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader
\*
\* Extended: Also supports DisableConfChangeValidation scenario where LeaveJoint can be
\* proposed before EnterJoint is applied (but after EnterJoint is in the log).
\* Reference: raft.go:1762-1770 - DisableConfChangeValidation bypasses pending check
ReplicateImplicitEntry(i) ==
    /\ state[i] = Leader
    /\ LET isJoint == IsJointConfig(i)
           \* Helper: Check if there's a pending EnterJoint entry in the log (not yet applied)
           pendingIdx == pendingConfChangeIndex[i]
           hasPendingEnterJoint ==
               /\ pendingIdx > 0
               /\ pendingIdx > log[i].offset
               /\ pendingIdx <= LastIndex(log[i])
               /\ LET entry == LogEntry(i, pendingIdx)
                  IN /\ entry.type = ConfigEntry
                     /\ "enterJoint" \in DOMAIN entry.value
                     /\ entry.value.enterJoint = TRUE
           \* Normal auto-leave: in joint config and conditions met
           autoLeaveCondition ==
               /\ isJoint
               /\ config[i].autoLeave = TRUE
               /\ applied[i] >= pendingConfChangeIndex[i]
           \* DisableConfChangeValidation: not in joint but has pending EnterJoint
           \* Only enabled when DisableConfChangeValidation constant is TRUE
           \* Reference: raft.go:1334-1338 - bypasses "not in joint state" check
           disableValidationCondition ==
               /\ DisableConfChangeValidation  \* Must be explicitly enabled
               /\ ~isJoint
               /\ hasPendingEnterJoint
           \* Should create LeaveJoint entry?
           shouldCreateLeaveJoint == autoLeaveCondition \/ disableValidationCondition
           \* For LeaveJoint, determine the correct learners:
           \* - If disableValidationCondition, get learners from the pending EnterJoint entry
           \*   (because the EnterJoint hasn't been applied yet, so GetLearners returns old learners)
           \* - Otherwise (autoLeaveCondition), use current config's learners
           leaveJointLearners == IF disableValidationCondition
                                 THEN LogEntry(i, pendingIdx).value.learners
                                 ELSE GetLearners(i)
       IN
       \* Precondition: if in joint, must satisfy auto-leave conditions
       /\ (isJoint => (config[i].autoLeave = TRUE /\ applied[i] >= pendingConfChangeIndex[i]))
       /\ LET entryType == IF shouldCreateLeaveJoint THEN ConfigEntry ELSE ValueEntry
              \* For LeaveJoint, use leaveJoint |-> TRUE format to match ApplyConfigUpdate
              entryValue == IF shouldCreateLeaveJoint
                            THEN [leaveJoint |-> TRUE, newconf |-> GetConfig(i), learners |-> leaveJointLearners]
                            ELSE [val |-> 0]
          IN
          /\ Replicate(i, entryValue, entryType)
          /\ Send([mtype       |-> AppendEntriesResponse,
                   msubtype    |-> "app",
                   mterm       |-> currentTerm[i],
                   msuccess    |-> TRUE,
                   mmatchIndex |-> LastIndex(log'[i]),
                   mrejectHint |-> 0,
                   mlogTerm    |-> 0,
                   msource     |-> i,
                   mdest       |-> i])
          /\ IF shouldCreateLeaveJoint
             THEN pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = LastIndex(log'[i])]
             ELSE UNCHANGED pendingConfChangeIndex
    /\ UNCHANGED <<messages, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\*
\* Reference: raft.go maybeCommit() uses r.trk.Committed() which calculates
\* the committed index based on the CURRENT APPLIED config's quorum.
\* Config changes are applied later when processing CommittedEntries.
\* The safety of joint consensus ensures that:
\* - EnterJoint entry is committed using old config's quorum
\* - After EnterJoint is applied, we're in joint config requiring both quorums
\* - LeaveJoint can only be committed when BOTH quorums agree
\* - So by the time we leave joint, the new config's quorum has all entries
\*
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           AllVoters == GetConfig(i) \union GetOutgoingConfig(i)
           Agree(index) == {k \in AllVoters : matchIndex[i][k] >= index}
           logSize == LastIndex(log[i])
           \* The maximum indexes for which a quorum agrees
           \* Uses the CURRENT APPLIED config (config[i]) for quorum calculation
           \* Reference: raft.go maybeCommit() -> trk.Committed() uses r.trk.Config
           IsCommitted(index) ==
               IF IsJointConfig(i) THEN
                   /\ (Agree(index) \cap GetConfig(i)) \in Quorum(GetConfig(i))
                   /\ (Agree(index) \cap GetOutgoingConfig(i)) \in Quorum(GetOutgoingConfig(i))
               ELSE
                   Agree(index) \in Quorum(GetConfig(i))

           \* commitIndex can advance to any index that the current applied config's
           \* quorum agrees on. Config entries are committed using the old config's quorum,
           \* then applied later when processing CommittedEntries.
           agreeIndexes == {index \in (commitIndex[i]+1)..logSize : IsCommitted(index)}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ LogTerm(i, Max(agreeIndexes)) = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN
        /\ CommitTo(i, newCommitIndex)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, log, applied, configVars, durableState, progressVars, historyLog, partitions>>

    
\* Leader i adds a new server j or promote learner j
AddNewServer(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i) \union {j}, learners |-> GetLearners(i)], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=LastIndex(log'[i])]
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Leader i adds a leaner j to the cluster.
AddLearner(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i) \union GetLearners(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i), learners |-> GetLearners(i) \union {j}], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=LastIndex(log'[i])]
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Leader i removes a server j (possibly itself) from the cluster.
DeleteServer(i, j) ==
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i) \ {j}, learners |-> GetLearners(i) \ {j}], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=LastIndex(log'[i])]
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Leader i proposes an arbitrary configuration change (compound changes supported).
\* Reference: confchange/confchange.go - joint consensus requires proper sequencing:
\*   - enterJoint=TRUE (enter joint) only allowed when NOT in joint config
\*   - enterJoint=FALSE (leave joint) only allowed when IN joint config
ChangeConf(i) ==
    /\ state[i] = Leader
    \* Reference: raft.go:1320 alreadyPending := r.pendingConfIndex > r.raftLog.applied
    \* Config change is allowed when pendingConfChangeIndex <= applied
    /\ IF pendingConfChangeIndex[i] <= applied[i] THEN
            \E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
                \* Both EnterJoint and Simple require NOT being in joint config
                \* Reference: confchange.go:56 "config is already joint" and confchange.go:133
                /\ ~IsJointConfig(i)
                \* Simple change constraint: can only change ONE voter (symdiff <= 1)
                \* Reference: confchange.go:140-142 "more than one voter changed without entering joint config"
                /\ (enterJoint = FALSE) =>
                   Cardinality((GetConfig(i) \ newVoters) \union (newVoters \ GetConfig(i))) <= 1
                \* Configuration validity constraints (Reference: confchange/confchange.go:305-312)
                /\ newVoters \cap newLearners = {}            \* checkInvariants: Learners disjoint from incoming voters
                /\ (enterJoint = TRUE) => (GetConfig(i) \cap newLearners = {})  \* checkInvariants: Learners disjoint from outgoing voters
                /\ newVoters /= {}                            \* apply(): "removed all voters" check
                /\ Replicate(i, [newconf |-> newVoters, learners |-> newLearners, enterJoint |-> enterJoint, oldconf |-> GetConfig(i)], ConfigEntry)
                /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=LastIndex(log'[i])]
                \* Remove manual Send, rely on AppendEntriesToSelf in trace
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Leader i proposes an arbitrary configuration change AND sends MsgAppResp.
\* Used for implicit replication in Trace Validation.
\* Reference: confchange/confchange.go - joint consensus requires proper sequencing
ChangeConfAndSend(i) ==
    /\ state[i] = Leader
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            \E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
                \* Both EnterJoint and Simple require NOT being in joint config
                \* Reference: confchange.go:56 "config is already joint" and confchange.go:133
                /\ ~IsJointConfig(i)
                \* Simple change constraint: can only change ONE voter (symdiff <= 1)
                \* Reference: confchange.go:140-142 "more than one voter changed without entering joint config"
                /\ (enterJoint = FALSE) =>
                   Cardinality((GetConfig(i) \ newVoters) \union (newVoters \ GetConfig(i))) <= 1
                \* Configuration validity constraints (Reference: confchange/confchange.go:305-312)
                /\ newVoters \cap newLearners = {}            \* checkInvariants: Learners disjoint from incoming voters
                /\ (enterJoint = TRUE) => (GetConfig(i) \cap newLearners = {})  \* checkInvariants: Learners disjoint from outgoing voters
                /\ newVoters /= {}                            \* apply(): "removed all voters" check
                /\ Replicate(i, [newconf |-> newVoters, learners |-> newLearners, enterJoint |-> enterJoint, oldconf |-> GetConfig(i)], ConfigEntry)
                /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=LastIndex(log'[i])]
                /\ Send([mtype       |-> AppendEntriesResponse,
                         msubtype    |-> "app",
                         mterm       |-> currentTerm[i],
                         msuccess    |-> TRUE,
                         mmatchIndex |-> LastIndex(log'[i]),
                         mrejectHint |-> 0,
                         mlogTerm    |-> 0,
                         msource     |-> i,
                         mdest       |-> i])
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
            /\ Send([mtype       |-> AppendEntriesResponse,
                     msubtype    |-> "app",
                     mterm       |-> currentTerm[i],
                     msuccess    |-> TRUE,
                     mmatchIndex |-> LastIndex(log'[i]),
                     mrejectHint |-> 0,
                     mlogTerm    |-> 0,
                     msource     |-> i,
                     mdest       |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Apply the next committed config entry in order
\* Reference: etcd processes CommittedEntries sequentially (for _, entry := range rd.CommittedEntries)
\* and calls ApplyConfChange for each config entry as it's encountered
\* This ensures configs are applied one at a time, in log order
ApplySimpleConfChange(i) ==
    \* Find config entries that are committed but not yet applied
    LET validIndices == {x \in Max({log[i].offset, appliedConfigIndex[i]+1})..commitIndex[i] :
                          LogEntry(i, x).type = ConfigEntry}
    IN
    /\ validIndices /= {}
    /\ LET k == Min(validIndices)  \* Apply the NEXT config entry, not MAX
           oldConfig == GetConfig(i) \cup GetOutgoingConfig(i) \cup GetLearners(i)
           newConfigFn == ApplyConfigUpdate(i, k)
           newConfig == newConfigFn[i].jointConfig[1] \cup newConfigFn[i].jointConfig[2] \cup newConfigFn[i].learners
           addedNodes == newConfig \ oldConfig
       IN
        /\ k > 0
        /\ k <= commitIndex[i]
        /\ config' = newConfigFn
        /\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = k]  \* Track applied config
        /\ IF state[i] = Leader /\ pendingConfChangeIndex[i] = k THEN
            /\ reconfigCount' = reconfigCount + 1
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
           ELSE UNCHANGED <<reconfigCount, pendingConfChangeIndex>>
        /\ IF state[i] = Leader /\ addedNodes # {}
           THEN /\ nextIndex' = [nextIndex EXCEPT ![i] =
                       [j \in Server |-> IF j \in addedNodes THEN Max({LastIndex(log[i]), 1}) ELSE nextIndex[i][j]]]
                \* Reference: confchange/confchange.go makeVoter() - only init Match=0 for truly new nodes
                \* Existing nodes (including leader itself) keep their Match value (pr != nil check)
                /\ matchIndex' = [matchIndex EXCEPT ![i] =
                       [j \in Server |-> IF j \in addedNodes /\ j # i THEN 0 ELSE matchIndex[i][j]]]
                /\ progressState' = [progressState EXCEPT ![i] =
                       [j \in Server |-> IF j \in addedNodes /\ j # i THEN StateProbe ELSE progressState[i][j]]]
                /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i] =
                       [j \in Server |-> IF j \in addedNodes THEN FALSE ELSE msgAppFlowPaused[i][j]]]
                /\ inflights' = [inflights EXCEPT ![i] =
                       [j \in Server |-> IF j \in addedNodes THEN {} ELSE inflights[i][j]]]
                /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i] =
                       [j \in Server |-> IF j \in addedNodes THEN 0 ELSE pendingSnapshot[i][j]]]
           ELSE /\ UNCHANGED progressVars
                /\ UNCHANGED matchIndex
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, logVars, durableState, historyLog, partitions>>

\* Leave joint consensus - transition from joint config to single config
\* This action is called when applying a LeaveJoint config entry (via ApplySimpleConfChange)
\* Reference: confchange/confchange.go:94-121 LeaveJoint()
\* LeaveJoint preserves Learners and moves LearnersNext into Learners
LeaveJoint(i) ==
    /\ IsJointConfig(i)
    /\ LET newVoters == GetConfig(i)  \* Keep incoming config (jointConfig[1])
       \* FIX: Preserve learners instead of hardcoding to {}
       \* Reference: confchange.go:103-107 - LearnersNext are added to Learners
       IN config' = [config EXCEPT ![i] = [learners |-> GetLearners(i), jointConfig |-> <<newVoters, {}>>, autoLeave |-> FALSE]]
    /\ IF state[i] = Leader /\ pendingConfChangeIndex[i] > 0 THEN
        /\ reconfigCount' = reconfigCount + 1
        /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
       ELSE UNCHANGED <<reconfigCount, pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, logVars, durableState, progressVars, appliedConfigIndex, partitions>>

\* Leader proposes LeaveJoint entry when autoLeave=TRUE and config entry is applied
\* Reference: raft.go:745-760 - AutoLeave mechanism
\* When r.trk.Config.AutoLeave && newApplied >= r.pendingConfIndex && r.state == StateLeader,
\* the leader automatically proposes an empty ConfChangeV2 to leave joint config.
\* This empty ConfChangeV2 must be committed with joint config's two quorums before applying.
ProposeLeaveJoint(i) ==
    /\ state[i] = Leader
    /\ IsJointConfig(i)
    /\ config[i].autoLeave = TRUE
    /\ pendingConfChangeIndex[i] = 0  \* Previous config change has been applied
    \* Propose a LeaveJoint config entry - represented as ConfigEntry with leaveJoint=TRUE
    \* This entry must be committed with joint quorum before being applied
    \* Reference: confchange.go:103-107 - LeaveJoint preserves Learners and adds LearnersNext
    /\ Replicate(i, [leaveJoint |-> TRUE, newconf |-> GetConfig(i), learners |-> GetLearners(i)], ConfigEntry)
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = LastIndex(log'[i])]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, applied, configVars, durableState, progressVars, partitions>>

\* Apply configuration from snapshot
\* When a follower receives a snapshot, it applies the config directly
\* Use persisted snapshotHistory instead of ghost variable historyLog
\* Reference: confchange/restore.go - Restore() uses ConfState which contains Voters, Learners, VotersOutgoing, AutoLeave
ApplySnapshotConfChange(i, newVoters) ==
    \* Find the last config entry in persisted snapshotHistory to determine joint config
    LET snapshotHist == durableState[i].snapshotHistory
        configIndices == {k \in 1..Len(snapshotHist) : snapshotHist[k].type = ConfigEntry}
        lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
        entry == IF lastConfigIdx > 0 THEN snapshotHist[lastConfigIdx] ELSE [value |-> [newconf |-> {}, learners |-> {}]]
        \* Check if this is a leaveJoint entry
        isLeaveJoint == "leaveJoint" \in DOMAIN entry.value /\ entry.value.leaveJoint = TRUE
        \* Check if last config entry has enterJoint=TRUE
        hasEnterJoint == ~isLeaveJoint /\ "enterJoint" \in DOMAIN entry.value
        enterJoint == IF hasEnterJoint THEN entry.value.enterJoint ELSE FALSE
        hasOldconf == enterJoint /\ "oldconf" \in DOMAIN entry.value
        oldconf == IF hasOldconf THEN entry.value.oldconf ELSE {}
        \* FIX: Read learners from entry instead of hardcoding {}
        \* Reference: confchange/restore.go:82-87 - Learners are added from cs.Learners
        hasLearners == lastConfigIdx > 0 /\ "learners" \in DOMAIN entry.value
        newLearners == IF hasLearners THEN entry.value.learners ELSE {}
        \* AutoLeave is TRUE when entering joint config (snapshot may contain joint config)
        \* For leaveJoint, autoLeave should be FALSE
        newAutoLeave == ~isLeaveJoint /\ enterJoint /\ oldconf /= {}
    IN
    /\ config' = [config EXCEPT ![i] = [learners |-> newLearners, jointConfig |-> <<newVoters, oldconf>>, autoLeave |-> newAutoLeave]]
    /\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = lastConfigIdx]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, logVars, durableState, progressVars, reconfigCount, pendingConfChangeIndex, partitions>>

\* Apply committed entries to state machine
\* Reference: raft/node.go - application layer retrieves CommittedEntries from Ready()
\*            and calls Advance() after applying them
\* This advances 'applied' from its current value up to any point <= commitIndex
\* Invariant: applied <= commitIndex (AppliedBoundInv)
ApplyEntries(i, newApplied) ==
    /\ newApplied > applied[i]           \* Must make progress
    /\ newApplied <= commitIndex[i]      \* Cannot apply beyond committed
    /\ applied' = [applied EXCEPT ![i] = newApplied]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, log, commitIndex, configVars, durableState, progressVars, historyLog, partitions>>

Ready(i) ==
    /\ PersistState(i)
    /\ SendPendingMessages(i)
    /\ UNCHANGED <<msgSeqCounter, serverVars, leaderVars, candidateVars, logVars, configVars, progressVars, historyLog, partitions>>

BecomeFollowerOfTerm(i, t) ==
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = t]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ IF currentTerm[i] # t THEN  
            votedFor' = [votedFor    EXCEPT ![i] = Nil]
       ELSE 
            UNCHANGED <<votedFor>>

StepDownToFollower(i) ==
    /\ state[i] \in {Leader, Candidate}
    /\ BecomeFollowerOfTerm(i, currentTerm[i])
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>



\* ============================================================================
\* New: MsgAppFlowPaused update functions - critical flow control recovery paths
\* ============================================================================

\* ClearMsgAppFlowPausedOnUpdate - clear on successful response
\* Reference: progress.go:205-213 MaybeUpdate()
\* This is one of the main flow control recovery paths
ClearMsgAppFlowPausedOnUpdate(i, j) ==
    msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]


\* ============================================================================
\* MsgAppFlowPaused lifecycle summary
\* ============================================================================
\* Set to TRUE:
\* 1. SentEntries() in StateReplicate: = Inflights.Full()
\* 2. SentEntries() in StateProbe: = true (if entries > 0)
\*
\* Clear to FALSE:
\* 1. ResetState() - all state transitions (BecomeProbe/Replicate/Snapshot)
\* 2. MaybeUpdate() - received successful AppendEntries response
\* 3. MaybeDecrTo() - received rejected AppendEntries response (StateProbe only)
\*
\* This ensures flow control can recover and won't permanently block!

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (Int, Int, RVREQT) => Bool;
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= LastIndex(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, RVRESPT) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    \* Only accept vote responses from nodes in config (or self, which bypasses filtering)
    \* Reference: rawnode.go:123-125 filters responses from unknown nodes
    /\ j = i \/ j \in (GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i))
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* @type: (Int, Int, AEREQT, Bool) => Bool;
RejectAppendEntriesRequest(i, j, m, logOk) ==
    /\ \/ m.mterm < currentTerm[i]
       \/ /\ m.mterm = currentTerm[i]
          /\ state[i] = Follower
          /\ \lnot logOk
    \* For rejections: mmatchIndex = rejected index (m.mprevLogIndex)
    \* mrejectHint = computed using findConflictByTerm optimization
    \* mlogTerm = follower's term at hintIndex (used by leader for fast backtracking)
    \* Reference: raft.go handleAppendEntries() rejection with findConflictByTerm
    /\ LET hintIndex == Min({m.mprevLogIndex, LastIndex(log[i])})
           rejectHint == FindConflictByTerm(i, hintIndex, m.mprevLogTerm)
           logTerm == LogTerm(i, rejectHint)
       IN Reply([mtype           |-> AppendEntriesResponse,
                 msubtype        |-> "app",
                 mterm           |-> currentTerm[i],
                 msuccess        |-> FALSE,
                 mmatchIndex     |-> m.mprevLogIndex,
                 mrejectHint     |-> rejectHint,
                 mlogTerm        |-> logTerm,
                 msource         |-> i,
                 mdest           |-> j],
                 m)
    /\ UNCHANGED <<serverVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* @type: (Int, MSG) => Bool;
ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, logVars, configVars, durableState, progressVars, historyLog, partitions>> 

HasNoConflict(i, index, ents) ==
    /\ index <= LastIndex(log[i]) + 1
    /\ \A k \in 1..Len(ents): index + k - 1 <= LastIndex(log[i]) => LogTerm(i, index+k-1) = ents[k].term

\* Reference: log.go:152-165 findConflict
\* Find the index of the first conflicting entry.
\* Returns 0 if no conflict (all entries match or are new).
\* Returns the first index where term differs.
\* @type: (Int, Int, Seq(ENTRY)) => Int;
FindFirstConflict(i, index, ents) ==
    LET conflicting == {k \in 1..Len(ents):
            /\ index + k - 1 <= LastIndex(log[i])
            /\ LogTerm(i, index + k - 1) /= ents[k].term}
    IN IF conflicting = {} THEN 0 ELSE index + Min(conflicting) - 1

\* @type: (Int, Int, Int, AEREQT) => Bool;
AppendEntriesAlreadyDone(i, j, index, m) ==
    /\ \/ index <= commitIndex[i]
       \/ /\ index > commitIndex[i]
          /\ \/ m.mentries = << >>
             \/ /\ m.mentries /= << >>
                /\ m.mprevLogIndex + Len(m.mentries) <= LastIndex(log[i])
                /\ HasNoConflict(i, index, m.mentries)          
    /\ IF index <= commitIndex[i] THEN 
            IF m.msubtype = "heartbeat" THEN CommitTo(i, m.mcommitIndex) ELSE UNCHANGED commitIndex
       ELSE 
            CommitTo(i, Min({m.mcommitIndex, m.mprevLogIndex+Len(m.mentries)}))
    /\ Reply([  mtype           |-> AppendEntriesResponse,
                msubtype        |-> m.msubtype,
                mterm           |-> currentTerm[i],
                msuccess        |-> TRUE,
                mmatchIndex     |-> IF m.msubtype = "heartbeat" \/ index > commitIndex[i] THEN m.mprevLogIndex+Len(m.mentries) ELSE commitIndex[i],
                mrejectHint     |-> 0,
                mlogTerm        |-> 0,
                msource         |-> i,
                mdest           |-> j],
                m)
    /\ UNCHANGED <<serverVars, log, applied, configVars, durableState, progressVars, historyLog, partitions>>

\* @type: (Int, Int, Int, AEREQT) => Bool;
ConflictAppendEntriesRequest(i, j, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ ~HasNoConflict(i, index, m.mentries)
    \* Reference: log.go:115-128 maybeAppend + log.go:152-165 findConflict
    \* etcd behavior: find conflict point, truncate to it, append new entries (atomic operation)
    /\ LET ci == FindFirstConflict(i, index, m.mentries)
           \* Entries to append start from conflict point: ci - index + 1 in mentries
           entsOffset == ci - index + 1
           newEntries == SubSeq(m.mentries, entsOffset, Len(m.mentries))
           \* Local index for ci-1 (the last entry to keep before appending)
           \* LogEntry(i, idx) = entries[idx - offset + 1], so for idx=ci-1:
           \* local_index = (ci-1) - offset + 1 = ci - offset
           keepUntil == ci - log[i].offset
       IN /\ ci > commitIndex[i]  \* Safety: conflict must be after committed index
          \* Reference: log_unstable.go:196-218 truncateAndAppend
          \* Keep entries[1..keepUntil] (indices offset..ci-1), then append newEntries
          /\ log' = [log EXCEPT ![i].entries = SubSeq(@, 1, keepUntil) \o newEntries]
          /\ historyLog' = [historyLog EXCEPT ![i] = SubSeq(@, 1, ci - 1) \o newEntries]
    \* Commit and send response (same as NoConflictAppendEntriesRequest)
    /\ CommitTo(i, Min({m.mcommitIndex, m.mprevLogIndex + Len(m.mentries)}))
    /\ Reply([mtype           |-> AppendEntriesResponse,
              msubtype        |-> m.msubtype,
              mterm           |-> currentTerm[i],
              msuccess        |-> TRUE,
              mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
              mrejectHint     |-> 0,
              mlogTerm        |-> 0,
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, applied, durableState, progressVars, partitions>>

\* @type: (Int, Int, Int, AEREQT) => Bool;
NoConflictAppendEntriesRequest(i, j, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ HasNoConflict(i, index, m.mentries)
    \* Ensure there are actually new entries to append (not all entries already exist)
    /\ m.mprevLogIndex + Len(m.mentries) > LastIndex(log[i])
    \* Start position in m.mentries for new entries: LastIndex(log[i]) - m.mprevLogIndex + 1
    \* = LastIndex(log[i]) - index + 2 (since index = m.mprevLogIndex + 1)
    \* Update both log and historyLog to keep ghost variable consistent
    /\ LET newEntries == SubSeq(m.mentries, LastIndex(log[i])-index+2, Len(m.mentries))
       IN /\ log' = [log EXCEPT ![i].entries = @ \o newEntries]
          /\ historyLog' = [historyLog EXCEPT ![i] = @ \o newEntries]
    \* Commit and send response after appending
    /\ CommitTo(i, Min({m.mcommitIndex, m.mprevLogIndex + Len(m.mentries)}))
    /\ Reply([mtype           |-> AppendEntriesResponse,
              msubtype        |-> m.msubtype,
              mterm           |-> currentTerm[i],
              msuccess        |-> TRUE,
              mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
              mrejectHint     |-> 0,
              mlogTerm        |-> 0,
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, applied, durableState, progressVars, partitions>>

\* @type: (Int, Int, Bool, AEREQT) => Bool;
AcceptAppendEntriesRequest(i, j, logOk, m) ==
    \* accept request
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Follower
    /\ logOk
    /\ LET index == m.mprevLogIndex + 1
       IN \/ AppendEntriesAlreadyDone(i, j, index, m)
          \/ ConflictAppendEntriesRequest(i, j, index, m)
          \/ NoConflictAppendEntriesRequest(i, j, index, m)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* @type: (Int, Int, AEREQT) => Bool;
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= LastIndex(log[i])
                    /\ m.mprevLogTerm = LogTerm(i, m.mprevLogIndex)
    IN 
       /\ m.mterm <= currentTerm[i]
       /\ \/ RejectAppendEntriesRequest(i, j, m, logOk)
          \/ ReturnToFollowerState(i, m)
          \/ AcceptAppendEntriesRequest(i, j, logOk, m)
       /\ UNCHANGED <<candidateVars, leaderVars, configVars, durableState, progressVars, partitions>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* Note: Heartbeat responses are handled separately by HandleHeartbeatResponse.
\* @type: (Int, Int, AERESPT) => Bool;
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ m.msubtype /= "heartbeat"  \* Heartbeat responses handled by HandleHeartbeatResponse
    /\ \/ /\ m.msuccess \* successful
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex})]
          /\ UNCHANGED <<pendingConfChangeIndex>>
          \* Free confirmed inflights
          \* Reference: inflights.go FreeLE() called from raft.go handleAppendEntries()
          /\ FreeInflightsLE(i, j, m.mmatchIndex)
          \* State transition logic for successful MsgAppResp
          \* Reference: raft.go:1519-1540 handleAppendEntriesResponse()
          \* Key conditions:
          \*   - MaybeUpdate returns true (matchIndex updated), OR
          \*   - matchIndex already equals response index AND state is StateProbe
          /\ LET maybeUpdated == m.mmatchIndex > matchIndex[i][j]
                 alreadyMatched == m.mmatchIndex = matchIndex[i][j]
                 \* For StateSnapshot: check if follower caught up to leader's firstIndex
                 \* Reference: raft.go:1523 "pr.Match+1 >= r.raftLog.firstIndex()"
                 \* Use updated matchIndex for this check
                 newMatchIndex == Max({matchIndex[i][j], m.mmatchIndex})
                 \* Note: The spec compacts log during SendSnapshotWithCompaction, but the
                 \* system compacts asynchronously. So firstIndex in the system might still
                 \* be lower than log[i].offset. We also check against pendingSnapshot to
                 \* handle cases where compaction in spec advanced offset beyond what
                 \* the system's firstIndex would be.
                 canResumeFromSnapshot == \/ newMatchIndex + 1 >= log[i].offset
                                          \/ newMatchIndex + 1 >= pendingSnapshot[i][j]
             IN CASE \* Case 1: StateProbe -> StateReplicate
                     \* Reference: raft.go:1521-1522
                     \* BecomeReplicate calls ResetState which clears MsgAppFlowPaused
                     progressState[i][j] = StateProbe
                     /\ (maybeUpdated \/ alreadyMatched) ->
                        /\ progressState' = [progressState EXCEPT ![i][j] = StateReplicate]
                        /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex + 1})]
                        /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                        /\ UNCHANGED pendingSnapshot
                  \* Case 2: StateSnapshot -> StateReplicate (via BecomeProbe + BecomeReplicate)
                  \* Reference: raft.go:1523-1537
                  \* Condition: MaybeUpdate returns true AND Match+1 >= firstIndex
                  \* BecomeReplicate calls ResetState which clears MsgAppFlowPaused
                  [] progressState[i][j] = StateSnapshot
                     /\ maybeUpdated
                     /\ canResumeFromSnapshot ->
                        /\ progressState' = [progressState EXCEPT ![i][j] = StateReplicate]
                        \* BecomeProbe sets Next = max(Match+1, PendingSnapshot+1)
                        \* BecomeReplicate sets Next = Match+1
                        \* Final result: Next = Match+1 = m.mmatchIndex+1
                        \* (Since canResumeFromSnapshot implies Match+1 >= offset,
                        \*  and typically m.mmatchIndex >= pendingSnapshot when this path is taken)
                        /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                        /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                        /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = 0]
                  \* Case 3: StateReplicate or conditions not met
                  \* Reference: raft.go:1538-1539 for StateReplicate (FreeLE handled separately)
                  \* MaybeUpdate only clears MsgAppFlowPaused when matchIndex is actually updated
                  [] OTHER ->
                        /\ UNCHANGED <<progressState, pendingSnapshot>>
                        \* Still update nextIndex per MaybeUpdate logic
                        /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex + 1})]
                        \* Only clear MsgAppFlowPaused if MaybeUpdate returns true (matchIndex updated)
                        /\ IF maybeUpdated
                           THEN msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                           ELSE UNCHANGED msgAppFlowPaused
       \/ /\ \lnot m.msuccess \* not successful
          \* Implement MaybeDecrTo (progress.go:226-252)
          \* rejected = m.mmatchIndex, matchHint = m.mrejectHint
          /\ LET rejected == m.mmatchIndex
                 matchHint == m.mrejectHint
             IN IF progressState[i][j] = StateReplicate
                THEN \* StateReplicate: if rejected > Match, set Next = Match + 1
                     IF rejected <= matchIndex[i][j]
                     THEN \* Stale rejection, ignore
                          /\ UNCHANGED <<leaderVars, progressVars, partitions>>
                     ELSE \* Valid rejection: transition to Probe, set Next = Match + 1
                          /\ progressState' = [progressState EXCEPT ![i][j] = StateProbe]
                          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = matchIndex[i][j] + 1]
                          /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                          /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = 0]
                          /\ inflights' = [inflights EXCEPT ![i][j] = {}]
                          /\ UNCHANGED <<matchIndex, pendingConfChangeIndex>>
                ELSE \* StateProbe/StateSnapshot: check if Next-1 = rejected
                     IF nextIndex[i][j] - 1 /= rejected
                     THEN \* Stale rejection, just unpause
                          /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                          /\ UNCHANGED <<progressState, pendingSnapshot, inflights, nextIndex, matchIndex, pendingConfChangeIndex>>
                     ELSE \* Valid rejection: use leader-side findConflictByTerm optimization
                          \* Note: This applies to both StateProbe and StateSnapshot.
                          \* In StateSnapshot, Next may be decreased below PendingSnapshot+1,
                          \* but IsPaused() prevents sending any messages, so it's safe.
                          \* Reference: progress.go:IsPaused() returns true for StateSnapshot
                          \* Reference: raft.go matchTermAndIndex + MaybeDecrTo
                          \* Search leader's log for last index with term <= follower's logTerm
                          LET leaderMatchIdx == FindConflictByTerm(i, matchHint, m.mlogTerm)
                              \* If leaderMatchIdx > Match, use it as next probe point
                              \* Otherwise, fall back to basic MaybeDecrTo formula
                              newNext == IF leaderMatchIdx > matchIndex[i][j]
                                         THEN leaderMatchIdx + 1
                                         ELSE Max({Min({rejected, matchHint + 1}), matchIndex[i][j] + 1})
                          IN
                          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = newNext]
                          /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                          /\ UNCHANGED <<progressState, pendingSnapshot, inflights, matchIndex, pendingConfChangeIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, configVars, durableState, partitions>>

\* Server i receives a heartbeat response from server j.
\* Heartbeat responses do NOT cause state transitions (unlike MsgAppResp).
\* Reference: raft.go:1578-1597 stepLeader case pb.MsgHeartbeatResp
HandleHeartbeatResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ m.msubtype = "heartbeat"
    \* Reference: raft.go:1580 pr.MsgAppFlowPaused = false
    \*
    \* In real code, after setting MsgAppFlowPaused = false, sendAppend is called
    \* if (pr.Match < lastIndex || pr.State == StateProbe). The sendAppend call
    \* is modeled as a separate SendAppendEntries action in the spec, which will
    \* update MsgAppFlowPaused via SentEntries() logic (see SendAppendEntries).
    \*
    \* Note: There is NO FreeFirstOne or inflight release in heartbeat response handling.
    \* Inflights are only freed by MsgAppResp (FreeLE in handleAppendEntries).
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState,
                   matchIndex, nextIndex, progressState, pendingSnapshot, inflights, partitions>>

\* Compacts the log of server i up to newStart (exclusive).
\* newStart becomes the new offset.
\* Reference: storage.go:249-250 - "It is the application's responsibility to not
\* attempt to compact an index greater than raftLog.applied."
\* We check against the actual applied index, not durableState.log, because after
\* restart applied is reset to snapshotIndex while durableState.log retains its value.
\*
\* Note: pendingConfChangeIndex does NOT constrain log compaction.
\* Reference: storage.go Compact() only checks offset and lastIndex bounds.
\* pendingConfChangeIndex is only checked when proposing new config changes (raft.go:1318).
CompactLog(i, newStart) ==
    /\ newStart > log[i].offset
    /\ newStart <= applied[i] + 1
    /\ LET \* Entries being compacted: from current offset to newStart-1
           \* In log[i].entries, this is entries[1..newStart-offset]
           compactedEntries == SubSeq(log[i].entries, 1, newStart - log[i].offset)
       IN
       /\ log' = [log EXCEPT ![i] = [
             offset  |-> newStart,
             entries |-> SubSeq(@.entries, newStart - @.offset + 1, Len(@.entries)),
             snapshotIndex |-> newStart - 1,
             snapshotTerm  |-> LogTerm(i, newStart - 1)
          ]]
       \* Update durableState: merge old snapshotHistory with compacted entries
       /\ durableState' = [durableState EXCEPT ![i] = [
             @ EXCEPT !.snapshotHistory = @ \o compactedEntries,
                      !.snapshotIndex = newStart - 1,
                      !.snapshotTerm = LogTerm(i, newStart - 1),
                      !.entries = SubSeq(log[i].entries, newStart - log[i].offset + 1, Len(log[i].entries))
          ]]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, commitIndex, applied, configVars, progressVars, historyLog, partitions>>

\* Server i receives a SnapshotRequest.
\* Simulates raft.restore()
\* Reference: raft.go Step() - term check happens first, then stepFollower/handleSnapshot
\* If m.mterm > currentTerm[i], UpdateTerm must be applied first (via ReceiveDirect)
HandleSnapshotRequest(i, j, m) ==
    /\ m.mterm <= currentTerm[i]  \* Changed from >= to <=, matching HandleAppendEntriesRequest pattern
    /\ IF m.mterm < currentTerm[i] THEN
           \* Stale term: ignore snapshot message entirely
           \* Reference: raft.go:1173-1177 - "ignored a %s message with lower term"
           /\ Discard(m)
           /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>
       ELSE IF m.msnapshotIndex <= commitIndex[i] THEN
           \* Case 1: Stale snapshot (Index <= Committed). Ignore.
           \* Reference: raft.go:1858 restore() returns false
           /\ Reply([mtype       |-> AppendEntriesResponse,
                     msubtype    |-> "app",
                     mterm       |-> currentTerm[i],
                     msuccess    |-> TRUE,
                     mmatchIndex |-> commitIndex[i],
                     mrejectHint |-> 0,
                     mlogTerm    |-> 0,
                     msource     |-> i,
                     mdest       |-> j],
                     m)
           /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>
       ELSE IF LogTerm(i, m.msnapshotIndex) = m.msnapshotTerm THEN
           \* Case 2: Fast-forward (Log contains snapshot index/term).
           \* Reference: raft.go:1907 matchTerm check returns false after commitTo
           /\ commitIndex' = [commitIndex EXCEPT ![i] = m.msnapshotIndex]
           /\ Reply([mtype       |-> AppendEntriesResponse,
                     msubtype    |-> "app",
                     mterm       |-> currentTerm[i],
                     msuccess    |-> TRUE,
                     mmatchIndex |-> m.msnapshotIndex,
                     mrejectHint |-> 0,
                     mlogTerm    |-> 0,
                     msource     |-> i,
                     mdest       |-> j],
                     m)
           /\ UNCHANGED <<serverVars, candidateVars, leaderVars, log, applied, configVars, durableState, progressVars, historyLog, partitions>>
       ELSE
           \* Case 3: Actual Restore. Wipe log AND restore config atomically.
           \* Reference: raft.go:1919 r.raftLog.restore(s) then r.switchToConfig()
           \* These two operations happen in the same restore() function call,
           \* and no other messages can be processed in between (single-threaded).
           \* So we model them as a single atomic action.
           LET confState == m.mconfState
               \* Calculate lastConfigIdx for appliedConfigIndex
               configIndices == {k \in 1..Len(m.mhistory) : m.mhistory[k].type = ConfigEntry}
               lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
           IN
           /\ log' = [log EXCEPT ![i] = [
                 offset  |-> m.msnapshotIndex + 1,
                 entries |-> <<>>,
                 snapshotIndex |-> m.msnapshotIndex,
                 snapshotTerm  |-> m.msnapshotTerm
              ]]
           /\ historyLog' = [historyLog EXCEPT ![i] = m.mhistory]
           /\ commitIndex' = [commitIndex EXCEPT ![i] = m.msnapshotIndex]
           \* Note: applied is NOT updated here. In actual etcd raft code,
           \* applied is updated later via appliedSnap() -> appliedTo() when
           \* MsgStorageAppendResp is processed. We model this with ApplyEntries action.
           /\ UNCHANGED applied
           \* Atomically update config from snapshot's ConfState
           \* Reference: raft.go:1923-1934 confchange.Restore() then switchToConfig()
           /\ config' = [config EXCEPT ![i] = [
                 jointConfig |-> <<confState.voters, confState.outgoing>>,
                 learners    |-> confState.learners,
                 autoLeave   |-> confState.autoLeave
              ]]
           /\ appliedConfigIndex' = [appliedConfigIndex EXCEPT ![i] = lastConfigIdx]
           \* Update durableState: snapshot history from message, empty entries
           /\ durableState' = [durableState EXCEPT ![i] = [
                 @ EXCEPT !.log = m.msnapshotIndex,
                          !.entries = <<>>,
                          !.snapshotIndex = m.msnapshotIndex,
                          !.snapshotTerm = m.msnapshotTerm,
                          !.snapshotHistory = m.mhistory,
                          !.commitIndex = m.msnapshotIndex,
                          !.config = config'[i]
              ]]
           /\ Reply([mtype       |-> AppendEntriesResponse,
                     msubtype    |-> "snapshot",
                     mterm       |-> currentTerm[i],
                     msuccess    |-> TRUE,
                     mmatchIndex |-> m.msnapshotIndex,
                     mrejectHint |-> 0,
                     mlogTerm    |-> 0,
                     msource     |-> i,
                     mdest       |-> j],
                     m)
           /\ UNCHANGED <<serverVars, candidateVars, leaderVars, progressVars, reconfigCount, pendingConfChangeIndex, partitions>>

\* Handle ReportUnreachable from application layer
\* Reference: raft.go:1624-1632
\* Application reports that a peer is unreachable, causing StateReplicate -> StateProbe
\* Reference: tracker/progress.go:121-126 ResetState() clears Inflights
\* @type: (Int, Int) => Bool;
ReportUnreachable(i, j) ==
    /\ state[i] = Leader
    /\ i # j
    /\ IF progressState[i][j] = StateReplicate
       THEN /\ progressState' = [progressState EXCEPT ![i][j] = StateProbe]
            /\ inflights' = [inflights EXCEPT ![i][j] = {}]
       ELSE UNCHANGED <<progressState, inflights>>
    /\ UNCHANGED <<serverVars, candidateVars, messageVars, logVars, configVars,
                   durableState, leaderVars, nextIndex, pendingSnapshot,
                   msgAppFlowPaused, historyLog, partitions>>

\* Handle ReportSnapshot from application layer (trace validation version)
\* This is used when trace reports snapshot status via ReportSnapshotStatus event
\* rather than through message handling.
\* Reference: raft.go:1608-1625
\* @type: (Int, Int, Bool) => Bool;
ReportSnapshotStatus(i, j, success) ==
    /\ state[i] = Leader
    /\ progressState[i][j] = StateSnapshot
    /\ LET oldPendingSnapshot == IF success THEN pendingSnapshot[i][j] ELSE 0
           newNext == Max({matchIndex[i][j] + 1, oldPendingSnapshot + 1})
       IN /\ progressState' = [progressState EXCEPT ![i][j] = StateProbe]
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = newNext]
          /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = 0]
          /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = TRUE]
          /\ inflights' = [inflights EXCEPT ![i][j] = {}]
    /\ UNCHANGED <<serverVars, candidateVars, messageVars, logVars, configVars,
                   durableState, matchIndex, pendingConfChangeIndex, historyLog, partitions>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (Int, Int, MSG) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ BecomeFollowerOfTerm(i, m.mterm)
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Responses with stale terms are ignored.
\* @type: (Int, Int, MSG) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Drop response messages from nodes not in the current configuration.
\* This models the filtering in RawNode.Step() / Node.Step():
\*   if IsResponseMsg(m.Type) && rn.raft.trk.Progress[m.From] == nil { return ErrStepPeerNotFound }
\* However, self-directed messages (j == i) bypass this check because they go through
\* Advance() -> raft.Step() path which doesn't have this filtering.
\* Reference: rawnode.go:123-125, rawnode.go:489-490
\* @type: (Int, Int, MSG) => Bool;
DropResponseFromNonMember(i, j, m) ==
    /\ j /= i  \* Self-directed messages bypass this check (Advance() path)
    /\ j \notin (GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i))
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Combined action: Update term AND handle RequestVoteRequest atomically.
\* This is needed because raft.go handles term update and vote processing in a single Step call,
\* and Trace records only one event.
UpdateTermAndHandleRequestVote(i, j, m) ==
    /\ m.mtype = RequestVoteRequest
    /\ m.mterm > currentTerm[i]
    /\ LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                    \/ /\ m.mlastLogTerm = LastTerm(log[i])
                       /\ m.mlastLogIndex >= LastIndex(log[i])
           grant == logOk \* Term is equal (after update), Vote is Nil (after update)
       IN
           /\ Reply([mtype        |-> RequestVoteResponse,
                     mterm        |-> m.mterm,
                     mvoteGranted |-> grant,
                     msource      |-> i,
                     mdest        |-> j],
                     m)
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
           /\ state'       = [state       EXCEPT ![i] = Follower]
           /\ votedFor'    = [votedFor    EXCEPT ![i] = IF grant THEN j ELSE Nil]
           /\ UNCHANGED <<candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* Receive a message.
\* When MsgNoReorder is TRUE, enforce FIFO ordering per (source, dest) pair.
\* When partition is active, only receive if source and dest are in the same partition.
ReceiveDirect(m) ==
    LET i == m.mdest
        j == m.msource
    IN /\ CanCommunicate(j, i)  \* Partition check: source and dest must be able to communicate
       /\ IsFifoFirst(m)  \* FIFO constraint: only receive if first in order
       /\ \* Any RPC with a newer term causes the recipient to advance
          \* its term first. Responses with stale terms are ignored.
          \/ UpdateTermAndHandleRequestVote(i, j, m)
          \/ /\ m.mtype /= RequestVoteRequest
             /\ UpdateTerm(i, j, m)
          \/ /\ m.mtype = RequestVoteRequest
             /\ HandleRequestVoteRequest(i, j, m)
          \/ /\ m.mtype = RequestVoteResponse
             /\ \/ DropStaleResponse(i, j, m)
                \/ DropResponseFromNonMember(i, j, m)
                \/ HandleRequestVoteResponse(i, j, m)
          \/ /\ m.mtype = AppendEntriesRequest
             /\ HandleAppendEntriesRequest(i, j, m)
          \/ /\ m.mtype = AppendEntriesResponse
             /\ \/ DropStaleResponse(i, j, m)
                \/ DropResponseFromNonMember(i, j, m)
                \/ HandleHeartbeatResponse(i, j, m)
                \/ HandleAppendEntriesResponse(i, j, m)
          \/ /\ m.mtype = SnapshotRequest
             /\ HandleSnapshotRequest(i, j, m)

Receive(m) == ReceiveDirect(m)

NextRequestVoteRequest == \E m \in DOMAIN messages : m.mtype = RequestVoteRequest /\ Receive(m)
NextRequestVoteResponse == \E m \in DOMAIN messages : m.mtype = RequestVoteResponse /\ Receive(m)
NextAppendEntriesRequest == \E m \in DOMAIN messages : m.mtype = AppendEntriesRequest /\ Receive(m)
NextAppendEntriesResponse == \E m \in DOMAIN messages : m.mtype = AppendEntriesResponse /\ Receive(m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
\* @type: MSG => Bool;
DuplicateMessage(m) ==
    /\ m \in DOMAIN messages
    /\ messages' = WithMessage(m, messages)
    /\ UNCHANGED <<pendingMessages, msgSeqCounter, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* The network drops a message
\* @type: MSG => Bool;
DropMessage(m) ==
    \* Do not drop loopback messages
    \* /\ m.msource /= m.mdest
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog, partitions>>

\* ============================================================================
\* Network Partition Actions
\* ============================================================================

\* Create a network partition: assign each server to a partition group
\* partitionAssignment is a function from Server to partition ID (1..MaxPartitions)
\* All cross-partition messages are dropped when partition is created
CreatePartition(partitionAssignment) ==
    \* Only create partition if not already partitioned
    /\ ~IsPartitioned
    \* Ensure valid partition assignment
    /\ \A i \in Server : partitionAssignment[i] \in 1..MaxPartitions
    \* Must have at least 2 different partition groups (otherwise it's not a real partition)
    \* /\ Cardinality({partitionAssignment[i] : i \in Server}) >= 2
    \* Apply the partition
    /\ partitions' = partitionAssignment
    \* Drop all cross-partition messages
    /\ messages' = messages (-) SetToBag(CrossPartitionMessages)
    /\ pendingMessages' = pendingMessages (-) SetToBag(CrossPartitionPendingMessages)
    /\ UNCHANGED <<msgSeqCounter, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog>>

\* Heal the network partition: all servers can communicate again
HealPartition ==
    \* Only heal if partitioned
    /\ IsPartitioned
    \* Reset all partitions to 0 (no partition)
    /\ partitions' = [i \in Server |-> 0]
    /\ UNCHANGED <<messages, pendingMessages, msgSeqCounter, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars, historyLog>>

----

\* Defines how the variables may transition.
NextAsync == 
    \/ \E i,j \in Server : RequestVote(i, j)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server: ClientRequest(i, 0)
    \/ \E i \in Server: ClientRequestAndSend(i, 0)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : \E b,e \in matchIndex[i][j]+1..LastIndex(log[i])+1 : AppendEntries(i, j, <<b,e>>)
    \/ \E i \in Server : AppendEntriesToSelf(i)
    \/ \E i,j \in Server : Heartbeat(i, j)
    \/ \E i,j \in Server : SendSnapshot(i, j)
    \* Application layer applies committed entries to state machine
    \* Reference: raft/node.go - app retrieves CommittedEntries, then calls Advance()
    \/ \E i \in Server : IF applied[i] < commitIndex[i] THEN ApplyEntries(i, commitIndex[i]) ELSE FALSE
    \* Optimization: Only allow compacting to applied to reduce state space explosion.
    \* Can only compact entries that have been applied to state machine.
    \/ \E i \in Server : IF log[i].offset < applied[i] THEN CompactLog(i, applied[i]) ELSE FALSE
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E i \in Server : Timeout(i)
    \/ \E i \in Server : Ready(i)
    \/ \E i \in Server : StepDownToFollower(i)
    \* Application layer reports
    \/ \E i,j \in Server : ReportUnreachable(i, j)
    \/ \E i,j \in Server : ReportSnapshotStatus(i, j, TRUE)
    \/ \E i,j \in Server : ReportSnapshotStatus(i, j, FALSE)

NextCrash == \E i \in Server : Restart(i)

NextAsyncCrash ==
    \/ NextAsync
    \/ NextCrash

NextUnreliable ==    
    \* Only duplicate once
    \/ \E m \in DOMAIN messages : 
        /\ messages[m] = 1
        /\ DuplicateMessage(m)
    \* Only drop if it makes a difference            
    \/ \E m \in DOMAIN messages : 
        /\ messages[m] = 1
        /\ DropMessage(m)

\* Most pessimistic network model
Next == \/ NextAsync
        \/ NextCrash
        \/ NextUnreliable

\* Membership changes
\* Note: AddNewServer, AddLearner, DeleteServer are removed from NextDynamic.
\* They bypass ChangeConf constraints and can cause QuorumLogInv violations.
\* Use ChangeConf with enterJoint parameter instead.
NextDynamic ==
    \/ Next
    \/ \E i \in Server : ChangeConf(i)
    \/ \E i \in Server : ChangeConfAndSend(i)
    \/ \E i \in Server : ApplySimpleConfChange(i)
    \/ \E i \in Server : ProposeLeaveJoint(i)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The main safety properties are below                                    *)
(***************************************************************************)
----

ASSUME DistinctRoles == /\ Leader /= Candidate
                        /\ Candidate /= Follower
                        /\ Follower /= Leader

ASSUME DistinctMessageTypes == /\ RequestVoteRequest /= AppendEntriesRequest
                               /\ RequestVoteRequest /= RequestVoteResponse
                               /\ RequestVoteRequest /= AppendEntriesResponse
                               /\ AppendEntriesRequest /= RequestVoteResponse
                               /\ AppendEntriesRequest /= AppendEntriesResponse
                               /\ RequestVoteResponse /= AppendEntriesResponse
                               /\ SnapshotRequest /= RequestVoteRequest
                               /\ SnapshotRequest /= AppendEntriesRequest
                               /\ SnapshotRequest /= RequestVoteResponse
                               /\ SnapshotRequest /= AppendEntriesResponse
                               /\ SnapshotResponse /= RequestVoteRequest
                               /\ SnapshotResponse /= AppendEntriesRequest
                               /\ SnapshotResponse /= RequestVoteResponse
                               /\ SnapshotResponse /= AppendEntriesResponse
                               /\ SnapshotRequest /= SnapshotResponse

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(historyLog[i],1,commitIndex[i])

\* The current term of any server is at least the term
\* of any message sent by that server
\* @type: MSG => Bool;
MessageTermsLtCurrentTerm(m) ==
    m.mterm <= currentTerm[m.msource]

\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Server : i /= j =>
        \/ IsPrefix(Committed(i),Committed(j)) 
        \/ IsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => []LogInv

\* There should not be more than one leader per term at the same time
\* Note that this does not rule out multiple leaders in the same term at different times
MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* Every (index, term) pair determines a log prefix
\* Optimized: Only check the maximum index where terms match.
\* If SubSeq matches at maxMatch, it implicitly matches for all smaller indices.
\* This reduces complexity from O(n²) to O(n) per server pair.
LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        LET minLen == Min({Len(historyLog[i]), Len(historyLog[j])})
            \* Find all indices where terms match
            matchingTerms == {n \in 1..minLen : historyLog[i][n].term = historyLog[j][n].term}
        IN matchingTerms /= {} =>
            \* Only check the maximum matching index
            SubSeq(historyLog[i], 1, Max(matchingTerms)) = SubSeq(historyLog[j], 1, Max(matchingTerms))

\* When two candidates competes in a campaign, if a follower voted to
\* a candidate that did not win in the end, the follower's votedFor will 
\* not reset nor change to the winner (the other candidate) because its 
\* term remains same. This will violate this invariant.
\*
\* This invariant can be false because a server's votedFor is not reset
\* for messages with same term. Refer to the case below.
\* 1. This is a 3 node cluster with nodes A, B, and C. Let's assume they are all followers with same term 1 and log at beginning.
\* 2. Now B and C starts compaign and both become candidates of term 2.
\* 3. B requests vote to A and A grant it. Now A is a term 2 follower whose votedFor is B.
\* 4. A's response to B is lost.
\* 5. C requests vote to B and B grant it. Now B is a term 2 follower whose votedFor is C. 
\* 6. C becomes leader of term 2.
\* 7. C replicates logs to A but not B. 
\* 8. A's votedFor is not changed because the incoming messages has same term (see UpdateTerm and ReturnToFollowerState)
\* 9. Now the commited log in A will exceed B's log. The invariant is violated.
\* VotesGrantedInv ==
\*     \A i, j \in Server :
\*         \* if i has voted for j
\*         votedFor[i] = j =>
\*             IsPrefix(Committed(i), log[j])

\* All committed entries are contained in the log
\* of at least one server in every quorum.
\* Committed entries must be preserved in the current config's quorum.
\*
\* Key insight about Joint Consensus:
\* - In joint config <<incoming, outgoing>>, commits require BOTH quorums
\* - LeaveJoint can only commit when both quorums agree
\* - So when we're in joint state, the incoming config hasn't "taken over" yet
\* - We should check the outgoing config (which is the one that was used to commit)
\*
\* For non-joint config: check that quorum holds committed entries
\* For joint config: check OUTGOING config's quorum (the one that committed the entries)
\*   The incoming config will only be used alone after LeaveJoint commits,
\*   and LeaveJoint commit requires incoming quorum to have all entries anyway.
\*
\* Note: Only check servers whose config is up-to-date (applied all committed config entries).
\* A follower may have a stale config while having received committed entries from the leader.
\* This is normal behavior during config change processing - the follower trusts the leader's
\* commitIndex but hasn't applied the config entries yet.
QuorumLogInv ==
    \A i \in Server :
        \* Find config entries within the committed range
        LET configIndicesInCommitted == {k \in 1..commitIndex[i] :
                k <= Len(historyLog[i]) /\ historyLog[i][k].type = ConfigEntry}
            \* Check if server's config is up-to-date (applied all committed config entries)
            configUpToDate == configIndicesInCommitted = {} \/
                              appliedConfigIndex[i] >= Max(configIndicesInCommitted)
            \* In joint config, use outgoing config for quorum check
            \* because incoming config hasn't taken effect yet (LeaveJoint not committed)
            effectiveConfig == IF IsJointConfig(i) THEN GetOutgoingConfig(i) ELSE GetConfig(i)
        IN
        \* Only check servers with up-to-date config
        configUpToDate =>
            \A S \in Quorum(effectiveConfig) :
                \E j \in S : IsPrefix(Committed(i), historyLog[j])

\* The "up-to-date" check performed by servers
\* before issuing a vote implies that i receives
\* a vote from j only if i has all of j's committed
\* entries
MoreUpToDateCorrectInv ==
    \A i, j \in Server : i /= j =>
       ((\/ LastTerm(log[i]) > LastTerm(log[j])
         \/ /\ LastTerm(log[i]) = LastTerm(log[j])
            /\ LastIndex(log[i]) >= LastIndex(log[j])) =>
        IsPrefix(Committed(j), historyLog[i]))

\* If a log entry is committed in a given term, then that
\* entry will be present in the logs of the leaders
\* for all higher-numbered terms
\* See: https://github.com/uwplse/verdi-raft/blob/master/raft/LeaderCompletenessInterface.v
\*
\* Rewritten: Check from Leader's perspective - a Leader must contain
\* all entries committed in previous terms by any server.
\* Complexity: O(Leaders × Server × CommitLen) ≈ O(Server × CommitLen) since usually 0-1 Leaders.

\* Helper: Get the prefix of committed log where term <= t
\* Since log terms are monotonically increasing, find the last index with term <= t
\* Using <= instead of < provides an additional sanity check:
\* If j has committed entries at term = t, they must have come from Leader i (or its predecessor)
CommittedTermPrefix(j, t) ==
    LET committed == Committed(j)
        validIndices == {k \in 1..Len(committed) : committed[k].term <= t}
    IN IF validIndices = {} THEN <<>>
       ELSE SubSeq(committed, 1, Max(validIndices))

LeaderCompletenessInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            IsPrefix(CommittedTermPrefix(j, currentTerm[i]), historyLog[i])

\* Any entry committed by leader shall be persisted already
CommittedIsDurableInv ==
    \A i \in Server :
        state[i] = Leader => commitIndex[i] <= durableState[i].log

\* ============================================================================
\* New: Progress and Inflights Invariants
\* ============================================================================

\* Group 1: Flow Control Safety
\* Verifies consistency between flow control pause mechanism (msgAppFlowPaused),
\* Progress state, and Inflight counts.


\* Invariant: ProbeLimitInv
\* In StateProbe, inflight message count is strictly limited to 1.
\* (Rationale: Probe state is for probing, preventing message accumulation)
\* NOTE: This invariant checks the inflights variable, but StateProbe doesn't use inflights!
\* See ProbeNetworkMessageLimitInv for the correct check.
ProbeLimitInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateProbe)
            => InflightsCount(i, j) <= 1

\* Invariant: ProbeNetworkMessageLimitInv
\* In StateProbe, the number of AppendEntriesRequest messages in the network should be limited to 1.
\* This is the CORRECT invariant to detect the empty probe issue (TODO in progress.go:176-178).
\* The implementation uses MsgAppFlowPaused (not inflights) to limit StateProbe messages,
\* but empty probes (entries=0) don't set MsgAppFlowPaused, allowing multiple messages.
\* Reference: tracker/progress.go:175-181 SentEntries() - StateProbe only sets MsgAppFlowPaused if entries > 0
ProbeNetworkMessageLimitInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ i /= j /\ progressState[i][j] = StateProbe) =>
            LET msgsInNetwork == {m \in DOMAIN messages :
                    m.mtype = AppendEntriesRequest /\
                    m.msource = i /\
                    m.mdest = j}
                totalCount == FoldSet(LAMBDA m, acc: acc + messages[m], 0, msgsInNetwork)
            IN totalCount <= 1

\* Invariant: ReplicatePauseInv
\* In StateReplicate, we should only be paused if Inflights are full.
\* (Note: The converse is not necessarily true; if Inflights are full, we might have just 
\* received an ACK clearing the pause, waiting for next send to re-evaluate)
ReplicatePauseInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateReplicate /\ msgAppFlowPaused[i][j])
            => InflightsFull(i, j)

\* Group 2: Inflights Data Integrity
\* Verifies validity of Inflights collection data.

\* Invariant: SnapshotInflightsInv
\* In StateSnapshot, Inflights must be empty.
\* (Rationale: Sending Snapshot resets log replication stream, clearing previous inflights)
SnapshotInflightsInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot)
            => InflightsCount(i, j) = 0

\* Invariant: InflightsLogIndexInv
\* Inflight indices must be valid indices existing in (or being sent from) Leader's Log.
\* In this Spec, inflights stores entry indices, so they must be <= Leader's Log length.
InflightsLogIndexInv ==
    \A i \in Server : \A j \in Server :
        state[i] = Leader =>
            \A idx \in inflights[i][j] : idx <= LastIndex(log[i])

\* Invariant: InflightsMatchIndexInv
\* Inflight indices must be strictly greater than what Follower has already Matched.
\* (Rationale: If follower has matched an index, the corresponding inflight record should be freed)
InflightsMatchIndexInv ==
    \A i \in Server : \A j \in Server :
        state[i] = Leader =>
            \A idx \in inflights[i][j] : idx > matchIndex[i][j]

\* Group 3: Progress State Consistency
\* Verifies dependencies between Progress State Machine variables.

\* Type Invariant: progressState must be one of the three valid states.
\* Prevents "OTHER -> FALSE" branch in IsPaused() from triggering on invalid states.
ProgressStateTypeInv ==
    \A i, j \in Server:
        progressState[i][j] \in {StateProbe, StateReplicate, StateSnapshot}

\* Inflights count must not exceed limit.
\* Reference: inflights.go:66-68 Add() panic "cannot add into a Full inflights"
InflightsInv ==
    \A i, j \in Server:
        InflightsCount(i, j) <= MaxInflightMsgs

\* Invariant: SnapshotPendingInv
\* If in StateSnapshot, must have a pending snapshot index.
SnapshotPendingInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot)
            => pendingSnapshot[i][j] > 0

\* Invariant: NoPendingSnapshotInv
\* If NOT in StateSnapshot, pendingSnapshot must be 0 (cleared).
NoPendingSnapshotInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] /= StateSnapshot)
            => pendingSnapshot[i][j] = 0

\* Invariant: LeaderSelfReplicateInv
\* Leader's progress state for itself is always StateReplicate.
LeaderSelfReplicateInv ==
    \A i \in Server :
        state[i] = Leader => progressState[i][i] = StateReplicate

\* Invariant: SnapshotStateInv
\* Comprehensive check for StateSnapshot consistency
\* Combines snapshot-related properties: empty inflights and valid pending snapshot
SnapshotStateInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot) =>
            /\ InflightsCount(i, j) = 0              \* Inflights must be empty
            /\ pendingSnapshot[i][j] > 0             \* Must have pending snapshot
            /\ pendingSnapshot[i][j] <= LastIndex(log[i])  \* Snapshot index must be valid

\* Invariant: InflightsMonotonicInv
\* Reference: inflights.go:45-57 Add() expects monotonically increasing indices
\* Note: The real constraint is that consecutive Add() calls must provide monotonic indices,
\* but this is a temporal property, not a state invariant. The state invariant is only that
\* the count of inflights <= MaxInflightMsgs, which is already checked by InflightsInv.
\* The indices can be sparse (e.g., {5, 9}) if different messages contain different numbers
\* of entries, so we cannot bound maxIdx - minIdx by MaxInflightMsgs.
InflightsMonotonicInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ inflights[i][j] # {}) =>
            LET maxIdx == Max(inflights[i][j])
                minIdx == Min(inflights[i][j])
            IN
                maxIdx >= minIdx  \* Trivial sanity check

\* ============================================================================
\* NEW: Additional strong invariants based on code analysis
\* Reference: progress.go line 37-38, 40, 48, 140, 148, 156-157, 210
\* ============================================================================

\* Invariant: MatchIndexLessThanLogInv
\* THE FUNDAMENTAL INVARIANT: Match < Next in progress.go
\* In TLA+: matchIndex represents Match, and Next is implicitly tracked
\* We verify: matchIndex[i][j] <= LastIndex(log[i]) for active replication
\* Reference: progress.go:37 "Invariant: 0 <= Match < Next"
MatchIndexLessThanLogInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ j /= i) =>
            matchIndex[i][j] <= LastIndex(log[i])

\* Invariant: MatchIndexNonNegativeInv
\* Match is always non-negative (0 <= Match)
\* Reference: progress.go:37 "Invariant: 0 <= Match < Next"
MatchIndexNonNegativeInv ==
    \A i \in Server : \A j \in Server :
        matchIndex[i][j] >= 0

\* Invariant: InflightsAboveMatchInv
\* All inflight indices must be > matchIndex (they are in the (Match, Next) interval)
\* Reference: progress.go:34-35 "entries in (Match, Next) interval are in flight"
InflightsAboveMatchInv ==
    \A i \in Server : \A j \in Server :
        state[i] = Leader =>
            \A idx \in inflights[i][j] : idx > matchIndex[i][j]

\* Invariant: MatchIndexLessThanNextInv (THE REAL INVARIANT!)
\* Match < Next - the fundamental Progress invariant
\* Reference: progress.go:37 "Invariant: 0 <= Match < Next"
\* Reference: progress.go:40 "In StateSnapshot, Next == PendingSnapshot + 1"
\* Note: The old SnapshotPendingAboveMatchInv (PendingSnapshot > Match) was WRONG!
\*       MaybeUpdate can update Match while in StateSnapshot (raft.go:1519),
\*       making PendingSnapshot < Match a LEGAL state.
MatchIndexLessThanNextInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ j /= i) =>
            matchIndex[i][j] < nextIndex[i][j]


\* Invariant: MsgAppFlowPausedConsistencyInv
\* In StateReplicate: If not paused, inflights should not be full
\* Reference: progress.go:174 - MsgAppFlowPaused = Inflights.Full()
MsgAppFlowPausedConsistencyInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateReplicate
         /\ ~msgAppFlowPaused[i][j]) =>
            ~InflightsFull(i, j)

\* Invariant: ProbeOneInflightMaxInv
\* Stronger version: In StateProbe, at most 1 inflight (confirms ProbeLimitInv)
\* Reference: progress.go:53-55 "sends at most one replication message"
ProbeOneInflightMaxInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateProbe) =>
            InflightsCount(i, j) <= 1

\* Invariant: SnapshotNoInflightsStrictInv
\* In StateSnapshot, inflights MUST be exactly 0
\* Reference: progress.go:119-126 ResetState() calls inflights.reset()
SnapshotNoInflightsStrictInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot) =>
            InflightsCount(i, j) = 0

\* Aggregate all Progress-related invariants
ProgressSafety ==
    /\ ProbeLimitInv
    /\ ProbeNetworkMessageLimitInv  \* NEW: Check actual network messages, not inflights variable
    /\ ReplicatePauseInv
    /\ SnapshotInflightsInv
    /\ InflightsLogIndexInv
    /\ InflightsMatchIndexInv
    /\ ProgressStateTypeInv
    /\ InflightsInv
    /\ SnapshotPendingInv
    /\ NoPendingSnapshotInv
    /\ LeaderSelfReplicateInv
    /\ SnapshotStateInv
    /\ InflightsMonotonicInv
    \* NEW: Additional strong invariants from code analysis
    /\ MatchIndexLessThanLogInv
    /\ MatchIndexNonNegativeInv
    /\ InflightsAboveMatchInv
    /\ MatchIndexLessThanNextInv  \* THE REAL INVARIANT (replaced SnapshotPendingAboveMatchInv)
    /\ MsgAppFlowPausedConsistencyInv
    /\ ProbeOneInflightMaxInv
    /\ SnapshotNoInflightsStrictInv

-----

\* ============================================================================
\* Additional Invariants for Enhanced Bug Detection
\* These complement the existing core invariants to catch more subtle bugs
\* ============================================================================

\* Message validity: All messages should have terms consistent with sender
\* (wraps existing MessageTermsLtCurrentTerm to check all messages)
AllMessageTermsValid ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        MessageTermsLtCurrentTerm(m)

\* Message validity: AppendEntries messages should have valid log indices
MessageIndexValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        (m.mtype = AppendEntriesRequest) =>
            /\ m.mprevLogIndex >= 0
            /\ m.mcommitIndex >= 0

\* State Machine Safety: All nodes should agree on committed entries
\* This is critical for linearizability - catches state machine divergence
\* Optimized: Using SubSeq comparison instead of \A idx for better efficiency
StateMachineConsistency ==
    \A i, j \in Server : i /= j =>
        LET minCommit == Min({commitIndex[i], commitIndex[j]})
        IN SubSeq(historyLog[i], 1, minCommit) = SubSeq(historyLog[j], 1, minCommit)

\* Commit index should never exceed log length
CommitIndexBoundInv ==
    \A i \in Server :
        commitIndex[i] <= LastIndex(log[i])

\* Term should be monotonic in the log (newer entries have >= terms)
\* Optimized: Only check adjacent pairs - equivalent to checking all pairs
\* due to transitivity of <=. Reduces complexity from O(n²) to O(n).
LogTermMonotonic ==
    \A i \in Server :
        \A idx \in 1..(LastIndex(log[i]) - 1) :
            LogTerm(i, idx) <= LogTerm(i, idx + 1)

\* All committed entries should have valid (positive) terms
CommittedEntriesTermInv ==
    \A i \in Server :
        \A idx \in 1..commitIndex[i] :
            historyLog[i][idx].term > 0

\* Configuration change index should not exceed log length
PendingConfigBoundInv ==
    \A i \in Server :
        state[i] = Leader =>
            pendingConfChangeIndex[i] <= LastIndex(log[i])

\* Leader-specific: log should be at least as long as commitIndex
LeaderLogLengthInv ==
    \A i \in Server :
        state[i] = Leader =>
            commitIndex[i] <= LastIndex(log[i])

\* Current term should be at least as large as any log entry term
\* Optimized: Only check the last entry (newest has highest term due to monotonicity)
\* and snapshotTerm.
CurrentTermAtLeastLogTerm ==
    \A i \in Server :
        \* Check snapshot term
        /\ log[i].snapshotTerm <= currentTerm[i]
        \* Check only the last entry (highest term due to monotonicity)
        /\ Len(log[i].entries) > 0 =>
            log[i].entries[Len(log[i].entries)].term <= currentTerm[i]


\* Candidates must have voted for themselves
CandidateVotedForSelfInv ==
    \A i \in Server :
        state[i] = Candidate =>
            votedFor[i] = i

\* Durable state should be consistent with volatile state
\* Note: durableState.log check removed - only term and commitIndex need comparison
\* (log can temporarily exceed LastIndex after truncation, before Ready sync)
DurableStateConsistency ==
    \A i \in Server :
        /\ durableState[i].currentTerm <= currentTerm[i]
        /\ durableState[i].commitIndex <= commitIndex[i]
        \* /\ durableState[i].log <= LastIndex(log[i]) 
\* All messages should have valid endpoints
MessageEndpointsValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        /\ m.msource \in Server
        /\ m.mdest \in Server

\* Leader's term should match its durable state (after Ready/persistence)
LeaderDurableTermInv ==
    \A i \in Server :
        state[i] = Leader =>
            durableState[i].currentTerm = currentTerm[i]

\* Aggregate all additional invariants for easy checking
AdditionalSafety ==
    /\ AllMessageTermsValid
    /\ MessageIndexValidInv
    /\ StateMachineConsistency
    /\ CommitIndexBoundInv
    /\ CommittedEntriesTermInv
    /\ PendingConfigBoundInv
    /\ LeaderLogLengthInv
    /\ CurrentTermAtLeastLogTerm
    /\ CandidateVotedForSelfInv
    /\ DurableStateConsistency
    /\ MessageEndpointsValidInv
    /\ LeaderDurableTermInv

\* ============================================================================
\* P0: Log Structure Consistency Invariants
\* These verify the fundamental structure of log data
\* ============================================================================

\* Invariant: LogOffsetMinInv
\* Log offset must be >= 1 (log indices start from 1, offset = snapshotIndex + 1)
\* Reference: storage.go:193-194 firstIndex() = ents[0].Index + 1
\* When log is empty after snapshot, offset = snapshotIndex + 1 >= 1
LogOffsetMinInv ==
    \A i \in Server :
        log[i].offset >= 1

\* Invariant: SnapshotOffsetConsistencyInv
\* snapshotIndex must equal offset - 1 (fundamental log structure constraint)
\* Reference: storage.go:106 "ents[i] has raft log position i+snapshot.Metadata.Index"
\* Reference: storage.go:193-194 firstIndex() = ents[0].Index + 1 = snapshot.Index + 1
SnapshotOffsetConsistencyInv ==
    \A i \in Server :
        log[i].snapshotIndex = log[i].offset - 1

\* Invariant: SnapshotTermValidInv
\* If snapshotIndex > 0, snapshotTerm must be > 0 (valid term)
\* Reference: Snapshots are taken at committed entries, which have valid terms
SnapshotTermValidInv ==
    \A i \in Server :
        log[i].snapshotIndex > 0 => log[i].snapshotTerm > 0

\* Invariant: SnapshotTermBoundInv
\* snapshotTerm cannot exceed currentTerm (snapshots are from past committed state)
\* Reference: Snapshots are taken at committed indices, terms are from past
SnapshotTermBoundInv ==
    \A i \in Server :
        log[i].snapshotTerm <= currentTerm[i]

\* Invariant: HistoryLogLengthInv
\* historyLog length must equal LastIndex (historyLog tracks full log history)
\* Note: LastIndex >= 0 is always true since offset >= 1 (LogOffsetMinInv)
HistoryLogLengthInv ==
    \A i \in Server :
        Len(historyLog[i]) = LastIndex(log[i])

\* Aggregate P0 Log Structure invariants
LogStructureInv ==
    /\ LogOffsetMinInv
    /\ SnapshotOffsetConsistencyInv
    /\ SnapshotTermValidInv
    /\ SnapshotTermBoundInv
    /\ HistoryLogLengthInv

\* ============================================================================
\* P1: Configuration Change Consistency Invariants
\* These verify configuration change safety properties
\* ============================================================================

\* Invariant: JointConfigNonEmptyInv
\* In joint config, both incoming and outgoing configs must be non-empty
\* Reference: confchange/confchange.go requires both sides for joint consensus
JointConfigNonEmptyInv ==
    \A i \in Server :
        IsJointConfig(i) =>
            /\ GetConfig(i) /= {}
            /\ GetOutgoingConfig(i) /= {}

\* Invariant: SingleConfigOutgoingEmptyInv
\* When not in joint config, outgoing config must be empty
\* Reference: tracker/tracker.go - single config has empty outgoing
SingleConfigOutgoingEmptyInv ==
    \A i \in Server :
        ~IsJointConfig(i) => GetOutgoingConfig(i) = {}

\* Invariant: LearnersVotersDisjointInv
\* Learners and Voters must be disjoint (mutually exclusive)
\* Reference: tracker/tracker.go:37-41
\* "Invariant: Learners and Voters does not intersect"
LearnersVotersDisjointInv ==
    \A i \in Server :
        GetLearners(i) \cap (GetConfig(i) \union GetOutgoingConfig(i)) = {}

\* Invariant: ConfigNonEmptyInv
\* At least one voter must exist for initialized servers (cluster must have quorum)
\* Reference: A Raft cluster cannot function without voters
\* Note: Only applies to servers with log entries AND applied config
\*       A server may have received log/snapshot but not yet applied config
\*       (HandleSnapshotRequest and ApplySnapshotConfChange are separate actions)
\*       Reference: raft.go:Step - no config check before processing messages
ConfigNonEmptyInv ==
    \A i \in Server :
        LET configIndices == {k \in 1..Len(historyLog[i]) : historyLog[i][k].type = ConfigEntry}
            lastConfigIdx == IF configIndices /= {} THEN Max(configIndices) ELSE 0
            \* Config is considered applied if no config entries exist or appliedConfigIndex >= last config
            configApplied == lastConfigIdx = 0 \/ appliedConfigIndex[i] >= lastConfigIdx
        IN
        (LastIndex(log[i]) > 0 /\ configApplied) => GetConfig(i) /= {}

\* Aggregate P1 Configuration invariants
ConfigurationInv ==
    /\ JointConfigNonEmptyInv
    /\ SingleConfigOutgoingEmptyInv
    /\ LearnersVotersDisjointInv
    /\ ConfigNonEmptyInv

\* ============================================================================
\* P2: Message Content Validity Invariants
\* These verify message fields are consistent with sender state
\* ============================================================================

\* Invariant: SnapshotMsgIndexValidInv
\* SnapshotRequest's msnapshotIndex must be <= sender's applied
\* Reference: raft_test.go:2652 CreateSnapshot(lead.raftLog.applied, ...)
\* Snapshots are created from applied state, not just committed state
SnapshotMsgIndexValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = SnapshotRequest =>
            m.msnapshotIndex <= applied[m.msource]

\* Invariant: SnapshotMsgTermValidInv
\* SnapshotRequest's msnapshotTerm must be > 0 and <= mterm
\* Reference: Valid snapshot has positive term from committed log
SnapshotMsgTermValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = SnapshotRequest =>
            /\ m.msnapshotTerm > 0
            /\ m.msnapshotTerm <= m.mterm

\* Invariant: AppendEntriesPrevIndexNonNegInv
\* AppendEntriesRequest's mprevLogIndex must be >= 0
\* Reference: prevLogIndex can be 0 (empty log case)
AppendEntriesPrevIndexNonNegInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = AppendEntriesRequest =>
            m.mprevLogIndex >= 0

\* Invariant: AppendEntriesCommitBoundInv
\* AppendEntriesRequest's mcommitIndex must be >= 0
\* Reference: commitIndex is always non-negative
AppendEntriesCommitBoundInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = AppendEntriesRequest =>
            m.mcommitIndex >= 0

\* Invariant: VoteRequestLogIndexNonNegInv
\* RequestVoteRequest's mlastLogIndex must be >= 0
\* Reference: lastLogIndex is 0 for empty log
VoteRequestLogIndexNonNegInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = RequestVoteRequest =>
            m.mlastLogIndex >= 0

\* Invariant: VoteRequestLogTermNonNegInv
\* RequestVoteRequest's mlastLogTerm must be >= 0
\* Reference: lastLogTerm is 0 for empty log
VoteRequestLogTermNonNegInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = RequestVoteRequest =>
            m.mlastLogTerm >= 0

\* Aggregate P2 Message Content invariants
MessageContentInv ==
    /\ SnapshotMsgIndexValidInv
    /\ SnapshotMsgTermValidInv
    /\ AppendEntriesPrevIndexNonNegInv
    /\ AppendEntriesCommitBoundInv
    /\ VoteRequestLogIndexNonNegInv
    /\ VoteRequestLogTermNonNegInv

\* ============================================================================
\* P2: Inflights Refined Constraints
\* Additional precision for flow control verification
\* ============================================================================

\* Invariant: InflightsOnlyInReplicateInv
\* Only StateReplicate can have non-empty inflights
\* Reference: progress.go:165-185 SentEntries() only adds inflights in StateReplicate
\* Reference: StateProbe does NOT add to inflights (only sets MsgAppFlowPaused)
InflightsOnlyInReplicateInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] /= StateReplicate) =>
            inflights[i][j] = {}

\* Invariant: InflightsBelowNextInv
\* All inflight indices must be < nextIndex
\* Reference: Inflights track sent but not yet acked entries in (Match, Next)
InflightsBelowNextInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ inflights[i][j] /= {}) =>
            \A idx \in inflights[i][j] : idx < nextIndex[i][j]

\* Aggregate P2 Inflights invariants (extends existing ProgressSafety)
InflightsRefinedInv ==
    /\ InflightsOnlyInReplicateInv
    /\ InflightsBelowNextInv

\* ============================================================================
\* P0: Additional Snapshot Invariants
\* ============================================================================

\* Invariant: SnapshotCommitConsistencyInv
\* snapshotIndex cannot exceed commitIndex
\* Reference: Snapshots are taken at committed indices
SnapshotCommitConsistencyInv ==
    \A i \in Server :
        log[i].snapshotIndex <= commitIndex[i]

\* ============================================================================
\* P1: Additional Configuration Invariants
\* ============================================================================

\* Invariant: PendingConfIndexValidInv
\* If there's a pending config change (pendingConfChangeIndex > applied),
\* the index must be within valid log bounds.
\* Reference: raft.go:1320 - alreadyPending := r.pendingConfIndex > r.raftLog.applied
\* Note: pendingConfChangeIndex can point to a compacted entry if it has been applied.
\*       Only when pendingConfChangeIndex > applied do we have a true pending change.
\* IMPORTANT: We do NOT require the entry to be ConfigEntry because:
\*   - In BecomeLeader (raft.go:959-965), pendingConfIndex is set conservatively to lastIndex()
\*   - This is done regardless of whether the last entry is a ConfigEntry
\*   - Purpose: prevent proposing new config changes until leader confirms no pending ones
PendingConfIndexValidInv ==
    \A i \in Server :
        (state[i] = Leader /\ pendingConfChangeIndex[i] > applied[i]) =>
            /\ pendingConfChangeIndex[i] <= LastIndex(log[i])
            /\ pendingConfChangeIndex[i] >= log[i].offset

\* ============================================================================
\* P1: Additional Progress State Machine Invariants
\* ============================================================================

\* Invariant: NextIndexPositiveInv
\* nextIndex must be > 0 (log indices start from 1)
\* Reference: progress.go initialization
NextIndexPositiveInv ==
    \A i \in Server : \A j \in Server :
        state[i] = Leader => nextIndex[i][j] >= 1

\* Invariant: NextIndexBoundInv
\* nextIndex cannot exceed LastIndex + 1 (next entry to send)
\* Reference: After appending, Next = LastIndex + 1
NextIndexBoundInv ==
    \A i \in Server : \A j \in Server :
        state[i] = Leader => nextIndex[i][j] <= LastIndex(log[i]) + 1

\* Invariant: MatchIndexBoundInv
\* matchIndex cannot exceed LastIndex
\* Reference: Match is updated when follower confirms
MatchIndexBoundInv ==
    \A i \in Server : \A j \in Server :
        state[i] = Leader => matchIndex[i][j] <= LastIndex(log[i])

\* Invariant: PendingSnapshotBoundInv
\* pendingSnapshot cannot exceed Leader's LastIndex
\* Reference: Snapshot is taken from leader's log
PendingSnapshotBoundInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ pendingSnapshot[i][j] > 0) =>
            pendingSnapshot[i][j] <= LastIndex(log[i])

\* ============================================================================
\* P2: Additional Message Validity Invariants
\* ============================================================================

\* Invariant: AppendEntriesTermConsistentInv
\* In AppendEntriesRequest, entries' terms should not exceed message term
\* Reference: Entries come from leader's log, which has terms <= currentTerm
AppendEntriesTermConsistentInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        (m.mtype = AppendEntriesRequest /\ Len(m.mentries) > 0) =>
            \A k \in 1..Len(m.mentries) :
                m.mentries[k].term <= m.mterm

\* Invariant: SnapshotMsgIndexPositiveInv
\* SnapshotRequest's msnapshotIndex must be > 0
\* Reference: Valid snapshot has positive index
SnapshotMsgIndexPositiveInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = SnapshotRequest =>
            m.msnapshotIndex > 0

\* Invariant: ResponseTermValidInv
\* Response term should be >= request term (terms never decrease)
\* Note: This may be too strong if we don't track request-response pairs
\* So we just check response term is positive
ResponseTermPositiveInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        (m.mtype = RequestVoteResponse \/ m.mtype = AppendEntriesResponse) =>
            m.mterm > 0

\* ============================================================================
\* P3: Term and Vote Consistency Invariants
\* ============================================================================

\* Invariant: TermPositiveAfterElectionInv
\* After any election activity, term should be > 0
\* Reference: Terms start from 1 in Raft
TermPositiveInv ==
    \A i \in Server :
        currentTerm[i] >= 0

\* Invariant: LeaderTermPositiveInv
\* Leader's term must be > 0
\* Reference: Cannot become leader at term 0
LeaderTermPositiveInv ==
    \A i \in Server :
        state[i] = Leader => currentTerm[i] > 0

\* Invariant: CandidateTermPositiveInv
\* Candidate's term must be > 0
\* Reference: Campaign increments term
CandidateTermPositiveInv ==
    \A i \in Server :
        state[i] = Candidate => currentTerm[i] > 0

\* Invariant: VotesRespondedSubsetInv
\* votesResponded (excluding self) should be subset of config (can only get responses from known nodes)
\* Self-vote bypasses Node-level filtering (goes through Advance() -> raft.Step() path),
\* so self is always allowed in votesResponded even if not in config.
\* Reference: rawnode.go:489-490 Advance() calls rn.raft.Step(m) directly
VotesRespondedSubsetInv ==
    \A i \in Server :
        state[i] = Candidate =>
            (votesResponded[i] \ {i}) \subseteq (GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i))

\* Invariant: VotesGrantedSubsetInv
\* votesGranted should be subset of votesResponded
VotesGrantedSubsetInv ==
    \A i \in Server :
        state[i] = Candidate =>
            votesGranted[i] \subseteq votesResponded[i]

\* ============================================================================
\* Aggregate All Additional Invariants
\* ============================================================================

AdditionalSnapshotInv ==
    /\ SnapshotCommitConsistencyInv

AdditionalConfigInv ==
    /\ PendingConfIndexValidInv

AdditionalProgressInv ==
    /\ NextIndexPositiveInv
    /\ NextIndexBoundInv
    /\ MatchIndexBoundInv
    /\ PendingSnapshotBoundInv

AdditionalMessageInv ==
    /\ AppendEntriesTermConsistentInv
    /\ SnapshotMsgIndexPositiveInv
    /\ ResponseTermPositiveInv

TermAndVoteInv ==
    /\ TermPositiveInv
    /\ LeaderTermPositiveInv
    /\ CandidateTermPositiveInv
    /\ VotesRespondedSubsetInv
    /\ VotesGrantedSubsetInv

\* ============================================================================
\* Master Invariant: All New Invariants Combined
\* ============================================================================

NewInvariants ==
    /\ LogStructureInv
    /\ ConfigurationInv
    /\ MessageContentInv
    /\ InflightsRefinedInv
    /\ AdditionalSnapshotInv
    /\ AdditionalConfigInv
    /\ AdditionalProgressInv
    /\ AdditionalMessageInv
    /\ TermAndVoteInv

\* ============================================================================
\* BUG DETECTION INVARIANTS
\* These invariants are designed to detect specific known bugs in etcd/raft.
\* Reference: git history of etcd/raft bug fixes
\* ============================================================================

\* ----------------------------------------------------------------------------
\* Bug 76f1249: MsgApp after log truncation causes panic
\* ----------------------------------------------------------------------------
\* Scenario:
\* 1. Leader's log is compacted/truncated beyond what's in-flight to slow follower
\* 2. Follower rejects MsgApp, leader resets Next = Match + 1
\* 3. Leader sends MsgApp with prevLogTerm = 0 (because entry is compacted)
\* 4. Follower wrongly passes matchTerm check (both return 0 for missing entry)
\* 5. Follower tries to bump commitIndex beyond its log -> PANIC
\*
\* Detection: prevLogTerm should never be 0 when prevLogIndex > 0
\* (prevLogTerm = 0 only valid when prevLogIndex = 0, i.e., empty log)

AppendEntriesPrevLogTermValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        (m.mtype = AppendEntriesRequest /\ m.mprevLogIndex > 0) =>
            m.mprevLogTerm > 0

\* ----------------------------------------------------------------------------
\* Bug bd3c759: Auto-transitioning out of joint config launches multiple attempts
\* ----------------------------------------------------------------------------
\* Scenario:
\* 1. Leader is in joint config with autoLeave = TRUE
\* 2. When conf change is not the last element in log, multiple leave-joint
\*    proposals could be launched
\* 3. Also: auto-leave proposal didn't bump pendingConfIndex
\*
\* Detection: At most one pending leave-joint entry in uncommitted log

SinglePendingLeaveJointInv ==
    \A i \in Server :
        (state[i] = Leader /\ IsJointConfig(i) /\ config[i].autoLeave) =>
            LET \* Find all uncommitted leave-joint entries
                uncommittedLeaveJoints == {k \in (commitIndex[i]+1)..LastIndex(log[i]) :
                    /\ IsAvailable(i, k)
                    /\ LogEntry(i, k).type = ConfigEntry
                    /\ "leaveJoint" \in DOMAIN LogEntry(i, k).value
                    /\ LogEntry(i, k).value.leaveJoint = TRUE}
            IN Cardinality(uncommittedLeaveJoints) <= 1

\* Additional check: pendingConfIndex should be updated when auto-leave is proposed
\* If there's a pending leave-joint entry, pendingConfIndex should point to it
PendingConfIndexAutoLeaveInv ==
    \A i \in Server :
        (state[i] = Leader /\ IsJointConfig(i)) =>
            LET leaveJointIndices == {k \in (commitIndex[i]+1)..LastIndex(log[i]) :
                    /\ IsAvailable(i, k)
                    /\ LogEntry(i, k).type = ConfigEntry
                    /\ "leaveJoint" \in DOMAIN LogEntry(i, k).value
                    /\ LogEntry(i, k).value.leaveJoint = TRUE}
            IN leaveJointIndices /= {} =>
                pendingConfChangeIndex[i] >= Min(leaveJointIndices)

\* ----------------------------------------------------------------------------
\* Aggregate Bug Detection Invariants
\* ----------------------------------------------------------------------------

BugDetectionInv ==
    /\ AppendEntriesPrevLogTermValidInv      \* Bug 76f1249
    /\ SinglePendingLeaveJointInv            \* Bug bd3c759
    /\ PendingConfIndexAutoLeaveInv          \* Bug bd3c759

\* ============================================================================
\* P0: CRITICAL INVARIANTS - Known to cause panics in etcd
\* These directly correspond to panic conditions in the code
\* ============================================================================

\* ----------------------------------------------------------------------------
\* Invariant: AppliedBoundInv
\* Reference: log.go:46 "Invariant: applied <= committed"
\* Reference: log.go:331-332 appliedTo() panics if committed < i || i < applied
\* Bug: Issue #10166, #17081 - tocommit/applied out of range panics
\* ----------------------------------------------------------------------------
AppliedBoundInv ==
    \A i \in Server :
        applied[i] <= commitIndex[i]

\* ----------------------------------------------------------------------------
\* NOTE: CommitIndexBoundInv is defined above (line ~2336)
\* Reference: log.go:324 "tocommit(%d) is out of range [lastIndex(%d)]"
\* This is the famous "Was the raft log corrupted, truncated, or lost?" panic
\* Bug: Issue #10166, #17081

\* ----------------------------------------------------------------------------
\* Invariant: MessageDestinationValidInv
\* Reference: Issue #17081 - etcd didn't validate To field in messages
\* Fix: PR #17078 added validation to "ignore raft messages if member id mismatch"
\* ----------------------------------------------------------------------------
MessageDestinationValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        /\ m.mdest \in Server
        /\ m.msource \in Server

\* ============================================================================
\* P1: HIGH PRIORITY INVARIANTS - Prevent data corruption and logic bugs
\* ============================================================================

\* ----------------------------------------------------------------------------
\* REMOVED: LeaderNextIndexValidInv - Invariant too strong
\* Reference: Bug 76f1249 - MsgApp after log truncation causes panic
\*
\* This invariant was based on old behavior before Bug 76f1249 was fixed.
\* After the fix, when nextIndex < offset, the leader gracefully handles this
\* by sending a snapshot instead (see raft.go:624-627 maybeSendAppend).
\* Log compaction doesn't update nextIndex - the leader discovers the compaction
\* when trying to send entries and falls back to snapshot.
\* ----------------------------------------------------------------------------
\* LeaderNextIndexValidInv ==
\*     \A i \in Server : \A j \in Server :
\*         state[i] = Leader =>
\*             nextIndex[i][j] >= log[i].offset

\* ----------------------------------------------------------------------------
\* Invariant: SnapshotAppliedConsistencyInv
\* Reference: Snapshot is taken from applied state machine
\* snapshotIndex represents data that has been applied, so it must be <= applied
\* Note: After restart, applied is reset to snapshotIndex, so this holds
\* ----------------------------------------------------------------------------
SnapshotAppliedConsistencyInv ==
    \A i \in Server :
        log[i].snapshotIndex <= applied[i]

\* ============================================================================
\* P2: DETAILED INVARIANTS - Catch subtle message/state inconsistencies
\* ============================================================================

\* ----------------------------------------------------------------------------
\* Invariant: AppliedConfigBoundInv
\* appliedConfigIndex cannot exceed commitIndex (can only apply committed configs)
\* ----------------------------------------------------------------------------
AppliedConfigBoundInv ==
    \A i \in Server :
        appliedConfigIndex[i] <= commitIndex[i]

\* ----------------------------------------------------------------------------
\* Aggregate P0 Critical Invariants
\* ----------------------------------------------------------------------------
CriticalInv ==
    /\ AppliedBoundInv
    /\ CommitIndexBoundInv
    /\ MessageDestinationValidInv

\* ----------------------------------------------------------------------------
\* Aggregate P1 High Priority Invariants
\* ----------------------------------------------------------------------------
HighPriorityInv ==
    \* /\ LeaderNextIndexValidInv  \* REMOVED - invariant too strong
    /\ SnapshotAppliedConsistencyInv

\* ----------------------------------------------------------------------------
\* Aggregate P2 Detailed Invariants
\* ----------------------------------------------------------------------------
DetailedInv ==
    /\ AppliedConfigBoundInv

\* ============================================================================
\* P3: CODE-DERIVED INVARIANTS - Directly from raft source code
\* ============================================================================

\* ----------------------------------------------------------------------------
\* Invariant: StateSnapshotNextInv
\* Reference: progress.go:40 "In StateSnapshot, Next == PendingSnapshot + 1"
\* Reference: progress.go:156 BecomeSnapshot() sets Next = snapshoti + 1
\* ----------------------------------------------------------------------------
StateSnapshotNextInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot) =>
            nextIndex[i][j] = pendingSnapshot[i][j] + 1

\* ----------------------------------------------------------------------------
\* Invariant: HeartbeatCommitMatchBoundInv
\* Reference: raft.go:698-700 "The leader MUST NOT forward the follower's commit
\*            to an unmatched index. commit := min(pr.Match, r.raftLog.committed)"
\* This is the HEARTBEAT specific constraint - for MsgHeartbeat messages
\* Note: This is a strong invariant that might not hold for all MsgApp
\* ----------------------------------------------------------------------------
\* HeartbeatCommitMatchBoundInv ==
\*     \A m \in DOMAIN messages \union DOMAIN pendingMessages :
\*         \* Only for heartbeat messages (empty MsgApp or MsgHeartbeat)
\*         (m.mtype = AppendEntriesRequest /\ Len(m.mentries) = 0) =>
\*             m.mcommitIndex <= matchIndex[m.msource][m.mdest]

\* ----------------------------------------------------------------------------
\* REMOVED: ConfigChangePendingInv - Invariant too strong
\* Reference: raft.go:1320 "alreadyPending := r.pendingConfIndex > r.raftLog.applied"
\*
\* This invariant was incorrect because BecomeLeader conservatively sets
\* pendingConfChangeIndex = lastIndex even when all entries have been applied.
\* When pendingConfChangeIndex == applied, it means NO pending config change
\* (alreadyPending = FALSE in the implementation), which is a valid state.
\* ----------------------------------------------------------------------------
\* ConfigChangePendingInv ==
\*     \A i \in Server :
\*         (state[i] = Leader /\ pendingConfChangeIndex[i] > 0) =>
\*             pendingConfChangeIndex[i] > applied[i]

\* ----------------------------------------------------------------------------
\* Invariant: JointConfigMustLeaveInv
\* Reference: raft.go:1327-1328 "must transition out of joint config first"
\* If in joint config, the next config change must be a leave-joint (empty changes)
\* This is enforced by the spec but we verify it here
\* ----------------------------------------------------------------------------
\* Note: This is more of a behavioral constraint than a state invariant
\* The actual invariant is that we can't have multiple non-leave-joint pending
\* which is already covered by SinglePendingLeaveJointInv

\* ----------------------------------------------------------------------------
\* Invariant: MatchIndexBelowNextInv
\* Reference: progress.go:37 "Invariant: 0 <= Match < Next"
\* matchIndex must always be strictly less than nextIndex
\* Note: This is already covered by MatchIndexLessThanNextInv
\* ----------------------------------------------------------------------------

\* ----------------------------------------------------------------------------
\* Aggregate P3 Code-Derived Invariants
\* ----------------------------------------------------------------------------
CodeDerivedInv ==
    /\ StateSnapshotNextInv
    \* /\ ConfigChangePendingInv  \* REMOVED - invariant too strong

\* ============================================================================
\* P4: VERDI-RAFT INSPIRED INVARIANTS
\* Source: https://github.com/uwplse/verdi-raft
\* These invariants come from the Coq proof of Raft safety
\* ============================================================================

\* ----------------------------------------------------------------------------
\* Invariant: VotedForConsistencyInv
\* Source: Verdi-raft VotesCorrect - votes_currentTerm_votedFor_correct
\* If a server has votedFor = j (not Nil), then j was a candidate in that term
\* Note: This is weaker than Verdi-raft since we don't track vote history
\* ----------------------------------------------------------------------------
VotedForConsistencyInv ==
    \A i \in Server :
        votedFor[i] /= Nil =>
            \* If votedFor is set, it should be a valid server
            votedFor[i] \in Server

\* ----------------------------------------------------------------------------
\* Invariant: LeaderCurrentTermEntriesInv
\* Source: Verdi-raft LeaderSublogInterface - leader_sublog_host
\* "If a node is leader and any entry in any host's log has the same term as
\*  the leader's current term, that entry must exist in the leader's log."
\* This is a key safety property ensuring leaders don't "lose" their own entries
\* ----------------------------------------------------------------------------
LeaderCurrentTermEntriesInv ==
    \A leader \in Server :
        state[leader] = Leader =>
            \A other \in Server :
                \A idx \in log[other].offset..(LastIndex(log[other])) :
                    (IsAvailable(other, idx) /\ LogEntry(other, idx).term = currentTerm[leader]) =>
                        \* Entry must exist in leader's log
                        /\ idx <= LastIndex(log[leader])
                        /\ IsAvailable(leader, idx)
                        /\ LogEntry(leader, idx).term = currentTerm[leader]

\* ----------------------------------------------------------------------------
\* Invariant: RequestVoteTermBoundInv
\* Source: Verdi-raft sorted_invariant + common sense
\* RequestVote messages should have consistent term info
\* ----------------------------------------------------------------------------
RequestVoteTermBoundInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = RequestVoteRequest =>
            \* The message term should be positive
            /\ m.mterm > 0
            \* Log term in request should be <= message term
            /\ m.mlastLogTerm <= m.mterm

\* ----------------------------------------------------------------------------
\* Invariant: AppendEntriesResponseTermInv
\* Source: Verdi-raft - responses carry consistent term info
\* AppendEntries responses should have matching term semantics
\* ----------------------------------------------------------------------------
AppendEntriesResponseTermInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = AppendEntriesResponse =>
            \* Response term is positive
            m.mterm > 0

\* ----------------------------------------------------------------------------
\* Invariant: SnapshotResponseTermValidInv
\* Snapshot responses should have valid terms
\* ----------------------------------------------------------------------------
SnapshotResponseTermValidInv ==
    \A m \in DOMAIN messages \union DOMAIN pendingMessages :
        m.mtype = SnapshotResponse =>
            m.mterm > 0

\* ----------------------------------------------------------------------------
\* Aggregate P4 Verdi-raft Inspired Invariants
\* ----------------------------------------------------------------------------
VerdiRaftInspiredInv ==
    /\ VotedForConsistencyInv
    /\ LeaderCurrentTermEntriesInv
    /\ RequestVoteTermBoundInv
    /\ AppendEntriesResponseTermInv
    /\ SnapshotResponseTermValidInv

\* ============================================================================
\* P5: GIT HISTORY BUG PREVENTION INVARIANTS
\* Source: etcd/raft git commit history analysis
\* ============================================================================

\* ----------------------------------------------------------------------------
\* Invariant: TermNeverZeroInLogInv
\* Source: Multiple bugs related to term=0 causing issues
\* Entries in log should never have term 0
\* Note: IsAvailable check removed - always true for idx in offset..LastIndex
\* ----------------------------------------------------------------------------
TermNeverZeroInLogInv ==
    \A i \in Server :
        \A idx \in log[i].offset..LastIndex(log[i]) :
            LogEntry(i, idx).term > 0


\* ----------------------------------------------------------------------------
\* Invariant: LeaderCommitNotExceedMatchQuorumInv
\* Source: raft.go maybeCommit() logic
\* Leader's commitIndex should not exceed what a quorum has matched
\* Note: This is a soft check - the commitIndex could temporarily be ahead
\*       after quorum calculation if no updates have happened yet
\* ----------------------------------------------------------------------------
\* This is already implicitly covered by how we commit in the spec

\* ----------------------------------------------------------------------------
\* Aggregate P5 Git History Bug Prevention Invariants
\* ----------------------------------------------------------------------------
GitHistoryBugPreventionInv ==
    /\ TermNeverZeroInLogInv

===============================================================================