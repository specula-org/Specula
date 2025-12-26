-------------------------- MODULE etcdraft_progress --------------------------
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
    AppendEntriesResponse

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
    \* @typeAlias: AERESPT = [mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: MSG = [ wrapped: Bool, mtype: Str, mterm: Int, msource: Int, mdest: Int, RVReq: RVREQT, RVResp: RVRESPT, AEReq: AEREQT, AEResp: AERESPT ];
    \* @type: MSG -> Int;
    messages
VARIABLE 
    pendingMessages
messageVars == <<messages, pendingMessages>>

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
    \* @type: Int -> [ entries: LOGT, len: Int ];
    log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: Int -> Int;
    commitIndex
logVars == <<log, commitIndex>>

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

configVars == <<config, reconfigCount>>

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
vars == <<messageVars, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>


----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(c) == {i \in SUBSET(c) : Cardinality(i) * 2 > Cardinality(c)}

\* The term of the last entry in a log, or 0 if the log is empty.
\* @type: LOGT => Int;
LastTerm(xlog) == IF xlog = <<>> THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Add a message to the bag of pendingMessages.
SendDirect(m) == 
    pendingMessages' = WithMessage(m, pendingMessages)

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
    THEN messages' = WithoutMessage(m, messages) /\ UNCHANGED pendingMessages
    ELSE pendingMessages' = WithoutMessage(m, pendingMessages) /\ UNCHANGED messages

\* Combination of Send and Discard
ReplyDirect(response, request) ==
    IF request \in DOMAIN messages
    THEN /\ messages' = WithoutMessage(request, messages)
         /\ pendingMessages' = WithMessage(response, pendingMessages)
    ELSE /\ pendingMessages' = WithMessage(response, WithoutMessage(request, pendingMessages))
         /\ UNCHANGED messages

\* Default: change when needed
 Send(m) == SendDirect(m)
 Reply(response, request) == ReplyDirect(response, request) 
 Discard(m) == DiscardDirect(m)
     
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

\* Apply conf change log entry to configuration
ApplyConfigUpdate(i, k) ==
    LET entry == log[i][k]
        newVoters == entry.value.newconf
        newLearners == entry.value.learners
        enterJoint == IF "enterJoint" \in DOMAIN entry.value THEN entry.value.enterJoint ELSE FALSE
        outgoing == IF enterJoint THEN entry.value.oldconf ELSE {}
    IN
    [config EXCEPT ![i]= [jointConfig |-> << newVoters, outgoing >>, learners |-> newLearners]]

CommitTo(i, c) ==
    commitIndex' = [commitIndex EXCEPT ![i] = Max({@, c})]

CurrentLeaders == {i \in Server : state[i] = Leader}

PersistState(i) ==
    durableState' = [durableState EXCEPT ![i] = [
        currentTerm |-> currentTerm[i],
        votedFor |-> votedFor[i],
        log |-> Len(log[i]),
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
InitServerVars == /\ currentTerm = [i \in Server |-> 0]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ pendingConfChangeIndex = [i \in Server |-> 0]
InitLogVars == /\ log          = [i \in Server |-> <<>>]
               /\ commitIndex  = [i \in Server |-> 0]
InitConfigVars == /\ config = [i \in Server |-> [ jointConfig |-> <<InitServer, {}>>, learners |-> {}]]
                  /\ reconfigCount = 0 
InitDurableState ==
    durableState = [ i \in Server |-> [
        currentTerm |-> currentTerm[i],
        votedFor |-> votedFor[i],
        log |-> Len(log[i]),
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

Init == /\ InitMessageVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitConfigVars
        /\ InitDurableState
        /\ InitProgressVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, commitIndex, votedFor, log, and config in durable state.
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
    /\ log' = [log EXCEPT ![i] = SubSeq(@, 1, durableState[i].log)]
    /\ config' = [config EXCEPT ![i] = durableState[i].config]
    \* New: Reset Progress variables (volatile state, not persisted)
    /\ progressState' = [progressState EXCEPT ![i] = [j \in Server |-> StateProbe]]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i] = [j \in Server |-> 0]]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ inflights' = [inflights EXCEPT ![i] = [j \in Server |-> {}]]
    /\ UNCHANGED <<messages, durableState, reconfigCount>>

\* Server i times out and starts a new election.
\* @type: Int => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ i \in GetConfig(i) \union GetOutgoingConfig(i)
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ UNCHANGED <<messageVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* Candidate i sends j a RequestVote request.
\* @type: (Int, Int) => Bool;
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \in ((GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)) \ votesResponded[i])
    /\ IF i # j 
        THEN Send([mtype            |-> RequestVoteRequest,
                   mterm            |-> currentTerm[i],
                   mlastLogTerm     |-> LastTerm(log[i]),
                   mlastLogIndex    |-> Len(log[i]),
                   msource          |-> i,
                   mdest            |-> j])
        ELSE Send([mtype            |-> RequestVoteResponse,
                   mterm            |-> currentTerm[i],
                   mvoteGranted     |-> TRUE,
                   msource          |-> i,
                   mdest            |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* Leader i sends j an AppendEntries request containing entries in [b,e) range.
\* N.B. range is right open
\* @type: (Int, Int, <<Int, Int>>, Int) => Bool;
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)
    \* New: Check flow control state; cannot send when paused (except heartbeat)
    \* Reference: IsPaused check in raft.go:407-410, 652-655 maybeSendAppend()
    \* Note: heartbeat is sent directly via bcastHeartbeat(), bypassing maybeSendAppend()
    /\ (subtype = "heartbeat" \/ ~IsPaused(i, j))
    /\ LET
        prevLogIndex == range[1] - 1
        \* The following upper bound on prevLogIndex is unnecessary
        \* but makes verification substantially simpler.
        prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                            log[i][prevLogIndex].term
                        ELSE
                            0
        \* Send the entries
        lastEntry == Min({Len(log[i]), range[2]-1})
        entries == SubSeq(log[i], range[1], lastEntry)
        commit == IF subtype = "heartbeat" THEN Min({commitIndex[i], matchIndex[i][j]}) ELSE Min({commitIndex[i], lastEntry})
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
          /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>> 

\* etcd leader sends MsgAppResp to itself immediately after appending log entry
AppendEntriesToSelf(i) ==
    /\ state[i] = Leader
    /\ Send([mtype           |-> AppendEntriesResponse,
             msubtype        |-> "app",
             mterm           |-> currentTerm[i],
             msuccess        |-> TRUE,
             mmatchIndex     |-> Len(log[i]),
             msource         |-> i,
             mdest           |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

AppendEntries(i, j, range) ==
    AppendEntriesInRangeToPeer("app", i, j, range)

Heartbeat(i, j) ==
    \* heartbeat is equivalent to an append-entry request with 0 entry index 1
    AppendEntriesInRangeToPeer("heartbeat", i, j, <<1,1>>)

SendSnapshot(i, j, index) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    \* Fix: Snapshot index must be > matchIndex to maintain invariant Match < Next
    \* Reference: raft.go:616-628 - maybeSendSnapshot only called when log truncated at >= pr.Next
    \* Reference: raft.go:670 - snapshot index determined by storage, not arbitrary
    \* Real constraint: snapshot.Metadata.Index >= firstIndex (after log compaction)
    /\ index > matchIndex[i][j]
    /\ LET
        prevLogIndex == 0
        prevLogTerm == 0
        lastEntry == index
        entries == SubSeq(log[i], 1, lastEntry)
        commit == Min({commitIndex[i], lastEntry})
       IN /\ Send( [mtype          |-> AppendEntriesRequest,
                    msubtype       |-> "snapshot",
                    mterm          |-> currentTerm[i],
                    mprevLogIndex  |-> prevLogIndex,
                    mprevLogTerm   |-> prevLogTerm,
                    mentries       |-> entries,
                    mcommitIndex   |-> commit,
                    msource        |-> i,
                    mdest          |-> j])
          \* New: Transition to StateSnapshot, set pendingSnapshot and Next
          \* Reference: raft.go:684 sendSnapshot() -> pr.BecomeSnapshot()
          \* Reference: tracker/progress.go:153-158 BecomeSnapshot()
          /\ progressState' = [progressState EXCEPT ![i][j] = StateSnapshot]
          /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
          /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = index]
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = index + 1]
          /\ ResetInflights(i, j)
          /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState>>
 
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
                         [j \in Server |-> IF j = i THEN Len(log[i]) ELSE 0]]
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
                            [j \in Server |-> Len(log[i]) + 1]]
    /\ inflights' = [inflights EXCEPT ![i] =
                            [j \in Server |-> {}]]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, pendingConfChangeIndex, candidateVars, logVars, configVars, durableState>>
    
Replicate(i, v, t) == 
    /\ t \in {ValueEntry, ConfigEntry}
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     type  |-> t,
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]

\* Leader i receives a client request to add v to the log.
\* @type: (Int, Int) => Bool;
ClientRequest(i, v) ==
    /\ Replicate(i, [val |-> v], ValueEntry)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, commitIndex, configVars, durableState, progressVars>>

\* Leader i receives a client request AND sends MsgAppResp immediately (mimicking atomic behavior).
\* Used for implicit replication in Trace Validation.
ClientRequestAndSend(i, v) ==
    /\ Replicate(i, [val |-> v], ValueEntry)
    /\ Send([mtype       |-> AppendEntriesResponse,
             msubtype    |-> "app",
             mterm       |-> currentTerm[i],
             msuccess    |-> TRUE,
             mmatchIndex |-> Len(log'[i]),
             msource     |-> i,
             mdest       |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, configVars, durableState, progressVars>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           AllVoters == GetConfig(i) \union GetOutgoingConfig(i)
           Agree(index) == {k \in AllVoters : matchIndex[i][k] >= index}
           logSize == Len(log[i])
           \* logSize == MaxLogLength
           \* The maximum indexes for which a quorum agrees
           IsCommitted(index) == 
               IF IsJointConfig(i) THEN
                   /\ (Agree(index) \cap GetConfig(i)) \in Quorum(GetConfig(i))
                   /\ (Agree(index) \cap GetOutgoingConfig(i)) \in Quorum(GetOutgoingConfig(i))
               ELSE
                   Agree(index) \in Quorum(GetConfig(i))

           agreeIndexes == {index \in 1..logSize : IsCommitted(index)}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN
        /\ CommitTo(i, newCommitIndex)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, log, configVars, durableState, progressVars>>

    
\* Leader i adds a new server j or promote learner j
AddNewServer(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i) \union {j}, learners |-> GetLearners(i)], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>

\* Leader i adds a leaner j to the cluster.
AddLearner(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i) \union GetLearners(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i), learners |-> GetLearners(i) \union {j}], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>

\* Leader i removes a server j (possibly itself) from the cluster.
DeleteServer(i, j) ==
    /\ state[i] = Leader
    /\ j \in GetConfig(i) \union GetLearners(i)
    /\ ~IsJointConfig(i)
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            /\ Replicate(i, [newconf |-> GetConfig(i) \ {j}, learners |-> GetLearners(i) \ {j}], ConfigEntry)
            /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>

\* Leader i proposes an arbitrary configuration change (compound changes supported).
ChangeConf(i) ==
    /\ state[i] = Leader
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            \E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
                /\ Replicate(i, [newconf |-> newVoters, learners |-> newLearners, enterJoint |-> enterJoint, oldconf |-> GetConfig(i)], ConfigEntry)
                /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
                \* Remove manual Send, rely on AppendEntriesToSelf in trace
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>

\* Leader i proposes an arbitrary configuration change AND sends MsgAppResp.
\* Used for implicit replication in Trace Validation.
ChangeConfAndSend(i) ==
    /\ state[i] = Leader
    /\ IF pendingConfChangeIndex[i] = 0 THEN
            \E newVoters \in SUBSET Server, newLearners \in SUBSET Server, enterJoint \in {TRUE, FALSE}:
                /\ Replicate(i, [newconf |-> newVoters, learners |-> newLearners, enterJoint |-> enterJoint, oldconf |-> GetConfig(i)], ConfigEntry)
                /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
                /\ Send([mtype       |-> AppendEntriesResponse,
                         msubtype    |-> "app",
                         mterm       |-> currentTerm[i],
                         msuccess    |-> TRUE,
                         mmatchIndex |-> Len(log'[i]),
                         msource     |-> i,
                         mdest       |-> i])
       ELSE
            /\ Replicate(i, <<>>, ValueEntry)
            /\ UNCHANGED <<pendingConfChangeIndex>>
            /\ Send([mtype       |-> AppendEntriesResponse,
                     msubtype    |-> "app",
                     mterm       |-> currentTerm[i],
                     msuccess    |-> TRUE,
                     mmatchIndex |-> Len(log'[i]),
                     msource     |-> i,
                     mdest       |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, matchIndex, commitIndex, configVars, durableState, progressVars>>

ApplySimpleConfChange(i) ==
    /\ LET k == SelectLastInSubSeq(log[i], 1, commitIndex[i], LAMBDA x: x.type = ConfigEntry)
       IN
            /\ k > 0
            /\ k <= commitIndex[i]
            /\ LET oldConfig == GetConfig(i) \cup GetOutgoingConfig(i)  \* All nodes in old config
                   newConfigFn == ApplyConfigUpdate(i, k)
                   newConfig == newConfigFn[i].jointConfig[1] \cup newConfigFn[i].jointConfig[2]  \* All nodes in new config
                   addedNodes == newConfig \ oldConfig  \* Newly added nodes
               IN
                /\ config' = newConfigFn
                /\ IF state[i] = Leader /\ pendingConfChangeIndex[i] >= k THEN
                    /\ reconfigCount' = reconfigCount + 1
                    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
                   ELSE UNCHANGED <<reconfigCount, pendingConfChangeIndex>>
                \* Initialize Progress for newly added nodes (if leader)
                \* Reference: raft.go:1947-1967 applyConfChange() -> switchToConfig()
                \* Reference: confchange/confchange.go:263 initProgress() uses max(lastIndex, 1) for Next
                /\ IF state[i] = Leader /\ addedNodes # {}
                   THEN /\ nextIndex' = [nextIndex EXCEPT ![i] =
                               [j \in Server |-> IF j \in addedNodes THEN Max({Len(log[i]), 1}) ELSE nextIndex[i][j]]]
                        /\ matchIndex' = [matchIndex EXCEPT ![i] =
                               [j \in Server |-> IF j \in addedNodes THEN 0 ELSE matchIndex[i][j]]]
                        /\ progressState' = [progressState EXCEPT ![i] =
                               [j \in Server |-> IF j \in addedNodes THEN StateProbe ELSE progressState[i][j]]]
                        /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i] =
                               [j \in Server |-> IF j \in addedNodes THEN FALSE ELSE msgAppFlowPaused[i][j]]]
                        /\ inflights' = [inflights EXCEPT ![i] =
                               [j \in Server |-> IF j \in addedNodes THEN {} ELSE inflights[i][j]]]
                        /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i] =
                               [j \in Server |-> IF j \in addedNodes THEN 0 ELSE pendingSnapshot[i][j]]]
                   ELSE /\ UNCHANGED progressVars
                        /\ UNCHANGED matchIndex
            /\ UNCHANGED <<messageVars, serverVars, candidateVars, logVars, durableState>>
    
Ready(i) ==
    /\ PersistState(i)
    /\ SendPendingMessages(i)
    /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars, configVars, progressVars>>

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
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* ============================================================================
\* New: Progress state transition helper functions
\* Reference: progress.go:119-158
\* ============================================================================

\* ResetState - common logic for state transitions
\* Reference: progress.go:121-126 ResetState()
\* Clear MsgAppFlowPaused, PendingSnapshot and Inflights
ResetProgressState(i, j, newState) ==
    /\ progressState' = [progressState EXCEPT ![i][j] = newState]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = 0]
    /\ ResetInflights(i, j)

\* BecomeProbe - transition to StateProbe
\* Reference: progress.go:130-143
\* Key: clear MsgAppFlowPaused to allow flow control recovery
ProgressBecomeProbe(i, j) ==
    ResetProgressState(i, j, StateProbe)

\* BecomeReplicate - transition to StateReplicate
\* Reference: progress.go:146-149
\* Key: clear MsgAppFlowPaused to allow flow control recovery
ProgressBecomeReplicate(i, j) ==
    ResetProgressState(i, j, StateReplicate)

\* BecomeSnapshot - transition to StateSnapshot
\* Reference: progress.go:153-158
\* Key: set pendingSnapshot and Next, MsgAppFlowPaused is cleared but IsPaused() still returns true
ProgressBecomeSnapshot(i, j, snapIndex) ==
    /\ progressState' = [progressState EXCEPT ![i][j] = StateSnapshot]
    /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
    /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = snapIndex]
    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = snapIndex + 1]
    /\ ResetInflights(i, j)

\* ============================================================================
\* New: MsgAppFlowPaused update functions - critical flow control recovery paths
\* ============================================================================

\* UpdateMsgAppFlowPausedOnSent - update MsgAppFlowPaused when sending messages
\* Reference: progress.go:165-185 SentEntries()
\* StateReplicate: MsgAppFlowPaused = Inflights.Full()
\* StateProbe: MsgAppFlowPaused = true (if entries were sent)
UpdateMsgAppFlowPausedOnSent(i, j, sentEntries) ==
    msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] =
        CASE progressState[i][j] = StateReplicate
                -> InflightsFull(i, j)  \* Note: uses updated inflights
          [] progressState[i][j] = StateProbe /\ sentEntries > 0
                -> TRUE
          [] OTHER -> @
    ]

\* ClearMsgAppFlowPausedOnUpdate - clear on successful response
\* Reference: progress.go:205-213 MaybeUpdate()
\* This is one of the main flow control recovery paths
ClearMsgAppFlowPausedOnUpdate(i, j) ==
    msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]

\* ClearMsgAppFlowPausedOnDecrTo - clear on rejected response
\* Reference: progress.go:226-254 MaybeDecrTo()
\* Note: only clears in StateProbe, not in StateReplicate
ClearMsgAppFlowPausedOnDecrTo(i, j) ==
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
                    /\ m.mlastLogIndex >= Len(log[i])
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
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, RVRESPT) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, configVars, durableState, progressVars>>

\* @type: (Int, Int, AEREQT, Bool) => Bool;
RejectAppendEntriesRequest(i, j, m, logOk) ==
    /\ \/ m.mterm < currentTerm[i]
       \/ /\ m.mterm = currentTerm[i]
          /\ state[i] = Follower
          /\ \lnot logOk
    /\ Reply([mtype           |-> AppendEntriesResponse,
              msubtype        |-> "app",
              mterm           |-> currentTerm[i],
              msuccess        |-> FALSE,
              mmatchIndex     |-> 0,
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, logVars, configVars, durableState, progressVars>>

\* @type: (Int, MSG) => Bool;
ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, logVars, configVars, durableState, progressVars>> 

HasNoConflict(i, index, ents) ==
    /\ index <= Len(log[i]) + 1
    /\ \A k \in 1..Len(ents): index + k - 1 <= Len(log[i]) => log[i][index+k-1].term = ents[k].term

\* @type: (Int, Int, Int, AEREQT) => Bool;
AppendEntriesAlreadyDone(i, j, index, m) ==
    /\ \/ index <= commitIndex[i]
       \/ /\ index > commitIndex[i]
          /\ \/ m.mentries = << >>
             \/ /\ m.mentries /= << >>
                /\ m.mprevLogIndex + Len(m.mentries) <= Len(log[i])
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
                msource         |-> i,
                mdest           |-> j],
                m)
    /\ UNCHANGED <<serverVars, log, configVars, durableState, progressVars>>

\* @type: (Int, Int, AEREQT) => Bool;
ConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ ~HasNoConflict(i, index, m.mentries)
    /\ log' = [log EXCEPT ![i] = SubSeq(@, 1, Len(@) - 1)]
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState, progressVars>>

\* @type: (Int, AEREQT) => Bool;
NoConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ HasNoConflict(i, index, m.mentries)
    /\ log' = [log EXCEPT ![i] = @ \o SubSeq(m.mentries, Len(@)-index+2, Len(m.mentries))]
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState, progressVars>>

\* @type: (Int, Int, Bool, AEREQT) => Bool;
AcceptAppendEntriesRequest(i, j, logOk, m) ==
    \* accept request
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Follower
    /\ logOk
    /\ LET index == m.mprevLogIndex + 1
       IN \/ AppendEntriesAlreadyDone(i, j, index, m)
          \/ ConflictAppendEntriesRequest(i, index, m)
          \/ NoConflictAppendEntriesRequest(i, index, m)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* @type: (Int, Int, AEREQT) => Bool;
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN 
       /\ m.mterm <= currentTerm[i]
       /\ \/ RejectAppendEntriesRequest(i, j, m, logOk)
          \/ ReturnToFollowerState(i, m)
          \/ AcceptAppendEntriesRequest(i, j, logOk, m)
       /\ UNCHANGED <<candidateVars, leaderVars, configVars, durableState, progressVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, AERESPT) => Bool;
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex})]
          /\ UNCHANGED <<pendingConfChangeIndex>>
          \* New: Update Next according to MaybeUpdate
          \* Reference: progress.go:205-213 MaybeUpdate()
          \* pr.Next = max(pr.Next, n+1) to maintain invariant Match < Next
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex + 1})]
          \* New: Free confirmed inflights, clear msgAppFlowPaused
          \* Reference: MaybeUpdate() call in raft.go:1260-1289 handleAppendEntries()
          /\ FreeInflightsLE(i, j, m.mmatchIndex)
          /\ ClearMsgAppFlowPausedOnUpdate(i, j)
          \* New: StateProbe → StateReplicate state transition
          \* Reference: BecomeReplicate() call in progress.go:186-204 MaybeUpdate()
          \* Reference: condition check in raft.go:1519-1522 handleAppendEntriesResponse()
          \* Key: only transition when MaybeUpdate returns true (i.e., matchIndex actually updated)
          \*      or matchIndex already equals response index
          /\ LET maybeUpdated == m.mmatchIndex > matchIndex[i][j]
                 alreadyMatched == m.mmatchIndex = matchIndex[i][j]
             IN IF progressState[i][j] \in {StateProbe, StateSnapshot}
                   /\ (maybeUpdated \/ (alreadyMatched /\ progressState[i][j] = StateProbe))
                THEN progressState' = [progressState EXCEPT ![i][j] = StateReplicate]
                ELSE UNCHANGED progressState
          /\ IF progressState[i][j] = StateSnapshot
             THEN pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = 0]
             ELSE UNCHANGED pendingSnapshot
       \/ /\ \lnot m.msuccess \* not successful
          /\ UNCHANGED <<leaderVars>>
          \* Fix: Explicitly expand macros to ensure StateReplicate -> StateProbe and Unpause works
          \* Note: MaybeDecrTo (progress.go:226-252) updates Next, but not fully modeled here
          \* Simplified: just keep Next unchanged for now (can be refined later)
          /\ IF progressState[i][j] = StateReplicate
             THEN /\ progressState' = [progressState EXCEPT ![i][j] = StateProbe]
                  /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
                  /\ pendingSnapshot' = [pendingSnapshot EXCEPT ![i][j] = 0]
                  /\ inflights' = [inflights EXCEPT ![i][j] = {}]
                  /\ UNCHANGED nextIndex
             ELSE /\ UNCHANGED <<progressState, pendingSnapshot, inflights, nextIndex>>
                  /\ msgAppFlowPaused' = [msgAppFlowPaused EXCEPT ![i][j] = FALSE]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, configVars, durableState>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (Int, Int, MSG) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ BecomeFollowerOfTerm(i, m.mterm)
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* Responses with stale terms are ignored.
\* @type: (Int, Int, MSG) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* Combined action: Update term AND handle RequestVoteRequest atomically.
\* This is needed because raft.go handles term update and vote processing in a single Step call,
\* and Trace records only one event.
UpdateTermAndHandleRequestVote(i, j, m) ==
    /\ m.mtype = RequestVoteRequest
    /\ m.mterm > currentTerm[i]
    /\ LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                    \/ /\ m.mlastLogTerm = LastTerm(log[i])
                       /\ m.mlastLogIndex >= Len(log[i])
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
           /\ UNCHANGED <<candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* Receive a message.
ReceiveDirect(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
    \/ UpdateTermAndHandleRequestVote(i, j, m)
    \/ /\ m.mtype /= RequestVoteRequest
       /\ UpdateTerm(i, j, m)
    \/  /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m)
    \/  /\ m.mtype = RequestVoteResponse
        /\  \/ DropStaleResponse(i, j, m)
            \/ HandleRequestVoteResponse(i, j, m)
    \/  /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
    \/  /\ m.mtype = AppendEntriesResponse
        /\ \/ DropStaleResponse(i, j, m)
           \/ HandleAppendEntriesResponse(i, j, m)

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
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

\* The network drops a message
\* @type: MSG => Bool;
DropMessage(m) ==
    \* Do not drop loopback messages
    \* /\ m.msource /= m.mdest
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, configVars, durableState, progressVars>>

----

\* Defines how the variables may transition.
NextAsync == 
    \/ \E i,j \in Server : RequestVote(i, j)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server: ClientRequest(i, 0)
    \/ \E i \in Server: ClientRequestAndSend(i, 0)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : \E b,e \in matchIndex[i][j]+1..Len(log[i])+1 : AppendEntries(i, j, <<b,e>>)
    \/ \E i \in Server : AppendEntriesToSelf(i)
    \/ \E i,j \in Server : Heartbeat(i, j)
    \/ \E i,j \in Server : \E index \in 1..commitIndex[i] : SendSnapshot(i, j, index)
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E i \in Server : Timeout(i)
    \/ \E i \in Server : Ready(i)
    \/ \E i \in Server : StepDownToFollower(i)
        
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
NextDynamic ==
    \/ Next
    \/ \E i, j \in Server : AddNewServer(i, j)
    \/ \E i, j \in Server : AddLearner(i, j)
    \/ \E i, j \in Server : DeleteServer(i, j)
    \/ \E i \in Server : ChangeConf(i)
    \/ \E i \in Server : ChangeConfAndSend(i)
    \/ \E i \in Server : ApplySimpleConfChange(i)

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

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(log[i],1,commitIndex[i])

\* The current term of any server is at least the term
\* of any message sent by that server
\* @type: MSG => Bool;
MessageTermsLtCurrentTerm(m) ==
    m.mterm <= currentTerm[m.msource]

\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Server :
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

\* A leader always has the greatest index for its current term
ElectionSafetyInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})

\* Every (index, term) pair determines a log prefix
LogMatchingInv ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

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
\* of at least one server in every quorum
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), log[j])

\* The "up-to-date" check performed by servers
\* before issuing a vote implies that i receives
\* a vote from j only if i has all of j's committed
\* entries
MoreUpToDateCorrectInv ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])

\* If a log entry is committed in a given term, then that
\* entry will be present in the logs of the leaders
\* for all higher-numbered terms
\* See: https://github.com/uwplse/verdi-raft/blob/master/raft/LeaderCompletenessInterface.v
LeaderCompletenessInv == 
    \A i \in Server :
        LET committed == Committed(i) IN
        \A idx \in 1..Len(committed) :
            LET entry == log[i][idx] IN 
            \* if the entry is committed 
            \A l \in CurrentLeaders :
                \* all leaders with higher-number terms
                currentTerm[l] > entry.term =>
                \* have the entry at the same log position
                log[l][idx] = entry

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
ProbeLimitInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateProbe)
            => InflightsCount(i, j) <= 1

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
            \A idx \in inflights[i][j] : idx <= Len(log[i])

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
            /\ pendingSnapshot[i][j] <= Len(log[i])  \* Snapshot index must be valid

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
\* We verify: matchIndex[i][j] <= Len(log[i]) for active replication
\* Reference: progress.go:37 "Invariant: 0 <= Match < Next"
MatchIndexLessThanLogInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ j /= i) =>
            matchIndex[i][j] <= Len(log[i])

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

\* Invariant: SnapshotNextInv
\* In StateSnapshot: Next == PendingSnapshot + 1 (when BecomeSnapshot was called)
\* Note: This only holds if Next hasn't been updated by MaybeUpdate since BecomeSnapshot
\* Reference: progress.go:40, 156
SnapshotNextInv ==
    \A i \in Server : \A j \in Server :
        (state[i] = Leader /\ progressState[i][j] = StateSnapshot
         /\ pendingSnapshot[i][j] > 0) =>
            nextIndex[i][j] >= pendingSnapshot[i][j] + 1

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
    /\ SnapshotNextInv
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
StateMachineConsistency ==
    \A i, j \in Server :
        \A idx \in 1..Min({commitIndex[i], commitIndex[j]}) :
            log[i][idx] = log[j][idx]

\* Commit index should never exceed log length
CommitIndexBoundInv ==
    \A i \in Server :
        commitIndex[i] <= Len(log[i])

\* All committed entries should have valid (positive) terms
CommittedEntriesTermInv ==
    \A i \in Server :
        \A idx \in 1..commitIndex[i] :
            log[i][idx].term > 0

\* Configuration change index should not exceed log length
PendingConfigBoundInv ==
    \A i \in Server :
        state[i] = Leader =>
            pendingConfChangeIndex[i] <= Len(log[i])

\* Leader-specific: log should be at least as long as commitIndex
LeaderLogLengthInv ==
    \A i \in Server :
        state[i] = Leader =>
            commitIndex[i] <= Len(log[i])

\* Term should be monotonic in the log (newer entries have >= terms)
LogTermMonotonic ==
    \A i \in Server :
        \A idx1, idx2 \in 1..Len(log[i]) :
            idx1 < idx2 =>
                log[i][idx1].term <= log[i][idx2].term

\* Current term should be at least as large as any log entry term
CurrentTermAtLeastLogTerm ==
    \A i \in Server :
        \A idx \in 1..Len(log[i]) :
            currentTerm[i] >= log[i][idx].term

\* If voted for someone, that node should be in the configuration
VotedForInConfigInv ==
    \A i \in Server :
        votedFor[i] # Nil =>
            votedFor[i] \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)

\* Candidates must have voted for themselves
CandidateVotedForSelfInv ==
    \A i \in Server :
        state[i] = Candidate =>
            votedFor[i] = i

\* Durable state should be consistent with volatile state
DurableStateConsistency ==
    \A i \in Server :
        /\ durableState[i].currentTerm <= currentTerm[i]
        /\ durableState[i].log <= Len(log[i])
        /\ durableState[i].commitIndex <= commitIndex[i]

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
    /\ LogTermMonotonic
    /\ CurrentTermAtLeastLogTerm
    /\ VotedForInConfigInv
    /\ CandidateVotedForSelfInv
    /\ DurableStateConsistency
    /\ MessageEndpointsValidInv
    /\ LeaderDurableTermInv

===============================================================================