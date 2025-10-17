---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,
    MaxElectionTimeout,
    HeartbeatTimeout,
    MaxUncommittedSize

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    leader,
    electionElapsed,
    randomizedElectionTimeout,
    leadTransferee,
    uncommittedSize,
    msgs,
    msgsAfterAppend,
    pendingReadIndexMessages,
    readStates,
    kvStore

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
            nextIndex, matchIndex, leader, electionElapsed, 
            randomizedElectionTimeout, leadTransferee, uncommittedSize,
            msgs, msgsAfterAppend, pendingReadIndexMessages, readStates, kvStore>>

NodeState == {"Follower", "Candidate", "Leader"}
MessageType == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp",
                "MsgApp", "MsgAppResp", "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp",
                "MsgTransferLeader", "MsgTimeoutNow", "MsgReadIndex", "MsgReadIndexResp",
                "MsgForgetLeader", "StorageAppendResp", "StorageApplyResp"}

Message == [type : MessageType, from : Nodes, to : Nodes, term : Nat, 
            logTerm : Nat, index : Nat, entries : Seq(LogEntry), 
            commit : Nat, context : STRING, reject : BOOLEAN, 
            rejectHint : Nat, snapshot : [metadata: [index: Nat, term: Nat]]]

LogEntry == [term : Nat, index : Nat, type : {"Normal", "ConfChange"}, data : STRING]

Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 1]
    /\ votedFor = [n \in Nodes |-> 0]
    /\ log = [n \in Nodes |-> <<[term |-> 0, index |-> 0, type |-> "Normal", data |-> ""]>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leader = [n \in Nodes |-> 0]
    /\ electionElapsed = [n \in Nodes |-> 0]
    /\ randomizedElectionTimeout = [n \in Nodes |-> MaxElectionTimeout + 1]
    /\ leadTransferee = [n \in Nodes |-> 0]
    /\ uncommittedSize = [n \in Nodes |-> 0]
    /\ msgs = {}
    /\ msgsAfterAppend = {}
    /\ pendingReadIndexMessages = {}
    /\ readStates = [n \in Nodes |-> <<>>]
    /\ kvStore = [n \in Nodes |-> [key \in {} |-> ""]]

TypeInvariant ==
    /\ state \in [Nodes -> NodeState]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> (Nodes \cup {0})]
    /\ log \in [Nodes -> Seq(LogEntry)]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ leader \in [Nodes -> (Nodes \cup {0})]
    /\ electionElapsed \in [Nodes -> Nat]
    /\ randomizedElectionTimeout \in [Nodes -> (MaxElectionTimeout .. (2*MaxElectionTimeout-1))]
    /\ leadTransferee \in [Nodes -> (Nodes \cup {0})]
    /\ uncommittedSize \in [Nodes -> Nat]
    /\ msgs \subseteq Message
    /\ msgsAfterAppend \subseteq Message
    /\ pendingReadIndexMessages \subseteq Message
    /\ readStates \in [Nodes -> Seq([index: Nat, requestCtx: STRING])]
    /\ kvStore \in [Nodes -> [{} -> STRING]]

IsLeader(n) == state[n] = "Leader"

CanVote(n, term, lastLogTerm, lastLogIndex) ==
    \/ votedFor[n] = 0
    \/ votedFor[n] = n
    \/ term > currentTerm[n]
    \/ /\ term = currentTerm[n]
       /\ lastLogTerm > LastLogTerm(n)
    \/ /\ term = currentTerm[n]
       /\ lastLogTerm = LastLogTerm(n)
       /\ lastLogIndex >= LastLogIndex(n)

LastLogTerm(n) ==
    LET log_n == log[n] IN
        IF Len(log_n) > 0 THEN log_n[Len(log_n)].term ELSE 0

LastLogIndex(n) == Len(log[n])

LogTerm(n, index) ==
    IF index > 0 /\ index <= Len(log[n]) THEN log[n][index].term ELSE 0

LogMatch(n, prevIndex, prevTerm) ==
    \/ prevIndex = 0
    \/ (prevIndex <= Len(log[n]) /\ log[n][prevIndex].term = prevTerm)

Majority(S) == Cardinality(S) >= Cardinality(Nodes) \div 2 + 1

AppendEntries(n, m) ==
    LET entries == m.entries IN
    LET prevIndex == m.index IN
    LET prevTerm == m.logTerm IN
    LET newCommit == Min(m.commit, prevIndex + Len(entries)) IN
    IF LogMatch(n, prevIndex, prevTerm)
    THEN
        LET newLog == 
            IF Len(entries) > 0 
            THEN Append(SubSeq(log[n], 1, prevIndex), entries)
            ELSE log[n] IN
        LET newCommitIndex == Max(commitIndex[n], newCommit) IN
        [log EXCEPT ![n] = newLog,
         commitIndex EXCEPT ![n] = newCommitIndex]
    ELSE
        LET hintIndex == Min(m.index, LastLogIndex(n)) IN
        LET hintTerm == LogTerm(n, hintIndex) IN
        [msgs := msgs \cup {[type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n],
                              logTerm |-> hintTerm, index |-> m.index, reject |-> TRUE, rejectHint |-> hintIndex]}]

HandleAppendEntries(n, m) ==
    IF m.term < currentTerm[n]
    THEN
        [msgs := msgs \cup {[type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n], reject |-> TRUE]}]
    ELSE
        LET stateUpdate == AppendEntries(n, m) IN
        stateUpdate

HandleVoteRequest(n, m) ==
    LET canGrant == 
        /\ m.term >= currentTerm[n]
        /\ CanVote(n, m.term, m.logTerm, m.index)
    IN
    IF canGrant
    THEN
        [votedFor EXCEPT ![n] = m.from,
         currentTerm EXCEPT ![n] = m.term,
         msgsAfterAppend := msgsAfterAppend \cup {[type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> m.term]}]
    ELSE
        [msgsAfterAppend := msgsAfterAppend \cup {[type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> currentTerm[n], reject |-> TRUE]}]

HandleHeartbeat(n, m) ==
    IF m.term < currentTerm[n]
    THEN [msgs := msgs \cup {[type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, term |-> currentTerm[n]]}]
    ELSE
        [leader EXCEPT ![n] = m.from,
         electionElapsed EXCEPT ![n] = 0,
         msgs := msgs \cup {[type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, context |-> m.context]}]

BecomeFollower(n, term, lead) ==
    [state EXCEPT ![n] = "Follower",
     currentTerm EXCEPT ![n] = term,
     votedFor EXCEPT ![n] = 0,
     leader EXCEPT ![n] = lead,
     electionElapsed EXCEPT ![n] = 0,
     randomizedElectionTimeout EXCEPT ![n] = CHOOSE t \in MaxElectionTimeout..(2*MaxElectionTimeout-1) : TRUE]

BecomeCandidate(n) ==
    [state EXCEPT ![n] = "Candidate",
     currentTerm EXCEPT ![n] = currentTerm[n] + 1,
     votedFor EXCEPT ![n] = n,
     leader EXCEPT ![n] = 0,
     electionElapsed EXCEPT ![n] = 0,
     randomizedElectionTimeout EXCEPT ![n] = CHOOSE t \in MaxElectionTimeout..(2*MaxElectionTimeout-1) : TRUE]

StartElection(n) ==
    LET lastLogIndex == LastLogIndex(n) IN
    LET lastLogTerm == LogTerm(n, lastLogIndex) IN
    [msgsAfterAppend := msgsAfterAppend \cup {[type |-> "MsgVote", from |-> n, to |-> m, 
        term |-> currentTerm[n] + 1, logTerm |-> lastLogTerm, index |-> lastLogIndex] 
        : m \in Nodes \ {n}}]

BecomeLeader(n) ==
    [state EXCEPT ![n] = "Leader",
     leader EXCEPT ![n] = n,
     nextIndex EXCEPT ![n] = [m \in Nodes |-> LastLogIndex(n) + 1],
     matchIndex EXCEPT ![n] = [m \in Nodes |-> 0],
     uncommittedSize EXCEPT ![n] = 0,
     msgsAfterAppend := msgsAfterAppend \cup {[type |-> "MsgApp", from |-> n, to |-> n, term |-> currentTerm[n],
        entries |-> <<[term |-> currentTerm[n], index |-> LastLogIndex(n)+1, type |-> "Normal", data |-> ""]>>]}]

AdvanceCommitIndex(n) ==
    LET N == Cardinality(Nodes) IN
    LET matchIndices == {matchIndex[n][m] : m \in Nodes} IN
    LET sorted == SORT(matchIndices) IN
    LET newCommit == sorted[N \div 2 + 1] IN
    IF newCommit > commitIndex[n] /\ LogTerm(n, newCommit) = currentTerm[n]
    THEN [commitIndex EXCEPT ![n] = newCommit]
    ELSE [state EXCEPT ![n] = state[n]]  \* No change

ApplyLogEntry(n) ==
    LET start == lastApplied[n] + 1 IN
    LET end == commitIndex[n] IN
    IF start <= end
    THEN
        LET entries == SubSeq(log[n], start, end) IN
        LET newKv == 
            [k \in DOMAIN kvStore[n] |-> 
                IF \E i \in start..end: log[n][i].type = "Normal" /\ log[n][i].data = k
                THEN ""  \* Simplified for model
                ELSE kvStore[n][k]]  \* Placeholder for actual KV operations
        IN
        [lastApplied EXCEPT ![n] = end,
         kvStore EXCEPT ![n] = newKv]
    ELSE [state EXCEPT ![n] = state[n]]  \* No change

HandleClientRequest(n, cid, op) ==
    LET newEntry == [term |-> currentTerm[n], index |-> LastLogIndex(n) + 1, type |-> "Normal", data |-> op] IN
    LET newLog == Append(log[n], newEntry) IN
    IF uncommittedSize[n] + Len(op) <= MaxUncommittedSize
    THEN
        [log EXCEPT ![n] = newLog,
         uncommittedSize EXCEPT ![n] = uncommittedSize[n] + Len(op),
         msgsAfterAppend := msgsAfterAppend \cup {[type |-> "MsgAppResp", from |-> n, to |-> n, index |-> LastLogIndex(n)+1]}]
    ELSE [state EXCEPT ![n] = state[n]]  \* No change

Next ==
    \/ \E n \in Nodes:
        \/ /\ state[n] = "Follower" 
           /\ electionElapsed[n] >= randomizedElectionTimeout[n]
           /\ BecomeCandidate(n)
           /\ StartElection(n)
        \/ /\ state[n] = "Leader"
           /\ \E m \in Nodes \ {n}: 
                msgs := msgs \cup {[type |-> "MsgHeartbeat", from |-> n, to |-> m, term |-> currentTerm[n]]}
        \/ ApplyLogEntry(n)
    \/ \E msg \in msgs:
        \/ /\ msg.type = "MsgApp"
           /\ HandleAppendEntries(msg.to, msg)
        \/ /\ msg.type = "MsgVote"
           /\ HandleVoteRequest(msg.to, msg)
        \/ /\ msg.type = "MsgHeartbeat"
           /\ HandleHeartbeat(msg.to, msg)
    \/ \E n \in Nodes, cid \in DOMAIN kvStore[n]:
        /\ IsLeader(n)
        /\ HandleClientRequest(n, cid, "op")

Termination ==
    \A n \in Nodes: state[n] = "Leader" \/ state[n] = "Follower"

Safety ==
    \A n1, n2 \in Nodes:
        \/ commitIndex[n1] = commitIndex[n2]
        \/ \E i \in 1..Min(commitIndex[n1], commitIndex[n2]) : 
            log[n1][i] = log[n2][i]

====