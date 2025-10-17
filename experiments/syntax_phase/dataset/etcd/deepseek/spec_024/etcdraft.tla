---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

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
    pendingReadIndexMessages,
    readStates,
    kvStore

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
            nextIndex, matchIndex, leader, electionElapsed, 
            randomizedElectionTimeout, leadTransferee, uncommittedSize,
            msgs, pendingReadIndexMessages, readStates, kvStore>>

NodeState == {"Follower", "Candidate", "Leader"}
MessageType == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp",
                "MsgApp", "MsgAppResp", "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp",
                "MsgTransferLeader", "MsgTimeoutNow", "MsgReadIndex", "MsgReadIndexResp",
                "MsgForgetLeader", "StorageAppendResp", "StorageApplyResp"}

LogEntry == [term : Nat, index : Nat, type : {"Normal", "ConfChange"}, data : STRING]
Message == [type : MessageType, from : Nodes, to : Nodes, term : Nat, 
            logTerm : Nat, index : Nat, entries : Seq(LogEntry), 
            commit : Nat, context : STRING, reject : BOOLEAN, 
            rejectHint : Nat, snapshot : [metadata: [index: Nat, term: Nat]]]

Min(a,b) == IF a < b THEN a ELSE b
Max(a,b) == IF a > b THEN a ELSE b

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
    /\ pendingReadIndexMessages \subseteq Message
    /\ readStates \in [Nodes -> Seq([index: Nat, requestCtx: STRING])]
    /\ kvStore \in [Nodes -> [{} -> STRING]]

IsLeader(n) == state[n] = "Leader"

LastLogTerm(n) ==
    LET log_n == log[n] IN
        IF Len(log_n) > 0 THEN log_n[Len(log_n)].term ELSE 0

LastLogIndex(n) == Len(log[n])

LogTerm(n, index) ==
    IF index > 0 /\ index <= Len(log[n]) THEN log[n][index].term ELSE 0

CanVote(n, term, lastLogTerm, lastLogIndex) ==
    \/ votedFor[n] = 0
    \/ votedFor[n] = n
    \/ term > currentTerm[n]
    \/ /\ term = currentTerm[n]
       /\ lastLogTerm > LastLogTerm(n)
    \/ /\ term = currentTerm[n]
       /\ lastLogTerm = LastLogTerm(n)
       /\ lastLogIndex >= LastLogIndex(n)

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
        /\ log' = [log EXCEPT ![n] = newLog]
        /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
        /\ msgs' = msgs \cup { [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n], index |-> m.index + Len(entries), reject |-> FALSE] }
    ELSE
        LET hintIndex == Min(m.index, LastLogIndex(n)) IN
        LET hintTerm == LogTerm(n, hintIndex) IN
        /\ msgs' = msgs \cup { [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n], logTerm |-> hintTerm, index |-> m.index, reject |-> TRUE, rejectHint |-> hintIndex] }

HandleAppendEntries(n, m) ==
    IF m.term < currentTerm[n]
    THEN
        /\ msgs' = msgs \cup { [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n], reject |-> TRUE] }
    ELSE
        AppendEntries(n, m)

HandleVoteRequest(n, m) ==
    LET canGrant == 
        /\ m.term >= currentTerm[n]
        /\ CanVote(n, m.term, m.logTerm, m.index)
    IN
    IF canGrant
    THEN
        /\ votedFor' = [votedFor EXCEPT ![n] = m.from]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
        /\ msgs' = msgs \cup { [type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> m.term] }
    ELSE
        /\ msgs' = msgs \cup { [type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> currentTerm[n], reject |-> TRUE] }

HandleHeartbeat(n, m) ==
    IF m.term < currentTerm[n]
    THEN /\ msgs' = msgs \cup { [type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, term |-> currentTerm[n]] }
    ELSE
        /\ leader' = [leader EXCEPT ![n] = m.from]
        /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
        /\ msgs' = msgs \cup { [type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, context |-> m.context] }

BecomeFollower(n, term, lead) ==
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = 0]
    /\ leader' = [leader EXCEPT ![n] = lead]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![n] = CHOOSE t \in MaxElectionTimeout..(2*MaxElectionTimeout-1) : TRUE]

BecomeCandidate(n) ==
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ leader' = [leader EXCEPT ![n] = 0]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![n] = CHOOSE t \in MaxElectionTimeout..(2*MaxElectionTimeout-1) : TRUE]

StartElection(n) ==
    LET lastLogIndex == LastLogIndex(n) IN
    LET lastLogTerm == LogTerm(n, lastLogIndex) IN
    /\ msgs' = msgs \cup { [type |-> "MsgVote", from |-> n, to |-> m, term |-> currentTerm[n] + 1, logTerm |-> lastLogTerm, index |-> lastLogIndex] : m \in Nodes \ {n} }

BecomeLeader(n) ==
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leader' = [leader EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> LastLogIndex(n) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = 0]
    /\ msgs' = msgs \cup { [type |-> "MsgApp", from |-> n, to |-> n, term |-> currentTerm[n], entries |-> <<[term |-> currentTerm[n], index |-> LastLogIndex(n)+1, type |-> "Normal", data |-> ""]>>] }

MaxSet(S) == CHOOSE x \in S : \A y \in S : y <= x

AdvanceCommitIndex(n) ==
    LET quorum == Cardinality(Nodes) \div 2 + 1
    LET maxIndex == LastLogIndex(n)
    LET candidateIndices == { i \in (commitIndex[n]+1)..maxIndex : 
        log[n][i].term = currentTerm[n] 
        /\ Cardinality({ m \in Nodes : matchIndex[n][m] >= i }) >= quorum }
    IN
    IF candidateIndices # {} 
    THEN 
        LET newCommit == MaxSet(candidateIndices) 
        IN
        /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommit]
    ELSE 
        /\ UNCHANGED commitIndex

ApplyLogEntry(n) ==
    LET start == lastApplied[n] + 1 IN
    LET end == commitIndex[n] IN
    IF start <= end
    THEN
        LET newKv == 
            [k \in DOMAIN kvStore[n] |-> 
                IF \E i \in start..end: log[n][i].type = "Normal" /\ log[n][i].data = k
                THEN "" 
                ELSE kvStore[n][k]] 
        IN
        /\ lastApplied' = [lastApplied EXCEPT ![n] = end]
        /\ kvStore' = [kvStore EXCEPT ![n] = newKv]
    ELSE /\ UNCHANGED <<lastApplied, kvStore>>

HandleClientRequest(n, cid, op) ==
    LET newEntry == [term |-> currentTerm[n], index |-> LastLogIndex(n) + 1, type |-> "Normal", data |-> op] IN
    LET newLog == Append(log[n], newEntry) IN
    IF uncommittedSize[n] + Len(op) <= MaxUncommittedSize
    THEN
        /\ log' = [log EXCEPT ![n] = newLog]
        /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = uncommittedSize[n] + Len(op)]
        /\ msgs' = msgs \cup { [type |-> "MsgAppResp", from |-> n, to |-> n, index |-> LastLogIndex(n)+1] }
    ELSE /\ UNCHANGED <<log, uncommittedSize, msgs>>

Next ==
    \/ \E n \in Nodes:
        \/ /\ state[n] = "Follower" 
           /\ electionElapsed[n] >= randomizedElectionTimeout[n]
           /\ BecomeCandidate(n)
           /\ StartElection(n)
        \/ /\ state[n] = "Leader"
           /\ \E m \in Nodes \ {n}: 
                /\ msgs' = msgs \cup { [type |-> "MsgHeartbeat", from |-> n, to |-> m, term |-> currentTerm[n]] }
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