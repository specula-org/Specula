---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Nodes, None

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    electionTimeout,
    leaderId,
    votesResponded,
    votesGranted,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, leaderId, votesResponded, votesGranted, messages>>

Node == Nodes \cup {None}

LogEntry == [term : Nat, type : {"NO_OP", "NORMAL", "ADD_NODE", "REMOVE_NODE", "ADD_NONVOTING_NODE"}]

State == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}

MessageType == {"AppendEntriesRequest", "AppendEntriesResponse", "RequestVoteRequest", "RequestVoteResponse"}

Message ==
    [type : MessageType,
     term : Nat,
     sender : Node,
     receiver : Node,
     success : BOOLEAN,
     prevLogIndex : Nat,
     prevLogTerm : Nat,
     entries : Seq(LogEntry),
     leaderCommit : Nat,
     voteGranted : BOOLEAN,
     lastLogIndex : Nat,
     lastLogTerm : Nat,
     matchIndex : Nat]

Init ==
    /\ state = [n \in Nodes |-> "FOLLOWER"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ electionTimeout = [n \in Nodes |-> 0]
    /\ leaderId = [n \in Nodes |-> None]
    /\ votesResponded = [n \in Nodes |-> {}]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ messages = EmptyBag

GetLastLogTerm(n) ==
    IF Len(log[n]) = 0 THEN 0
    ELSE log[n][Len(log[n])].term

GetLastLogIndex(n) ==
    Len(log[n])

LogUpToDate(n, candidateTerm, candidateIndex) ==
    \/ candidateTerm > GetLastLogTerm(n)
    \/ /\ candidateTerm = GetLastLogTerm(n)
       /\ candidateIndex >= GetLastLogIndex(n)

Majority ==
    LET total == Cardinality(Nodes)
    IN (total \div 2) + 1

AppendEntriesRequest(n) ==
    LET self == n
        entriesToSend ==
            IF nextIndex[n][self] <= GetLastLogIndex(n)
            THEN SubSeq(log[n], nextIndex[n][self], GetLastLogIndex(n))
            ELSE <<>>
        prevIndex == nextIndex[n][self] - 1
        prevTerm ==
            IF prevIndex = 0 THEN 0
            ELSE log[n][prevIndex].term
    IN [type |-> "AppendEntriesRequest",
        term |-> currentTerm[n],
        sender |-> n,
        receiver |-> self,
        success |-> TRUE,
        prevLogIndex |-> prevIndex,
        prevLogTerm |-> prevTerm,
        entries |-> entriesToSend,
        leaderCommit |-> commitIndex[n],
        voteGranted |-> FALSE,
        lastLogIndex |-> 0,
        lastLogTerm |-> 0,
        matchIndex |-> 0]

BecomeFollower(n, term, leader) ==
    /\ state[n] \in {"PRECANDIDATE", "CANDIDATE", "LEADER"}
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ leaderId' = [leaderId EXCEPT ![n] = leader]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ votesResponded' = [votesResponded EXCEPT ![n] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]

BecomePreCandidate(n) ==
    /\ state[n] = "FOLLOWER"
    /\ electionTimeout[n] >= 1000
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votesResponded' = [votesResponded EXCEPT ![n] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ \E m \in Nodes \ {n}:
        LET msg == [type |-> "RequestVoteRequest",
                   term |-> currentTerm[n] + 1,
                   sender |-> n,
                   receiver |-> m,
                   success |-> FALSE,
                   prevLogIndex |-> 0,
                   prevLogTerm |-> 0,
                   entries |-> <<>>,
                   leaderCommit |-> 0,
                   voteGranted |-> FALSE,
                   lastLogIndex |-> GetLastLogIndex(n),
                   lastLogTerm |-> GetLastLogTerm(n),
                   matchIndex |-> 0]
        IN messages' = messages (+) {msg}

BecomeCandidate(n) ==
    /\ state[n] = "PRECANDIDATE"
    /\ Cardinality(votesGranted[n]) >= Majority
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesResponded' = [votesResponded EXCEPT ![n] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ \E m \in Nodes \ {n}:
        LET msg == [type |-> "RequestVoteRequest",
                   term |-> currentTerm[n] + 1,
                   sender |-> n,
                   receiver |-> m,
                   success |-> FALSE,
                   prevLogIndex |-> 0,
                   prevLogTerm |-> 0,
                   entries |-> <<>>,
                   leaderCommit |-> 0,
                   voteGranted |-> FALSE,
                   lastLogIndex |-> GetLastLogIndex(n),
                   lastLogTerm |-> GetLastLogTerm(n),
                   matchIndex |-> 0]
        IN messages' = messages (+) {msg}

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ Cardinality(votesGranted[n]) >= Majority
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> GetLastLogIndex(n) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = 0]
    /\ \E noop : noop = [term |-> currentTerm[n], type |-> "NO_OP"]
        /\ log' = [log EXCEPT ![n] = Append(log[n], noop)]
        /\ \E m \in Nodes:
            messages' = messages (+) {AppendEntriesRequest(n)}

HandleAppendEntriesRequest(n, msg) ==
    /\ msg.type = "AppendEntriesRequest"
    /\ msg.term >= currentTerm[n]
    /\ \/ msg.term > currentTerm[n]
       \/ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ IF msg.term > currentTerm[n] THEN
          BecomeFollower(n, msg.term, msg.sender)
       ELSE TRUE
    /\ \/ msg.prevLogIndex = 0
       \/ /\ msg.prevLogIndex <= GetLastLogIndex(n)
          /\ msg.prevLogTerm = log[n][msg.prevLogIndex].term
    /\ \A i \in 1..Len(msg.entries):
        IF msg.prevLogIndex + i <= GetLastLogIndex(n) THEN
            log[n][msg.prevLogIndex + i].term = msg.entries[i].term
        ELSE TRUE
    /\ LET newLog ==
           IF msg.prevLogIndex + Len(msg.entries) > GetLastLogIndex(n)
           THEN SubSeq(log[n], 1, msg.prevLogIndex) \o msg.entries
           ELSE log[n]
       IN log' = [log EXCEPT ![n] = newLog]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = 
        IF msg.leaderCommit > commitIndex[n] THEN
            Min(msg.leaderCommit, GetLastLogIndex(n))
        ELSE
            commitIndex[n]]
    /\ LET response == [type |-> "AppendEntriesResponse",
                       term |-> currentTerm[n],
                       sender |-> n,
                       receiver |-> msg.sender,
                       success |-> TRUE,
                       prevLogIndex |-> 0,
                       prevLogTerm |-> 0,
                       entries |-> <<>>,
                       leaderCommit |-> 0,
                       voteGranted |-> FALSE,
                       lastLogIndex |-> 0,
                       lastLogTerm |-> 0,
                       matchIndex |-> GetLastLogIndex(n)]
       IN messages' = messages (+) {response}

HandleRequestVoteRequest(n, msg) ==
    /\ msg.type = "RequestVoteRequest"
    /\ msg.term >= currentTerm[n]
    /\ \/ msg.term > currentTerm[n]
       \/ votedFor[n] \in {None, msg.sender}
    /\ LogUpToDate(n, msg.lastLogTerm, msg.lastLogIndex)
    /\ IF msg.term > currentTerm[n] THEN
          BecomeFollower(n, msg.term, leaderId[n])
       ELSE TRUE
    /\ votedFor' = [votedFor EXCEPT ![n] = msg.sender]
    /\ LET response == [type |-> "RequestVoteResponse",
                       term |-> currentTerm[n],
                       sender |-> n,
                       receiver |-> msg.sender,
                       success |-> FALSE,
                       prevLogIndex |-> 0,
                       prevLogTerm |-> 0,
                       entries |-> <<>>,
                       leaderCommit |-> 0,
                       voteGranted |-> TRUE,
                       lastLogIndex |-> 0,
                       lastLogTerm |-> 0,
                       matchIndex |-> 0]
       IN messages' = messages (+) {response}

HandleRequestVoteResponse(n, msg) ==
    /\ msg.type = "RequestVoteResponse"
    /\ msg.term = currentTerm[n]
    /\ state[n] \in {"PRECANDIDATE", "CANDIDATE"}
    /\ msg.voteGranted = TRUE
    /\ votesResponded' = [votesResponded EXCEPT ![n] = votesResponded[n] \cup {msg.sender}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = votesGranted[n] \cup {msg.sender}]

HandleAppendEntriesResponse(n, msg) ==
    /\ msg.type = "AppendEntriesResponse"
    /\ state[n] = "LEADER"
    /\ msg.term = currentTerm[n]
    /\ msg.success = TRUE
    /\ matchIndex' = [matchIndex EXCEPT ![n][msg.sender] = msg.matchIndex]
    /\ nextIndex' = [nextIndex EXCEPT ![n][msg.sender] = msg.matchIndex + 1]
    /\ LET indices == {matchIndex[n][m] : m \in Nodes}
           N == Cardinality(Nodes)
           MajorityCount == (N \div 2) + 1
           potentialCommit == 
               IF indices = {} THEN commitIndex[n]
               ELSE LET maxIndex == Max(indices) IN
                    LET S == { i \in (commitIndex[n]+1)..maxIndex :
                               Cardinality({ m \in Nodes : matchIndex[n][m] >= i }) >= MajorityCount /\
                               i <= Len(log[n]) /\ log[n][i].term = currentTerm[n] }
                    IN IF S = {} THEN commitIndex[n] ELSE MAX(S)
       IN commitIndex' = [commitIndex EXCEPT ![n] = potentialCommit]

IncrementTime ==
    /\ electionTimeout' = [n \in Nodes |-> electionTimeout[n] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, votesResponded, votesGranted, messages>>

Next ==
    \/ \E n \in Nodes: BecomePreCandidate(n)
    \/ \E n \in Nodes: BecomeCandidate(n)
    \/ \E n \in Nodes: BecomeLeader(n)
    \/ \E msg \in BagToSet(messages):
        \E n \in Nodes:
            /\ msg.receiver = n
            /\ \/ HandleAppendEntriesRequest(n, msg)
               \/ HandleRequestVoteRequest(n, msg)
               \/ HandleRequestVoteResponse(n, msg)
               \/ HandleAppendEntriesResponse(n, msg)
    \/ IncrementTime

Spec == Init /\ [][Next]_vars

====