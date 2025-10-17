---- MODULE redisraft ----
EXTENDS Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, NoNode

VARIABLES 
    state, 
    currentTerm, 
    votedFor, 
    log, 
    commitIndex, 
    lastApplied,
    nextIndex,
    matchIndex,
    leaderId,
    electionTimeout,
    votesReceived,
    snapshotIndex,
    snapshotTerm,
    nodes,
    membership

(* Define missing operators *)
LastTerm(logSeq) == IF Len(logSeq) = 0 THEN 0 ELSE logSeq[Len(logSeq)].term
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b
MaxSet(S) == CHOOSE x \in S : \A y \in S : x >= y

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

NodeStateType == {{"Follower", "PreCandidate", "Candidate", "Leader"}}
MessageType == {{"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse"}}

Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> NoNode]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leaderId = [n \in Nodes |-> NoNode]
    /\ electionTimeout = [n \in Nodes |-> {{}}]
    /\ votesReceived = [n \in Nodes |-> {{}}]
    /\ snapshotIndex = [n \in Nodes |-> 0]
    /\ snapshotTerm = [n \in Nodes |-> 0]
    /\ nodes = Nodes
    /\ membership = [n \in Nodes |-> {{}}]

BecomeFollower(n) ==
    /\ state[n] /= "Follower"
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

BecomeCandidate(n) ==
    /\ state[n] = "Follower" \/ state[n] = "PreCandidate"
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {{n}}]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, snapshotIndex, snapshotTerm, nodes, membership>>

BecomePreCandidate(n) ==
    /\ state[n] = "Follower"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {{}}]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, snapshotIndex, snapshotTerm, nodes, membership>>

BecomeLeader(n) ==
    /\ state[n] = "Candidate"
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in nodes |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

RecvRequestVote(n, m, term, candidateId, lastLogIndex, lastLogTerm, prevote) ==
    /\ m \in nodes
    /\ IF prevote THEN state[n] = "PreCandidate" ELSE state[n] = "Candidate"
    /\ term = currentTerm[n] + IF prevote THEN 1 ELSE 0
    /\ candidateId \in nodes
    /\ \/ term > currentTerm[m]
       \/ /\ term = currentTerm[m]
          /\ \/ votedFor[m] = NoNode
             \/ votedFor[m] = candidateId
    /\ lastLogTerm >= LastTerm(log[m])
    /\ lastLogIndex >= Len(log[m])
    /\ votedFor' = [votedFor EXCEPT ![m] = candidateId]
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

RecvRequestVoteResponse(n, m, term, voteGranted, prevote, requestTerm) ==
    /\ m \in nodes
    /\ IF prevote THEN state[n] = "PreCandidate" ELSE state[n] = "Candidate"
    /\ requestTerm = currentTerm[n] + IF prevote THEN 1 ELSE 0
    /\ term <= currentTerm[n]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = IF voteGranted THEN votesReceived[n] \union {{m}} ELSE votesReceived[n]]
    /\ \/ /\ voteGranted
          /\ Cardinality(votesReceived'[n]) > Cardinality(nodes) \div 2
          /\ IF prevote THEN BecomeCandidate(n) ELSE BecomeLeader(n)
       \/ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, snapshotIndex, snapshotTerm, nodes, membership>>

RecvAppendEntries(n, m, term, appendLeaderId, prevLogIndex, prevLogTerm, entries, leaderCommit) ==
    /\ m \in nodes
    /\ term >= currentTerm[n]
    /\ \/ term > currentTerm[n]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
          /\ votedFor' = [votedFor EXCEPT ![n] = NoNode]
          /\ state' = [state EXCEPT ![n] = "Follower"]
       \/ UNCHANGED <<currentTerm, votedFor, state>>
    /\ leaderId' = [leaderId EXCEPT ![n] = appendLeaderId]
    /\ \/ prevLogIndex = 0
       \/ /\ prevLogIndex > 0
          /\ prevLogIndex <= Len(log[n])
          /\ (log[n])[prevLogIndex].term = prevLogTerm
    /\ log' = [log EXCEPT ![n] = IF prevLogIndex > 0 THEN SubSeq(log[n], 1, prevLogIndex) \o entries ELSE entries]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(leaderCommit, Len(log'[n]))]
    /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

RecvAppendEntriesResponse(n, m, term, success, matchIdx) ==
    /\ m \in nodes
    /\ state[n] = "Leader"
    /\ term <= currentTerm[n]
    /\ \/ /\ success
          /\ matchIndex' = [matchIndex EXCEPT ![n][m] = matchIdx]
          /\ nextIndex' = [nextIndex EXCEPT ![n][m] = matchIdx + 1]
       \/ /\ ~success
          /\ nextIndex' = [nextIndex EXCEPT ![n][m] = Max(1, nextIndex[n][m] - 1)]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

SendAppendEntries(n, m) ==
    /\ state[n] = "Leader"
    /\ m \in nodes
    /\ m /= n
    /\ nextIndex[n][m] <= Len(log[n]) + 1
    /\ UNCHANGED vars

SendHeartbeat(n) ==
    /\ state[n] = "Leader"
    /\ UNCHANGED vars

ElectionStart(n) ==
    /\ state[n] = "Follower"
    /\ electionTimeout[n] = {{}}
    /\ BecomePreCandidate(n)

ElectionTimeout(n) ==
    /\ state[n] /= "Leader"
    /\ electionTimeout[n] = {{}}
    /\ ElectionStart(n)

LogAppend(n, entry) ==
    /\ state[n] = "Leader"
    /\ log' = [log EXCEPT ![n] = log[n] \o [entry]]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

LogDelete(n, index) ==
    /\ index > commitIndex[n]
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, index - 1)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

LogCommit(n) ==
    /\ state[n] = "Leader"
    /\ \E m \in nodes :
         matchIndex[n][m] > commitIndex[n]
         /\ Cardinality({{k \in nodes : matchIndex[n][k] >= matchIndex[n][m]}}) > Cardinality(nodes) \div 2
    /\ LET S == { matchIndex[n][m] : m \in nodes } IN
       commitIndex' = [commitIndex EXCEPT ![n] = MaxSet(S)]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = commitIndex'[n]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

PeriodicElectionTimeout(n) ==
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = {{}}]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

PeriodicHeartbeat(n) ==
    /\ state[n] = "Leader"
    /\ UNCHANGED vars

AddNode(n, newNode) ==
    /\ newNode \notin nodes
    /\ nodes' = nodes \union {{newNode}}
    /\ membership' = [membership EXCEPT ![n] = membership[n] \union {{newNode}}]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in nodes' |-> IF m = newNode THEN 1 ELSE nextIndex[n][m]]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in nodes' |-> IF m = newNode THEN 0 ELSE matchIndex[n][m]]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm>>

RemoveNode(n, oldNode) ==
    /\ oldNode \in nodes
    /\ oldNode /= n
    /\ nodes' = nodes \ {{oldNode}}
    /\ membership' = [membership EXCEPT ![n] = membership[n] \ {{oldNode}}]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm>>

SnapshotBegin(n) ==
    /\ snapshotIndex' = [snapshotIndex EXCEPT ![n] = commitIndex[n]]
    /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = IF commitIndex[n] > 0 THEN (log[n])[commitIndex[n]].term ELSE 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, nodes, membership>>

SnapshotEnd(n) ==
    /\ snapshotIndex[n] > 0
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], snapshotIndex[n] + 1, Len(log[n]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, nodes, membership>>

ApplyConfigChange(n, config) ==
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : BecomeFollower(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n, m \in Nodes : \E term, candidateId, lastLogIndex, lastLogTerm, prevote \in BOOLEAN : 
           RecvRequestVote(n, m, term, candidateId, lastLogIndex, lastLogTerm, prevote)
    \/ \E n, m \in Nodes : \E term, voteGranted, prevote, requestTerm \in BOOLEAN : 
           RecvRequestVoteResponse(n, m, term, voteGranted, prevote, requestTerm)
    \/ \E n, m \in Nodes : \E term, appendLeaderId, prevLogIndex, prevLogTerm, entries, leaderCommit : 
           RecvAppendEntries(n, m, term, appendLeaderId, prevLogIndex, prevLogTerm, entries, leaderCommit)
    \/ \E n, m \in Nodes : \E term, success, matchIdx : 
           RecvAppendEntriesResponse(n, m, term, success, matchIdx)
    \/ \E n, m \in Nodes : SendAppendEntries(n, m)
    \/ \E n \in Nodes : SendHeartbeat(n)
    \/ \E n \in Nodes : ElectionStart(n)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : \E entry : LogAppend(n, entry)
    \/ \E n \in Nodes : \E index : LogDelete(n, index)
    \/ \E n \in Nodes : LogCommit(n)
    \/ \E n \in Nodes : PeriodicElectionTimeout(n)
    \/ \E n \in Nodes : PeriodicHeartbeat(n)
    \/ \E n \in Nodes : \E newNode : AddNode(n, newNode)
    \/ \E n \in Nodes : \E oldNode : RemoveNode(n, oldNode)
    \/ \E n \in Nodes : SnapshotBegin(n)
    \/ \E n \in Nodes : SnapshotEnd(n)
    \/ \E n \in Nodes : \E config : ApplyConfigChange(n, config)

Spec == Init /\ [][Next]_vars

====