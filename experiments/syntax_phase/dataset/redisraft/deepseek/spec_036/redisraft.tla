---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Nodes, MaxTerm, MaxLogIndex, Nil
VARIABLES state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config
vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
NodeState == {"Follower", "PreCandidate", "Candidate", "Leader"}
LastTerm(logSeq) == IF logSeq = <<>> THEN 0 ELSE logSeq[Len(logSeq)].term
Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leaderId = [n \in Nodes |-> Nil]
    /\ electionTimeout \in [Nodes -> 1000..2000]
    /\ votes = [n \in Nodes |-> {}]
    /\ snapshotIndex = [n \in Nodes |-> 0]
    /\ snapshotTerm = [n \in Nodes |-> 0]
    /\ config = Nodes
BecomeFollower(n) ==
    /\ state[n] /= "Follower"
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![n] = Nil]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] \in 1000..2000]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, snapshotIndex, snapshotTerm, config>>
BecomePreCandidate(n) ==
    /\ state[n] = "Follower"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votes' = [votes EXCEPT ![n] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, snapshotIndex, snapshotTerm, config>>
BecomeCandidate(n) ==
    /\ state[n] \in {"Follower", "PreCandidate"}
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] \in 1000..2000]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leaderId, snapshotIndex, snapshotTerm, config>>
BecomeLeader(n) ==
    /\ state[n] = "Candidate"
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
RecvRequestVote(n, m, term, candidateId, lastLogIndex, lastLogTerm) ==
    /\ term >= currentTerm[n]
    /\ \/ term > currentTerm[n]
       \/ votedFor[n] = Nil \/ votedFor[n] = candidateId
    /\ \/ lastLogTerm > LastTerm(log[n])
       \/ /\ lastLogTerm = LastTerm(log[n])
          /\ lastLogIndex >= Len(log[n])
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = candidateId]
    /\ UNCHANGED <<state, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
RecvRequestVoteResponse(n, m, term, voteGranted) ==
    /\ state[n] \in {"PreCandidate", "Candidate"}
    /\ term = currentTerm[n]
    /\ voteGranted
    /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m}]
    /\ \/ Cardinality(votes'[n]) > Cardinality(config) \div 2
       /\ \/ state[n] = "PreCandidate" /\ BecomeCandidate(n)
          \/ state[n] = "Candidate" /\ BecomeLeader(n)
       \/ UNCHANGED state
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, snapshotIndex, snapshotTerm, config>>
RecvAppendEntries(n, m, term, leaderId, prevLogIndex, prevLogTerm, entries, leaderCommit) ==
    /\ term >= currentTerm[n]
    /\ \/ term > currentTerm[n]
       /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
       \/ UNCHANGED currentTerm
    /\ \/ prevLogIndex = 0
       \/ /\ prevLogIndex > 0
          /\ prevLogIndex <= Len(log[n])
          /\ log[n][prevLogIndex].term = prevLogTerm
    /\ log' = [log EXCEPT ![n] = IF prevLogIndex > 0 THEN SubSeq(log[n], 1, prevLogIndex) \o entries ELSE entries]
    /\ \/ leaderCommit > commitIndex[n]
       /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(leaderCommit, Len(log'[n]))]
       \/ UNCHANGED commitIndex
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![n] = m]
    /\ UNCHANGED <<votedFor, nextIndex, matchIndex, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
RecvAppendEntriesResponse(n, m, term, success, matchIdx) ==
    /\ state[n] = "Leader"
    /\ term = currentTerm[n]
    /\ \/ success
       /\ matchIndex' = [matchIndex EXCEPT ![n][m] = matchIdx]
       /\ nextIndex' = [nextIndex EXCEPT ![n][m] = matchIdx + 1]
       \/ UNCHANGED <<matchIndex, nextIndex>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
SendAppendEntries(n, m) ==
    /\ state[n] = "Leader"
    /\ nextIndex[n][m] <= Len(log[n]) + 1
    /\ UNCHANGED vars
SendHeartbeat(n) ==
    /\ state[n] = "Leader"
    /\ UNCHANGED vars
ElectionStart(n) ==
    /\ state[n] = "Follower"
    /\ BecomePreCandidate(n)
ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate"}
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] \in 1000..2000]
    /\ \/ state[n] = "Follower" /\ ElectionStart(n)
       \/ state[n] = "Candidate" /\ BecomeCandidate(n)
LogAppend(n, entry) ==
    /\ state[n] = "Leader"
    /\ log' = [log EXCEPT ![n] = log[n] \o [entry]]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
LogDelete(n, index) ==
    /\ index > commitIndex[n]
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, index - 1)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
LogCommit(n) ==
    /\ state[n] = "Leader"
    /\ LET maxIndex == Max({matchIndex[n][m] : m \in config})
       IN \/ \A i \in {commitIndex[n] + 1 .. maxIndex} :
             Cardinality({m \in config : matchIndex[n][m] >= i}) > Cardinality(config) \div 2
          /\ commitIndex' = [commitIndex EXCEPT ![n] = maxIndex]
          \/ UNCHANGED commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
PeriodicElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "Candidate"}
    /\ ElectionTimeout(n)
PeriodicHeartbeat(n) ==
    /\ state[n] = "Leader"
    /\ SendHeartbeat(n)
AddNode(n, newNode) ==
    /\ config' = config \cup {newNode}
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![newNode] = Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![newNode] = 0]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm>>
RemoveNode(n, oldNode) ==
    /\ config' = config \ {oldNode}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm>>
SnapshotBegin(n) ==
    /\ commitIndex[n] > snapshotIndex[n]
    /\ snapshotIndex' = [snapshotIndex EXCEPT ![n] = commitIndex[n]]
    /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = log[n][commitIndex[n]].term]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, config>>
SnapshotEnd(n) ==
    /\ snapshotIndex[n] > 0
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], snapshotIndex[n] + 1, Len(log[n]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
ApplyConfigChange(n, newConfig) ==
    /\ config' = newConfig
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, electionTimeout, votes, snapshotIndex, snapshotTerm>>
Next ==
    \/ \E n \in Nodes : BecomeFollower(n)
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n, m \in Nodes : \E term \in 0..MaxTerm : \E candidateId \in Nodes : \E lastLogIndex \in 0..MaxLogIndex : \E lastLogTerm \in 0..MaxTerm :
          RecvRequestVote(n, m, term, candidateId, lastLogIndex, lastLogTerm)
    \/ \E n, m \in Nodes : \E term \in 0..MaxTerm : \E voteGranted \in BOOLEAN :
          RecvRequestVoteResponse(n, m, term, voteGranted)
    \/ \E n, m \in Nodes : \E term \in 0..MaxTerm : \E leaderId \in Nodes : \E prevLogIndex \in 0..MaxLogIndex : \E prevLogTerm \in 0..MaxTerm : \E entries \in Seq([term: Nat, data: ANY]) : \E leaderCommit \in 0..MaxLogIndex :
          RecvAppendEntries(n, m, term, leaderId, prevLogIndex, prevLogTerm, entries, leaderCommit)
    \/ \E n, m \in Nodes : \E term \in 0..MaxTerm : \E success \in BOOLEAN : \E matchIdx \in 0..MaxLogIndex :
          RecvAppendEntriesResponse(n, m, term, success, matchIdx)
    \/ \E n, m \in Nodes : SendAppendEntries(n, m)
    \/ \E n \in Nodes : SendHeartbeat(n)
    \/ \E n \in Nodes : ElectionStart(n)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : \E entry \in [term: Nat, data: ANY] : LogAppend(n, entry)
    \/ \E n \in Nodes : \E index \in 1..MaxLogIndex : LogDelete(n, index)
    \/ \E n \in Nodes : LogCommit(n)
    \/ \E n \in Nodes : PeriodicElectionTimeout(n)
    \/ \E n \in Nodes : PeriodicHeartbeat(n)
    \/ \E n, newNode \in Nodes : AddNode(n, newNode)
    \/ \E n, oldNode \in Nodes : RemoveNode(n, oldNode)
    \/ \E n \in Nodes : SnapshotBegin(n)
    \/ \E n \in Nodes : SnapshotEnd(n)
    \/ \E n \in Nodes : \E newConfig \in SUBSET Nodes : ApplyConfigChange(n, newConfig)
Spec == Init /\ [][Next]_vars
Termination ==
    \E n \in Nodes : state[n] = "Leader"
====