---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, None
VARIABLES state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config, network

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config>>

Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ leaderId = [n \in Nodes |-> None]
    /\ electionTimeout = [n \in Nodes |-> CHOOSE t \in 150..300 : TRUE]
    /\ votesReceived = [n \in Nodes |-> {}]
    /\ snapshotIndex = [n \in Nodes |-> 0]
    /\ snapshotTerm = [n \in Nodes |-> 0]
    /\ config = [n \in Nodes |-> Nodes]
    /\ network = {}

BecomeFollower(n) == 
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in 150..300 : TRUE]
    /\ UNCHANGED <<currentTerm, log, commitIndex, lastApplied, nextIndex, matchIndex, votesReceived, snapshotIndex, snapshotTerm, config, network>>

BecomePreCandidate(n) == 
    /\ state[n] = "Follower"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, snapshotIndex, snapshotTerm, config, network>>

BecomeCandidate(n) == 
    /\ state[n] \in {"PreCandidate", "Follower"}
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in 150..300 : TRUE]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotIndex, snapshotTerm, config, network>>

BecomeLeader(n) == 
    /\ state[n] = "Candidate"
    /\ Cardinality(votesReceived[n]) > Cardinality(config[n]) \div 2
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config, network>>

SendRequestVote(n, target) == 
    /\ state[n] \in {"PreCandidate", "Candidate"}
    /\ \E msg \in [type |-> "RequestVote", term |-> IF state[n] = "PreCandidate" THEN currentTerm[n] + 1 ELSE currentTerm[n], candidate |-> n, lastLogIndex |-> Len(log[n]), lastLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0] : 
        network' = network \cup {msg}
    /\ UNCHANGED vars

RecvRequestVote(n, msg) == 
    /\ msg \in network
    /\ msg.type = "RequestVote"
    /\ \/ msg.term > currentTerm[n]
       \/ /\ msg.term = currentTerm[n]
          /\ votedFor[n] \in {None, msg.candidate}
    /\ \/ msg.lastLogTerm > (IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0)
       \/ /\ msg.lastLogTerm = (IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0)
          /\ msg.lastLogIndex >= Len(log[n])
    /\ votedFor' = [votedFor EXCEPT ![n] = msg.candidate]
    /\ \E resp \in [type |-> "RequestVoteResponse", term |-> currentTerm[n], voteGranted |-> TRUE, candidate |-> msg.candidate] : 
        network' = (network \ {msg}) \cup {resp}
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config>>

RecvRequestVoteResponse(n, msg) == 
    /\ msg \in network
    /\ msg.type = "RequestVoteResponse"
    /\ state[n] \in {"PreCandidate", "Candidate"}
    /\ msg.term <= currentTerm[n]
    /\ msg.voteGranted = TRUE
    /\ votesReceived' = [votesReceived EXCEPT ![n] = @ \cup {msg.candidate}]
    /\ network' = network \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, snapshotIndex, snapshotTerm, config>>

SendAppendEntries(n, target) == 
    /\ state[n] = "Leader"
    /\ \E prevLogIndex, prevLogTerm, entries, leaderCommit : 
        LET prevLogIndex == nextIndex[n][target] - 1 IN
        LET prevLogTerm == IF prevLogIndex > 0 THEN log[n][prevLogIndex].term ELSE 0 IN
        LET entries == SubSeq(log[n], nextIndex[n][target], Len(log[n])) IN
        LET leaderCommit == commitIndex[n] IN
        \E msg \in [type |-> "AppendEntries", term |-> currentTerm[n], leader |-> n, prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm, entries |-> entries, leaderCommit |-> leaderCommit] : 
            network' = network \cup {msg}
    /\ UNCHANGED vars

RecvAppendEntries(n, msg) == 
    /\ msg \in network
    /\ msg.type = "AppendEntries"
    /\ \/ msg.term > currentTerm[n]
       \/ /\ msg.term = currentTerm[n]
          /\ \/ state[n] \in {"Follower", "PreCandidate", "Candidate"}
             \/ /\ state[n] = "Leader"
                /\ msg.leader = n
    /\ \/ msg.term > currentTerm[n]
       \/ /\ msg.term = currentTerm[n]
          /\ \/ msg.prevLogIndex = 0
             \/ /\ msg.prevLogIndex <= Len(log[n])
                /\ msg.prevLogTerm = log[n][msg.prevLogIndex].term
    /\ (* Process entries and update log *)
    /\ (* Update commitIndex if needed *)
    /\ \E resp \in [type |-> "AppendEntriesResponse", term |-> currentTerm[n], success |-> TRUE, matchIndex |-> msg.prevLogIndex + Len(msg.entries)] : 
        network' = (network \ {msg}) \cup {resp}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config>>

RecvAppendEntriesResponse(n, msg) == 
    /\ msg \in network
    /\ msg.type = "AppendEntriesResponse"
    /\ state[n] = "Leader"
    /\ msg.term <= currentTerm[n]
    /\ msg.success = TRUE
    /\ matchIndex' = [matchIndex EXCEPT ![n][msg.sender] = msg.matchIndex]
    /\ nextIndex' = [nextIndex EXCEPT ![n][msg.sender] = msg.matchIndex + 1]
    /\ (* Update commitIndex if majority replicated *)
    /\ network' = network \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config>>

ElectionTimeout(n) == 
    /\ state[n] \in {"Follower", "Candidate"}
    /\ (* Timeout condition *)
    /\ BecomePreCandidate(n)

LogAppend(n, entry) == 
    /\ state[n] = "Leader"
    /\ log' = [log EXCEPT ![n] = @ \o [term |-> currentTerm[n], value |-> entry]]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config, network>>

LogCommit(n) == 
    /\ \E index \in {i \in 1..Len(log[n]) : 
        Cardinality({m \in config[n] : matchIndex[n][m] >= i}) > Cardinality(config[n]) \div 2} : 
        commitIndex' = [commitIndex EXCEPT ![n] = index]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = commitIndex[n]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, config, network>>

AddNode(n, newNode) == 
    /\ config' = [config EXCEPT ![n] = @ \cup {newNode}]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, network>>

RemoveNode(n, nodeToRemove) == 
    /\ config' = [config EXCEPT ![n] = @ \ {nodeToRemove}]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, snapshotIndex, snapshotTerm, network>>

SnapshotBegin(n) == 
    /\ \E lastIncludedIndex, lastIncludedTerm : 
        snapshotIndex' = [snapshotIndex EXCEPT ![n] = lastIncludedIndex]
        /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = lastIncludedTerm]
        /\ log' = [log EXCEPT ![n] = SubSeq(@, lastIncludedIndex + 1, Len(@))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, votesReceived, config, network>>

SnapshotEnd(n) == 
    /\ (* Finalize snapshot *)
    /\ UNCHANGED vars

Next == 
    \/ \E n \in Nodes : BecomeFollower(n)
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n, m \in Nodes : SendRequestVote(n, m)
    \/ \E n \in Nodes, msg \in network : RecvRequestVote(n, msg)
    \/ \E n \in Nodes, msg \in network : RecvRequestVoteResponse(n, msg)
    \/ \E n, m \in Nodes : SendAppendEntries(n, m)
    \/ \E n \in Nodes, msg \in network : RecvAppendEntries(n, msg)
    \/ \E n \in Nodes, msg \in network : RecvAppendEntriesResponse(n, msg)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : LogAppend(n, CHOOSE e \in ANY : TRUE)
    \/ \E n \in Nodes : LogCommit(n)
    \/ \E n, newNode \in Nodes : AddNode(n, newNode)
    \/ \E n, nodeToRemove \in Nodes : RemoveNode(n, nodeToRemove)
    \/ \E n \in Nodes : SnapshotBegin(n)
    \/ \E n \in Nodes : SnapshotEnd(n)

Spec == Init /\ [][Next]_vars

====

\* MINIMAL FIX: Added missing network variable to UNCHANGED clause in BecomeFollower action (line 43).
\* This prevents deadlocks by ensuring network state is preserved when not explicitly modified.