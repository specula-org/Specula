---- MODULE redisraft ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, None

VARIABLES state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm

StateType == {"Follower", "PreCandidate", "Candidate", "Leader"}
MessageType == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "Snapshot"}

Init == 
    activeNodes = Nodes
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ log = [n \in Nodes |-> <<>>]
    /\ nextIndex = [n, f \in Nodes |-> 1]
    /\ matchIndex = [n, f \in Nodes |-> 0]
    /\ messages = {}
    /\ isVoting = [n \in Nodes |-> TRUE]
    /\ votedForMe = [n, f \in Nodes |-> FALSE]
    /\ snapshotLastIndex = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]

BecomeFollower(n, term) == 
    /\ term > currentTerm[n]
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ UNCHANGED <<commitIndex, log, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

BecomePreCandidate(n) == 
    /\ state[n] = "Follower"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ votedForMe' = [votedForMe EXCEPT ![n] = [f \in Nodes |-> FALSE]]
    /\ LET lastLogIndex == Len(log[n]), 
           lastLogTerm == IF lastLogIndex > 0 THEN log[n][lastLogIndex] ELSE 0
       IN
       messages' = messages \cup { [type |-> "RequestVote", sender |-> n, receiver |-> f, term |-> currentTerm[n] + 1, candidateId |-> n, lastLogIndex |-> lastLogIndex, lastLogTerm |-> lastLogTerm, prevote |-> TRUE] : f \in (activeNodes \ {n}) | isVoting[f] }
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(n) == 
    /\ state[n] = "Follower" \/ state[n] = "PreCandidate"
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ votedForMe' = [votedForMe EXCEPT ![n] = [f \in Nodes |-> FALSE]]
    /\ LET lastLogIndex = Len(log[n]),
           lastLogTerm = IF lastLogIndex > 0 THEN log[n][lastLogIndex] ELSE 0
       IN
       messages' = messages \cup { [type |-> "RequestVote", sender |-> n, receiver |-> f, term |-> currentTerm[n], candidateId |-> n, lastLogIndex |-> lastLogIndex, lastLogTerm |-> lastLogTerm, prevote |-> FALSE] : f \in (activeNodes \ {n}) | isVoting[f] }
    /\ UNCHANGED <<commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(n) == 
    /\ state[n] = "Candidate"
    /\ \A f \in activeNodes \ {n} : votedForMe[n][f] \/ ~isVoting[f]
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ log' = [log EXCEPT ![n] = Append(log[n], currentTerm[n])]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [f \in Nodes |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [f \in Nodes |-> 0]]
    /\ messages' = messages \cup { [type |-> "AppendEntries", sender |-> n, receiver |-> f, term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[n]] : f \in activeNodes \ {n} }
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVote(msg) == 
    /\ msg \in messages
    /\ msg.type = "RequestVote"
    /\ IF msg.term > currentTerm[msg.receiver] THEN
           BecomeFollower(msg.receiver, msg.term)
       ELSE TRUE
    /\ LET n = msg.receiver,
           lastLogIndex = Len(log[n]),
           lastLogTerm = IF lastLogIndex > 0 THEN log[n][lastLogIndex] ELSE 0
       IN
       IF msg.term = currentTerm[n] \/ (msg.prevote /\ msg.term = currentTerm[n] + 1) THEN
           IF (votedFor[n] = None \/ votedFor[n] = msg.candidateId) /\ 
              (msg.lastLogTerm > lastLogTerm \/ (msg.lastLogTerm = lastLogTerm /\ msg.lastLogIndex >= lastLogIndex)) THEN
               /\ IF ~msg.prevote THEN votedFor' = [votedFor EXCEPT ![n] = msg.candidateId] ELSE votedFor' = votedFor
               /\ messages' = (messages \ {msg}) \cup { [type |-> "RequestVoteResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], voteGranted |-> TRUE, requestTerm |-> msg.term] }
           ELSE
               /\ messages' = (messages \ {msg}) \cup { [type |-> "RequestVoteResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], voteGranted |-> FALSE, requestTerm |-> msg.term] }
       ELSE
           /\ messages' = (messages \ {msg}) \cup { [type |-> "RequestVoteResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], voteGranted |-> FALSE, requestTerm |-> msg.term] }
    /\ UNCHANGED <<state, currentTerm, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVoteResponse(msg) == 
    /\ msg \in messages
    /\ msg.type = "RequestVoteResponse"
    /\ IF msg.term > currentTerm[msg.receiver] THEN
           BecomeFollower(msg.receiver, msg.term)
       ELSE TRUE
    /\ LET n = msg.receiver
       IN
       IF (state[n] = "PreCandidate" /\ msg.requestTerm = currentTerm[n] + 1) \/ (state[n] = "Candidate" /\ msg.requestTerm = currentTerm[n]) THEN
           IF msg.voteGranted THEN
               /\ votedForMe' = [votedForMe EXCEPT ![n][msg.sender] = TRUE]
               /\ LET votes = Cardinality({f \in activeNodes : isVoting[f] /\ votedForMe[n][f]})
               IN
               IF votes > Cardinality(activeNodes) / 2 THEN
                   IF state[n] = "PreCandidate" THEN
                       BecomeCandidate(n)
                   ELSE
                       BecomeLeader(n)
               ELSE
                   UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, snapshotLastIndex, snapshotLastTerm>>
           ELSE
               UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>
       ELSE
           UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>
    /\ messages' = messages \ {msg}

RecvAppendEntries(msg) == 
    /\ msg \in messages
    /\ msg.type = "AppendEntries"
    /\ IF msg.term > currentTerm[msg.receiver] THEN
           BecomeFollower(msg.receiver, msg.term)
       ELSE TRUE
    /\ LET n = msg.receiver
       IN
       IF msg.term >= currentTerm[n] THEN
           state' = [state EXCEPT ![n] = "Follower"]
           /\ IF msg.prevLogIndex = snapshotLastIndex[n] THEN
                  IF msg.prevLogTerm = snapshotLastTerm[n] THEN
                      /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.prevLogIndex) \o msg.entries]
                      /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(msg.leaderCommit, Len(log[n]))]
                      /\ messages' = (messages \ {msg}) \cup { [type |-> "AppendEntriesResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], success |-> TRUE, currentIdx |-> Len(log[n])] }
                  ELSE
                      /\ messages' = (messages \ {msg}) \cup { [type |-> "AppendEntriesResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], success |-> FALSE, currentIdx |-> Len(log[n])] }
              ELSE
                  IF msg.prevLogIndex > 0 /\ msg.prevLogIndex <= Len(log[n]) THEN
                      IF log[n][msg.prevLogIndex] = msg.prevLogTerm THEN
                          /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.prevLogIndex) \o msg.entries]
                          /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(msg.leaderCommit, Len(log[n]))]
                          /\ messages' = (messages \ {msg}) \cup { [type |-> "AppendEntriesResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], success |-> TRUE, currentIdx |-> Len(log[n])] }
                      ELSE
                          /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.prevLogIndex - 1)]
                          /\ messages' = (messages \ {msg}) \cup { [type |-> "AppendEntriesResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], success |-> FALSE, currentIdx |-> Len(log[n])] }
                  ELSE
                      /\ messages' = (messages \ {msg}) \cup { [type |-> "AppendEntriesResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], success |-> FALSE, currentIdx |-> Len(log[n])] }
       ELSE
           /\ messages' = (messages \ {msg}) \cup { [type |-> "AppendEntriesResponse", sender |-> n, receiver |-> msg.sender, term |-> currentTerm[n], success |-> FALSE, currentIdx |-> Len(log[n])] }
    /\ UNCHANGED <<currentTerm, votedFor, nextIndex, matchIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntriesResponse(msg) == 
    /\ msg \in messages
    /\ msg.type = "AppendEntriesResponse"
    /\ IF msg.term > currentTerm[msg.receiver] THEN
           BecomeFollower(msg.receiver, msg.term)
       ELSE TRUE
    /\ LET n = msg.receiver
       IN
       IF state[n] = "Leader" THEN
           IF msg.success THEN
               /\ matchIndex' = [matchIndex EXCEPT ![n][msg.sender] = msg.currentIdx]
               /\ nextIndex' = [nextIndex EXCEPT ![n][msg.sender] = msg.currentIdx + 1]
               /\ LET majorities = {i \in 1..Len(log[n]) : Cardinality({f \in activeNodes : isVoting[f] /\ matchIndex[n][f] >= i}) > Cardinality(activeNodes) / 2}
               IN
               IF majorities # {} THEN
                   commitIndex' = [commitIndex EXCEPT ![n] = Max(majorities)]
               ELSE
                   commitIndex' = commitIndex
           ELSE
               /\ nextIndex' = [nextIndex EXCEPT ![n][msg.sender] = nextIndex[n][msg.sender] - 1]
       ELSE
           UNCHANGED <<nextIndex, matchIndex, commitIndex>>
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

SendAppendEntries(n, f) == 
    /\ state[n] = "Leader"
    /\ n # f
    /\ f \in activeNodes
    /\ LET nextIdx = nextIndex[n][f],
           prevLogIndex = nextIdx - 1,
           prevLogTerm = IF prevLogIndex > 0 THEN IF prevLogIndex > snapshotLastIndex[n] THEN log[n][prevLogIndex] ELSE snapshotLastTerm[n] ELSE 0,
           entries = IF nextIdx <= Len(log[n]) THEN SubSeq(log[n], nextIdx, Len(log[n])) ELSE <<>>
       IN
       messages' = messages \cup { [type |-> "AppendEntries", sender |-> n, receiver |-> f, term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm, entries |-> entries, leaderCommit |-> commitIndex[n]] }
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

SendHeartbeat(n) == 
    /\ state[n] = "Leader"
    /\ messages' = messages \cup { [type |-> "AppendEntries", sender |-> n, receiver |-> f, term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[n]] : f \in activeNodes \ {n} }
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

ElectionStart(n) == 
    /\ state[n] = "Follower"
    /\ BecomePreCandidate(n)

ElectionTimeout(n) == 
    /\ state[n] = "Follower" \/ state[n] = "Candidate"
    /\ ElectionStart(n)

LogAppend(n, entry) == 
    /\ state[n] = "Leader"
    /\ log' = [log EXCEPT ![n] = Append(log[n], entry)]
    /\ nextIndex' = [nextIndex EXCEPT ![n][n] = Len(log[n]) + 1]
    /\ matchIndex' = [matchIndex EXCEPT ![n][n] = Len(log[n])]
    /\ messages' = messages \cup { [type |-> "AppendEntries", sender |-> n, receiver |-> f, term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, entries |-> <<entry>>, leaderCommit |-> commitIndex[n]] : f \in activeNodes \ {n} }
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

LogDelete(n, index) == 
    /\ index > commitIndex[n]
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, index - 1)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

LogCommit(n, index) == 
    /\ state[n] = "Leader"
    /\ index <= Len(log[n])
    /\ Cardinality({f \in activeNodes : isVoting[f] /\ matchIndex[n][f] >= index}) > Cardinality(activeNodes) / 2
    /\ LET majorities = {i \in 1..Len(log[n]) : Cardinality({f \in activeNodes : isVoting[f] /\ matchIndex[n][f] >= i}) > Cardinality(activeNodes) / 2}
    IN
    IF majorities # {} THEN
        commitIndex' = [commitIndex EXCEPT ![n] = Max(majorities)]
    ELSE
        commitIndex' = commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

PeriodicElectionTimeout(n) == 
    /\ state[n] = "Follower" \/ state[n] = "Candidate"
    /\ ElectionTimeout(n)

PeriodicHeartbeat(n) == 
    /\ state[n] = "Leader"
    /\ SendHeartbeat(n)

AddNode(n) == 
    /\ n \in Nodes \ activeNodes
    /\ activeNodes' = activeNodes \cup {n}
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = 0]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = 0]
    /\ log' = [log EXCEPT ![n] = <<>>]
    /\ nextIndex' = [i \in Nodes, j \in Nodes |-> IF i = n \/ j = n THEN 1 ELSE nextIndex[i][j] ]
    /\ matchIndex' = [i \in Nodes, j \in Nodes |-> IF i = n \/ j = n THEN 0 ELSE matchIndex[i][j] ]
    /\ isVoting' = [isVoting EXCEPT ![n] = TRUE]
    /\ votedForMe' = [i \in Nodes, j \in Nodes |-> IF i = n \/ j = n THEN FALSE ELSE votedForMe[i][j] ]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = 0]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = 0]
    /\ UNCHANGED <<messages>>

RemoveNode(n) == 
    /\ n \in activeNodes
    /\ activeNodes' = activeNodes \ {n}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, messages, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

SnapshotBegin(n) == 
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = commitIndex[n]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = log[n][commitIndex[n]]]
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], commitIndex[n] + 1, Len(log[n]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe>>

SnapshotEnd(n) == 
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

ApplyConfigChange(n, change) == 
    /\ change \in {"AddVoting", "RemoveVoting"}
    /\ IF change = "AddVoting" THEN
           isVoting' = [isVoting EXCEPT ![n] = TRUE]
       ELSE
           isVoting' = [isVoting EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, messages, activeNodes, votedForMe, snapshotLastIndex, snapshotLastTerm>>

Next == 
    \/ \E n \in Nodes, term \in Nat : term > currentTerm[n] /\ BecomeFollower(n, term)
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E msg \in messages : RecvRequestVote(msg)
    \/ \E msg \in messages : RecvRequestVoteResponse(msg)
    \/ \E msg \in messages : RecvAppendEntries(msg)
    \/ \E msg \in messages : RecvAppendEntriesResponse(msg)
    \/ \E n \in Nodes : \E f \in Nodes : SendAppendEntries(n, f)
    \/ \E n \in Nodes : SendHeartbeat(n)
    \/ \E n \in Nodes : ElectionStart(n)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : \E entry \in Nat : LogAppend(n, entry)
    \/ \E n \in Nodes : \E index \in Nat : LogDelete(n, index)
    \/ \E n \in Nodes : \E index \in Nat : LogCommit(n, index)
    \/ \E n \in Nodes : PeriodicElectionTimeout(n)
    \/ \E n \in Nodes : PeriodicHeartbeat(n)
    \/ \E n \in Nodes : AddNode(n)
    \/ \E n \in Nodes : RemoveNode(n)
    \/ \E n \in Nodes : SnapshotBegin(n)
    \/ \E n \in Nodes : SnapshotEnd(n)
    \/ \E n \in Nodes : \E change \in {"AddVoting", "RemoveVoting"} : ApplyConfigChange(n, change)

vars == <<state, currentTerm, votedFor, commitIndex, log, nextIndex, matchIndex, messages, activeNodes, isVoting, votedForMe, snapshotLastIndex, snapshotLastTerm>>

Spec == Init /\ [][Next]_vars

====