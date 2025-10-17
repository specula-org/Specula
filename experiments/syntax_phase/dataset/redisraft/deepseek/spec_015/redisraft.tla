---- MODULE redisraft ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Nodes, NoNode
StateSet == {"Follower", "PreCandidate", "Candidate", "Leader"}
VARIABLES cluster, isVoting, currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, votesReceived, net
vars == <<cluster, isVoting, currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, votesReceived, net>>
Init == 
    cluster = Nodes /\
    isVoting = [n \in Nodes |-> TRUE] /\
    currentTerm = [n \in Nodes |-> 0] /\
    state = [n \in Nodes |-> "Follower"] /\
    votedFor = [n \in Nodes |-> NoNode] /\
    log = [n \in Nodes |-> <<>>] /\
    commitIndex = [n \in Nodes |-> 0] /\
    nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]] /\
    matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]] /\
    leaderId = [n \in Nodes |-> NoNode] /\
    votesReceived = [n \in Nodes |-> {}] /\
    net = {}
BecomeFollower(n) == 
    /\ state[n] # "Follower"
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesReceived, net, cluster, isVoting>>
BecomePreCandidate(n) == 
    /\ state[n] = "Follower"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ net' = net \cup { [type |-> "RequestVote", term |-> currentTerm[n] + 1, candidateId |-> n, lastLogIndex |-> Len(log[n]), lastLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, sender |-> n, receiver |-> m ] : m \in { x \in cluster \ {n} : isVoting[x] } }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesReceived, leaderId, cluster, isVoting>>
BecomeCandidate(n) == 
    /\ state[n] = "Follower" \/ state[n] = "PreCandidate"
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ IF isVoting[n] THEN votedFor' = [votedFor EXCEPT ![n] = n] ELSE votedFor' = votedFor
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {}]
    /\ net' = net \cup { [type |-> "RequestVote", term |-> currentTerm[n] + 1, candidateId |-> n, lastLogIndex |-> Len(log[n]), lastLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, sender |-> n, receiver |-> m ] : m \in { x \in cluster \ {n} : isVoting[x] } }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leaderId, cluster, isVoting>>
BecomeLeader(n) == 
    /\ state[n] = "Candidate"
    /\ LET votingNodes == {m \in cluster : isVoting[m]} IN
       Cardinality(votesReceived[n] \cap votingNodes) > Cardinality(votingNodes) / 2
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> IF m # n THEN Len(log[n]) + 1 ELSE nextIndex[n][m] ] ]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m # n THEN 0 ELSE matchIndex[n][m] ] ]
    /\ net' = net \cup { [type |-> "AppendEntries", term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[n], sender |-> n, receiver |-> m ] : m \in cluster \ {n} }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesReceived, cluster, isVoting>>
RecvRequestVote(msg) == 
    LET n == msg["receiver"] IN
    /\ msg \in net
    /\ msg["type"] = "RequestVote"
    /\ IF msg["term"] > currentTerm[n] THEN
         currentTerm' = [currentTerm EXCEPT ![n] = msg["term"]]
         /\ votedFor' = [votedFor EXCEPT ![n] = NoNode]
         /\ state' = [state EXCEPT ![n] = "Follower"]
         /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
       ELSE currentTerm' = currentTerm
    /\ IF msg["term"] < currentTerm[n] THEN
         net' = (net \ {msg}) \cup { [type |-> "RequestVoteResponse", term |-> currentTerm[n], voteGranted |-> FALSE, requestTerm |-> msg["term"], sender |-> n, receiver |-> msg["sender"]] }
       ELSE 
         LET lastLogIndex == Len(log[n])
             lastLogTerm == IF lastLogIndex > 0 THEN log[n][lastLogIndex] ELSE 0
         IN
         IF (votedFor[n] # NoNode AND votedFor[n] # msg["candidateId"]) OR 
            (msg["lastLogTerm"] < lastLogTerm OR (msg["lastLogTerm"] = lastLogTerm AND msg["lastLogIndex"] < lastLogIndex)) THEN
            net' = (net \ {msg}) \cup { [type |-> "RequestVoteResponse", term |-> currentTerm[n], voteGranted |-> FALSE, requestTerm |-> msg["term"], sender |-> n, receiver |-> msg["sender"]] }
         ELSE
            /\ IF msg["term"] = currentTerm[n] THEN votedFor' = [votedFor EXCEPT ![n] = msg["candidateId"]] ELSE votedFor' = votedFor
            /\ net' = (net \ {msg}) \cup { [type |-> "RequestVoteResponse", term |-> currentTerm[n], voteGranted |-> TRUE, requestTerm |-> msg["term"], sender |-> n, receiver |-> msg["sender"]] }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesReceived, cluster, isVoting>>
RecvRequestVoteResponse(msg) == 
    LET n == msg["receiver"] IN
    /\ msg \in net
    /\ msg["type"] = "RequestVoteResponse"
    /\ IF msg["term"] > currentTerm[n] THEN
         currentTerm' = [currentTerm EXCEPT ![n] = msg["term"]]
         /\ votedFor' = [votedFor EXCEPT ![n] = NoNode]
         /\ state' = [state EXCEPT ![n] = "Follower"]
         /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
       ELSE currentTerm' = currentTerm
    /\ IF msg["voteGranted"] THEN
         votesReceived' = [votesReceived EXCEPT ![n] = votesReceived[n] \cup {msg["sender"]}]
       ELSE votesReceived' = votesReceived
    /\ net' = net \ {msg}
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, cluster, isVoting>>
ElectionTimeout(n) == 
    /\ state[n] = "Follower"
    /\ \/ BecomePreCandidate(n)
       \/ BecomeCandidate(n)
HeartbeatTimeout(n) == 
    /\ state[n] = "Leader"
    /\ net' = net \cup { [type |-> "AppendEntries", term |-> currentTerm[n], leaderId |-> n, prevLogIndex |-> Len(log[n]), prevLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])] ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[n], sender |-> n, receiver |-> m ] : m \in cluster \ {n} }
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, votesReceived, leaderId, cluster, isVoting>>
Next == 
    \/ \E n \in Nodes : BecomeFollower(n)
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E msg \in net : RecvRequestVote(msg)
    \/ \E msg \in net : RecvRequestVoteResponse(msg)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : HeartbeatTimeout(n)
Spec == Init /\ [][Next]_vars
====