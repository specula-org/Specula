---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Node, None, ElectionTimeoutMin, ElectionTimeoutMax, RequestTimeout
ASSUME None \notin Node

VARIABLES clusterNodes, state, currentTerm, votedFor, log, commitIndex, leaderId, snapshotLastIndex, snapshotLastTerm, timeoutElapsed, electionTimeout, msgId, nextIndex, matchIndex, msgs

vars == <<clusterNodes, state, currentTerm, votedFor, log, commitIndex, leaderId, snapshotLastIndex, snapshotLastTerm, timeoutElapsed, electionTimeout, msgId, nextIndex, matchIndex, msgs>>

Init == 
    /\ clusterNodes \subseteq Node
    /\ state = [n \in Node |-> "Follower"]
    /\ currentTerm = [n \in Node |-> 0]
    /\ votedFor = [n \in Node |-> None]
    /\ log = [n \in Node |-> <<>>]
    /\ commitIndex = [n \in Node |-> 0]
    /\ leaderId = [n \in Node |-> None]
    /\ snapshotLastIndex = [n \in Node |-> 0]
    /\ snapshotLastTerm = [n \in Node |-> 0]
    /\ timeoutElapsed = [n \in Node |-> 0]
    /\ electionTimeout = [n \in Node |-> CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
    /\ msgId = [n \in Node |-> 0]
    /\ nextIndex = [n \in Node |-> [m \in Node |-> 1]]
    /\ matchIndex = [n \in Node |-> [m \in Node |-> 0]]
    /\ msgs = {{}}

BecomeFollower(node) == 
    /\ state[node] \in {"Candidate", "PreCandidate", "Leader"}
    /\ state' = [state EXCEPT ![node] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![node] = None]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
    /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
    /\ UNCHANGED <<clusterNodes, currentTerm, votedFor, log, commitIndex, snapshotLastIndex, snapshotLastTerm, msgId, nextIndex, matchIndex, msgs>>

BecomeCandidate(node) == 
    /\ state[node] = "Follower" \/ state[node] = "PreCandidate"
    /\ currentTerm' = [currentTerm EXCEPT ![node] = currentTerm[node] + 1]
    /\ votedFor' = [votedFor EXCEPT ![node] = node]
    /\ state' = [state EXCEPT ![node] = "Candidate"]
    /\ leaderId' = [leaderId EXCEPT ![node] = None]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
    /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
    /\ msgs' = msgs \cup { ["RequestVote", node, other, currentTerm[node] + 1, node, Len(log[node]), IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, FALSE] : other \in clusterNodes \ {node} }
    /\ UNCHANGED <<clusterNodes, log, commitIndex, snapshotLastIndex, snapshotLastTerm, msgId, nextIndex, matchIndex>>

BecomePreCandidate(node) == 
    /\ state[node] = "Follower"
    /\ state' = [state EXCEPT ![node] = "PreCandidate"]
    /\ leaderId' = [leaderId EXCEPT ![node] = None]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
    /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
    /\ msgs' = msgs \cup { ["RequestVote", node, other, currentTerm[node] + 1, node, Len(log[node]), IF Len(log[node]) > 极 THEN log[node][Len(log[node])] ELSE 0, TRUE] : other \in clusterNodes \ {node} }
    /\ UNCHANGED <<clusterNodes, currentTerm, votedFor, log, commitIndex, snapshotLastIndex, snapshotLastTerm, msgId, nextIndex, matchIndex>>

BecomeLeader(node) == 
    /\ state[node] = "Candidate"
    /\ LET votes == { n \in clusterNodes : votedFor[n] = node } IN
       Cardinality(votes) > Cardinality(clusterNodes) / 2
    /\ state' = [state EXCEPT ![node] = "Leader"]
    /\ leader极' = [leaderId EXCEPT ![node] = node]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![node] = [m \in Node |-> IF m = node THEN nextIndex[node][m] ELSE Len(log[node]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![node] = [m \in Node |-> IF m = node THEN matchIndex[node][m] ELSE 0]]
    /\ msgs' = msgs \cup { ["AppendEntries", node, other, currentTerm[node], node, Len(log[node]), IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, <<>>, commitIndex[node]] : other \in clusterNodes \ {node} }
    /\ UNCHANGED <<clusterNodes, currentTerm, votedFor, log, commitIndex, snapshotLastIndex, snapshotLastTerm, electionTimeout, msgId>>

ReceiveRequestVote(msg) == 
    /\ msg \in msgs
    /\ msg[1] = "RequestVote"
    /\ LET sender == msg[2], receiver == msg[3], term == msg[4], candidateId == msg[5], lastLogIndex == msg[6], lastLogTerm == msg[7], prevote == msg[8] IN
       receiver \in clusterNodes
       /\ IF term > currentTerm[receiver] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![receiver] = term]
            /\ votedFor' = [votedFor EXCEPT ![receiver] = None]
            /\ state' = [state EXCEPT ![receiver] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![receiver] = None]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
            /\ electionTimeout' = [electionTimeout EXCEPT ![receiver] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
        ELSE TRUE
       /\ IF (currentTerm[receiver] = term \/ (prevote /\ term = currentTerm[receiver] + 1)) /\ 
          (LET lastLogIndexRcv == Len(log[receiver]), lastLogTermRcv == IF lastLogIndexRcv > 0 THEN log[receiver][lastLogIndexRcv] ELSE 0 IN
           lastLogTerm > lastLogTermRcv \/ (lastLogTerm = lastLogTermRcv /\ lastLogIndex >= lastLogIndexRcv)) /\
          (prevote \/ votedFor[receiver] = None \/ votedFor[receiver] = candidateId) THEN
            /\ IF prevote THEN 
                 msgs' = msgs \ {msg} \cup { ["RequestVoteResponse", receiver, sender, currentTerm[receiver], TRUE, term, prevote] }
               ELSE
                 votedFor' = [voted极 EXCEPT ![receiver] = candidateId]
                 /\ msgs' = msgs \ {msg} \cup { ["RequestVoteResponse", receiver, sender, currentTerm[receiver], TRUE, term, prevote] }
        ELSE
            msgs' = msgs \ {msg} \cup { ["RequestVoteResponse", receiver, sender, currentTerm[receiver], FALSE, term, prevote] }
       /\ UNCHANGED <<clusterNodes, log, commitIndex, snapshotLastIndex, snapshotLastTerm, msgId, nextIndex, matchIndex>>

ReceiveRequestVoteResponse(msg) == 
    /\ msg \in msgs
    /\ msg[1] = "RequestVoteResponse"
    /\ LET sender == msg[2], receiver == msg[3], term == msg[4], voteGranted == msg[5], requestTerm == msg[6], prevote == msg[7] IN
       receiver \in clusterNodes
       /\ IF term > currentTerm[receiver] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![receiver] = term]
            /\ votedFor' = [votedFor EXCEPT ![receiver] = None]
            /\ state' = [state EXCEPT ![receiver] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![receiver] = None]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
            /\ electionTimeout' = [electionTimeout EXCEPT ![receiver] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
        ELSE TRUE
       /\ IF prevote THEN
            /\ state[receiver] = "PreCandidate" /\ requestTerm = currentTerm[receiver] + 1
            /\ IF voteGranted THEN
                 \* update votes, check majority
                 LET votes == { n \in clusterNodes : votedFor[n] = receiver } IN
                 IF Cardinality(votes) > Cardinality(clusterNodes) / 2 THEN
                     state' = [state EXCEPT ![receiver] = "Candidate"]
                     /\ currentTerm' = [currentTerm EXCEPT ![receiver] = currentTerm[receiver] + 1]
                     /\ votedFor' = [votedFor EXCEPT ![receiver] = receiver]
                     /\ leaderId' = [leaderId EXCEPT ![receiver] = None]
                     /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
                     /\ electionTimeout' = [electionTimeout EXCEPT ![receiver] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
                     /\ msgs' = msgs \ {msg} \cup { ["RequestVote", receiver, other, currentTerm[receiver] + 1, receiver, Len(log[receiver]), IF Len(log[receiver]) > 0 THEN log[receiver][Len(log[receiver])] ELSE 0, FALSE] : other \in clusterNodes \ {receiver} }
                 ELSE UNCHANGED <<state, currentTerm, votedFor, leaderId, timeoutElapsed, electionTimeout, msgs>>
            ELSE UNCHANGED <<state, currentTerm, votedFor, leaderId, timeoutElapsed, electionTimeout, msgs>>
        ELSE
            /\ state[receiver] = "Candidate" /\ requestTerm = currentTerm[receiver]
            /\ IF voteGranted THEN
                 \* update votes, check majority
                 LET votes == { n \in clusterNodes : votedFor[n] = receiver } IN
                 IF Cardinality(votes) > Cardinality(clusterNodes) / 2 THEN
                     state' = [state EXCEPT ![receiver] = "Leader"]
                     /\ leaderId' = [leaderId EXCEPT ![receiver] = receiver]
                     /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
                     /\ nextIndex' = [nextIndex EXCEPT ![receiver] = [m \in Node |-> IF m = receiver THEN nextIndex[receiver][m] ELSE Len(log[receiver]) + 1]]
                     /\ matchIndex' = [matchIndex EXCEPT ![receiver] = [m \in Node |-> IF m = receiver THEN matchIndex[receiver][m] ELSE 0]]
                     /\ msgs' = msgs \ {msg} \cup { ["AppendEntries", receiver, other, currentTerm[receiver], receiver, Len(log[receiver]), IF Len(log[receiver]) > 0 THEN log[receiver][Len(log[receiver])] ELSE 0, <<>>, commitIndex[receiver]] : other \in clusterNodes \ {receiver} }
                 ELSE UNCHANGED <<state, leaderId, timeoutElapsed, nextIndex, matchIndex, msgs>>
            ELSE UNCHANGED <<state, leaderId, timeoutElapsed, nextIndex, matchIndex, msgs>>
       /\ UNCHANGED <<clusterNodes, log, commitIndex, snapshotLastIndex, snapshotLastTerm, msgId>>

SendAppendEntries(leader, follower) == 
    /\ state[leader] = "Leader"
    /\ follower \in clusterNodes
    /\ follower /= leader
    /\ LET nextIdx == nextIndex[leader][follower] IN
       nextIdx <= Len(log[leader]) + 1
    /\ LET prevLogIndex == nextIdx - 1 IN
       LET prevLogTerm == IF prevLogIndex > 0 THEN log[leader][prevLogIndex] ELSE 0 IN
    /\ LET entries == SubSeq(log[leader], nextIdx, Len(log[leader])) IN
    /\ leaderCommit = commitIndex[leader]
    /\ msgId' = [msgId EXCEPT ![leader] = msgId[leader] + 1]
    /\ msgs' = msgs \cup { ["AppendEntries", leader, follower, currentTerm[leader], leader, prevLogIndex, prevLogTerm, entries, leaderCommit] }
    /\ UNCHANGED <<clusterNodes, state, currentTerm, votedFor, log, commitIndex, leaderId, snapshotLastIndex, snapshotLastTerm, timeoutElapsed, electionTimeout, nextIndex, matchIndex>>

ReceiveAppendEntries(msg) == 
    /\ msg \in msgs
    /\ msg[极] = "AppendEntries"
    /\ LET sender == msg[2], receiver == msg[3], term == msg[4], leaderIdMsg == msg[5], prevLogIndex == msg[6], prevLogTerm == msg[7], entries == msg[8], leaderCommit == msg[9] IN
       receiver \in clusterNodes
       /\ IF term > currentTerm[receiver] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![receiver] = term]
            /\ votedFor' = [votedFor EXCEPT ![receiver] = None]
            /\ state' = [state EXCEPT ![receiver] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![receiver] = leaderIdMsg]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
            /\ electionTimeout' = [electionTimeout EXCEPT ![receiver极 = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
        ELSE TRUE
       /\ IF term < currentTerm[receiver] THEN
            msgs' = msgs \ {msg} \cup { ["AppendEntriesResponse", receiver, sender, currentTerm[receiver], FALSE, Len(log[receiver]), msgId[receiver]] }
        ELSE
            /\ leaderId' = [leaderId EXCEPT ![receiver] = leaderIdMsg]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
            /\ IF prevLogIndex > Len(log[receiver]) \/ (prevLogIndex > 0 /\ prevLogIndex <= Len(log[receiver]) /\ log[receiver][prevLogIndex] /= prevLogTerm) THEN
                 msgs' = msgs \ {msg} \cup { ["AppendEntriesResponse", receiver, sender, currentTerm[receiver], FALSE, Len(log[receiver]), msgId[receiver]] }
            ELSE
                 \* delete conflicting entries and append new ones
                 LET newLog == IF prevLogIndex < Len(log[receiver]) THEN SubSeq(log[receiver], 1, prevLogIndex) \o entries ELSE log[receiver] \o entries IN
                 log' = [log EXCEPT ![receiver] = newLog]
                 /\ IF leaderCommit > commitIndex[receiver] THEN
                      commitIndex' = [commitIndex EXCEPT ![receiver] = Min(leaderCommit, Len(newLog))]
                   ELSE TRUE
                 /\ msgs' = msgs \ {msg} \cup { ["AppendEntriesResponse", receiver, sender, currentTerm[receiver], TRUE, Len(newLog), msg极[receiver]] }
       /\ UNCHANGED <<clusterNodes, electionTimeout, msgId, nextIndex, matchIndex>>

ReceiveAppendEntriesResponse(msg) == 
    /\ msg \in msgs
    /\ msg[1] = "AppendEntriesResponse"
    /\ LET sender == msg[2], receiver == msg[3], term == msg[4], success == msg[5], currentIdx == msg[6], msgIdResp == msg[7] IN
       receiver \in clusterNodes /\ state[receiver] = "Leader"
       /\ IF term > currentTerm[receiver] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![receiver] = term]
            /\ votedFor' = [votedFor EXCEPT ![receiver] = None]
            /\ state' = [state EXCEPT ![receiver] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![receiver] = None]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![receiver] = 0]
            /\ electionTimeout' = [electionTimeout EXCEPT ![receiver] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
        ELSE TRUE
       /\ IF success THEN
            /\ nextIndex' = [nextIndex EXCEPT ![receiver][sender] = currentIdx + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![receiver][sender] = currentIdx]
            /\ \* update commit index
            LET matchIndices == { matchIndex[receiver][n] : n \in clusterNodes } IN
            LET sorted == Sort(matchIndices) IN
            LET N == sorted[Cardinality(clusterNodes) \div 2 + 1] IN
            IF N > commitIndex[receiver] /\ log[receiver][N] = currentTerm[receiver] THEN
                 commitIndex' = [commitIndex EXCEPT ![receiver] = N]
            ELSE TRUE
        ELSE
            nextIndex' = [nextIndex EXCEPT ![receiver][sender] = Max(1, nextIndex[receiver][sender] - 1)]
       /\ msgs' = msgs \ {msg}
       /\ UNCHANGED <<clusterNodes, votedFor, log, leaderId, snapshotLastIndex, snapshotLastTerm, timeoutElapsed, electionTimeout>>

Periodic(node) == 
    /\ node \in clusterNodes
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = timeoutElapsed[node] + 1]
    /\ IF state[node] \in {"Follower", "Candidate"} /\ timeoutElapsed[node] + 1 >= electionTimeout[node] THEN
         IF state[node] = "Follower" THEN
             state' = [state EXCEPT ![node] = "PreCandidate"]
             /\ leaderId' = [leaderId EXCEPT ![node] = None]
             /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
             /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
             /\ msgs' = msgs \cup { ["RequestVote", node, other, currentTerm[node] + 1, node极 Len(log[node]), IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, TRUE] : other \in clusterNodes \ {node} }
         ELSE
             currentTerm' = [currentTerm EXCEPT ![node] = currentTerm[node] + 1]
             /\ votedFor' = [votedFor EXCEPT ![node] = node]
             /\ state' = [state EXCEPT ![node] = "Candidate"]
             /\ leaderId' = [leaderId EXCEPT ![node] = None]
             /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
             /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
             /\ msgs' =极 msgs \cup { ["RequestVote", node, other, currentTerm[node] + 1, node, Len(log[node]), IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, FALSE] : other \in clusterNodes \ {node} }
         ELSE TRUE
    /\ IF state[node] = "Leader" /\ timeoutElapsed[node] + 1 >= RequestTimeout THEN
         timeoutElapsed' = [timeoutElapsed EXCEPT ![node] = 0]
         /\ msgs' = msgs \cup { ["AppendEntries", node, other, currentTerm[node], node, Len(log[node]), IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, <<>>, commitIndex[node]] : other \in clusterNodes \ {node} }
    ELSE TRUE
    /\ UNCHANGED <<clusterNodes, currentTerm, votedFor, log, commitIndex, snapshotLastIndex, snapshotLastTerm, msgId, nextIndex, matchIndex>>

LogAppend(leader, entryTerm) == 
    /\ state[leader] = "Leader"
    /\ entryTerm <= currentTerm[leader]
    /\ log' = [log EXCEPT ![leader] = Append(log[leader], entryTerm)]
    /\ UNCHANGED <<clusterNodes, state, currentTerm, votedFor, commitIndex, leaderId, snapshotLastIndex, snapshotLastTerm, timeoutElapsed, electionTimeout, msgId, nextIndex, matchIndex, msgs>>

AddNode(newNode) == 
    /\ newNode \in Node \ clusterNodes
    /\ clusterNodes' = clusterNodes \cup {newNode}
    /\ state' = [state EXCEPT ![newNode] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![newNode] = 0]
    /\ votedFor' = [votedFor EXCEPT ![newNode] = None]
    /\ log' = [log EXCEPT ![newNode] = <<>>]
    /\ commitIndex' = [commitIndex EXCEPT ![newNode] = 0]
    /\ leaderId' = [leaderId EXCEPT ![newNode] = None]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![newNode] = 0]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![newNode] = 0]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![newNode] = 0]
    /\ electionTimeout' = [electionTimeout EXCEPT ![newNode] = CHOOSE et \in ElectionTimeoutMin .. ElectionTimeoutMax : TRUE]
    /\ msgId' = [msgId EXCEPT ![newNode] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![newNode] = [m \in Node |-> 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![newNode] = [m \in Node |-> 0]]
    /\ UNCHANGED msgs

RemoveNode(nodeToRemove) == 
    /\ nodeToRemove \in clusterNodes
    /\ clusterNodes' = clusterNodes \ {nodeToRemove}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId, snapshotLastIndex, snapshotLastTerm, timeoutElapsed, electionTimeout, msgId, nextIndex, matchIndex, msgs>>

Next == 
    \/ \E node \in Node : BecomeFollower(node)
    \/ \E node \in Node : BecomeCandidate(node)
    \/ \E node \in Node : BecomePreCandidate(node)
    \/ \E node \in Node : BecomeLeader(node)
    \/ \E msg \in msgs : ReceiveRequestVote(msg)
    \/ \E msg \in msgs : ReceiveRequestVoteResponse(msg)
    \/ \E msg \in msgs : ReceiveAppendEntries(msg)
    \/ \E msg \in msgs : ReceiveAppendEntriesResponse(msg)
    \/ \E node \in Node : Periodic(node)
    \/ \E leader \in Node, follower \in Node : SendAppendEntries(leader, follower)
    \/ \E leader \in Node, entryTerm \in Nat : LogAppend(leader, entryTerm)
    \/ \E newNode \in Node \ clusterNodes : AddNode(newNode)
    \/ \E nodeToRemove \极 clusterNodes : RemoveNode(nodeToRemove)

Spec == Init /\ [][Next]_vars
====