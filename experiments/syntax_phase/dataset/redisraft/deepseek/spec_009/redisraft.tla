---- MODULE redisraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS AllNodes, None, InitialNodes
ASSUME InitialNodes \subseteq AllNodes
ASSUME None \notin AllNodes
NodeID == AllNodes \cup {None}
StateType == {"Follower", "PreCandidate", "Candidate", "Leader"}
VARIABLES inCluster, state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs
vars == <<inCluster, state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
Init == 
    /\ inCluster = [n \in AllNodes |-> n \in InitialNodes]
    /\ state = [n \in AllNodes |-> "Follower"]
    /\ currentTerm = [n \in AllNodes |-> 0]
    /\ votedFor = [n \in AllNodes |-> None]
    /\ commitIndex = [n \in AllNodes |-> 0]
    /\ log = [n \in AllNodes |-> <<>>]
    /\ leaderId = [n \in AllNodes |-> None]
    /\ isVoting = [n \in AllNodes |-> n \in InitialNodes]
    /\ rvMsgs = {}
    /\ rvRespMsgs = {}
    /\ aeMsgs = {}
    /\ aeRespMsgs = {}
BecomeFollower(node, newTerm) ==
    /\ newTerm >= currentTerm[node]
    /\ state' = [state EXCEPT ![node] = "Follower"]
    /\ IF newTerm > currentTerm[node] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![node] = newTerm]
           /\ votedFor' = [votedFor EXCEPT ![node] = None]
       ELSE TRUE
    /\ leaderId' = [leaderId EXCEPT ![node] = None]
    /\ UNCHANGED <<inCluster, commitIndex, log, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
BecomePreCandidate(node) ==
    /\ state[node] \neq "PreCandidate"
    /\ state' = [state EXCEPT ![node] = "PreCandidate"]
    /\ leaderId' = [leaderId EXCEPT ![node] = None]
    /\ LET votingNodes = {n \in AllNodes : inCluster[n] /\ n \neq node /\ isVoting[n]}
       IN rvMsgs' = rvMsgs \cup { [sender |-> node, receiver |-> n, term |-> currentTerm[node] + 1, candidateId |-> node, lastLogIndex |-> Len(log[node]), lastLogTerm |-> IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, prevote |-> TRUE] : n \in votingNodes }
    /\ UNCHANGED <<inCluster, currentTerm, votedFor, commitIndex, log, isVoting, rvRespMsgs, aeMsgs, aeRespMsgs>>
BecomeCandidate(node) ==
    /\ state[node] \neq "Candidate"
    /\ currentTerm' = [currentTerm EXCEPT ![node] = currentTerm[node] + 1]
    /\ votedFor' = [votedFor EXCEPT ![node] = node]
    /\ state' = [state EXCEPT ![node] = "Candidate"]
    /\ leaderId' = [leaderId EXCEPT ![node] = None]
    /\ LET votingNodes = {n \in AllNodes : inCluster[n] /\ n \neq node /\ isVoting[n]}
       IN rvMsgs' = rvMsgs \cup { [sender |-> node, receiver |-> n, term |-> currentTerm[node] + 1, candidateId |-> node, lastLogIndex |-> Len(log[node]), lastLogTerm |-> IF Len(log[node]) > 0 THEN log[node][Len(log[node])] ELSE 0, prevote |-> FALSE] : n \in votingNodes }
    /\ UNCHANGED <<inCluster, commitIndex, log, isVoting, rvRespMsgs, aeMsgs, aeRespMsgs>>
BecomeLeader(node) ==
    /\ state[node] = "Candidate"
    /\ state' = [state EXCEPT ![node] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![node] = node]
    /\ log' = [log EXCEPT ![node] = Append(log[node], currentTerm[node])]
    /\ commitIndex' = [commitIndex EXCEPT ![node] = IF Cardinality({n \in AllNodes : inCluster[n] /\ isVoting[n]}) = 1 THEN Len(log[node]) ELSE commitIndex[node]]
    /\ LET followers = {n \in AllNodes : inCluster[n] /\ n \neq node}
       IN aeMsgs' = aeMsgs \cup { [sender |-> node, receiver |-> n, term |-> currentTerm[node], leaderId |-> node, prevLogIndex |-> IF Len(log[node]) > 0 THEN Len(log[node]) - 1 ELSE 0, prevLogTerm |-> IF Len(log[node]) > 0 THEN log[node][Len(log[node]) - 1] ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[node]] : n \in followers }
    /\ UNCHANGED <<inCluster, currentTerm, votedFor, isVoting, rvMsgs, rvRespMsgs, aeRespMsgs>>
RecvRequestVote(msg) ==
    /\ msg \in rvMsgs
    /\ inCluster[msg["receiver"]]
    /\ IF msg["term"] < currentTerm[msg["receiver"]] THEN
           rvRespMsgs' = rvRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], voteGranted |-> FALSE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]] }
           /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting>>
       ELSE
           IF msg["term"] > currentTerm[msg["receiver"]] THEN
               /\ currentTerm' = [currentTerm EXCEPT ![msg["receiver"]] = msg["term"]]
               /\ votedFor' = [votedFor EXCEPT ![msg["receiver"]] = None]
               /\ state' = [state EXCEPT ![msg["receiver"]] = "Follower"]
               /\ leaderId' = [leaderId EXCEPT ![msg["receiver"]] = None]
               /\ LET lastLogIndex = Len(log[msg["receiver"]])
                  lastLogTerm = IF lastLogIndex > 0 THEN log[msg["receiver"]][lastLogIndex] ELSE 0
                  IN
                  IF msg["lastLogTerm"] > lastLogTerm \/ (msg["lastLogTerm"] = lastLogTerm /\ msg["lastLogIndex"] >= lastLogIndex) THEN
                     /\ IF NOT msg["prevote"] THEN
                            votedFor' = [votedFor EXCEPT ![msg["receiver"]] = msg["candidateId"]]
                        ELSE TRUE
                     /\ rvRespMsgs' = rvRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], voteGranted |-> TRUE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]] }
                  ELSE
                     rvRespMsgs' = rvRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], voteGranted |-> FALSE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]] }
           ELSE
               /\ IF votedFor[msg["receiver"]] = None \/ votedFor[msg["receiver"]] = msg["candidateId"] THEN
                      LET lastLogIndex = Len(log[msg["receiver"]])
                         lastLogTerm = IF lastLogIndex > 0 THEN log[msg["receiver"]][lastLogIndex] ELSE 0
                         IN
                         IF msg["lastLogTerm"] > lastLogTerm \/ (msg["lastLogTerm"] = lastLogTerm /\ msg["lastLogIndex"] >= lastLogIndex) THEN
                            /\ IF NOT msg["prevote"] THEN
                                   votedFor' = [votedFor EXCEPT ![msg["receiver"]] = msg["candidateId"]]
                               ELSE TRUE
                            /\ rvRespMsgs' = rvRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], voteGranted |-> TRUE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]] }
                         ELSE
                            rvRespMsgs' = rvRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], voteGranted |-> FALSE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]] }
               ELSE
                   rvRespMsgs' = rvRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], voteGranted |-> FALSE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]] }
    /\ rvMsgs' = rvMsgs \ {msg}
    /\ UNCHANGED <<inCluster, commitIndex, log, isVoting, aeMsgs, aeRespMsgs>>
RecvRequestVoteResponse(msg) ==
    /\ msg \in rvRespMsgs
    /\ inCluster[msg["receiver"]]
    /\ IF msg["term"] > currentTerm[msg["receiver"]] THEN
           /\ BecomeFollower(msg["receiver"], msg["term"])
           /\ UNCHANGED <<rvRespMsgs>>
       ELSE
           /\ IF msg["prevote"] THEN
                  /\ state[msg["receiver"]] = "PreCandidate"
                  /\ msg["requestTerm"] = currentTerm[msg["receiver"]] + 1
              ELSE
                  /\ state[msg["receiver"]] = "Candidate"
                  /\ msg["requestTerm"] = currentTerm[msg["receiver"]]
           /\ IF msg["voteGranted"] THEN
                  /\ LET node = msg["receiver"]
                     votes = Cardinality({n \in AllNodes : inCluster[n] /\ isVoting[n] /\ (n = node \/ \E resp \in rvRespMsgs : resp["sender"] = n /\ resp["receiver"] = node /\ resp["voteGranted"] /\ resp["requestTerm"] = currentTerm[node] + IF msg["prevote"] THEN 1 ELSE 0)})
                     IN
                     IF votes > Cardinality({n \in AllNodes : inCluster[n] /\ isVoting[n]}) / 2 THEN
                         IF msg["prevote"] THEN BecomeCandidate(node) ELSE BecomeLeader(node)
                     ELSE UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, leaderId>>
           ELSE UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, leaderId>>
    /\ rvRespMsgs' = rvRespMsgs \ {msg}
    /\ UNCHANGED <<inCluster, isVoting, rvMsgs, aeMsgs, aeRespMsgs>>
SendAppendEntries(node, follower) ==
    /\ state[node] = "Leader"
    /\ inCluster[follower]
    /\ follower \neq node
    /\ LET nextIndex = CHOOSE i \in 1..Len(log[node]) + 1 : TRUE
       prevLogIndex = nextIndex - 1
       prevLogTerm = IF prevLogIndex > 0 THEN log[node][prevLogIndex] ELSE 0
       entries = SubSeq(log[node], nextIndex, Len(log[node]))
       IN
       aeMsgs' = aeMsgs \cup { [sender |-> node, receiver |-> follower, term |-> currentTerm[node], leaderId |-> node, prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm, entries |-> entries, leaderCommit |-> commitIndex[node]] }
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeRespMsgs>>
RecvAppendEntries(msg) ==
    /\ msg \in aeMsgs
    /\ inCluster[msg["receiver"]]
    /\ IF msg["term"] < currentTerm[msg["receiver"]] THEN
           aeRespMsgs' = aeRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], success |-> FALSE, currentIdx |-> Len(log[msg["receiver"]])] }
           /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting>>
       ELSE
           IF msg["term"] > currentTerm[msg["receiver"]] THEN
               /\ BecomeFollower(msg["receiver"], msg["term"])
               /\ IF msg["prevLogIndex"] = 0 \/ (msg["prevLogIndex"] <= Len(log[msg["receiver"]]) /\ log[msg["receiver"]][msg["prevLogIndex"]] = msg["prevLogTerm"]) THEN
                      /\ log' = [log EXCEPT ![msg["receiver"]] = IF Len(msg["entries"]) > 0 THEN SubSeq(log[msg["receiver"]], 1, msg["prevLogIndex"]) \o msg["entries"] ELSE log[msg["receiver"]]]
                      /\ commitIndex' = [commitIndex EXCEPT ![msg["receiver"]] = Min(msg["leaderCommit"], Len(log[msg["receiver"]]))]
                      /\ aeRespMsgs' = aeRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], success |-> TRUE, currentIdx |-> Len(log[msg["receiver"]])] }
               ELSE
                  aeRespMsgs' = aeRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], success |-> FALSE, currentIdx |-> Len(log[msg["receiver"]])] }
           ELSE
               /\ IF msg["leaderId"] \neq None THEN leaderId' = [leaderId EXCEPT ![msg["receiver"]] = msg["leaderId"]] ELSE UNCHANGED leaderId
               /\ IF msg["prevLogIndex"] = 0 \/ (msg["prevLogIndex"] <= Len(log[msg["receiver"]]) /\ log[msg["receiver"]][msg["prevLogIndex"]] = msg["prevLogTerm"]) THEN
                      /\ log' = [log EXCEPT ![msg["receiver"]] = IF Len(msg["entries"]) > 0 THEN SubSeq(log[msg["receiver"]], 1, msg["prevLogIndex"]) \o msg["entries"] ELSE log[msg["receiver"]]]
                      /\ commitIndex' = [commitIndex EXCEPT ![msg["receiver"]] = Min(msg["leaderCommit"], Len(log[msg["receiver"]]))]
                      /\ aeRespMsgs' = aeRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], success |-> TRUE, currentIdx |-> Len(log[msg["receiver"]])] }
               ELSE
                  aeRespMsgs' = aeRespMsgs \cup { [sender |-> msg["receiver"], receiver |-> msg["sender"], term |-> currentTerm[msg["receiver"]], success |-> FALSE, currentIdx |-> Len(log[msg["receiver"]])] }
    /\ aeMsgs' = aeMsgs \ {msg}
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, isVoting, rvMsgs, rvRespMsgs>>
RecvAppendEntriesResponse(msg) ==
    /\ msg \in aeRespMsgs
    /\ inCluster[msg["receiver"]]
    /\ state[msg["receiver"]] = "Leader"
    /\ IF msg["term"] > currentTerm[msg["receiver"]] THEN
           /\ BecomeFollower(msg["receiver"], msg["term"])
           /\ UNCHANGED <<aeRespMsgs>>
       ELSE
           /\ IF msg["success"] THEN
                  /\ LET matchIndex = msg["currentIdx"]
                     quorum = Cardinality({n \in AllNodes : inCluster[n] /\ isVoting[n] /\ (n = msg["receiver"] \/ \E resp \in aeRespMsgs : resp["sender"] = n /\ resp["receiver"] = msg["receiver"] /\ resp["success"] /\ resp["currentIdx"] >= matchIndex)})
                     IN
                     IF quorum > Cardinality({n \in AllNodes : inCluster[n] /\ isVoting[n]}) / 2 THEN
                         commitIndex' = [commitIndex EXCEPT ![msg["receiver"]] = matchIndex]
                     ELSE UNCHANGED commitIndex
           ELSE UNCHANGED commitIndex
    /\ aeRespMsgs' = aeRespMsgs \ {msg}
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs>>
ElectionTimeout(node) ==
    /\ inCluster[node]
    /\ state[node] \in {"Follower", "Candidate"}
    /\ \E skip \in BOOLEAN : 
        IF skip THEN BecomeCandidate(node) ELSE BecomePreCandidate(node)
    /\ UNCHANGED <<inCluster, commitIndex, log, isVoting, rvRespMsgs, aeMsgs, aeRespMsgs>>
PeriodicHeartbeat(node) ==
    /\ state[node] = "Leader"
    /\ LET followers = {n \in AllNodes : inCluster[n] /\ n \neq node}
       IN aeMsgs' = aeMsgs \cup { [sender |-> node, receiver |-> n, term |-> currentTerm[node], leaderId |-> node, prevLogIndex |-> IF Len(log[node]) > 0 THEN Len(log[node]) - 1 ELSE 0, prevLogTerm |-> IF Len(log[node]) > 0 THEN log[node][Len(log[node]) - 1] ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[node]] : n \in followers }
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeRespMsgs>>
LogAppend(node, entryTerm) ==
    /\ entryTerm <= currentTerm[node]
    /\ log' = [log EXCEPT ![node] = Append(log[node], entryTerm)]
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, commitIndex, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
LogDelete(node, fromIndex) ==
    /\ fromIndex > commitIndex[node]
    /\ log' = [log EXCEPT ![node] = SubSeq(log[node], 1, fromIndex - 1)]
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, commitIndex, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
LogCommit(node) ==
    /\ LET quorum = CHOOSE q \in 0..Cardinality({n \in AllNodes : inCluster[n] /\ isVoting[n]}) : TRUE
       IN commitIndex' = [commitIndex EXCEPT ![node] = Min(commitIndex[node] + 1, Len(log[node]))]
    /\ UNCHANGED <<inCluster, state, currentTerm, votedFor, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
AddNode(newNode) ==
    /\ newNode \in AllNodes \setminus {n \in AllNodes : inCluster[n]}
    /\ inCluster' = [inCluster EXCEPT ![newNode] = TRUE]
    /\ isVoting' = [isVoting EXCEPT ![newNode] = TRUE]
    /\ state' = [state EXCEPT ![newNode] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![newNode] = 0]
    /\ votedFor' = [votedFor EXCEPT ![newNode] = None]
    /\ commitIndex' = [commitIndex EXCEPT ![newNode] = 0]
    /\ log' = [log EXCEPT ![newNode] = <<>>]
    /\ leaderId' = [leaderId EXCEPT ![newNode] = None]
    /\ UNCHANGED <<rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
RemoveNode(nodeToRemove) ==
    /\ inCluster[nodeToRemove]
    /\ inCluster' = [inCluster EXCEPT ![nodeToRemove] = FALSE]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, log, leaderId, isVoting, rvMsgs, rvRespMsgs, aeMsgs, aeRespMsgs>>
SnapshotBegin(node) ==
    /\ UNCHANGED vars
SnapshotEnd(node) ==
    /\ UNCHANGED vars
ApplyConfigChange(node) ==
    /\ UNCHANGED vars
Next == 
    \/ \E node \in AllNodes, newTerm \in Nat : BecomeFollower(node, newTerm)
    \/ \E node \in AllNodes : BecomePreCandidate(node)
    \/ \E node \in AllNodes : BecomeCandidate(node)
    \/ \E node \in AllNodes : BecomeLeader(node)
    \/ \E msg \in rvMsgs : RecvRequestVote(msg)
    \/ \E msg \in rvRespMsgs : RecvRequestVoteResponse(msg)
    \/ \E node, follower \in AllNodes : SendAppendEntries(node, follower)
    \/ \E msg \in aeMsgs : RecvAppendEntries(msg)
    \/ \E msg \in aeRespMsgs : RecvAppendEntriesResponse(msg)
    \/ \E node \in AllNodes : ElectionTimeout(node)
    \/ \E node \in AllNodes : PeriodicHeartbeat(node)
    \/ \E node \in AllNodes, entryTerm \in Nat : LogAppend(node, entryTerm)
    \/ \E node \in AllNodes, fromIndex \in Nat : LogDelete(node, fromIndex)
    \/ \E node \in AllNodes : LogCommit(node)
    \/ \E newNode \in AllNodes : AddNode(newNode)
    \/ \E nodeToRemove \in AllNodes : RemoveNode(nodeToRemove)
    \/ \E node \in AllNodes : SnapshotBegin(node)
    \/ \E node \in AllNodes : SnapshotEnd(node)
    \/ \E node \in AllNodes : ApplyConfigChange(node)
Spec == Init /\ [][Next]_vars
====