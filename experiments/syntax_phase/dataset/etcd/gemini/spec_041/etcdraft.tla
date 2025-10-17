---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Nodes, Value, Nil
ASSUME IsFiniteSet(Nodes)
ASSUME Nil \notin Nodes
ASSUME Cardinality(Nodes) % 2 = 1
ASSUME Nil \notin Value

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    votesGranted,
    electionTimer,
    heartbeatTimer,
    network,
    nextIndex,
    matchIndex

vars == <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
          electionTimer, heartbeatTimer, network, nextIndex, matchIndex>>

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}

ElectionTimeoutMin == 10
ElectionTimeoutMax == 20
HeartbeatTimeout == 2

Quorum == Cardinality(Nodes) \div 2 + 1

LastIndex(lg) == Len(lg)
LastTerm(lg) == IF Len(lg) > 0 THEN lg[Len(lg)]["term"] ELSE 0
IsUpToDate(candidateLogTerm, candidateLogIndex, myLog) ==
    LET myLastTerm == LastTerm(myLog) IN
    LET myLastIndex == LastIndex(myLog) IN
    \/ candidateLogTerm > myLastTerm
    \/ (candidateLogTerm = myLastTerm /\ candidateLogIndex >= myLastIndex)

Init ==
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ leader = Nil
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ electionTimer = [n \in Nodes |-> CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax: TRUE]
    /\ heartbeatTimer = [n \in Nodes |-> 0]
    /\ network = EmptyBag
    /\ nextIndex = [n \in Nodes |-> [p \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [p \in Nodes |-> 0]]

Tick ==
    /\ electionTimer' = [n \in Nodes |-> IF state[n] \in {"Follower", "PreCandidate", "Candidate"} THEN electionTimer[n] - 1 ELSE electionTimer[n]]
    /\ heartbeatTimer' = [n \in Nodes |-> IF state[n] = "Leader" THEN heartbeatTimer[n] - 1 ELSE heartbeatTimer[n]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, network, nextIndex, matchIndex>>

TimeoutStartElection(i) ==
    /\ state[i] \in {"Follower", "PreCandidate"}
    /\ electionTimer[i] <= 0
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax: TRUE]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ network' = network (+) Bagify({[type |-> "MsgPreVote", from |-> i, to |-> j, term |-> currentTerm[i] + 1,
                                      logTerm |-> LastTerm(log[i]), index |-> LastIndex(log[i])] : j \in Nodes \ {i}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader, heartbeatTimer, nextIndex, matchIndex>>

TimeoutSendHeartbeat(i) ==
    /\ state[i] = "Leader"
    /\ heartbeatTimer[i] <= 0
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = HeartbeatTimeout]
    /\ network' = network (+) Bagify({[type |-> "MsgHeartbeat", from |-> i, to |-> j, term |-> currentTerm[i],
                                      leaderCommit |-> commitIndex[i]] : j \in Nodes \ {i}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, nextIndex, matchIndex>>

ClientRequest(val) ==
    /\ leader /= Nil
    /\ LET i == leader
           newEntry == [term |-> currentTerm[i], value |-> val]
           oldLog == log[i]
       IN
       /\ log' = [log EXCEPT ![i] = Append(oldLog, newEntry)]
       /\ network' = network (+) Bagify({[type |-> "MsgApp", from |-> i, to |-> j, term |-> currentTerm[i],
                                          prevLogIndex |-> LastIndex(oldLog), prevLogTerm |-> LastTerm(oldLog),
                                          entries |-> <<newEntry>>,
                                          leaderCommit |-> commitIndex[i]] : j \in Nodes \ {i}})
       /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>

Step(i) ==
    \E msg \in BagToSet(network):
        /\ msg["to"] = i
        /\ LET from == msg["from"] IN
        /\ \/ /\ msg["term"] > currentTerm[i]
              /\ \/ /\ msg["type"] = "MsgPreVoteResp" /\ \neg msg["reject"] /\ state[i] = "PreCandidate" /\ msg["term"] = currentTerm[i] + 1
                    /\ LET temp_votesGranted == votesGranted[i] \cup {from} IN
                    /\ IF Cardinality(temp_votesGranted) >= Quorum THEN
                        \* Become Candidate
                        /\ state' = [state EXCEPT ![i] = "Candidate"]
                        /\ currentTerm' = [currentTerm EXCEPT ![i] = msg["term"]]
                        /\ votedFor' = [votedFor EXCEPT ![i] = i]
                        /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
                        /\ electionTimer' = [electionTimer EXCEPT ![i] = CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax: TRUE]
                        /\ network' = (network (-) [msg]) (+) Bagify({[type |-> "MsgVote", from |-> i, to |-> j, term |-> msg["term"],
                                                          logTerm |-> LastTerm(log[i]), index |-> LastIndex(log[i])] : j \in Nodes \ {i}})
                        /\ UNCHANGED <<log, commitIndex, leader, heartbeatTimer, nextIndex, matchIndex>>
                    ELSE
                        /\ votesGranted' = [votesGranted EXCEPT ![i] = temp_votesGranted]
                        /\ network' = network (-) [msg]
                        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
                 \/ /\ msg["type"] # "MsgPreVote"
                       /\ state' = [state EXCEPT ![i] = "Follower"]
                       /\ currentTerm' = [currentTerm EXCEPT ![i] = msg["term"]]
                       /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                       /\ leader' = IF msg["type"] \in {"MsgApp", "MsgHeartbeat"} THEN from ELSE Nil
                       /\ network' = network (-) [msg]
                       /\ UNCHANGED <<log, commitIndex, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
           \/ /\ msg["term"] < currentTerm[i]
                 /\ network' = network (-) [msg]
                 /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
           \/ /\ msg["term"] = currentTerm[i]
                 /\ LET networkAfterRecv == network (-) [msg] IN
                 /\ CASE msg["type"] = "MsgPreVote" ->
                     /\ LET grant == IsUpToDate(msg["logTerm"], msg["index"], log[i]) IN
                     /\ network' = networkAfterRecv (+) {[type |-> "MsgPreVoteResp", from |-> i, to |-> from, term |-> msg["term"], reject |-> \neg grant]}
                     /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
                 [] msg["type"] = "MsgVote" ->
                     /\ LET grant == (votedFor[i] = Nil \/ votedFor[i] = from) /\ IsUpToDate(msg["logTerm"], msg["index"], log[i]) IN
                     /\ votedFor' = IF grant THEN [votedFor EXCEPT ![i] = from] ELSE votedFor
                     /\ network' = networkAfterRecv (+) {[type |-> "MsgVoteResp", from |-> i, to |-> from, term |-> msg["term"], reject |-> \neg grant]}
                     /\ UNCHANGED <<state, currentTerm, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
                 [] msg["type"] = "MsgVoteResp" /\ state[i] = "Candidate" ->
                     /\ LET temp_votesGranted == IF \neg msg["reject"] THEN votesGranted[i] \cup {from} ELSE votesGranted[i] IN
                     /\ IF Cardinality(temp_votesGranted) >= Quorum THEN
                         \* Become Leader
                         /\ state' = [state EXCEPT ![i] = "Leader"]
                         /\ leader' = i
                         /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = HeartbeatTimeout]
                         /\ LET oldLog == log[i]
                                newEntry == [term |-> currentTerm[i], value |-> "NoOp"]
                            IN
                            /\ log' = [log EXCEPT ![i] = Append(oldLog, newEntry)]
                            /\ nextIndex' = [nextIndex EXCEPT ![i] = [p \in Nodes |-> LastIndex(log'[i]) + 1]]
                            /\ matchIndex' = [matchIndex EXCEPT ![i] = [p \in Nodes |-> 0]]
                            /\ network' = networkAfterRecv (+) Bagify({[type |-> "MsgApp", from |-> i, to |-> j, term |-> currentTerm[i],
                                                                prevLogIndex |-> LastIndex(oldLog), prevLogTerm |-> LastTerm(oldLog),
                                                                entries |-> <<newEntry>>,
                                                                leaderCommit |-> commitIndex[i]] : j \in Nodes \ {i}})
                         /\ UNCHANGED <<currentTerm, votedFor, commitIndex, votesGranted, electionTimer>>
                     ELSE
                         /\ votesGranted' = [votesGranted EXCEPT ![i] = temp_votesGranted]
                         /\ network' = networkAfterRecv
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
                 [] msg["type"] = "MsgApp" ->
                     /\ state' = [state EXCEPT ![i] = "Follower"]
                     /\ leader' = from
                     /\ electionTimer' = [electionTimer EXCEPT ![i] = CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax: TRUE]
                     /\ LET prevLogIndex == msg["prevLogIndex"]
                            prevLogTerm == msg["prevLogTerm"]
                        IN
                        /\ IF prevLogIndex > 0 /\ (prevLogIndex > Len(log[i]) \/ log[i][prevLogIndex]["term"] /= prevLogTerm) THEN
                            /\ network' = networkAfterRecv (+) {[type |-> "MsgAppResp", from |-> i, to |-> from, term |-> currentTerm[i],
                                                                  success |-> FALSE, matchIndex |-> 0]}
                            /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted, heartbeatTimer, nextIndex, matchIndex>>
                        ELSE
                            /\ LET newLog == SubSeq(log[i], 1, prevLogIndex) \o msg["entries"] IN
                            /\ log' = [log EXCEPT ![i] = newLog]
                            /\ commitIndex' = [commitIndex EXCEPT ![i] = commitIndex[i] \max (msg["leaderCommit"] \min LastIndex(newLog))]
                            /\ network' = networkAfterRecv (+) {[type |-> "MsgAppResp", from |-> i, to |-> from, term |-> currentTerm[i],
                                                                  success |-> TRUE, matchIndex |-> LastIndex(newLog)]}
                            /\ UNCHANGED <<currentTerm, votedFor, votesGranted, heartbeatTimer, nextIndex, matchIndex>>
                 [] msg["type"] = "MsgHeartbeat" ->
                     /\ state' = [state EXCEPT ![i] = "Follower"]
                     /\ leader' = from
                     /\ electionTimer' = [electionTimer EXCEPT ![i] = CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax: TRUE]
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = commitIndex[i] \max msg["leaderCommit"]]
                     /\ network' = networkAfterRecv
                     /\ UNCHANGED <<currentTerm, votedFor, log, votesGranted, heartbeatTimer, nextIndex, matchIndex>>
                 [] msg["type"] = "MsgAppResp" /\ state[i] = "Leader" ->
                     /\ IF msg["success"] THEN
                         /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![from] = msg["matchIndex"] + 1]]
                         /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![from] = msg["matchIndex"]]]
                         /\ LET newCommitCand == {idx \in (commitIndex[i] + 1)..Len(log[i]) |
                                                      /\ log[i][idx]["term"] = currentTerm[i]
                                                      /\ Cardinality({p \in Nodes | matchIndex'[i][p] >= idx}) >= Quorum} IN
                         /\ commitIndex' = [commitIndex EXCEPT ![i] = IF newCommitCand = {} THEN commitIndex[i] ELSE Max(newCommitCand)]
                         /\ network' = networkAfterRecv
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, votesGranted, electionTimer, heartbeatTimer>>
                     ELSE
                         /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![from] = 1 \max (nextIndex[i][from] - 1)]]
                         /\ LET prevIdx == nextIndex'[i][from] - 1
                                prevTerm == IF prevIdx > 0 THEN log[i][prevIdx]["term"] ELSE 0
                                entries == SubSeq(log[i], nextIndex'[i][from], Len(log[i]))
                            IN
                            /\ network' = networkAfterRecv (+) {[type |-> "MsgApp", from |-> i, to |-> from, term |-> currentTerm[i],
                                                                  prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                                                                  entries |-> entries, leaderCommit |-> commitIndex[i]]}
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, matchIndex>>
                 [] OTHER ->
                     /\ network' = networkAfterRecv
                     /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>

DropMessage ==
    \E msg \in BagToSet(network):
        /\ network' = network (-) [msg]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer, nextIndex, matchIndex>>

Next ==
    \/ Tick
    \/ \E i \in Nodes: TimeoutStartElection(i)
    \/ \E i \in Nodes: TimeoutSendHeartbeat(i)
    \/ \E v \in Value: ClientRequest(v)
    \/ \E i \in Nodes: Step(i)
    \/ DropMessage

Spec == Init /\ [][Next]_vars

====
```