---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS 
    Nodes,
    MaxTerm,
    MaxLogLen,
    NONE

VARIABLES
    currentTerm,
    votedFor,
    state,
    leaderId,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votes,
    timeoutElapsed,
    electionTimeout,
    votingConfigChangeIndex,
    nodes,
    snapshotLastIndex,
    snapshotLastTerm

vars == <<currentTerm, votedFor, state, leaderId, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout, 
          votingConfigChangeIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
Terms == 0..MaxTerm
Indices == 0..MaxLogLen
LogEntries == [term: Terms, type: {"NORMAL", "CONFIG_ADD", "CONFIG_REMOVE", "NOOP"}]

TypeOK ==
    /\ currentTerm \in [Nodes -> Terms]
    /\ votedFor \in [Nodes -> Nodes \cup {NONE}]
    /\ state \in [Nodes -> NodeStates]
    /\ leaderId \in [Nodes -> Nodes \cup {NONE}]
    /\ log \in [Nodes -> Seq(LogEntries)]
    /\ commitIndex \in [Nodes -> Indices]
    /\ lastApplied \in [Nodes -> Indices]
    /\ nextIndex \in [Nodes -> [Nodes -> Indices]]
    /\ matchIndex \in [Nodes -> [Nodes -> Indices]]
    /\ votes \in [Nodes -> SUBSET Nodes]
    /\ timeoutElapsed \in [Nodes -> Nat]
    /\ electionTimeout \in [Nodes -> Nat]
    /\ votingConfigChangeIndex \in [Nodes -> Int]
    /\ nodes \in [Nodes -> SUBSET Nodes]
    /\ snapshotLastIndex \in [Nodes -> Indices]
    /\ snapshotLastTerm \in [Nodes -> Terms]

Init ==
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> NONE]
    /\ state = [n \in Nodes |-> "FOLLOWER"]
    /\ leaderId = [n \in Nodes |-> NONE]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votes = [n \in Nodes |-> {}]
    /\ timeoutElapsed = [n \in Nodes |-> 0]
    /\ electionTimeout = [n \in Nodes |-> 5]
    /\ votingConfigChangeIndex = [n \in Nodes |-> -1]
    /\ nodes = [n \in Nodes |-> Nodes]
    /\ snapshotLastIndex = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]

BecomeFollower(n) ==
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in {3, 4, 5, 6, 7} : TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, 
                   nextIndex, matchIndex, votes, votingConfigChangeIndex, 
                   nodes, snapshotLastIndex, snapshotLastTerm>>

BecomePreCandidate(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votes' = [votes EXCEPT ![n] = {}]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, votingConfigChangeIndex,
                   nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ currentTerm[n] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   electionTimeout, votingConfigChangeIndex, nodes,
                   snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ Cardinality(votes[n]) * 2 > Cardinality(nodes[n])
    /\ Len(log[n]) < MaxLogLen
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "NOOP"])]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log'[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN Len(log'[n]) ELSE 0]]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votes,
                   electionTimeout, votingConfigChangeIndex, nodes,
                   snapshotLastIndex, snapshotLastTerm>>

ElectionStart(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ timeoutElapsed[n] >= electionTimeout[n]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in {3, 4, 5, 6, 7} : TRUE]
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votes' = [votes EXCEPT ![n] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, votingConfigChangeIndex, nodes,
                   snapshotLastIndex, snapshotLastTerm>>

ElectionTimeout(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ timeoutElapsed[n] >= electionTimeout[n]
    /\ ElectionStart(n)

RecvRequestVote(n, m, term, lastLogIndex, lastLogTerm, prevote) ==
    /\ m \in nodes[n]
    /\ m # n
    /\ LET termUpdated == term > currentTerm[n]
           logOk == \/ Len(log[n]) = 0
                    \/ lastLogTerm > log[n][Len(log[n])].term
                    \/ /\ lastLogTerm = log[n][Len(log[n])].term
                       /\ lastLogIndex >= Len(log[n])
           voteOk == \/ term > currentTerm[n]
                     \/ /\ term = currentTerm[n]
                        /\ votedFor[n] \in {NONE, m}
       IN /\ IF termUpdated
             THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
                  /\ votedFor' = [votedFor EXCEPT ![n] = NONE]
                  /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                  /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
                  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                  /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in {3, 4, 5, 6, 7} : TRUE]
             ELSE /\ UNCHANGED <<currentTerm, state, leaderId, timeoutElapsed, electionTimeout>>
                  /\ votedFor' = votedFor
          /\ LET newVotedFor == IF /\ term >= currentTerm'[n]
                                   /\ voteOk
                                   /\ logOk
                                THEN IF ~prevote
                                     THEN [votedFor' EXCEPT ![n] = m]
                                     ELSE votedFor'
                                ELSE votedFor'
             IN votedFor' = newVotedFor
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votes,
                         votingConfigChangeIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVoteResponse(n, m, term, voteGranted, prevote) ==
    /\ m \in nodes[n]
    /\ m # n
    /\ \/ /\ term > currentTerm[n]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
          /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
          /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
          /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
          /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in {3, 4, 5, 6, 7} : TRUE]
          /\ UNCHANGED <<votedFor, votes, log, nextIndex, matchIndex>>
       \/ /\ term = currentTerm[n]
          /\ \/ /\ state[n] = "PRECANDIDATE"
                /\ prevote
                /\ voteGranted
                /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m}]
                /\ IF Cardinality(votes'[n]) * 2 > Cardinality(nodes[n])
                   THEN /\ currentTerm[n] < MaxTerm
                        /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
                        /\ votedFor' = [votedFor EXCEPT ![n] = n]
                        /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
                        /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
                        /\ votes' = [votes EXCEPT ![n] = {n}]
                        /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                   ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, timeoutElapsed, electionTimeout>>
             \/ /\ state[n] = "CANDIDATE"
                /\ ~prevote
                /\ voteGranted
                /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m}]
                /\ IF Cardinality(votes'[n]) * 2 > Cardinality(nodes[n])
                   THEN BecomeLeader(n)
                   ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, log, nextIndex, matchIndex, timeoutElapsed, electionTimeout>>
             \/ UNCHANGED <<currentTerm, votedFor, state, leaderId, votes, log, nextIndex, matchIndex, timeoutElapsed, electionTimeout>>
    /\ UNCHANGED <<commitIndex, lastApplied, votingConfigChangeIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

LogAppend(n, entry) ==
    /\ state[n] = "LEADER"
    /\ Len(log[n]) < MaxLogLen
    /\ log' = [log EXCEPT ![n] = Append(log[n], entry)]
    /\ IF entry.type \in {"CONFIG_ADD", "CONFIG_REMOVE"}
       THEN votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![n] = Len(log'[n])]
       ELSE UNCHANGED votingConfigChangeIndex
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastApplied,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   nodes, snapshotLastIndex, snapshotLastTerm>>

LogDelete(n, index) ==
    /\ index > commitIndex[n]
    /\ index <= Len(log[n])
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, index - 1)]
    /\ IF votingConfigChangeIndex[n] >= index
       THEN votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![n] = -1]
       ELSE UNCHANGED votingConfigChangeIndex
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastApplied,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   nodes, snapshotLastIndex, snapshotLastTerm>>

LogCommit(n) ==
    /\ state[n] = "LEADER"
    /\ \E index \in (commitIndex[n] + 1)..Len(log[n]):
        /\ log[n][index].term = currentTerm[n]
        /\ LET agreementCount == Cardinality({m \in nodes[n] : matchIndex[n][m] >= index})
           IN agreementCount * 2 > Cardinality(nodes[n])
        /\ commitIndex' = [commitIndex EXCEPT ![n] = index]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, log, lastApplied,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   votingConfigChangeIndex, nodes, snapshotLastIndex, snapshotTerm>>

RecvAppendEntries(n, m, term, prevLogIndex, prevLogTerm, entries, leaderCommit) ==
    /\ m \in nodes[n]
    /\ m # n
    /\ \/ /\ term < currentTerm[n]
          /\ UNCHANGED vars
       \/ /\ term >= currentTerm[n]
          /\ IF term > currentTerm[n]
             THEN currentTerm' = [currentTerm EXCEPT ![n] = term]
             ELSE UNCHANGED currentTerm
          /\ leaderId' = [leaderId EXCEPT ![n] = m]
          /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
          /\ IF state[n] # "FOLLOWER"
             THEN state' = [state EXCEPT ![n] = "FOLLOWER"]
             ELSE UNCHANGED state
          /\ LET logOk == \/ prevLogIndex = 0
                          \/ /\ prevLogIndex > 0
                             /\ prevLogIndex <= Len(log[n])
                             /\ \/ /\ prevLogIndex = snapshotLastIndex[n]
                                   /\ prevLogTerm = snapshotLastTerm[n]
                                \/ /\ prevLogIndex > snapshotLastIndex[n]
                                   /\ log[n][prevLogIndex].term = prevLogTerm
             IN IF logOk
                THEN /\ LET newLog == SubSeq(log[n], 1, prevLogIndex) \o entries
                        IN log' = [log EXCEPT ![n] = newLog]
                     /\ IF leaderCommit > commitIndex[n]
                        THEN commitIndex' = [commitIndex EXCEPT ![n] = Min(leaderCommit, Len(log'[n]))]
                        ELSE UNCHANGED commitIndex
                ELSE /\ IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[n])
                        THEN log' = [log EXCEPT ![n] = SubSeq(log[n], 1, prevLogIndex - 1)]
                        ELSE UNCHANGED log
                     /\ UNCHANGED commitIndex
          /\ UNCHANGED <<votedFor, lastApplied, nextIndex, matchIndex, votes,
                         electionTimeout, votingConfigChangeIndex, nodes,
                         snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntriesResponse(n, m, term, success, matchIdx) ==
    /\ state[n] = "LEADER"
    /\ m \in nodes[n]
    /\ m # n
    /\ \/ /\ term > currentTerm[n]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
          /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
          /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
          /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
          /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in {3, 4, 5, 6, 7} : TRUE]
          /\ UNCHANGED <<votedFor, log, nextIndex, matchIndex>>
       \/ /\ term = currentTerm[n]
          /\ IF success
             THEN /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![m] = matchIdx]]
                  /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![m] = matchIdx + 1]]
             ELSE /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![m] = Max(1, nextIndex[n][m] - 1)]]
                  /\ UNCHANGED matchIndex
          /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, log, timeoutElapsed, electionTimeout>>
    /\ UNCHANGED <<commitIndex, lastApplied, votes, votingConfigChangeIndex,
                   nodes, snapshotLastIndex, snapshotLastTerm>>

SendAppendEntries(n, m) ==
    /\ state[n] = "LEADER"
    /\ m \in nodes[n]
    /\ m # n
    /\ nextIndex[n][m] <= Len(log[n])
    /\ LET prevLogIndex == nextIndex[n][m] - 1
           prevLogTerm == IF prevLogIndex = 0 THEN 0
                         ELSE IF prevLogIndex = snapshotLastIndex[n] THEN snapshotLastTerm[n]
                         ELSE log[n][prevLogIndex].term
           entries == SubSeq(log[n], nextIndex[n][m], Len(log[n]))
       IN RecvAppendEntries(m, n, currentTerm[n], prevLogIndex, prevLogTerm, entries, commitIndex[n])

SendHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ timeoutElapsed[n] >= 2
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ \A m \in nodes[n] \ {n}: 
        \/ nextIndex[n][m] > Len(log[n])
        \/ SendAppendEntries(n, m)

PeriodicElectionTimeout(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
    /\ IF timeoutElapsed'[n] >= electionTimeout[n]
       THEN ElectionTimeout(n)
       ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, log, commitIndex, lastApplied,
                        nextIndex, matchIndex, votes, electionTimeout, votingConfigChangeIndex,
                        nodes, snapshotLastIndex, snapshotLastTerm>>

PeriodicHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
    /\ IF timeoutElapsed'[n] >= 2
       THEN SendHeartbeat(n)
       ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, log, commitIndex, lastApplied,
                        nextIndex, matchIndex, votes, electionTimeout, votingConfigChangeIndex,
                        nodes, snapshotLastIndex, snapshotLastTerm>>

AddNode(n, newNode) ==
    /\ state[n] = "LEADER"
    /\ newNode \in Nodes
    /\ newNode \notin nodes[n]
    /\ Len(log[n]) < MaxLogLen
    /\ nodes' = [nodes EXCEPT ![n] = nodes[n] \cup {newNode}]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![newNode] = Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![newNode] = 0]]
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "CONFIG_ADD"])]
    /\ votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![n] = Len(log'[n])]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastApplied,
                   votes, timeoutElapsed, electionTimeout, snapshotLastIndex, snapshotLastTerm>>

RemoveNode(n, oldNode) ==
    /\ state[n] = "LEADER"
    /\ oldNode \in nodes[n]
    /\ oldNode # n
    /\ Len(log[n]) < MaxLogLen
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "CONFIG_REMOVE"])]
    /\ votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![n] = Len(log'[n])]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastApplied,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   nodes, snapshotLastIndex, snapshotLastTerm>>

ApplyConfigChange(n, index) ==
    /\ index <= commitIndex[n]
    /\ index > lastApplied[n]
    /\ index <= Len(log[n])
    /\ log[n][index].type \in {"CONFIG_ADD", "CONFIG_REMOVE"}
    /\ lastApplied' = [lastApplied EXCEPT ![n] = index]
    /\ IF votingConfigChangeIndex[n] = index
       THEN votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![n] = -1]
       ELSE UNCHANGED votingConfigChangeIndex
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, log, commitIndex,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   nodes, snapshotLastIndex, snapshotLastTerm>>

SnapshotBegin(n) ==
    /\ commitIndex[n] = lastApplied[n]
    /\ commitIndex[n] > snapshotLastIndex[n]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = lastApplied[n]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = 
                            IF lastApplied[n] = 0 THEN 0 ELSE log[n][lastApplied[n]].term]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   votingConfigChangeIndex, nodes>>

SnapshotEnd(n) ==
    /\ snapshotLastIndex[n] > 0
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], snapshotLastIndex[n] + 1, Len(log[n]))]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastApplied,
                   nextIndex, matchIndex, votes, timeoutElapsed, electionTimeout,
                   votingConfigChangeIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

Next ==
    \E n \in Nodes:
        \/ BecomeFollower(n)
        \/ BecomePreCandidate(n)
        \/ BecomeCandidate(n)
        \/ BecomeLeader(n)
        \/ ElectionStart(n)
        \/ ElectionTimeout(n)
        \/ PeriodicElectionTimeout(n)
        \/ PeriodicHeartbeat(n)
        \/ LogCommit(n)
        \/ SnapshotBegin(n)
        \/ SnapshotEnd(n)
        \/ \E m \in Nodes:
            \/ RecvRequestVote(n, m, currentTerm[m], Len(log[m]), 
                              IF Len(log[m]) = 0 THEN 0 ELSE log[m][Len(log[m])].term, FALSE)
            \/ RecvRequestVoteResponse(n, m, currentTerm[m], TRUE, FALSE)
            \/ SendAppendEntries(n, m)
            \/ RecvAppendEntriesResponse(n, m, currentTerm[m], TRUE, Len(log[m]))
        \/ \E entry \in LogEntries:
            LogAppend(n, entry)
        \/ \E index \in 1..Len(log[n]):
            \/ LogDelete(n, index)
            \/ ApplyConfigChange(n, index)
        \/ \E newNode \in Nodes:
            AddNode(n, newNode)
        \/ \E oldNode \in Nodes:
            RemoveNode(n, oldNode)

Spec == Init /\ [][Next]_vars

====