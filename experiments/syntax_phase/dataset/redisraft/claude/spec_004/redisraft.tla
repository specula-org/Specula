---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS 
    Nodes,
    MaxTerm,
    MaxLogIndex,
    MaxEntries

VARIABLES
    currentTerm,
    votedFor,
    state,
    leaderId,
    commitIndex,
    lastAppliedIndex,
    timeoutElapsed,
    electionTimeoutRand,
    log,
    nodes,
    votingCfgChangeLogIdx,
    msgId,
    nextIndex,
    matchIndex,
    votes,
    snapshotLastIndex,
    snapshotLastTerm,
    snapshotInProgress

vars == <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex,
          timeoutElapsed, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx,
          msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm,
          snapshotInProgress>>

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
LogEntryTypes == {"NO_OP", "ADD_NODE", "REMOVE_NODE", "ADD_NONVOTING_NODE", "NORMAL"}
NONE == "NONE"

Init ==
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> NONE]
    /\ state = [n \in Nodes |-> "FOLLOWER"]
    /\ leaderId = [n \in Nodes |-> NONE]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastAppliedIndex = [n \in Nodes |-> 0]
    /\ timeoutElapsed = [n \in Nodes |-> 0]
    /\ electionTimeoutRand = [n \in Nodes |-> 1000]
    /\ log = [n \in Nodes |-> <<>>]
    /\ nodes = [n \in Nodes |-> Nodes]
    /\ votingCfgChangeLogIdx = [n \in Nodes |-> 0 - 1]
    /\ msgId = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votes = [n \in Nodes |-> [m \in Nodes |-> FALSE]]
    /\ snapshotLastIndex = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]
    /\ snapshotInProgress = [n \in Nodes |-> FALSE]

BecomeFollower(n) ==
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE t \in {800, 900, 1000, 1100, 1200} : TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastAppliedIndex, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

BecomePreCandidate(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votes' = [votes EXCEPT ![n] = [m \in Nodes |-> FALSE]]
    /\ UNCHANGED <<currentTerm, votedFor, leaderId, commitIndex, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

BecomeCandidate(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ currentTerm[n] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![n] = @ + 1]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votes' = [votes EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN TRUE ELSE FALSE]]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ UNCHANGED <<commitIndex, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ Cardinality({m \in Nodes : votes[n][m]}) * 2 > Cardinality(Nodes)
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ Len(log[n]) < MaxEntries
    /\ log' = [log EXCEPT ![n] = Append(@, [term |-> currentTerm[n], type |-> "NO_OP", index |-> Len(@) + 1])]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log'[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN Len(log'[n]) ELSE 0]]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastAppliedIndex, electionTimeoutRand, nodes, votingCfgChangeLogIdx, msgId, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

RecvRequestVote(n, m, term, lastLogIndex, lastLogTerm, prevote) ==
    /\ m \in Nodes
    /\ n # m
    /\ IF term > currentTerm[n]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
            /\ IF ~prevote THEN votedFor' = [votedFor EXCEPT ![n] = NONE]
                           ELSE UNCHANGED votedFor
            /\ IF ~prevote THEN /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                                /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                                /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
                                /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE t \in {800, 900, 1000, 1100, 1200} : TRUE]
                           ELSE UNCHANGED <<state, leaderId, timeoutElapsed, electionTimeoutRand>>
       ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, timeoutElapsed, electionTimeoutRand>>
    /\ LET voteGranted == 
           /\ term >= currentTerm'[n]
           /\ (prevote \/ votedFor'[n] \in {NONE, m})
           /\ LET lastTerm == IF Len(log[n]) = 0 THEN 0 ELSE log[n][Len(log[n])]["term"]
                  lastIndex == Len(log[n])
              IN \/ lastLogTerm > lastTerm
                 \/ /\ lastLogTerm = lastTerm
                    /\ lastLogIndex >= lastIndex
       IN IF voteGranted /\ ~prevote
          THEN votedFor' = [votedFor' EXCEPT ![n] = m]
          ELSE UNCHANGED (votedFor')
    /\ UNCHANGED <<commitIndex, lastAppliedIndex, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

RecvRequestVoteResponse(n, m, term, voteGranted, prevote) ==
    /\ m \in Nodes
    /\ n # m
    /\ IF term > currentTerm[n]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
            /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
            /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
            /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE t \in {800, 900, 1000, 1100, 1200} : TRUE]
       ELSE /\ UNCHANGED <<currentTerm, state, leaderId, timeoutElapsed, electionTimeoutRand>>
            /\ IF voteGranted /\ state[n] \in {"CANDIDATE", "PRECANDIDATE"}
               THEN /\ votes' = [votes EXCEPT ![n][m] = TRUE]
                    /\ LET voteCount == Cardinality({k \in Nodes : votes'[n][k]})
                       IN IF voteCount * 2 > Cardinality(Nodes)
                          THEN IF state[n] = "PRECANDIDATE"
                               THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = @ + 1]
                                    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
                                    /\ votedFor' = [votedFor EXCEPT ![n] = n]
                                    /\ votes' = [votes EXCEPT ![n] = [k \in Nodes |-> IF k = n THEN TRUE ELSE FALSE]]
                                    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
                               ELSE /\ state' = [state EXCEPT ![n] = "LEADER"]
                                    /\ leaderId' = [leaderId EXCEPT ![n] = n]
                                    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                                    /\ log' = [log EXCEPT ![n] = Append(@, [term |-> currentTerm[n], type |-> "NO_OP", index |-> Len(@) + 1])]
                                    /\ nextIndex' = [nextIndex EXCEPT ![n] = [k \in Nodes |-> Len(log'[n]) + 1]]
                                    /\ matchIndex' = [matchIndex EXCEPT ![n] = [k \in Nodes |-> IF k = n THEN Len(log'[n]) ELSE 0]]
                          ELSE UNCHANGED <<state, leaderId, timeoutElapsed, log, nextIndex, matchIndex>>
               ELSE UNCHANGED <<votes, state, leaderId, timeoutElapsed, log, nextIndex, matchIndex>>
    /\ UNCHANGED <<votedFor, commitIndex, lastAppliedIndex, electionTimeoutRand, nodes, votingCfgChangeLogIdx, msgId, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

RecvAppendEntries(n, m, term, prevLogIndex, prevLogTerm, entries, leaderCommit) ==
    /\ m \in Nodes
    /\ n # m
    /\ IF term > currentTerm[n]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
            /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
            /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE t \in {800, 900, 1000, 1100, 1200} : TRUE]
       ELSE UNCHANGED <<currentTerm, state, timeoutElapsed, electionTimeoutRand>>
    /\ leaderId' = [leaderId EXCEPT ![n] = m]
    /\ LET logOk == 
           \/ prevLogIndex = 0
           \/ /\ prevLogIndex <= Len(log[n])
              /\ (prevLogIndex > 0) => (log[n][prevLogIndex]["term"] = prevLogTerm)
       IN IF logOk
          THEN /\ log' = [log EXCEPT ![n] = SubSeq(@, 1, prevLogIndex) \o entries]
               /\ commitIndex' = [commitIndex EXCEPT ![n] = 
                    IF leaderCommit > commitIndex[n]
                    THEN IF leaderCommit < Len(log'[n]) THEN leaderCommit ELSE Len(log'[n])
                    ELSE commitIndex[n]]
          ELSE UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<votedFor, lastAppliedIndex, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

RecvAppendEntriesResponse(n, m, term, success, matchIdx) ==
    /\ m \in Nodes
    /\ n # m
    /\ state[n] = "LEADER"
    /\ IF term > currentTerm[n]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
            /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
            /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
            /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
            /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE t \in {800, 900, 1000, 1100, 1200} : TRUE]
       ELSE /\ UNCHANGED <<currentTerm, state, leaderId, timeoutElapsed, electionTimeoutRand>>
            /\ IF success
               THEN /\ matchIndex' = [matchIndex EXCEPT ![n][m] = matchIdx]
                    /\ nextIndex' = [nextIndex EXCEPT ![n][m] = matchIdx + 1]
                    /\ LET newCommitIndex == 
                           CHOOSE idx \in 0..Len(log[n]) :
                               /\ idx > commitIndex[n]
                               /\ Cardinality({k \in Nodes : matchIndex'[n][k] >= idx}) * 2 > Cardinality(Nodes)
                               /\ (idx > 0) => (log[n][idx]["term"] = currentTerm[n])
                       IN commitIndex' = [commitIndex EXCEPT ![n] = newCommitIndex]
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![n][m] = IF nextIndex[n][m] - 1 > 1 THEN nextIndex[n][m] - 1 ELSE 1]
                    /\ UNCHANGED <<matchIndex, commitIndex>>
    /\ UNCHANGED <<votedFor, lastAppliedIndex, log, nodes, votingCfgChangeLogIdx, msgId, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

SendAppendEntries(n, m) ==
    /\ n # m
    /\ state[n] = "LEADER"
    /\ m \in Nodes
    /\ LET prevLogIndex == nextIndex[n][m] - 1
           prevLogTerm == IF prevLogIndex = 0 THEN 0 ELSE log[n][prevLogIndex]["term"]
           entries == SubSeq(log[n], nextIndex[n][m], Len(log[n]))
       IN RecvAppendEntries(m, n, currentTerm[n], prevLogIndex, prevLogTerm, entries, commitIndex[n])

SendHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ \E m \in Nodes : m # n /\ SendAppendEntries(n, m)

ElectionStart(n, skipPrecandidate) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ timeoutElapsed[n] >= electionTimeoutRand[n]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE t \in {800, 900, 1000, 1100, 1200} : TRUE]
    /\ IF skipPrecandidate
       THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = @ + 1]
            /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
            /\ votedFor' = [votedFor EXCEPT ![n] = n]
            /\ votes' = [votes EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN TRUE ELSE FALSE]]
       ELSE /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
            /\ votes' = [votes EXCEPT ![n] = [m \in Nodes |-> FALSE]]
            /\ UNCHANGED <<currentTerm, votedFor>>
    /\ UNCHANGED <<commitIndex, lastAppliedIndex, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

ElectionTimeout(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ timeoutElapsed[n] >= electionTimeoutRand[n]
    /\ ElectionStart(n, FALSE)

LogAppend(n, entry) ==
    /\ state[n] = "LEADER"
    /\ Len(log[n]) < MaxEntries
    /\ log' = [log EXCEPT ![n] = Append(@, entry)]
    /\ IF entry["type"] \in {"ADD_NODE", "REMOVE_NODE"}
       THEN votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![n] = Len(log'[n])]
       ELSE UNCHANGED votingCfgChangeLogIdx
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, nodes, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

LogDelete(n, fromIndex) ==
    /\ fromIndex > commitIndex[n]
    /\ fromIndex <= Len(log[n])
    /\ log' = [log EXCEPT ![n] = SubSeq(@, 1, fromIndex - 1)]
    /\ IF votingCfgChangeLogIdx[n] >= fromIndex
       THEN votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![n] = 0 - 1]
       ELSE UNCHANGED votingCfgChangeLogIdx
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, nodes, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

LogCommit(n) ==
    /\ state[n] = "LEADER"
    /\ \E idx \in (commitIndex[n] + 1)..Len(log[n]) :
        /\ Cardinality({m \in Nodes : matchIndex[n][m] >= idx}) * 2 > Cardinality(Nodes)
        /\ log[n][idx]["term"] = currentTerm[n]
        /\ commitIndex' = [commitIndex EXCEPT ![n] = idx]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

PeriodicElectionTimeout(n) ==
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = @ + 1]
    /\ IF timeoutElapsed'[n] >= electionTimeoutRand[n] /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
       THEN ElectionStart(n, FALSE)
       ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

PeriodicHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = @ + 1]
    /\ IF timeoutElapsed'[n] >= 200
       THEN /\ timeoutElapsed' = [timeoutElapsed' EXCEPT ![n] = 0]
            /\ \E m \in Nodes : m # n /\ SendAppendEntries(n, m)
       ELSE UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

AddNode(n, nodeId) ==
    /\ state[n] = "LEADER"
    /\ nodeId \notin nodes[n]
    /\ nodes' = [nodes EXCEPT ![n] = @ \cup {nodeId}]
    /\ LogAppend(n, [term |-> currentTerm[n], type |-> "ADD_NODE", index |-> Len(log[n]) + 1])

RemoveNode(n, nodeId) ==
    /\ state[n] = "LEADER"
    /\ nodeId \in nodes[n]
    /\ nodeId # n
    /\ nodes' = [nodes EXCEPT ![n] = @ \ {nodeId}]
    /\ LogAppend(n, [term |-> currentTerm[n], type |-> "REMOVE_NODE", index |-> Len(log[n]) + 1])

SnapshotBegin(n) ==
    /\ ~snapshotInProgress[n]
    /\ commitIndex[n] > snapshotLastIndex[n]
    /\ lastAppliedIndex[n] = commitIndex[n]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, log, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm>>

SnapshotEnd(n) ==
    /\ snapshotInProgress[n]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = lastAppliedIndex[n]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = 
        IF lastAppliedIndex[n] > 0 /\ lastAppliedIndex[n] <= Len(log[n])
        THEN log[n][lastAppliedIndex[n]]["term"]
        ELSE 0]
    /\ log' = [log EXCEPT ![n] = SubSeq(@, snapshotLastIndex'[n] + 1, Len(@))]
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, lastAppliedIndex, timeoutElapsed, electionTimeoutRand, nodes, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes>>

ApplyConfigChange(n, entry, index) ==
    /\ entry["type"] \in {"ADD_NODE", "REMOVE_NODE", "ADD_NONVOTING_NODE"}
    /\ index <= commitIndex[n]
    /\ lastAppliedIndex[n] < index
    /\ lastAppliedIndex' = [lastAppliedIndex EXCEPT ![n] = index]
    /\ IF entry["type"] = "REMOVE_NODE"
       THEN nodes' = [nodes EXCEPT ![n] = @ \ {CHOOSE nodeId \in @ : TRUE}]
       ELSE IF entry["type"] = "ADD_NODE"
            THEN nodes' = [nodes EXCEPT ![n] = @ \cup {CHOOSE nodeId \in Nodes \ @ : TRUE}]
            ELSE UNCHANGED nodes
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, commitIndex, timeoutElapsed, electionTimeoutRand, log, votingCfgChangeLogIdx, msgId, nextIndex, matchIndex, votes, snapshotLastIndex, snapshotLastTerm, snapshotInProgress>>

Next ==
    \/ \E n \in Nodes : BecomeFollower(n)
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n, m \in Nodes, term \in 0..MaxTerm, lastLogIndex \in 0..MaxLogIndex, lastLogTerm \in 0..MaxTerm, prevote \in BOOLEAN :
        RecvRequestVote(n, m, term, lastLogIndex, lastLogTerm, prevote)
    \/ \E n, m \in Nodes, term \in 0..MaxTerm, voteGranted \in BOOLEAN, prevote \in BOOLEAN :
        RecvRequestVoteResponse(n, m, term, voteGranted, prevote)
    \/ \E n, m \in Nodes, term \in 0..MaxTerm, prevLogIndex \in 0..MaxLogIndex, prevLogTerm \in 0..MaxTerm, entries \in Seq([term : 0..MaxTerm, type : LogEntryTypes, index : 1..MaxLogIndex]), leaderCommit \in 0..MaxLogIndex :
        RecvAppendEntries(n, m, term, prevLogIndex, prevLogTerm, entries, leaderCommit)
    \/ \E n, m \in Nodes, term \in 0..MaxTerm, success \in BOOLEAN, matchIdx \in 0..MaxLogIndex :
        RecvAppendEntriesResponse(n, m, term, success, matchIdx)
    \/ \E n, m \in Nodes : SendAppendEntries(n, m)
    \/ \E n \in Nodes : SendHeartbeat(n)
    \/ \E n \in Nodes, skipPrecandidate \in BOOLEAN : ElectionStart(n, skipPrecandidate)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes, entry \in [term : 0..MaxTerm, type : LogEntryTypes, index : 1..MaxLogIndex] : LogAppend(n, entry)
    \/ \E n \in Nodes, fromIndex \in 1..MaxLogIndex : LogDelete(n, fromIndex)
    \/ \E n \in Nodes : LogCommit(n)
    \/ \E n \in Nodes : PeriodicElectionTimeout(n)
    \/ \E n \in Nodes : PeriodicHeartbeat(n)
    \/ \E n \in Nodes, nodeId \in Nodes : AddNode(n, nodeId)
    \/ \E n \in Nodes, nodeId \in Nodes : RemoveNode(n, nodeId)
    \/ \E n \in Nodes : SnapshotBegin(n)
    \/ \E n \in Nodes : SnapshotEnd(n)
    \/ \E n \in Nodes, entry \in [term : 0..MaxTerm, type : LogEntryTypes, index : 1..MaxLogIndex], index \in 1..MaxLogIndex :
        ApplyConfigChange(n, entry, index)

Spec == Init /\ [][Next]_vars

====