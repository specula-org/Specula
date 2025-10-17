---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, MaxTerm, MaxLogLen

VARIABLES
    currentTerm,
    votedFor,
    state,
    log,
    commitIndex,
    leaderId,
    timeoutElapsed,
    electionTimeoutRand,
    nextIndex,
    matchIndex,
    votingCfgChangeLogIdx,
    messages,
    lastAppliedIdx,
    lastAppliedTerm

vars == <<currentTerm, votedFor, state, log, commitIndex, leaderId, 
          timeoutElapsed, electionTimeoutRand, nextIndex, matchIndex,
          votingCfgChangeLogIdx, messages, lastAppliedIdx, lastAppliedTerm>>

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
MessageTypes == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse"}
LogEntryTypes == {"Normal", "AddNode", "RemoveNode", "AddNonVotingNode", "NoOp"}

NONE == 0

Init ==
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> NONE]
    /\ state = [n \in Nodes |-> "FOLLOWER"]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ leaderId = [n \in Nodes |-> NONE]
    /\ timeoutElapsed = [n \in Nodes |-> 0]
    /\ electionTimeoutRand = [n \in Nodes |-> 1]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votingCfgChangeLogIdx = [n \in Nodes |-> -1]
    /\ messages = {}
    /\ lastAppliedIdx = [n \in Nodes |-> 0]
    /\ lastAppliedTerm = [n \in Nodes |-> 0]

GetCurrentIdx(n) == Len(log[n])
GetLastLogTerm(n) == IF Len(log[n]) = 0 THEN 0 ELSE log[n][Len(log[n])].term

VotingNodes == Nodes
GetNumVotingNodes == Cardinality(VotingNodes)
IsMajority(votes) == votes * 2 > GetNumVotingNodes

BecomeFollower(n) ==
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionTimeoutRand,
                   nextIndex, matchIndex, votingCfgChangeLogIdx, messages,
                   lastAppliedIdx, lastAppliedTerm>>

BecomePreCandidate(n) ==
    /\ state[n] = "FOLLOWER"
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ LET requestVoteMsg == [type |-> "RequestVote",
                              term |-> currentTerm[n] + 1,
                              candidateId |-> n,
                              lastLogIdx |-> GetCurrentIdx(n),
                              lastLogTerm |-> GetLastLogTerm(n),
                              prevote |-> TRUE,
                              dest |-> m,
                              source |-> n]
       IN messages' = messages \cup {requestVoteMsg : m \in Nodes \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leaderId,
                   electionTimeoutRand, nextIndex, matchIndex, votingCfgChangeLogIdx,
                   lastAppliedIdx, lastAppliedTerm>>

BecomeCandidate(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = NONE]
    /\ LET requestVoteMsg == [type |-> "RequestVote",
                              term |-> currentTerm[n] + 1,
                              candidateId |-> n,
                              lastLogIdx |-> GetCurrentIdx(n),
                              lastLogTerm |-> GetLastLogTerm(n),
                              prevote |-> FALSE,
                              dest |-> m,
                              source |-> n]
       IN messages' = messages \cup {requestVoteMsg : m \in Nodes \ {n}}
    /\ UNCHANGED <<log, commitIndex, electionTimeoutRand, nextIndex, matchIndex,
                   votingCfgChangeLogIdx, lastAppliedIdx, lastAppliedTerm>>

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ LET votes == Cardinality({m \in Nodes : votedFor[m] = n})
       IN IsMajority(votes)
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ LET noopEntry == [term |-> currentTerm[n], type |-> "NoOp", data |-> ""]
       IN log' = [log EXCEPT ![n] = Append(log[n], noopEntry)]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> GetCurrentIdx(n) + 2]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN GetCurrentIdx(n) + 1 ELSE 0]]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, electionTimeoutRand,
                   votingCfgChangeLogIdx, messages, lastAppliedIdx, lastAppliedTerm>>

ElectionStart(n) ==
    /\ state[n] = "FOLLOWER"
    /\ timeoutElapsed[n] >= electionTimeoutRand[n]
    /\ BecomePreCandidate(n)

ElectionTimeout(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ timeoutElapsed[n] >= electionTimeoutRand[n]
    /\ \/ BecomePreCandidate(n)
       \/ BecomeCandidate(n)

PeriodicElectionTimeout(n) ==
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leaderId,
                   electionTimeoutRand, nextIndex, matchIndex, votingCfgChangeLogIdx,
                   messages, lastAppliedIdx, lastAppliedTerm>>

RecvRequestVote(n, m) ==
    /\ \E msg \in messages :
        /\ msg.type = "RequestVote"
        /\ msg.dest = n
        /\ msg.source = m
        /\ LET voteGranted == 
               /\ \/ msg.term > currentTerm[n]
                  \/ /\ msg.term = currentTerm[n]
                     /\ \/ votedFor[n] = NONE
                        \/ votedFor[n] = msg.candidateId
               /\ \/ msg.lastLogTerm > GetLastLogTerm(n)
                  \/ /\ msg.lastLogTerm = GetLastLogTerm(n)
                     /\ msg.lastLogIdx >= GetCurrentIdx(n)
               /\ \/ ~msg.prevote
                  \/ /\ msg.prevote
                     /\ \/ leaderId[n] = NONE
                        \/ leaderId[n] = msg.candidateId
                        \/ timeoutElapsed[n] >= electionTimeoutRand[n]
           responseMsg == [type |-> "RequestVoteResponse",
                          term |-> IF msg.term > currentTerm[n] THEN msg.term ELSE currentTerm[n],
                          voteGranted |-> voteGranted,
                          prevote |-> msg.prevote,
                          dest |-> m,
                          source |-> n]
        IN /\ messages' = (messages \ {msg}) \cup {responseMsg}
           /\ IF msg.term > currentTerm[n]
              THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                   /\ BecomeFollower(n)
              ELSE /\ IF voteGranted /\ ~msg.prevote
                      THEN votedFor' = [votedFor EXCEPT ![n] = msg.candidateId]
                      ELSE UNCHANGED votedFor
                   /\ UNCHANGED <<currentTerm, state, leaderId, timeoutElapsed>>
           /\ UNCHANGED <<log, commitIndex, electionTimeoutRand, nextIndex, matchIndex,
                          votingCfgChangeLogIdx, lastAppliedIdx, lastAppliedTerm>>

RecvRequestVoteResponse(n, m) ==
    /\ \E msg \in messages :
        /\ msg.type = "RequestVoteResponse"
        /\ msg.dest = n
        /\ msg.source = m
        /\ IF msg.term > currentTerm[n]
           THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ BecomeFollower(n)
                /\ messages' = messages \ {msg}
           ELSE /\ IF msg.voteGranted
                   THEN LET votes == Cardinality({k \in Nodes : 
                                      \E resp \in messages : 
                                        resp.type = "RequestVoteResponse" /\
                                        resp.dest = n /\ resp.voteGranted}) + 1
                        IN IF IsMajority(votes)
                           THEN IF msg.prevote /\ state[n] = "PRECANDIDATE"
                                THEN BecomeCandidate(n)
                                ELSE IF ~msg.prevote /\ state[n] = "CANDIDATE"
                                THEN BecomeLeader(n)
                                ELSE UNCHANGED <<state, leaderId, timeoutElapsed, log, nextIndex, matchIndex>>
                           ELSE UNCHANGED <<state, leaderId, timeoutElapsed, log, nextIndex, matchIndex>>
                   ELSE UNCHANGED <<state, leaderId, timeoutElapsed, log, nextIndex, matchIndex>>
                /\ messages' = messages \ {msg}
                /\ UNCHANGED currentTerm
        /\ UNCHANGED <<votedFor, commitIndex, electionTimeoutRand, votingCfgChangeLogIdx,
                       lastAppliedIdx, lastAppliedTerm>>

SendAppendEntries(n, m) ==
    /\ state[n] = "LEADER"
    /\ n # m
    /\ LET prevLogIdx == nextIndex[n][m] - 1
           prevLogTerm == IF prevLogIdx = 0 THEN 0 ELSE log[n][prevLogIdx].term
           entries == IF nextIndex[n][m] <= Len(log[n])
                      THEN SubSeq(log[n], nextIndex[n][m], Len(log[n]))
                      ELSE <<>>
           msg == [type |-> "AppendEntries",
                   term |-> currentTerm[n],
                   leaderId |-> n,
                   prevLogIdx |-> prevLogIdx,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entries,
                   leaderCommit |-> commitIndex[n],
                   dest |-> m,
                   source |-> n]
       IN messages' = messages \cup {msg}
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leaderId,
                   timeoutElapsed, electionTimeoutRand, nextIndex, matchIndex,
                   votingCfgChangeLogIdx, lastAppliedIdx, lastAppliedTerm>>

SendHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ \A m \in Nodes \ {n} : SendAppendEntries(n, m)

PeriodicHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ timeoutElapsed[n] >= 1
    /\ SendHeartbeat(n)
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]

RecvAppendEntries(n, m) ==
    /\ \E msg \in messages :
        /\ msg.type = "AppendEntries"
        /\ msg.dest = n
        /\ msg.source = m
        /\ LET success == 
               /\ msg.term >= currentTerm[n]
               /\ \/ msg.prevLogIdx = 0
                  \/ /\ msg.prevLogIdx <= Len(log[n])
                     /\ log[n][msg.prevLogIdx].term = msg.prevLogTerm
           responseMsg == [type |-> "AppendEntriesResponse",
                          term |-> IF msg.term > currentTerm[n] THEN msg.term ELSE currentTerm[n],
                          success |-> success,
                          matchIndex |-> IF success THEN msg.prevLogIdx + Len(msg.entries) ELSE Len(log[n]),
                          dest |-> m,
                          source |-> n]
        IN /\ messages' = (messages \ {msg}) \cup {responseMsg}
           /\ IF msg.term > currentTerm[n]
              THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                   /\ BecomeFollower(n)
              ELSE UNCHANGED <<currentTerm, state, timeoutElapsed>>
           /\ IF success
              THEN /\ leaderId' = [leaderId EXCEPT ![n] = msg.leaderId]
                   /\ IF Len(msg.entries) > 0
                      THEN log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.prevLogIdx) \o msg.entries]
                      ELSE UNCHANGED log
                   /\ IF msg.leaderCommit > commitIndex[n]
                      THEN commitIndex' = [commitIndex EXCEPT ![n] = 
                                           Min(msg.leaderCommit, msg.prevLogIdx + Len(msg.entries))]
                      ELSE UNCHANGED commitIndex
              ELSE UNCHANGED <<log, commitIndex, leaderId>>
           /\ UNCHANGED <<votedFor, electionTimeoutRand, nextIndex, matchIndex,
                          votingCfgChangeLogIdx, lastAppliedIdx, lastAppliedTerm>>

RecvAppendEntriesResponse(n, m) ==
    /\ state[n] = "LEADER"
    /\ \E msg \in messages :
        /\ msg.type = "AppendEntriesResponse"
        /\ msg.dest = n
        /\ msg.source = m
        /\ IF msg.term > currentTerm[n]
           THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ BecomeFollower(n)
           ELSE /\ IF msg.success
                   THEN /\ matchIndex' = [matchIndex EXCEPT ![n][m] = msg.matchIndex]
                        /\ nextIndex' = [nextIndex EXCEPT ![n][m] = msg.matchIndex + 1]
                   ELSE /\ nextIndex' = [nextIndex EXCEPT ![n][m] = Max(1, nextIndex[n][m] - 1)]
                        /\ UNCHANGED matchIndex
                /\ UNCHANGED <<currentTerm, state, leaderId, timeoutElapsed>>
        /\ messages' = messages \ {msg}
        /\ UNCHANGED <<votedFor, log, commitIndex, electionTimeoutRand,
                       votingCfgChangeLogIdx, lastAppliedIdx, lastAppliedTerm>>

LogAppend(n, entry) ==
    /\ state[n] = "LEADER"
    /\ entry.term = currentTerm[n]
    /\ Len(log[n]) < MaxLogLen
    /\ log' = [log EXCEPT ![n] = Append(log[n], entry)]
    /\ IF entry.type \in {"AddNode", "RemoveNode"}
       THEN votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![n] = Len(log[n]) + 1]
       ELSE UNCHANGED votingCfgChangeLogIdx
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, leaderId,
                   timeoutElapsed, electionTimeoutRand, nextIndex, matchIndex,
                   messages, lastAppliedIdx, lastAppliedTerm>>

LogDelete(n, idx) ==
    /\ idx > commitIndex[n]
    /\ idx <= Len(log[n])
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, idx - 1)]
    /\ IF votingCfgChangeLogIdx[n] >= idx
       THEN votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![n] = -1]
       ELSE UNCHANGED votingCfgChangeLogIdx
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, leaderId,
                   timeoutElapsed, electionTimeoutRand, nextIndex, matchIndex,
                   messages, lastAppliedIdx, lastAppliedTerm>>

LogCommit(n) ==
    /\ state[n] = "LEADER"
    /\ LET indices == {matchIndex[n][m] : m \in Nodes}
           sortedIndices == SetToSeq(indices)
           majorityIndex == sortedIndices[Cardinality(VotingNodes) \div 2 + 1]
       IN /\ majorityIndex > commitIndex[n]
          /\ majorityIndex <= Len(log[n])
          /\ log[n][majorityIndex].term = currentTerm[n]
          /\ commitIndex' = [commitIndex EXCEPT ![n] = majorityIndex]
    /\ UNCHANGED <<currentTerm, votedFor, state, log, leaderId, timeoutElapsed,
                   electionTimeoutRand, nextIndex, matchIndex, votingCfgChangeLogIdx,
                   messages, lastAppliedIdx, lastAppliedTerm>>

AddNode(n, nodeId) ==
    /\ state[n] = "LEADER"
    /\ nodeId \notin Nodes
    /\ votingCfgChangeLogIdx[n] = -1
    /\ LET entry == [term |-> currentTerm[n], type |-> "AddNode", data |-> ToString(nodeId)]
       IN LogAppend(n, entry)

RemoveNode(n, nodeId) ==
    /\ state[n] = "LEADER"
    /\ nodeId \in Nodes
    /\ nodeId # n
    /\ votingCfgChangeLogIdx[n] = -1
    /\ LET entry == [term |-> currentTerm[n], type |-> "RemoveNode", data |-> ToString(nodeId)]
       IN LogAppend(n, entry)

ApplyConfigChange(n) ==
    /\ lastAppliedIdx[n] < commitIndex[n]
    /\ LET idx == lastAppliedIdx[n] + 1
           entry == log[n][idx]
       IN /\ entry.type \in {"AddNode", "RemoveNode", "AddNonVotingNode"}
          /\ lastAppliedIdx' = [lastAppliedIdx EXCEPT ![n] = idx]
          /\ lastAppliedTerm' = [lastAppliedTerm EXCEPT ![n] = entry.term]
          /\ IF idx = votingCfgChangeLogIdx[n]
             THEN votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![n] = -1]
             ELSE UNCHANGED votingCfgChangeLogIdx
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leaderId,
                   timeoutElapsed, electionTimeoutRand, nextIndex, matchIndex, messages>>

Next ==
    \/ \E n \in Nodes : 
        \/ BecomeFollower(n)
        \/ BecomePreCandidate(n)
        \/ BecomeCandidate(n)
        \/ BecomeLeader(n)
        \/ ElectionStart(n)
        \/ ElectionTimeout(n)
        \/ PeriodicElectionTimeout(n)
        \/ PeriodicHeartbeat(n)
        \/ SendHeartbeat(n)
        \/ LogCommit(n)
        \/ ApplyConfigChange(n)
        \/ \E m \in Nodes \ {n} :
            \/ RecvRequestVote(n, m)
            \/ RecvRequestVoteResponse(n, m)
            \/ SendAppendEntries(n, m)
            \/ RecvAppendEntries(n, m)
            \/ RecvAppendEntriesResponse(n, m)
        \/ \E entry \in [term: 0..MaxTerm, type: LogEntryTypes, data: STRING] :
            LogAppend(n, entry)
        \/ \E idx \in 1..MaxLogLen :
            LogDelete(n, idx)
        \/ \E nodeId \in 1..10 :
            \/ AddNode(n, nodeId)
            \/ RemoveNode(n, nodeId)

Spec == Init /\ [][Next]_vars

====