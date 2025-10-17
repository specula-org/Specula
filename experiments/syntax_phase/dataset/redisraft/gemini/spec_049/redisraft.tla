---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Server,      \* The initial set of server IDs
    Value,       \* The set of possible client command values
    DefaultVote, \* A value indicating no vote has been cast
    Nil          \* A value indicating no leader is known

ASSUME Server \subseteq Nat
ASSUME Value \subseteq STRING
ASSUME DefaultVote \notin Server
ASSUME Nil \notin Server

VARIABLES
    state,            \* [server -> {{"Follower", "PreCandidate", "Candidate", "Leader"}}]
    currentTerm,      \* [server -> Nat]
    votedFor,         \* [server -> Server \cup {{DefaultVote}}]
    log,              \* [server -> Seq([term: Nat, value: Value \cup STRING])]
    commitIndex,      \* [server -> Nat]
    lastApplied,      \* [server -> Nat]
    nextIndex,        \* [leader -> [server -> Nat]]
    matchIndex,       \* [leader -> [server -> Nat]]
    votesGranted,     \* [candidate -> SUBSET Server]
    leaderId,         \* [server -> Server \cup {{Nil}}]
    messages,         \* A bag of messages in the network
    servers,          \* The current set of voting servers
    lastIncludedIndex, \* [server -> Nat]
    lastIncludedTerm,  \* [server -> Nat]
    electionTimer     \* [server -> Nat]

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, votesGranted, leaderId, messages, servers,
          lastIncludedIndex, lastIncludedTerm, electionTimer>>

otherVars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
               nextIndex, matchIndex, votesGranted, leaderId, servers,
               lastIncludedIndex, lastIncludedTerm, electionTimer>>

\* Helper functions
LogTerm(lg, idx) ==
    IF idx > 0 /\ idx <= Len(lg) THEN lg[idx].term ELSE 0

LastLogIndex(s) ==
    IF Len(log[s]) > 0 THEN Len(log[s]) + lastIncludedIndex[s] ELSE lastIncludedIndex[s]

LastLogTerm(s) ==
    LET lastIdx == LastLogIndex(s) IN
    IF lastIdx > lastIncludedIndex[s] THEN
        log[s][lastIdx - lastIncludedIndex[s]].term
    ELSE
        lastIncludedTerm[s]

IsUpToDate(candidateLogTerm, candidateLogIndex, myLogTerm, myLogIndex) ==
    (candidateLogTerm > myLogTerm) \/
    (candidateLogTerm = myLogTerm /\ candidateLogIndex >= myLogIndex)

Quorum(s) == (Cardinality(s) \div 2) + 1

\* Message definitions
RequestVoteMsg(term, candidateId, lastLogIdx, lastLogTerm, prevote) ==
    [type |-> "RequestVote", term |-> term, candidateId |-> candidateId,
     lastLogIndex |-> lastLogIdx, lastLogTerm |-> lastLogTerm, prevote |-> prevote]

RequestVoteRespMsg(term, voteGranted, requestTerm, prevote) ==
    [type |-> "RequestVoteResponse", term |-> term, voteGranted |-> voteGranted,
     requestTerm |-> requestTerm, prevote |-> prevote]

AppendEntriesMsg(term, leader, prevLogIdx, prevLogTerm, entries, leaderCommit, msgId) ==
    [type |-> "AppendEntries", term |-> term, leaderId |-> leader,
     prevLogIndex |-> prevLogIdx, prevLogTerm |-> prevLogTerm,
     entries |-> entries, leaderCommit |-> leaderCommit, msg_id |-> msgId]

AppendEntriesRespMsg(term, success, matchIndex, msgId) ==
    [type |-> "AppendEntriesResponse", term |-> term, success |-> success,
     current_idx |-> matchIndex, msg_id |-> msgId]

SnapshotMsg(term, leader, lastIdx, lastTerm) ==
    [type |-> "InstallSnapshot", term |-> term, leaderId |-> leader,
     lastIncludedIndex |-> lastIdx, lastIncludedTerm |-> lastTerm]

\* Initial state
Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> DefaultVote]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [l \in Server |-> [s \in Server |-> 1]]
    /\ matchIndex = [l \in Server |-> [s \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ leaderId = [s \in Server |-> Nil]
    /\ messages = {}
    /\ servers = Server
    /\ lastIncludedIndex = [s \in Server |-> 0]
    /\ lastIncludedTerm = [s \in Server |-> 0]
    /\ electionTimer = [s \in Server |-> 0]

\* State Transitions

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = DefaultVote]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, servers, lastIncludedIndex, lastIncludedTerm>>

StepDown(s, term) ==
    /\ state[s] # "Follower"
    /\ BecomeFollower(s, term)

\* Leader Election

ElectionTimeout(s) ==
    /\ s \in servers
    /\ state[s] \in {"Follower", "PreCandidate"}
    /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, messages, servers, lastIncludedIndex, lastIncludedTerm>>

BecomePreCandidate(s) ==
    /\ s \in servers
    /\ state[s] = "Follower"
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ LET newTerm == currentTerm[s] + 1
           req == RequestVoteMsg(newTerm, s, LastLogIndex(s), LastLogTerm(s), TRUE)
       IN messages' = messages \cup {[from |-> s, to |-> t, msg |-> req] : t \in servers \ {s}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, servers, lastIncludedIndex, lastIncludedTerm>>

BecomeCandidate(s) ==
    /\ s \in servers
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ LET newTerm == currentTerm[s] + 1
           req == RequestVoteMsg(newTerm, s, LastLogIndex(s), LastLogTerm(s), FALSE)
       IN messages' = messages \cup {[from |-> s, to |-> t, msg |-> req] : t \in servers \ {s}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, servers, lastIncludedIndex, lastIncludedTerm>>

RecvRequestVote(s, t, m) ==
    /\ m.msg.type = "RequestVote"
    /\ LET msg == m.msg
    /\ IF msg.term < currentTerm[t]
       THEN /\ LET resp == RequestVoteRespMsg(currentTerm[t], FALSE, msg.term, msg.prevote)
            IN messages' = (messages \ {m}) \cup {[from |-> t, to |-> s, msg |-> resp]}
            /\ UNCHANGED otherVars
       ELSE /\ LET higherTerm == msg.term > currentTerm[t]
                 votedForOK == votedFor[t] = DefaultVote \/ votedFor[t] = s
                 logOK == IsUpToDate(msg.lastLogTerm, msg.lastLogIndex, LastLogTerm(t), LastLogIndex(t))
                 grant == votedForOK /\ logOK
            /\ \/ /\ grant
                  /\ LET newTerm == IF higherTerm THEN msg.term ELSE currentTerm[t]
                         resp == RequestVoteRespMsg(newTerm, TRUE, msg.term, msg.prevote)
                  /\ messages' = (messages \ {m}) \cup {[from |-> t, to |-> s, msg |-> resp]}
                  /\ currentTerm' = [currentTerm EXCEPT ![t] = newTerm]
                  /\ state' = [state EXCEPT ![t] = IF state[t] # "Follower" \/ higherTerm THEN "Follower" ELSE state[t]]
                  /\ votedFor' = [votedFor EXCEPT ![t] = IF msg.prevote THEN votedFor[t] ELSE s]
                  /\ leaderId' = [leaderId EXCEPT ![t] = IF state'[t] = "Follower" THEN Nil ELSE leaderId[t]]
                  /\ electionTimer' = [electionTimer EXCEPT ![t] = 0]
                  /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, servers, lastIncludedIndex, lastIncludedTerm>>
               \/ /\ \lnot grant
                  /\ LET newTerm == IF higherTerm THEN msg.term ELSE currentTerm[t]
                         resp == RequestVoteRespMsg(newTerm, FALSE, msg.term, msg.prevote)
                  /\ messages' = (messages \ {m}) \cup {[from |-> t, to |-> s, msg |-> resp]}
                  /\ currentTerm' = [currentTerm EXCEPT ![t] = newTerm]
                  /\ state' = [state EXCEPT ![t] = IF state[t] # "Follower" \/ higherTerm THEN "Follower" ELSE state[t]]
                  /\ leaderId' = [leaderId EXCEPT ![t] = IF state'[t] = "Follower" THEN Nil ELSE leaderId[t]]
                  /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>

RecvRequestVoteResponse(s, t, m) ==
    /\ m.msg.type = "RequestVoteResponse"
    /\ LET msg == m.msg
    /\ IF msg.term > currentTerm[s]
       THEN /\ messages' = messages \ {m}
            /\ StepDown(s, msg.term)
       ELSE /\ \/ /\ \/ msg.term < currentTerm[s]
                     \/ (msg.prevote /\ state[s] # "PreCandidate")
                     \/ (\lnot msg.prevote /\ state[s] # "Candidate")
                     \/ (msg.prevote /\ msg.requestTerm # currentTerm[s] + 1)
                     \/ (\lnot msg.prevote /\ msg.requestTerm # currentTerm[s])
                  /\ messages' = messages \ {m}
                  /\ UNCHANGED otherVars
            \/ /\ msg.voteGranted
               /\ LET newVotes == votesGranted[s] \cup {t}
               /\ \/ /\ Cardinality(newVotes) < Quorum(servers)
                     /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                     /\ messages' = messages \ {m}
                     /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>
                  \/ /\ Cardinality(newVotes) >= Quorum(servers)
                     /\ \/ /\ state[s] = "PreCandidate"
                           /\ state' = [state EXCEPT ![s] = "Candidate"]
                           /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                           /\ votedFor' = [votedFor EXCEPT ![s] = s]
                           /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                           /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
                           /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                           /\ LET newTerm == currentTerm[s] + 1
                                  req == RequestVoteMsg(newTerm, s, LastLogIndex(s), LastLogTerm(s), FALSE)
                              IN messages' = (messages \ {m}) \cup {[from |-> s, to |-> peer, msg |-> req] : peer \in servers \ {s}}
                           /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, servers, lastIncludedIndex, lastIncludedTerm>>
                        \/ /\ state[s] = "Candidate"
                           /\ state' = [state EXCEPT ![s] = "Leader"]
                           /\ leaderId' = [leaderId EXCEPT ![s] = s]
                           /\ LET lastIdx == LastLogIndex(s)
                           /\ nextIndex' = [nextIndex EXCEPT ![s] = [peer \in servers |-> lastIdx + 1]]
                           /\ matchIndex' = [matchIndex EXCEPT ![s] = [peer \in servers |-> 0] WITH [s] = lastIdx]
                           /\ LET noop == [term |-> currentTerm[s], value |-> "NoOp"]
                           /\ log' = [log EXCEPT ![s] = Append(log[s], noop)]
                           /\ messages' = messages \ {m}
                           /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>
            \/ /\ \lnot msg.voteGranted
               /\ messages' = messages \ {m}
               /\ UNCHANGED otherVars

BecomeLeader(s) ==
    /\ s \in servers
    /\ state[s] = "Candidate"
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ LET lastIdx == LastLogIndex(s)
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in servers |-> lastIdx + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in servers |-> 0] WITH [s] = lastIdx]
    /\ LET noop == [term |-> currentTerm[s], value |-> "NoOp"]
    /\ log' = [log EXCEPT ![s] = Append(log[s], noop)]
    /\ messages' = messages
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>

\* Log Replication

RecvClientRequest(s, v) ==
    /\ s \in servers
    /\ state[s] = "Leader"
    /\ v \in Value \cup {[type |-> "AddNode", node |-> n] : n \in Server \ servers}
                 \cup {[type |-> "RemoveNode", node |-> n] : n \in servers \ {s}}
    /\ LET newEntry == [term |-> currentTerm[s], value |-> v]
    /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, messages, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>

SendAppendEntries(s, t) ==
    /\ s \in servers
    /\ t \in servers \ {s}
    /\ state[s] = "Leader"
    /\ LET prevIdx == nextIndex[s][t] - 1
    /\ \/ /\ prevIdx >= lastIncludedIndex[s]
          /\ LET prevTerm == IF prevIdx > lastIncludedIndex[s] THEN log[s][prevIdx - lastIncludedIndex[s]].term ELSE lastIncludedTerm[s]
                 entries == SubSeq(log[s], prevIdx - lastIncludedIndex[s] + 1, Len(log[s]))
                 msg == AppendEntriesMsg(currentTerm[s], s, prevIdx, prevTerm, entries, commitIndex[s], 0)
          /\ messages' = messages \cup {[from |-> s, to |-> t, msg |-> msg]}
          /\ UNCHANGED otherVars
       \/ /\ prevIdx < lastIncludedIndex[s]
          /\ LET msg == SnapshotMsg(currentTerm[s], s, lastIncludedIndex[s], lastIncludedTerm[s])
          /\ messages' = messages \cup {[from |-> s, to |-> t, msg |-> msg]}
          /\ UNCHANGED otherVars

PeriodicHeartbeat(s) ==
    /\ s \in servers
    /\ state[s] = "Leader"
    /\ LET req(t) ==
        LET prevIdx == nextIndex[s][t] - 1 IN
        IF prevIdx >= lastIncludedIndex[s] THEN
            LET prevTerm == IF prevIdx > lastIncludedIndex[s] THEN log[s][prevIdx - lastIncludedIndex[s]].term ELSE lastIncludedTerm[s]
            IN AppendEntriesMsg(currentTerm[s], s, prevIdx, prevTerm, <<>>, commitIndex[s], 0)
        ELSE
            SnapshotMsg(currentTerm[s], s, lastIncludedIndex[s], lastIncludedTerm[s])
    /\ messages' = messages \cup {[from |-> s, to |-> t, msg |-> req(t)] : t \in servers \ {s}}
    /\ UNCHANGED otherVars

RecvAppendEntries(s, t, m) ==
    /\ m.msg.type = "AppendEntries"
    /\ LET msg == m.msg
    /\ \/ /\ msg.term < currentTerm[t]
          /\ LET resp == AppendEntriesRespMsg(currentTerm[t], FALSE, 0, msg.msg_id)
          /\ messages' = (messages \ {m}) \cup {[from |-> t, to |-> s, msg |-> resp]}
          /\ UNCHANGED otherVars
       \/ /\ msg.term >= currentTerm[t]
          /\ LET newTerm == msg.term
                 logOK == \/ msg.prevLogIndex = lastIncludedIndex[t] /\ msg.prevLogTerm = lastIncludedTerm[t]
                           \/ /\ msg.prevLogIndex > lastIncludedIndex[t]
                              /\ msg.prevLogIndex <= LastLogIndex(t)
                              /\ log[t][msg.prevLogIndex - lastIncludedIndex[t]].term = msg.prevLogTerm
          /\ \/ /\ \lnot logOK
                /\ LET resp == AppendEntriesRespMsg(newTerm, FALSE, LastLogIndex(t), msg.msg_id)
                /\ messages' = (messages \ {m}) \cup {[from |-> t, to |-> s, msg |-> resp]}
                /\ currentTerm' = [currentTerm EXCEPT ![t] = newTerm]
                /\ state' = [state EXCEPT ![t] = "Follower"]
                /\ leaderId' = [leaderId EXCEPT ![t] = s]
                /\ electionTimer' = [electionTimer EXCEPT ![t] = 0]
                /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, servers, lastIncludedIndex, lastIncludedTerm>>
             \/ /\ logOK
                /\ LET conflicting_indices == { i \in 1..Len(msg.entries) :
                                                  (msg.prevLogIndex + i <= LastLogIndex(t)) /\
                                                  (log[t][msg.prevLogIndex + i - lastIncludedIndex[t]].term # msg.entries[i].term) }
                /\ LET prefix ==
                       IF conflicting_indices = {} THEN
                           SubSeq(log[t], 1, msg.prevLogIndex - lastIncludedIndex[t])
                       ELSE
                           LET conflictIndex == Min(conflicting_indices)
                           IN SubSeq(log[t], 1, msg.prevLogIndex + conflictIndex - 1 - lastIncludedIndex[t])
                /\ LET newLog == prefix \o msg.entries
                /\ log' = [log EXCEPT ![t] = newLog]
                /\ LET newLastIdx == Len(newLog) + lastIncludedIndex[t]
                /\ commitIndex' = [commitIndex EXCEPT ![t] = Max({commitIndex[t], Min({msg.leaderCommit, newLastIdx})})]
                /\ LET resp == AppendEntriesRespMsg(newTerm, TRUE, msg.prevLogIndex + Len(msg.entries), msg.msg_id)
                /\ messages' = (messages \ {m}) \cup {[from |-> t, to |-> s, msg |-> resp]}
                /\ currentTerm' = [currentTerm EXCEPT ![t] = newTerm]
                /\ state' = [state EXCEPT ![t] = "Follower"]
                /\ leaderId' = [leaderId EXCEPT ![t] = s]
                /\ electionTimer' = [electionTimer EXCEPT ![t] = 0]
                /\ UNCHANGED <<votedFor, lastApplied, nextIndex, matchIndex, votesGranted, servers, lastIncludedIndex, lastIncludedTerm>>

RecvAppendEntriesResponse(s, t, m) ==
    /\ m.msg.type = "AppendEntriesResponse"
    /\ LET msg == m.msg
    /\ messages' = messages \ {m}
    /\ IF msg.term > currentTerm[s]
       THEN /\ StepDown(s, msg.term)
       ELSE /\ IF state[s] = "Leader" /\ msg.term = currentTerm[s]
              THEN /\ \/ /\ msg.success
                         /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![t] = msg.current_idx + 1]]
                         /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![t] = msg.current_idx]]
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, leaderId, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>
                      \/ /\ \lnot msg.success
                         /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![t] = Max({1, msg.current_idx + 1})]]
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, matchIndex, votesGranted, leaderId, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>
              ELSE /\ UNCHANGED otherVars

AdvanceCommitIndex(s) ==
    /\ s \in servers
    /\ state[s] = "Leader"
    /\ LET matchIndices == {matchIndex[s][t] : t \in servers}
           replicatedIndices == {idx \in 1..LastLogIndex(s) | Cardinality({t \in servers | matchIndex[s][t] >= idx}) >= Quorum(servers)}
           newCommitIndex == IF replicatedIndices # {} THEN Max(replicatedIndices) ELSE commitIndex[s]
    /\ newCommitIndex > commitIndex[s]
    /\ LogTerm(log[s], newCommitIndex - lastIncludedIndex[s]) = currentTerm[s]
    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, messages, servers, lastIncludedIndex, lastIncludedTerm, electionTimer>>

Apply(s) ==
    /\ s \in servers
    /\ commitIndex[s] > lastApplied[s]
    /\ LET applyIdx == lastApplied[s] + 1
    /\ lastApplied' = [lastApplied EXCEPT ![s] = applyIdx]
    /\ LET entry == log[s][applyIdx - lastIncludedIndex[s]].value
    /\ servers' = IF DOMAIN entry = {"type", "node"} /\ entry.type = "AddNode" THEN servers \cup {entry.node}
                  ELSE IF DOMAIN entry = {"type", "node"} /\ entry.type = "RemoveNode" THEN servers \ {entry.node}
                  ELSE servers
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, leaderId, messages, lastIncludedIndex, lastIncludedTerm, electionTimer>>

\* Snapshotting

BeginSnapshot(s, idx) ==
    /\ s \in servers
    /\ state[s] = "Leader"
    /\ idx > lastIncludedIndex[s]
    /\ idx <= commitIndex[s]
    /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = idx]
    /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = log[s][idx - lastIncludedIndex[s]].term]
    /\ log' = [log EXCEPT ![s] = SubSeq(log[s], idx - lastIncludedIndex[s] + 1, Len(log[s]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, messages, servers, electionTimer>>

RecvSnapshot(s, t, m) ==
    /\ m.msg.type = "InstallSnapshot"
    /\ LET msg == m.msg
    /\ messages' = messages \ {m}
    /\ IF msg.term < currentTerm[t]
       THEN UNCHANGED otherVars
       ELSE /\ currentTerm' = [currentTerm EXCEPT ![t] = Max({currentTerm[t], msg.term})]
            /\ state' = [state EXCEPT ![t] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![t] = s]
            /\ electionTimer' = [electionTimer EXCEPT ![t] = 0]
            /\ IF msg.lastIncludedIndex > lastIncludedIndex[t]
               THEN /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![t] = msg.lastIncludedIndex]
                    /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![t] = msg.lastIncludedTerm]
                    /\ commitIndex' = [commitIndex EXCEPT ![t] = Max({commitIndex[t], msg.lastIncludedIndex})]
                    /\ lastApplied' = [lastApplied EXCEPT ![t] = Max({lastApplied[t], msg.lastIncludedIndex})]
                    /\ LET matching_indices == { i \in 1..Len(log[t]) :
                                                   (i + lastIncludedIndex[t] = msg.lastIncludedIndex) /\
                                                   (log[t][i].term = msg.lastIncludedTerm) }
                    /\ log' = [log EXCEPT ![t] = IF matching_indices # {}
                                                THEN LET idx = CHOOSE i \in matching_indices IN i
                                                     IN SubSeq(log[t], idx + 1, Len(log[t]))
                                                ELSE <<>>]
                    /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votesGranted, servers>>
               ELSE UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, servers, lastIncludedIndex, lastIncludedTerm>>

\* Overall Next State Relation
Next ==
    \/ \E s \in servers: ElectionTimeout(s)
    \/ \E s \in servers: BecomePreCandidate(s)
    \/ \E s \in servers: BecomeCandidate(s)
    \/ \E s, t \in servers, m \in messages:
        m.from = s /\ m.to = t /\ RecvRequestVote(s, t, m)
    \/ \E s, t \in servers, m \in messages:
        m.from = t /\ m.to = s /\ RecvRequestVoteResponse(s, t, m)
    \/ \E s \in servers, v \in Value \cup {[type |-> "AddNode", node |-> n] : n \in Server} \cup {[type |-> "RemoveNode", node |-> n] : n \in Server}:
        RecvClientRequest(s, v)
    \/ \E s, t \in servers: SendAppendEntries(s, t)
    \/ \E s \in servers: PeriodicHeartbeat(s)
    \/ \E s, t \in servers, m \in messages:
        m.from = s /\ m.to = t /\ RecvAppendEntries(s, t, m)
    \/ \E s, t \in servers, m \in messages:
        m.from = t /\ m.to = s /\ RecvAppendEntriesResponse(s, t, m)
    \/ \E s \in servers: AdvanceCommitIndex(s)
    \/ \E s \in servers: Apply(s)
    \/ \E s \in servers, idx \in (lastIncludedIndex[s]+1)..commitIndex[s]: BeginSnapshot(s, idx)
    \/ \E s, t \in servers, m \in messages:
        m.from = s /\ m.to = t /\ RecvSnapshot(s, t, m)

====
