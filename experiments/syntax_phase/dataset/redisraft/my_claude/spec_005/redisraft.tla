---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, MaxTerm, MaxLogLen

VARIABLES
    currentTerm,
    state,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    electionTimeout,
    heartbeatTimeout,
    messages,
    snapshotLastIndex,
    snapshotLastTerm,
    votingConfigChangeIndex

vars == <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, electionTimeout, heartbeatTimeout, 
          messages, snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

States == {"Follower", "PreCandidate", "Candidate", "Leader"}

MessageTypes == {"RequestVoteRequest", "RequestVoteResponse", 
                 "AppendEntriesRequest", "AppendEntriesResponse",
                 "SnapshotRequest", "SnapshotResponse"}

LogEntryTypes == {"Normal", "AddNode", "RemoveNode", "NoOp"}

Message == [type: MessageTypes, term: Nat, source: Servers, dest: Servers]

LogEntry == [term: Nat, type: LogEntryTypes, data: STRING]

TypeOK ==
    /\ currentTerm \in [Servers -> Nat]
    /\ state \in [Servers -> States]
    /\ votedFor \in [Servers -> Servers \cup {Null}]
    /\ log \in [Servers -> Seq(LogEntry)]
    /\ commitIndex \in [Servers -> Nat]
    /\ lastApplied \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ electionTimeout \in [Servers -> BOOLEAN]
    /\ heartbeatTimeout \in [Servers -> BOOLEAN]
    /\ messages \subseteq Message
    /\ snapshotLastIndex \in [Servers -> Nat]
    /\ snapshotLastTerm \in [Servers -> Nat]
    /\ votingConfigChangeIndex \in [Servers -> Int]

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ state = [s \in Servers |-> "Follower"]
    /\ votedFor = [s \in Servers |-> Null]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ lastApplied = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ electionTimeout = [s \in Servers |-> FALSE]
    /\ heartbeatTimeout = [s \in Servers |-> FALSE]
    /\ messages = {}
    /\ snapshotLastIndex = [s \in Servers |-> 0]
    /\ snapshotLastTerm = [s \in Servers |-> 0]
    /\ votingConfigChangeIndex = [s \in Servers |-> -1]

LastLogIndex(s) == Len(log[s])

LastLogTerm(s) == 
    IF LastLogIndex(s) = 0 
    THEN snapshotLastTerm[s]
    ELSE log[s][LastLogIndex(s)].term

IsUpToDate(s, lastLogTerm, lastLogIndex) ==
    \/ lastLogTerm > LastLogTerm(s)
    \/ /\ lastLogTerm = LastLogTerm(s)
       /\ lastLogIndex >= LastLogIndex(s)

VotingNodes == Servers

QuorumSize == (Cardinality(VotingNodes) \div 2) + 1

HasQuorum(votes) == Cardinality(votes) >= QuorumSize

BecomeFollower(s, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![s] = Null]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]

BecomePreCandidate(s) ==
    /\ state[s] = "Follower"
    /\ electionTimeout[s] = TRUE
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, messages,
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

BecomeCandidate(s) ==
    /\ \/ /\ state[s] = "Follower"
          /\ electionTimeout[s] = TRUE
       \/ /\ state[s] = "PreCandidate"
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   heartbeatTimeout, messages, snapshotLastIndex, 
                   snapshotLastTerm, votingConfigChangeIndex>>

BecomeLeader(s) ==
    /\ state[s] = "Candidate"
    /\ LET votes == {t \in VotingNodes : 
                        /\ \E m \in messages : 
                           /\ m.type = "RequestVoteResponse"
                           /\ m.source = t
                           /\ m.dest = s
                           /\ m.term = currentTerm[s]} \cup {s}
       IN HasQuorum(votes)
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = 
                        [t \in Servers |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = 
                         [t \in Servers |-> IF t = s THEN LastLogIndex(s) ELSE 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   electionTimeout, messages, snapshotLastIndex, 
                   snapshotLastTerm, votingConfigChangeIndex>>

ElectionTimeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, messages,
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

HeartbeatTimeout(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, messages,
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

SendRequestVote(s, t) ==
    /\ state[s] \in {"PreCandidate", "Candidate"}
    /\ s # t
    /\ LET term == IF state[s] = "PreCandidate" 
                   THEN currentTerm[s] + 1 
                   ELSE currentTerm[s]
           msg == [type |-> "RequestVoteRequest",
                   term |-> term,
                   source |-> s,
                   dest |-> t,
                   candidateId |-> s,
                   lastLogIndex |-> LastLogIndex(s),
                   lastLogTerm |-> LastLogTerm(s),
                   prevote |-> state[s] = "PreCandidate"]
       IN messages' = messages \cup {msg}
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

RecvRequestVote(s, m) ==
    /\ m.type = "RequestVoteRequest"
    /\ m.dest = s
    /\ LET grant == /\ m.term >= currentTerm[s]
                    /\ \/ votedFor[s] = Null
                       \/ votedFor[s] = m.candidateId
                    /\ IsUpToDate(s, m.lastLogTerm, m.lastLogIndex)
           response == [type |-> "RequestVoteResponse",
                        term |-> IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s],
                        source |-> s,
                        dest |-> m.source,
                        voteGranted |-> grant,
                        prevote |-> m.prevote]
       IN /\ messages' = (messages \ {m}) \cup {response}
          /\ IF m.term > currentTerm[s]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                  /\ state' = [state EXCEPT ![s] = "Follower"]
                  /\ votedFor' = [votedFor EXCEPT ![s] = IF grant THEN m.candidateId ELSE Null]
             ELSE /\ IF grant /\ ~m.prevote
                     THEN votedFor' = [votedFor EXCEPT ![s] = m.candidateId]
                     ELSE UNCHANGED votedFor
                  /\ UNCHANGED <<currentTerm, state>>
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   electionTimeout, heartbeatTimeout, snapshotLastIndex, 
                   snapshotLastTerm, votingConfigChangeIndex>>

RecvRequestVoteResponse(s, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ m.dest = s
    /\ state[s] \in {"PreCandidate", "Candidate"}
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE /\ messages' = messages \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, 
                           lastApplied, nextIndex, matchIndex, electionTimeout,
                           heartbeatTimeout, snapshotLastIndex, snapshotLastTerm,
                           votingConfigChangeIndex>>

SendAppendEntries(s, t) ==
    /\ state[s] = "Leader"
    /\ s # t
    /\ LET prevLogIndex == nextIndex[s][t] - 1
           prevLogTerm == IF prevLogIndex = 0 
                          THEN snapshotLastTerm[s]
                          ELSE IF prevLogIndex <= Len(log[s])
                               THEN log[s][prevLogIndex].term
                               ELSE 0
           entries == IF nextIndex[s][t] <= Len(log[s])
                      THEN SubSeq(log[s], nextIndex[s][t], Len(log[s]))
                      ELSE <<>>
           msg == [type |-> "AppendEntriesRequest",
                   term |-> currentTerm[s],
                   source |-> s,
                   dest |-> t,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entries,
                   leaderCommit |-> commitIndex[s]]
       IN messages' = messages \cup {msg}
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

RecvAppendEntries(s, m) ==
    /\ m.type = "AppendEntriesRequest"
    /\ m.dest = s
    /\ LET success == /\ m.term >= currentTerm[s]
                      /\ \/ m.prevLogIndex = 0
                         \/ /\ m.prevLogIndex <= Len(log[s])
                            /\ log[s][m.prevLogIndex].term = m.prevLogTerm
           response == [type |-> "AppendEntriesResponse",
                        term |-> IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s],
                        source |-> s,
                        dest |-> m.source,
                        success |-> success,
                        matchIndex |-> IF success 
                                       THEN m.prevLogIndex + Len(m.entries)
                                       ELSE 0]
       IN /\ messages' = (messages \ {m}) \cup {response}
          /\ IF m.term > currentTerm[s]
             THEN BecomeFollower(s, m.term)
             ELSE /\ IF success /\ Len(m.entries) > 0
                     THEN /\ log' = [log EXCEPT ![s] = 
                                        SubSeq(log[s], 1, m.prevLogIndex) \o m.entries]
                          /\ commitIndex' = [commitIndex EXCEPT ![s] = 
                                               Min(m.leaderCommit, Len(log'[s]))]
                     ELSE /\ IF success
                             THEN commitIndex' = [commitIndex EXCEPT ![s] = 
                                                    Min(m.leaderCommit, Len(log[s]))]
                             ELSE UNCHANGED commitIndex
                          /\ UNCHANGED log
                  /\ UNCHANGED <<currentTerm, state, votedFor>>
    /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, electionTimeout,
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm,
                   votingConfigChangeIndex>>

RecvAppendEntriesResponse(s, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ m.dest = s
    /\ state[s] = "Leader"
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE /\ messages' = messages \ {m}
            /\ IF m.success
               THEN /\ nextIndex' = [nextIndex EXCEPT ![s][m.source] = m.matchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![s][m.source] = m.matchIndex]
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.source] = 
                                       Max(nextIndex[s][m.source] - 1, 1)]
                    /\ UNCHANGED matchIndex
            /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                           lastApplied, electionTimeout, heartbeatTimeout,
                           snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

ClientRequest(s, entry) ==
    /\ state[s] = "Leader"
    /\ Len(log[s]) < MaxLogLen
    /\ LET newEntry == [term |-> currentTerm[s], 
                        type |-> entry.type,
                        data |-> entry.data]
       IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm, 
                   votingConfigChangeIndex>>

UpdateCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET indices == {matchIndex[s][t] : t \in VotingNodes}
           sortedIndices == CHOOSE seq \in Seq(indices) : 
                              /\ Len(seq) = Cardinality(indices)
                              /\ \A i \in 1..Len(seq)-1 : seq[i] >= seq[i+1]
           newCommitIndex == sortedIndices[QuorumSize]
       IN /\ newCommitIndex > commitIndex[s]
          /\ newCommitIndex <= Len(log[s])
          /\ log[s][newCommitIndex].term = currentTerm[s]
          /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm,
                   votingConfigChangeIndex>>

ApplyEntry(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm,
                   votingConfigChangeIndex>>

BeginSnapshot(s) ==
    /\ lastApplied[s] > snapshotLastIndex[s]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = lastApplied[s]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = 
                              IF lastApplied[s] <= Len(log[s])
                              THEN log[s][lastApplied[s]].term
                              ELSE snapshotLastTerm[s]]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votingConfigChangeIndex>>

EndSnapshot(s) ==
    /\ snapshotLastIndex[s] > 0
    /\ log' = [log EXCEPT ![s] = SubSeq(log[s], snapshotLastIndex[s] + 1, Len(log[s]))]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm,
                   votingConfigChangeIndex>>

AddNode(s, newNode) ==
    /\ state[s] = "Leader"
    /\ newNode \notin Servers
    /\ votingConfigChangeIndex[s] = -1
    /\ LET entry == [term |-> currentTerm[s], 
                     type |-> "AddNode",
                     data |-> ToString(newNode)]
       IN /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
          /\ votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![s] = Len(log'[s])]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm>>

RemoveNode(s, nodeToRemove) ==
    /\ state[s] = "Leader"
    /\ nodeToRemove \in Servers
    /\ nodeToRemove # s
    /\ votingConfigChangeIndex[s] = -1
    /\ LET entry == [term |-> currentTerm[s], 
                     type |-> "RemoveNode",
                     data |-> ToString(nodeToRemove)]
       IN /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
          /\ votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![s] = Len(log'[s])]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm>>

ApplyConfigChange(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ lastApplied[s] + 1 <= Len(log[s])
    /\ log[s][lastApplied[s] + 1].type \in {"AddNode", "RemoveNode"}
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ IF votingConfigChangeIndex[s] = lastApplied'[s]
       THEN votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![s] = -1]
       ELSE UNCHANGED votingConfigChangeIndex
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, snapshotLastIndex, snapshotLastTerm>>

Next ==
    \/ \E s \in Servers : ElectionTimeout(s)
    \/ \E s \in Servers : HeartbeatTimeout(s)
    \/ \E s \in Servers : BecomePreCandidate(s)
    \/ \E s \in Servers : BecomeCandidate(s)
    \/ \E s \in Servers : BecomeLeader(s)
    \/ \E s, t \in Servers : SendRequestVote(s, t)
    \/ \E s \in Servers, m \in messages : RecvRequestVote(s, m)
    \/ \E s \in Servers, m \in messages : RecvRequestVoteResponse(s, m)
    \/ \E s, t \in Servers : SendAppendEntries(s, t)
    \/ \E s \in Servers, m \in messages : RecvAppendEntries(s, m)
    \/ \E s \in Servers, m \in messages : RecvAppendEntriesResponse(s, m)
    \/ \E s \in Servers, entry \in LogEntry : ClientRequest(s, entry)
    \/ \E s \in Servers : UpdateCommitIndex(s)
    \/ \E s \in Servers : ApplyEntry(s)
    \/ \E s \in Servers : ApplyConfigChange(s)
    \/ \E s \in Servers : BeginSnapshot(s)
    \/ \E s \in Servers : EndSnapshot(s)
    \/ \E s \in Servers, n \in Servers : AddNode(s, n)
    \/ \E s \in Servers, n \in Servers : RemoveNode(s, n)

Spec == Init /\ [][Next]_vars

====