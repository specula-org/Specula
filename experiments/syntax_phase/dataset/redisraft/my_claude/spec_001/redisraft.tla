---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, MaxTerm, MaxLogLen

VARIABLES
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    state,
    nextIndex,
    matchIndex,
    votesReceived,
    electionTimeout,
    heartbeatTimeout,
    snapshotLastIndex,
    snapshotLastTerm,
    messages

vars == <<currentTerm, votedFor, log, commitIndex, lastApplied, state, 
          nextIndex, matchIndex, votesReceived, electionTimeout, 
          heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, messages>>

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}

Message == [type: {"RequestVote", "RequestVoteResponse", "AppendEntries", 
                   "AppendEntriesResponse", "InstallSnapshot", "InstallSnapshotResponse"},
            term: Nat,
            source: Nodes,
            dest: Nodes]

LogEntry == [term: Nat, index: Nat, type: {"NORMAL", "CONFIG_ADD", "CONFIG_REMOVE"}]

TypeOK ==
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {Nil}]
    /\ log \in [Nodes -> Seq(LogEntry)]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ state \in [Nodes -> NodeStates]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ votesReceived \in [Nodes -> SUBSET Nodes]
    /\ electionTimeout \in [Nodes -> BOOLEAN]
    /\ heartbeatTimeout \in [Nodes -> BOOLEAN]
    /\ snapshotLastIndex \in [Nodes -> Nat]
    /\ snapshotLastTerm \in [Nodes -> Nat]
    /\ messages \subseteq Message

Init ==
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ state = [n \in Nodes |-> "FOLLOWER"]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votesReceived = [n \in Nodes |-> {}]
    /\ electionTimeout = [n \in Nodes |-> FALSE]
    /\ heartbeatTimeout = [n \in Nodes |-> FALSE]
    /\ snapshotLastIndex = [n \in Nodes |-> 0]
    /\ snapshotLastTerm = [n \in Nodes |-> 0]
    /\ messages = {}

LastLogIndex(n) == Len(log[n]) + snapshotLastIndex[n]

LastLogTerm(n) == 
    IF Len(log[n]) = 0 
    THEN snapshotLastTerm[n]
    ELSE log[n][Len(log[n])].term

GetLogTerm(n, i) ==
    IF i = 0 THEN 0
    ELSE IF i <= snapshotLastIndex[n] THEN snapshotLastTerm[n]
    ELSE log[n][i - snapshotLastIndex[n]].term

IsQuorum(S) == Cardinality(S) * 2 > Cardinality(Nodes)

BecomeFollower(n, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = FALSE]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {}]

BecomePreCandidate(n) ==
    /\ state[n] = "FOLLOWER"
    /\ electionTimeout[n] = TRUE
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ LET msg == [type |-> "RequestVote",
                   term |-> currentTerm[n] + 1,
                   source |-> n,
                   dest |-> m,
                   candidateId |-> n,
                   lastLogIndex |-> LastLogIndex(n),
                   lastLogTerm |-> LastLogTerm(n),
                   prevote |-> TRUE]
       IN messages' = messages \cup {msg : m \in Nodes \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, 
                   snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(n) ==
    /\ \/ /\ state[n] = "FOLLOWER"
          /\ electionTimeout[n] = TRUE
       \/ /\ state[n] = "PRECANDIDATE"
          /\ IsQuorum(votesReceived[n])
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ LET msg == [type |-> "RequestVote",
                   term |-> currentTerm[n] + 1,
                   source |-> n,
                   dest |-> m,
                   candidateId |-> n,
                   lastLogIndex |-> LastLogIndex(n),
                   lastLogTerm |-> LastLogTerm(n),
                   prevote |-> FALSE]
       IN messages' = messages \cup {msg : m \in Nodes \ {n}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ IsQuorum(votesReceived[n])
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> LastLogIndex(n) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = TRUE]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   snapshotLastIndex, snapshotLastTerm, messages>>

ElectionTimeout(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   state, nextIndex, matchIndex, votesReceived,
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, messages>>

HeartbeatTimeout(n) ==
    /\ state[n] = "LEADER"
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   state, nextIndex, matchIndex, votesReceived,
                   electionTimeout, snapshotLastIndex, snapshotLastTerm, messages>>

SendAppendEntries(n, m) ==
    /\ state[n] = "LEADER"
    /\ heartbeatTimeout[n] = TRUE
    /\ m \in Nodes \ {n}
    /\ LET prevLogIndex == nextIndex[n][m] - 1
           prevLogTerm == GetLogTerm(n, prevLogIndex)
           entries == IF nextIndex[n][m] <= LastLogIndex(n)
                      THEN SubSeq(log[n], 
                                  Max(1, nextIndex[n][m] - snapshotLastIndex[n]),
                                  Len(log[n]))
                      ELSE <<>>
           msg == [type |-> "AppendEntries",
                   term |-> currentTerm[n],
                   source |-> n,
                   dest |-> m,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entries,
                   leaderCommit |-> commitIndex[n]]
       IN messages' = messages \cup {msg}
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   state, nextIndex, matchIndex, votesReceived,
                   electionTimeout, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVote(m) ==
    /\ \E msg \in messages :
        /\ msg.type = "RequestVote"
        /\ msg.dest = m
        /\ LET n == msg.source
               prevote == IF "prevote" \in DOMAIN msg THEN msg.prevote ELSE FALSE
               grant == /\ msg.term >= currentTerm[m]
                        /\ \/ votedFor[m] = Nil
                           \/ votedFor[m] = n
                           \/ prevote
                        /\ \/ msg.lastLogTerm > LastLogTerm(m)
                           \/ /\ msg.lastLogTerm = LastLogTerm(m)
                              /\ msg.lastLogIndex >= LastLogIndex(m)
               response == [type |-> "RequestVoteResponse",
                           term |-> IF msg.term > currentTerm[m] THEN msg.term ELSE currentTerm[m],
                           source |-> m,
                           dest |-> n,
                           voteGranted |-> grant,
                           prevote |-> prevote]
           IN /\ IF msg.term > currentTerm[m]
                 THEN BecomeFollower(m, msg.term)
                 ELSE /\ IF grant /\ ~prevote
                         THEN votedFor' = [votedFor EXCEPT ![m] = n]
                         ELSE UNCHANGED votedFor
                      /\ UNCHANGED <<currentTerm, state, electionTimeout, 
                                     heartbeatTimeout, votesReceived>>
              /\ messages' = (messages \ {msg}) \cup {response}
              /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, 
                             matchIndex, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVoteResponse(n) ==
    /\ \E msg \in messages :
        /\ msg.type = "RequestVoteResponse"
        /\ msg.dest = n
        /\ LET m == msg.source
               prevote == IF "prevote" \in DOMAIN msg THEN msg.prevote ELSE FALSE
           IN /\ IF msg.term > currentTerm[n]
                 THEN BecomeFollower(n, msg.term)
                 ELSE /\ IF msg.voteGranted
                         THEN votesReceived' = [votesReceived EXCEPT ![n] = @ \cup {m}]
                         ELSE UNCHANGED votesReceived
                      /\ UNCHANGED <<currentTerm, votedFor, state, electionTimeout,
                                     heartbeatTimeout>>
              /\ messages' = messages \ {msg}
              /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex,
                             matchIndex, snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntries(m) ==
    /\ \E msg \in messages :
        /\ msg.type = "AppendEntries"
        /\ msg.dest = m
        /\ LET n == msg.source
               logOk == \/ msg.prevLogIndex = 0
                        \/ /\ msg.prevLogIndex <= LastLogIndex(m)
                           /\ GetLogTerm(m, msg.prevLogIndex) = msg.prevLogTerm
               success == /\ msg.term >= currentTerm[m]
                          /\ logOk
               response == [type |-> "AppendEntriesResponse",
                           term |-> IF msg.term > currentTerm[m] THEN msg.term ELSE currentTerm[m],
                           source |-> m,
                           dest |-> n,
                           success |-> success,
                           matchIndex |-> IF success 
                                         THEN msg.prevLogIndex + Len(msg.entries)
                                         ELSE 0]
           IN /\ IF msg.term > currentTerm[m]
                 THEN BecomeFollower(m, msg.term)
                 ELSE /\ IF msg.term = currentTerm[m]
                         THEN /\ state' = [state EXCEPT ![m] = "FOLLOWER"]
                              /\ electionTimeout' = [electionTimeout EXCEPT ![m] = FALSE]
                         ELSE UNCHANGED <<state, electionTimeout>>
                      /\ UNCHANGED <<currentTerm, votedFor, heartbeatTimeout, votesReceived>>
              /\ IF success /\ Len(msg.entries) > 0
                 THEN /\ log' = [log EXCEPT ![m] = 
                                   SubSeq(@, 1, Max(0, msg.prevLogIndex - snapshotLastIndex[m])) 
                                   \o msg.entries]
                      /\ commitIndex' = [commitIndex EXCEPT ![m] = 
                                          Min(msg.leaderCommit, LastLogIndex(m))]
                 ELSE UNCHANGED <<log, commitIndex>>
              /\ messages' = (messages \ {msg}) \cup {response}
              /\ UNCHANGED <<lastApplied, nextIndex, matchIndex,
                             snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntriesResponse(n) ==
    /\ \E msg \in messages :
        /\ msg.type = "AppendEntriesResponse"
        /\ msg.dest = n
        /\ state[n] = "LEADER"
        /\ LET m == msg.source
           IN /\ IF msg.term > currentTerm[n]
                 THEN BecomeFollower(n, msg.term)
                 ELSE /\ IF msg.success
                         THEN /\ nextIndex' = [nextIndex EXCEPT ![n][m] = msg.matchIndex + 1]
                              /\ matchIndex' = [matchIndex EXCEPT ![n][m] = msg.matchIndex]
                         ELSE /\ nextIndex' = [nextIndex EXCEPT ![n][m] = Max(1, @[m] - 1)]
                              /\ UNCHANGED matchIndex
                      /\ UNCHANGED <<currentTerm, votedFor, state, electionTimeout,
                                     heartbeatTimeout, votesReceived>>
              /\ messages' = messages \ {msg}
              /\ UNCHANGED <<log, commitIndex, lastApplied,
                             snapshotLastIndex, snapshotLastTerm>>

LogAppend(n, entry) ==
    /\ state[n] = "LEADER"
    /\ Len(log[n]) < MaxLogLen
    /\ LET newEntry == [term |-> currentTerm[n], 
                        index |-> LastLogIndex(n) + 1,
                        type |-> entry.type]
       IN log' = [log EXCEPT ![n] = Append(@, newEntry)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied,
                   state, nextIndex, matchIndex, votesReceived,
                   electionTimeout, heartbeatTimeout, snapshotLastIndex,
                   snapshotLastTerm, messages>>

UpdateCommitIndex(n) ==
    /\ state[n] = "LEADER"
    /\ LET indices == {i \in 1..LastLogIndex(n) : 
                        /\ i > commitIndex[n]
                        /\ GetLogTerm(n, i) = currentTerm[n]
                        /\ IsQuorum({m \in Nodes : matchIndex[n][m] >= i})}
       IN /\ indices # {}
          /\ commitIndex' = [commitIndex EXCEPT ![n] = Max(indices)]
    /\ UNCHANGED <<currentTerm, votedFor, log, lastApplied, state,
                   nextIndex, matchIndex, votesReceived, electionTimeout,
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, messages>>

ApplyLog(n) ==
    /\ lastApplied[n] < commitIndex[n]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state,
                   nextIndex, matchIndex, votesReceived, electionTimeout,
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, messages>>

BeginSnapshot(n) ==
    /\ lastApplied[n] > snapshotLastIndex[n]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = lastApplied[n]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = 
                             GetLogTerm(n, lastApplied[n])]
    /\ log' = [log EXCEPT ![n] = <<>>]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, state,
                   nextIndex, matchIndex, votesReceived, electionTimeout,
                   heartbeatTimeout, messages>>

Next ==
    \/ \E n \in Nodes : BecomePreCandidate(n)
    \/ \E n \in Nodes : BecomeCandidate(n)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E n \in Nodes : ElectionTimeout(n)
    \/ \E n \in Nodes : HeartbeatTimeout(n)
    \/ \E n, m \in Nodes : SendAppendEntries(n, m)
    \/ \E n \in Nodes : RecvRequestVote(n)
    \/ \E n \in Nodes : RecvRequestVoteResponse(n)
    \/ \E n \in Nodes : RecvAppendEntries(n)
    \/ \E n \in Nodes : RecvAppendEntriesResponse(n)
    \/ \E n \in Nodes, entry \in [type: {"NORMAL", "CONFIG_ADD", "CONFIG_REMOVE"}] : 
         LogAppend(n, entry)
    \/ \E n \in Nodes : UpdateCommitIndex(n)
    \/ \E n \in Nodes : ApplyLog(n)
    \/ \E n \in Nodes : BeginSnapshot(n)

Spec == Init /\ [][Next]_vars

====