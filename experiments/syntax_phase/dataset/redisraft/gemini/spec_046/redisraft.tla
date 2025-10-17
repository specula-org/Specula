---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Value, Nil

ASSUME Server \subseteq {"n1", "n2", "n3", "n4"}
ASSUME Value \subseteq {"v1", "v2"}

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nodes,
    leaderId,
    votesGranted,
    snapshot_last_idx,
    snapshot_last_term,
    nextIndex,
    matchIndex,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

TypeOK ==
    /\ state \in [Server -> {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \union {Nil}]
    /\ \A i \in Server: log[i] \in Seq({[term: Nat, command: Value \union {[type: {"ADD_NODE", "REMOVE_NODE"}, node: Server]}]})
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ \A i \in Server: nodes[i] \subseteq Server
    /\ leaderId \in [Server -> Server \union {Nil}]
    /\ \A i \in Server: votesGranted[i] \subseteq Server
    /\ snapshot_last_idx \in [Server -> Nat]
    /\ snapshot_last_term \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat \cup {-1}]]
    /\ matchIndex \in [Server -> [Server -> Nat \cup {-1}]]
    /\ messages \subseteq
        {[type: {"RequestVoteRequest", "RequestVoteResponse", "AppendEntriesRequest", "AppendEntriesResponse", "InstallSnapshotRequest"},
          src: Server,
          dest: Server,
          term: Nat] \cup UNION {
            {[type: "RequestVoteRequest", src: Server, dest: Server, term: Nat, lastLogIndex: Nat, lastLogTerm: Nat, prevote: BOOLEAN]},
            {[type: "RequestVoteResponse", src: Server, dest: Server, term: Nat, voteGranted: BOOLEAN, prevote: BOOLEAN]},
            {[type: "AppendEntriesRequest", src: Server, dest: Server, term: Nat, leaderId: Server, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq(@), leaderCommit: Nat]},
            {[type: "AppendEntriesResponse", src: Server, dest: Server, term: Nat, success: BOOLEAN, matchIndex: Nat]},
            {[type: "InstallSnapshotRequest", src: Server, dest: Server, term: Nat, leaderId: Server, lastIncludedIndex: Nat, lastIncludedTerm: Nat]}
        }}

\* Helper functions
IsMajority(i, votes) == Cardinality(votes) * 2 > Cardinality(nodes[i])

LastLogIndex(i) == IF Len(log[i]) = 0 THEN snapshot_last_idx[i] ELSE snapshot_last_idx[i] + Len(log[i])
LastLogTerm(i) == IF Len(log[i]) = 0 THEN snapshot_last_term[i] ELSE log[i][Len(log[i])].term

LogTerm(i, idx) ==
    IF idx = 0 THEN 0
    ELSE IF idx = snapshot_last_idx[i] THEN snapshot_last_term[i]
    ELSE IF idx < snapshot_last_idx[i] \/ idx > LastLogIndex(i) THEN -1
    ELSE log[i][idx - snapshot_last_idx[i]].term

\* Initial state
Init ==
    /\ state = [i \in Server |-> "FOLLOWER"]
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> Nil]
    /\ log = [i \in Server |-> << >>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ lastApplied = [i \in Server |-> 0]
    /\ nodes = [i \in Server |-> Server]
    /\ leaderId = [i \in Server |-> Nil]
    /\ votesGranted = [i \in Server |-> {}]
    /\ snapshot_last_idx = [i \in Server |-> 0]
    /\ snapshot_last_term = [i \in Server |-> 0]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ messages = {}

\* State Transitions
BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

BecomePreCandidate(i) ==
    /\ state[i] \in {"FOLLOWER", "CANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ messages' = messages \union
        {[type         |-> "RequestVoteRequest",
          src          |-> i,
          dest         |-> j,
          term         |-> currentTerm[i] + 1,
          lastLogIndex |-> LastLogIndex(i),
          lastLogTerm  |-> LastLogTerm(i),
          prevote      |-> TRUE]
         : j \in nodes[i] \ {i}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nodes, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

BecomeCandidate(i) ==
    /\ state[i] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ messages' = messages \union
        {[type         |-> "RequestVoteRequest",
          src          |-> i,
          dest         |-> j,
          term         |-> currentTerm[i] + 1,
          lastLogIndex |-> LastLogIndex(i),
          lastLogTerm  |-> LastLogTerm(i),
          prevote      |-> FALSE]
         : j \in nodes[i] \ {i}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

BecomeLeader(i) ==
    /\ state[i] = "CANDIDATE"
    /\ IsMajority(i, votesGranted[i])
    /\ state' = [state EXCEPT ![i] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastLogIndex(i) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nodes, votesGranted, snapshot_last_idx, snapshot_last_term, messages>>

\* Vote Processing
RecvRequestVote(i, m) ==
    /\ m.type = "RequestVoteRequest"
    /\ m.dest = i
    /\ LET
        lastLogOK == \/ m.lastLogTerm > LastLogTerm(i)
                     \/ /\ m.lastLogTerm = LastLogTerm(i)
                        /\ m.lastLogIndex >= LastLogIndex(i)
        grantVote == \/ m.term < currentTerm[i]
                       THEN FALSE
                     \/ m.prevote
                       THEN lastLogOK
                     \/ /\ m.term > currentTerm[i]
                        /\ lastLogOK
                     \/ /\ m.term = currentTerm[i]
                        /\ votedFor[i] \in {Nil, m.src}
                        /\ lastLogOK
       response == [type        |-> "RequestVoteResponse",
                    src         |-> i,
                    dest        |-> m.src,
                    term        |-> IF m.prevote THEN currentTerm[i] ELSE m.term,
                    voteGranted |-> grantVote,
                    prevote     |-> m.prevote]
    IN
    /\ IF m.term > currentTerm[i] /\ \lnot m.prevote
       THEN /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grantVote THEN m.src ELSE Nil]
       ELSE /\ votedFor' = [votedFor EXCEPT ![i] = IF grantVote /\ \lnot m.prevote THEN m.src ELSE votedFor[i]]
            /\ UNCHANGED <<state, currentTerm>>
    /\ messages' = (messages \ {m}) \cup {response}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

RecvRequestVoteResponse(i, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ m.dest = i
    /\ IF m.term > currentTerm[i]
       THEN /\ BecomeFollower(i, m.term)
            /\ messages' = messages \ {m}
       ELSE /\ IF m.voteGranted
               THEN /\ \/ /\ state[i] = "PRECANDIDATE"
                           /\ m.prevote
                           /\ m.term = currentTerm[i] + 1
                           /\ (LET newVotes == votesGranted[i] \cup {m.src}
                              IN  /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                                  /\ IF IsMajority(i, newVotes)
                                     THEN BecomeCandidate(i)
                                     ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>)
                        \/ /\ state[i] = "CANDIDATE"
                           /\ \lnot m.prevote
                           /\ m.term = currentTerm[i]
                           /\ (LET newVotes == votesGranted[i] \cup {m.src}
                              IN  /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                                  /\ IF IsMajority(i, newVotes)
                                     THEN BecomeLeader(i)
                                     ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>)
               ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>
            /\ messages' = messages \ {m}

\* Log Replication
RecvAppendEntries(i, m) ==
    /\ m.type = "AppendEntriesRequest"
    /\ m.dest = i
    /\ IF m.term < currentTerm[i]
       THEN /\ LET response == [type       |-> "AppendEntriesResponse",
                               src        |-> i,
                               dest       |-> m.src,
                               term       |-> currentTerm[i],
                               success    |-> FALSE,
                               matchIndex |-> LastLogIndex(i)]
            IN messages' = (messages \ {m}) \cup {response}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>
       ELSE /\ LET logOK == /\ m.prevLogIndex <= LastLogIndex(i)
                           /\ LogTerm(i, m.prevLogIndex) = m.prevLogTerm
            IN /\ IF m.term > currentTerm[i]
                  THEN /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                       /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                       /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  ELSE UNCHANGED <<state, currentTerm, votedFor>>
               /\ leaderId' = [leaderId EXCEPT ![i] = m.leaderId]
               /\ IF logOK
                  THEN /\ LET newLogEntries == m.entries
                           conflictIndex == CHOOSE idx \in 1..Len(newLogEntries) :
                                                \/ m.prevLogIndex + idx > LastLogIndex(i)
                                                \/ LogTerm(i, m.prevLogIndex + idx) # newLogEntries[idx].term
                           newLog == IF conflictIndex = Nil
                                     THEN log[i]
                                     ELSE SubSeq(log[i], 1, m.prevLogIndex + conflictIndex - 1 - snapshot_last_idx[i])
                           finalLog == newLog \o newLogEntries
                       IN log' = [log EXCEPT ![i] = finalLog]
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = max({commitIndex[i], min({m.leaderCommit, LastLogIndex(i)})})]
                       /\ LET response == [type       |-> "AppendEntriesResponse",
                                          src        |-> i,
                                          dest       |-> m.src,
                                          term       |-> currentTerm'[i],
                                          success    |-> TRUE,
                                          matchIndex |-> m.prevLogIndex + Len(m.entries)]
                       IN messages' = (messages \ {m}) \cup {response}
                  ELSE /\ LET response == [type       |-> "AppendEntriesResponse",
                                          src        |-> i,
                                          dest       |-> m.src,
                                          term       |-> currentTerm'[i],
                                          success    |-> FALSE,
                                          matchIndex |-> LastLogIndex(i)]
                       IN messages' = (messages \ {m}) \cup {response}
                       /\ UNCHANGED <<log, commitIndex>>
               /\ UNCHANGED <<lastApplied, nodes, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

RecvAppendEntriesResponse(i, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ m.dest = i
    /\ state[i] = "LEADER"
    /\ IF m.term > currentTerm[i]
       THEN /\ BecomeFollower(i, m.term)
            /\ messages' = messages \ {m}
       ELSE /\ IF m.success
               THEN /\ nextIndex' = [nextIndex EXCEPT ![i][m.src] = m.matchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][m.src] = m.matchIndex]
                    /\ LET newMatchIndexes == matchIndex'[i]
                           sortedIndexes == SortSeq({newMatchIndexes[n] : n \in nodes[i]}, ">")
                           majorityIndex == sortedIndexes[Cardinality(nodes[i]) \div 2 + 1]
                       IN IF majorityIndex > commitIndex[i] /\ LogTerm(i, majorityIndex) = currentTerm[i]
                          THEN commitIndex' = [commitIndex EXCEPT ![i] = majorityIndex]
                          ELSE UNCHANGED commitIndex
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m.src] = nextIndex[i][m.src] - 1]
                    /\ UNCHANGED <<matchIndex, commitIndex>>
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term>>

\* Leader Operations
SendAppendEntries(i, j) ==
    /\ state[i] = "LEADER"
    /\ j \in nodes[i] \ {i}
    /\ nextIndex[i][j] > snapshot_last_idx[i]
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == LogTerm(i, prevLogIndex)
           lastEntry == LastLogIndex(i)
           entries == SubSeq(log[i], prevLogIndex - snapshot_last_idx[i] + 1, lastEntry - snapshot_last_idx[i])
           msg == [type         |-> "AppendEntriesRequest",
                   src          |-> i,
                   dest         |-> j,
                   term         |-> currentTerm[i],
                   leaderId     |-> i,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm  |-> prevLogTerm,
                   entries      |-> entries,
                   leaderCommit |-> commitIndex[i]]
    IN /\ messages' = messages \cup {msg}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

SendHeartbeat(i, j) ==
    /\ state[i] = "LEADER"
    /\ j \in nodes[i] \ {i}
    /\ LET msg == [type         |-> "AppendEntriesRequest",
                   src          |-> i,
                   dest         |-> j,
                   term         |-> currentTerm[i],
                   leaderId     |-> i,
                   prevLogIndex |-> LastLogIndex(i),
                   prevLogTerm  |-> LastLogTerm(i),
                   entries      |-> << >>,
                   leaderCommit |-> commitIndex[i]]
    IN /\ messages' = messages \cup {msg}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

\* Election Management
ElectionStart(i) == BecomePreCandidate(i)

ElectionTimeout(i) ==
    /\ state[i] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ ElectionStart(i)

\* Log Management
LogAppend(i, val) ==
    /\ state[i] = "LEADER"
    /\ LET newEntry == [term |-> currentTerm[i], command |-> val]
       IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

LogCommit(i) ==
    /\ state[i] = "LEADER"
    /\ LET newMatchIndexes == [matchIndex[i] EXCEPT ![i] = LastLogIndex(i)]
           sortedIndexes == SortSeq({newMatchIndexes[n] : n \in nodes[i]}, ">")
           majorityIndex == sortedIndexes[Cardinality(nodes[i]) \div 2 + 1]
       IN IF majorityIndex > commitIndex[i] /\ LogTerm(i, majorityIndex) = currentTerm[i]
          THEN commitIndex' = [commitIndex EXCEPT ![i] = majorityIndex]
          ELSE UNCHANGED commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

\* Periodic Tasks
PeriodicElectionTimeout(i) == ElectionTimeout(i)
PeriodicHeartbeat(i) == \E j \in nodes[i] \ {i} : SendHeartbeat(i, j)

\* Node Management
AddNode(i, newNode) ==
    /\ state[i] = "LEADER"
    /\ newNode \notin nodes[i]
    /\ LET newEntry == [term |-> currentTerm[i], command |-> [type |-> "ADD_NODE", node |-> newNode]]
       IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

RemoveNode(i, oldNode) ==
    /\ state[i] = "LEADER"
    /\ oldNode \in nodes[i]
    /\ oldNode # i
    /\ LET newEntry == [term |-> currentTerm[i], command |-> [type |-> "REMOVE_NODE", node |-> oldNode]]
       IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

ApplyConfigChange(i) ==
    /\ lastApplied[i] < commitIndex[i]
    /\ LET entryIndex == lastApplied[i] + 1
           entry == log[i][entryIndex - snapshot_last_idx[i]]
    IN /\ entry.command.type \in {"ADD_NODE", "REMOVE_NODE"}
       /\ IF entry.command.type = "ADD_NODE"
          THEN nodes' = [nodes EXCEPT ![i] = nodes[i] \cup {entry.command.node}]
          ELSE nodes' = [nodes EXCEPT ![i] = nodes[i] \ {entry.command.node}]
       /\ lastApplied' = [lastApplied EXCEPT ![i] = entryIndex]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

\* Snapshot Handling
SnapshotBegin(i) ==
    /\ commitIndex[i] > snapshot_last_idx[i]
    /\ LET newSnapshotIndex == commitIndex[i]
           newSnapshotTerm == LogTerm(i, newSnapshotIndex)
           newLog == SubSeq(log[i], newSnapshotIndex - snapshot_last_idx[i] + 1, Len(log[i]))
    IN /\ snapshot_last_idx' = [snapshot_last_idx EXCEPT ![i] = newSnapshotIndex]
       /\ snapshot_last_term' = [snapshot_last_term EXCEPT ![i] = newSnapshotTerm]
       /\ log' = [log EXCEPT ![i] = newLog]
       /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes, leaderId, votesGranted, nextIndex, matchIndex, messages>>

SnapshotEnd(i) == SnapshotBegin(i) \* Simplified: Begin and End are one atomic action

RecvSnapshot(i, m) ==
    /\ m.type = "InstallSnapshotRequest"
    /\ m.dest = i
    /\ IF m.term >= currentTerm[i]
       THEN /\ IF m.term > currentTerm[i]
               THEN /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
               ELSE UNCHANGED <<state, currentTerm, votedFor>>
            /\ leaderId' = [leaderId EXCEPT ![i] = m.leaderId]
            /\ IF m.lastIncludedIndex > snapshot_last_idx[i]
               THEN /\ snapshot_last_idx' = [snapshot_last_idx EXCEPT ![i] = m.lastIncludedIndex]
                    /\ snapshot_last_term' = [snapshot_last_term EXCEPT ![i] = m.lastIncludedTerm]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = max({commitIndex[i], m.lastIncludedIndex})]
                    /\ lastApplied' = [lastApplied EXCEPT ![i] = max({lastApplied[i], m.lastIncludedIndex})]
                    /\ log' = [log EXCEPT ![i] = << >>]
               ELSE UNCHANGED <<snapshot_last_idx, snapshot_last_term, commitIndex, lastApplied, log>>
       ELSE UNCHANGED <<state, currentTerm, votedFor, leaderId, snapshot_last_idx, snapshot_last_term, commitIndex, lastApplied, log>>
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<nodes, votesGranted, nextIndex, matchIndex>>

\* Helper action to apply a normal committed entry
ApplyNormalEntry(i) ==
    /\ lastApplied[i] < commitIndex[i]
    /\ LET entryIndex == lastApplied[i] + 1
           entry == log[i][entryIndex - snapshot_last_idx[i]]
    IN /\ entry.command.type = UNDEFINED
       /\ lastApplied' = [lastApplied EXCEPT ![i] = entryIndex]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nodes, leaderId, votesGranted, snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex, messages>>

Next ==
    \/ \E i \in Server: PeriodicElectionTimeout(i)
    \/ \E i \in Server: PeriodicHeartbeat(i)
    \/ \E i, j \in Server: SendAppendEntries(i, j)
    \/ \E i \in Server, m \in messages: RecvRequestVote(i, m)
    \/ \E i \in Server, m \in messages: RecvRequestVoteResponse(i, m)
    \/ \E i \in Server, m \in messages: RecvAppendEntries(i, m)
    \/ \E i \in Server, m \in messages: RecvAppendEntriesResponse(i, m)
    \/ \E i \in Server, m \in messages: RecvSnapshot(i, m)
    \/ \E i \in Server, v \in Value: LogAppend(i, v)
    \/ \E i \in Server: LogCommit(i)
    \/ \E i \in Server: ApplyNormalEntry(i)
    \/ \E i \in Server: ApplyConfigChange(i)
    \/ \E i \in Server, n \in Server: AddNode(i, n)
    \/ \E i \in Server, n \in Server: RemoveNode(i, n)
    \/ \E i \in Server: SnapshotBegin(i)

Spec == Init /\ [][Next]_vars

====