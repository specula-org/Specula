---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Integers, FiniteSets, Bags

CONSTANTS Server, Value, ConfigValue

ASSUME Server \subseteq Nat
ASSUME Value \subseteq Nat
ASSUME ConfigValue \subseteq {"AddNode", "RemoveNode"}

State_Follower == "Follower"
State_PreCandidate == "PreCandidate"
State_Candidate == "Candidate"
State_Leader == "Leader"
States == {State_Follower, State_PreCandidate, State_Candidate, State_Leader}

Msg_RequestVote == "RequestVote"
Msg_RequestVoteResponse == "RequestVoteResponse"
Msg_AppendEntries == "AppendEntries"
Msg_AppendEntriesResponse == "AppendEntriesResponse"
Msg_Snapshot == "Snapshot"

LogType_Normal == "Normal"
LogType_NoOp == "NoOp"
LogType_Config == "Config"

vars == <<
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    leader,
    nodes,
    snapshotIndex,
    snapshotTerm,
    nextIndex,
    matchIndex,
    votesGranted,
    messages
>>

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
Quorum(s) == (Cardinality(s) \div 2) + 1

Init ==
    /\ state = [s \in Server |-> State_Follower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> "None"]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ leader = "None"
    /\ nodes = [s \in Server |-> Server]
    /\ snapshotIndex = [s \in Server |-> 0]
    /\ snapshotTerm = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ messages = EmptyBag

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = State_Follower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = "None"]
    /\ leader' = "None"
    \* FIX: Removed 'messages' from UNCHANGED clause. The calling actions (e.g., RecvRequestVoteResponse)
    \* already modify messages', and including it here caused a contradiction (double-priming the variable),
    \* which likely led to the reported TLC tool crash.
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>

BecomePreCandidate(s) ==
    /\ state[s] \in {State_Follower, State_PreCandidate}
    /\ state' = [state EXCEPT ![s] = State_PreCandidate]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ messages' = messages \+ Bagify({[
        type |-> Msg_RequestVote,
        term |-> currentTerm[s] + 1,
        candidateId |-> s,
        lastLogIndex |-> LastLogIndex(log[s]),
        lastLogTerm |-> LastLogTerm(log[s]),
        from |-> s,
        to |-> peer,
        prevote |-> TRUE
      ] : peer \in nodes[s] \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex>>

BecomeCandidate(s) ==
    /\ state[s] \in {State_Follower, State_PreCandidate, State_Candidate}
    /\ state' = [state EXCEPT ![s] = State_Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leader' = "None"
    /\ messages' = messages \+ Bagify({[
        type |-> Msg_RequestVote,
        term |-> currentTerm[s] + 1,
        candidateId |-> s,
        lastLogIndex |-> LastLogIndex(log[s]),
        lastLogTerm |-> LastLogTerm(log[s]),
        from |-> s,
        to |-> peer,
        prevote |-> FALSE
      ] : peer \in nodes[s] \ {s}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex>>

BecomeLeader(s) ==
    /\ state[s] \in {State_Candidate, State_PreCandidate}
    /\ Cardinality(votesGranted[s]) >= Quorum(nodes[s])
    /\ state' = [state EXCEPT ![s] = State_Leader]
    /\ leader' = s
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], type |-> LogType_NoOp, value |-> "NoOp"])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, nodes, snapshotIndex, snapshotTerm, votesGranted, messages>>

RecvRequestVote(s, m) ==
    /\ m.type = Msg_RequestVote
    /\ m.to = s
    /\ LET
        logIsOk == \/ m.lastLogTerm > LastLogTerm(log[s])
                   \/ /\ m.lastLogTerm = LastLogTerm(log[s])
                      /\ m.lastLogIndex >= LastLogIndex(log[s])
        grantVote == \/ /\ m.term > currentTerm[s]
                         /\ logIsOk
                     \/ /\ m.term = currentTerm[s]
                         /\ logIsOk
                         /\ votedFor[s] \in {"None", m.candidateId}
        response == [
            type |-> Msg_RequestVoteResponse,
            term |-> IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s],
            voteGranted |-> grantVote,
            from |-> s,
            to |-> m.from,
            prevote |-> m.prevote
        ]
    /\ messages' = (messages \- Bagify({m})) \+ Bagify({response})
    /\ IF m.term > currentTerm[s] /\ m.prevote = FALSE
       THEN /\ state' = [state EXCEPT ![s] = State_Follower]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![s] = IF grantVote THEN m.candidateId ELSE "None"]
            /\ leader' = "None"
            /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>
       ELSE /\ IF grantVote /\ m.prevote = FALSE
               THEN votedFor' = [votedFor EXCEPT ![s] = m.candidateId]
               ELSE UNCHANGED votedFor
            /\ UNCHANGED <<state, currentTerm, leader, log, commitIndex, lastApplied, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>

RecvRequestVoteResponse(s, m) ==
    /\ m.type = Msg_RequestVoteResponse
    /\ m.to = s
    /\ messages' = messages \- Bagify({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE /\ IF m.voteGranted
               THEN /\ \/ /\ m.prevote = TRUE
                           /\ state[s] = State_PreCandidate
                           /\ m.term = currentTerm[s] + 1
                        \/ /\ m.prevote = FALSE
                           /\ state[s] = State_Candidate
                           /\ m.term = currentTerm[s]
                    /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.from}]
               ELSE UNCHANGED votesGranted
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex>>

RecvAppendEntries(s, m) ==
    /\ m.type = Msg_AppendEntries
    /\ m.to = s
    /\ LET
        logOK == \/ m.prevLogIndex = 0
                 \/ /\ m.prevLogIndex > 0
                    /\ m.prevLogIndex <= Len(log[s])
                    /\ log[s][m.prevLogIndex].term = m.prevLogTerm
        newCommitIndex == IF m.leaderCommit > commitIndex[s]
                          THEN Min({m.leaderCommit, LastLogIndex(m.entries) + m.prevLogIndex})
                          ELSE commitIndex[s]
        response(success, matchIdx) == [
            type |-> Msg_AppendEntriesResponse,
            term |-> currentTerm[s],
            success |-> success,
            matchIndex |-> matchIdx,
            from |-> s,
            to |-> m.from
        ]
    /\ messages' = (messages \- Bagify({m}))
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = messages' \+ Bagify({response(FALSE, 0)})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>
       ELSE /\ state' = [state EXCEPT ![s] = State_Follower]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ leader' = m.from
            /\ IF logOK
               THEN /\ LET newLog == SubSeq(log[s], 1, m.prevLogIndex) \o m.entries
                    /\ log' = [log EXCEPT ![s] = newLog]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                    /\ messages' = messages' \+ Bagify({response(TRUE, LastLogIndex(newLog))})
               ELSE /\ log' = log
                    /\ commitIndex' = commitIndex
                    /\ messages' = messages' \+ Bagify({response(FALSE, 0)})
            /\ UNCHANGED <<votedFor, lastApplied, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>

RecvAppendEntriesResponse(s, m) ==
    /\ m.type = Msg_AppendEntriesResponse
    /\ m.to = s
    /\ state[s] = State_Leader
    /\ messages' = messages \- Bagify({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE /\ IF m.success
               THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.matchIndex + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![m.from] = m.matchIndex]]
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = Max({1, nextIndex[s][m.from] - 1})]]
                    /\ UNCHANGED matchIndex
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, votesGranted>>

SendAppendEntries(s, peer) ==
    /\ state[s] = State_Leader
    /\ peer \in nodes[s] \ {s}
    /\ LET
        prevIdx == nextIndex[s][peer] - 1
        prevTerm == IF prevIdx > 0 /\ prevIdx <= Len(log[s]) THEN log[s][prevIdx].term ELSE 0
        entriesToSend == SubSeq(log[s], prevIdx + 1, Len(log[s]))
    /\ messages' = messages \+ Bagify({[
        type |-> Msg_AppendEntries,
        term |-> currentTerm[s],
        from |-> s,
        to |-> peer,
        prevLogIndex |-> prevIdx,
        prevLogTerm |-> prevTerm,
        entries |-> entriesToSend,
        leaderCommit |-> commitIndex[s]
    ]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>

SendHeartbeat(s) ==
    /\ state[s] = State_Leader
    /\ messages' = messages \+ Bagify({[
        type |-> Msg_AppendEntries,
        term |-> currentTerm[s],
        from |-> s,
        to |-> peer,
        prevLogIndex |-> LastLogIndex(log[s]),
        prevLogTerm |-> LastLogTerm(log[s]),
        entries |-> << >>,
        leaderCommit |-> commitIndex[s]
      ] : peer \in nodes[s] \ {s}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted>>

ElectionStart(s) ==
    \/ BecomePreCandidate(s)
    \/ BecomeCandidate(s)

ElectionTimeout(s) ==
    /\ state[s] \in {State_Follower, State_Candidate, State_PreCandidate}
    /\ ElectionStart(s)

LogAppend(s, val) ==
    /\ state[s] = State_Leader
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], type |-> LogType_Normal, value |-> val])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

LogDelete(s, idx) ==
    /\ commitIndex[s] < idx
    /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, idx - 1)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

LogCommit(s) ==
    /\ state[s] = State_Leader
    /\ LET
        ReplicatedIndices == { i \in 1..LastLogIndex(log[s]) :
                                Cardinality({p \in nodes[s] : matchIndex[s][p] >= i}) >= Quorum(nodes[s]) }
        newCommitIndex == IF ReplicatedIndices = {} THEN commitIndex[s] ELSE Max(ReplicatedIndices)
    /\ newCommitIndex > commitIndex[s]
    /\ log[s][newCommitIndex].term = currentTerm[s]
    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

PeriodicElectionTimeout(s) == ElectionTimeout(s)

PeriodicHeartbeat(s) == SendHeartbeat(s)

AddNode(s, newNode) ==
    /\ state[s] = State_Leader
    /\ newNode \notin nodes[s]
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], type |-> LogType_Config, value |-> [op |-> "AddNode", node |-> newNode]])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

RemoveNode(s, oldNode) ==
    /\ state[s] = State_Leader
    /\ oldNode \in nodes[s] \ {s}
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], type |-> LogType_Config, value |-> [op |-> "RemoveNode", node |-> oldNode]])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

SnapshotBegin(s) ==
    /\ commitIndex[s] > snapshotIndex[s]
    /\ snapshotIndex' = [snapshotIndex EXCEPT ![s] = commitIndex[s]]
    /\ snapshotTerm' = [snapshotTerm EXCEPT ![s] = log[s][commitIndex[s]].term]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, nextIndex, matchIndex, votesGranted, messages>>

SnapshotEnd(s) ==
    /\ snapshotIndex[s] > 0
    /\ LET
        firstLogIndex == snapshotIndex[s] + 1
        newLog == IF firstLogIndex > Len(log[s])
                  THEN << >>
                  ELSE SubSeq(log[s], firstLogIndex, Len(log[s]))
    /\ log' = [log EXCEPT ![s] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

ApplyConfigChange(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET entry = log[s][lastApplied[s] + 1]
    /\ entry.type = LogType_Config
    /\ LET
        op == entry.value.op
        node == entry.value.node
        newNodes == IF op = "AddNode" THEN nodes[s] \cup {node} ELSE nodes[s] \ {node}
    /\ nodes' = [nodes EXCEPT ![s] = newNodes]
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

ApplyLog(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET entry = log[s][lastApplied[s] + 1]
    /\ entry.type # LogType_Config
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, nodes, snapshotIndex, snapshotTerm, nextIndex, matchIndex, votesGranted, messages>>

Next ==
    \/ \E s \in Server:
        \/ BecomeLeader(s)
        \/ LogCommit(s)
        \/ PeriodicElectionTimeout(s)
        \/ PeriodicHeartbeat(s)
        \/ SnapshotBegin(s)
        \/ SnapshotEnd(s)
        \/ ApplyConfigChange(s)
        \/ ApplyLog(s)
        \/ \E peer \in Server: SendAppendEntries(s, peer)
        \/ \E val \in Value: LogAppend(s, val)
        \/ \E n \in Server: AddNode(s, n)
        \/ \E n \in Server: RemoveNode(s, n)
        \/ \E idx \in 1..Len(log[s]): LogDelete(s, idx)
    \/ \E m \in BagToSet(messages):
        \/ RecvRequestVote(m.to, m)
        \/ RecvRequestVoteResponse(m.to, m)
        \/ RecvAppendEntries(m.to, m)
        \/ RecvAppendEntriesResponse(m.to, m)

Spec == Init /\ [][Next]_vars

====