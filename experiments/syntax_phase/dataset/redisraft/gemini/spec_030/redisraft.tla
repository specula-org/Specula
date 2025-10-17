---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Command, Nil

ASSUME Server = { "s1", "s2", "s3" }
ASSUME Command = { "c1", "c2" }

VARIABLES 
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votesGranted,
    messages,
    nodes,
    snapshotLastIndex,
    snapshotLastTerm

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, nodes, snapshotLastIndex, snapshotLastTerm>>

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}
MsgTypes == {"RequestVoteReq", "RequestVoteResp", "AppendEntriesReq", "AppendEntriesResp", "SnapshotReq"}

Quorum(s) == (Cardinality(s) * 2) > Cardinality(nodes[s])

IsUpToDate(log1, term1, log2, term2) ==
    LET lastTerm1 == IF Len(log1) > 0 THEN log1[Len(log1)].term ELSE term1
        lastTerm2 == IF Len(log2) > 0 THEN log2[Len(log2)].term ELSE term2
        lastIndex1 == Len(log1)
        lastIndex2 == Len(log2)
    IN  (lastTerm1 > lastTerm2) \/ ((lastTerm1 = lastTerm2) /\ (lastIndex1 >= lastIndex2))

TypeOK ==
    /\ state \in [Server -> NodeStates]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A s \in Server: IsSequence(log[s])
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ IsBag(messages)
    /\ nodes \in [Server -> SUBSET Server]
    /\ snapshotLastIndex \in [Server -> Nat]
    /\ snapshotLastTerm \in [Server -> Nat]

Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ messages = EmptyBag
    /\ nodes = [s \in Server |-> Server]
    /\ snapshotLastIndex = [s \in Server |-> 0]
    /\ snapshotLastTerm = [s \in Server |-> 0]

\* State Transitions
BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomePreCandidate(s) ==
    /\ state[s] \in {"Follower", "PreCandidate"}
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    \* FIX: Replaced `\+` with `(+)` for bag union, as required by the Bags module.
    /\ messages' = messages (+) Bag({[type |-> "RequestVoteReq", from |-> s, to |-> t, term |-> currentTerm[s] + 1, prevote |-> TRUE, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE snapshotLastTerm[s]] : t \in nodes[s] \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(s) ==
    /\ state[s] \in {"Follower", "Candidate", "PreCandidate"}
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages (+) Bag({[type |-> "RequestVoteReq", from |-> s, to |-> t, term |-> currentTerm[s] + 1, prevote |-> FALSE, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE snapshotLastTerm[s]] : t \in nodes[s] \ {s}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(s) ==
    /\ state[s] = "Candidate"
    /\ Quorum(votesGranted[s])
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
    \* FIX: Corrected a parse error by replacing the invalid `WITH` keyword with the correct `EXCEPT` operator for function updates and adding the necessary brackets.
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [[t \in Server |-> 0] EXCEPT ![s] = Len(log[s])]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, messages, nodes, snapshotLastIndex, snapshotLastTerm>>

\* Election Management
ElectionTimeout(s) ==
    /\ state[s] \in {"Follower", "Candidate", "PreCandidate"}
    /\ BecomePreCandidate(s)

\* Vote Processing
HandleRequestVote(s, m) ==
    LET
        logTerm(l, i) == IF i > 0 /\ i <= Len(l) THEN l[i].term ELSE snapshotLastTerm[s]
        myLastLogTerm == IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE snapshotLastTerm[s]
        myLastLogIndex == Len(log[s])
        candidateIsUpToDate == IsUpToDate(log[m.from], m.lastLogTerm, log[s], myLastLogTerm)
    IN
    /\ m.type = "RequestVoteReq"
    /\ m.to = s
    /\ LET
        grant ==
            /\ m.term >= currentTerm[s]
            /\ (IF m.prevote THEN TRUE ELSE (votedFor[s] = Nil \/ votedFor[s] = m.from))
            /\ candidateIsUpToDate
        resp == [type |-> "RequestVoteResp", from |-> s, to |-> m.from, term |-> currentTerm[s], voteGranted |-> grant, requestTerm |-> m.term, prevote |-> m.prevote]
    IN
    /\ messages' = (messages \- Bag({m})) (+) Bag({resp})
    /\ IF m.term > currentTerm[s] /\ NOT m.prevote
       THEN /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![s] = IF grant THEN m.from ELSE Nil]
       ELSE /\ votedFor' = [votedFor EXCEPT ![s] = IF grant /\ NOT m.prevote THEN m.from ELSE votedFor[s]]
            /\ UNCHANGED <<state, currentTerm>>
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

HandleRequestVoteResponse(s, m) ==
    /\ m.type = "RequestVoteResp"
    /\ m.to = s
    /\ messages' = messages \- Bag({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE /\ IF m.voteGranted
              THEN /\ IF m.prevote /\ state[s] = "PreCandidate" /\ m.requestTerm = currentTerm[s] + 1
                     THEN LET newVotes == votesGranted[s] \cup {m.from}
                          IN /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                             /\ IF Quorum(newVotes)
                                THEN BecomeCandidate(s)
                                ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>
                     ELSE /\ IF NOT m.prevote /\ state[s] = "Candidate" /\ m.requestTerm = currentTerm[s]
                            THEN LET newVotes == votesGranted[s] \cup {m.from}
                                 IN /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                                    /\ IF Quorum(newVotes)
                                       THEN BecomeLeader(s)
                                       ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>
                            ELSE UNCHANGED <<vars>>
              ELSE UNCHANGED <<vars>>

\* Log Replication and Leader Operations
LeaderSendAppendEntries(s) ==
    /\ state[s] = "Leader"
    /\ \E t \in nodes[s] \ {s}:
        LET prevLogIndex == nextIndex[s][t] - 1
            prevLogTerm == IF prevLogIndex > snapshotLastIndex[s] THEN log[s][prevLogIndex].term ELSE snapshotLastTerm[s]
            entries == SubSeq(log[s], nextIndex[s][t], Len(log[s]))
        IN \/ nextIndex[s][t] <= snapshotLastIndex[s]
           \/ \/ entries /= << >>
              \/ \A m \in BagToSet(messages): m.type /= "AppendEntriesReq" \/ m.to /= t \* Send heartbeat
    /\ messages' = messages (+) Bag({
        IF nextIndex[s][t] <= snapshotLastIndex[s]
        THEN [type |-> "SnapshotReq", from |-> s, to |-> t, term |-> currentTerm[s], lastIncludedIndex |-> snapshotLastIndex[s], lastIncludedTerm |-> snapshotLastTerm[s]]
        ELSE LET prevLogIndex == nextIndex[s][t] - 1
                 prevLogTerm == IF prevLogIndex > snapshotLastIndex[s] THEN log[s][prevLogIndex].term ELSE snapshotLastTerm[s]
                 entries == SubSeq(log[s], nextIndex[s][t], Len(log[s]))
             IN [type |-> "AppendEntriesReq", from |-> s, to |-> t, term |-> currentTerm[s], prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm, entries |-> entries, leaderCommit |-> commitIndex[s]]
        : t \in nodes[s] \ {s}
    })
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

HandleAppendEntries(s, m) ==
    /\ m.type = "AppendEntriesReq"
    /\ m.to = s
    /\ messages' = messages \- Bag({m})
    /\ IF m.term < currentTerm[s]
       THEN /\ LET resp == [type |-> "AppendEntriesResp", from |-> s, to |-> m.from, term |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0]
            IN messages' = (messages \- Bag({m})) (+) Bag({resp})
            /\ UNCHANGED <<vars>>
       ELSE /\ LET
                prevLogExists ==
                    /\ m.prevLogIndex <= Len(log[s])
                    /\ m.prevLogIndex >= snapshotLastIndex[s]
                prevLogMatches ==
                    /\ prevLogExists
                    /\ (IF m.prevLogIndex > snapshotLastIndex[s] THEN log[s][m.prevLogIndex].term = m.prevLogTerm ELSE snapshotLastTerm[s] = m.prevLogTerm)
            IN
            /\ IF m.term > currentTerm[s]
               THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                    /\ state' = [state EXCEPT ![s] = "Follower"]
                    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
               ELSE UNCHANGED <<currentTerm, state, votedFor>>
            /\ IF prevLogMatches
               THEN /\ LET newLog ==
                            LET conflictIndex == CHOOSE i \in 1..Len(m.entries) :
                                    m.prevLogIndex + i <= Len(log[s]) /\ log[s][m.prevLogIndex + i].term /= m.entries[i].term
                            IN IF conflictIndex = {}
                               THEN log[s] \o m.entries
                               ELSE SubSeq(log[s], 1, m.prevLogIndex + conflictIndex - 1) \o SubSeq(m.entries, conflictIndex, Len(m.entries))
                    IN log' = [log EXCEPT ![s] = newLog]
                 /\ commitIndex' = [commitIndex EXCEPT ![s] = max({commitIndex[s], min({m.leaderCommit, Len(newLog)})})]
                 /\ LET resp == [type |-> "AppendEntriesResp", from |-> s, to |-> m.from, term |-> currentTerm'[s], success |-> TRUE, matchIndex |-> m.prevLogIndex + Len(m.entries)]
                    IN messages' = (messages \- Bag({m})) (+) Bag({resp})
               ELSE /\ LET resp == [type |-> "AppendEntriesResp", from |-> s, to |-> m.from, term |-> currentTerm'[s], success |-> FALSE, matchIndex |-> 0]
                    IN messages' = (messages \- Bag({m})) (+) Bag({resp})
                    /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

HandleAppendEntriesResponse(s, m) ==
    /\ m.type = "AppendEntriesResp"
    /\ m.to = s
    /\ state[s] = "Leader"
    /\ messages' = messages \- Bag({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE /\ IF m.success
              THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.matchIndex + 1]]
                   /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![m.from] = m.matchIndex]]
              ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = max({1, nextIndex[s][m.from] - 1})]]
                   /\ UNCHANGED <<matchIndex>>
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

\* Log Management
ClientRequest(s, cmd) ==
    /\ state[s] = "Leader"
    /\ LET newEntry == [term |-> currentTerm[s], command |-> cmd]
    IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, nodes, snapshotLastIndex, snapshotLastTerm>>

AdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET
        Indices == {matchIndex[s][t] : t \in nodes[s]} \cup {Len(log[s])}
        MajorityIndex(is) == CHOOSE i \in is : i > commitIndex[s] /\ log[s][i].term = currentTerm[s] /\ Quorum({t \in nodes[s] : matchIndex[s][t] >= i})
    IN
    /\ \E i \in Indices: MajorityIndex(Indices) = i
    /\ commitIndex' = [commitIndex EXCEPT ![s] = MajorityIndex(Indices)]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votesGranted, messages, nodes, snapshotLastIndex, snapshotLastTerm>>

ApplyLog(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET idx == lastApplied[s] + 1
           entry == log[s][idx]
    IN
    /\ lastApplied' = [lastApplied EXCEPT ![s] = idx]
    /\ IF entry.command.type = "AddNode"
       THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \cup {entry.command.node}]
       ELSE IF entry.command.type = "RemoveNode"
            THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \ {entry.command.node}]
            ELSE UNCHANGED <<nodes>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm>>

\* Snapshot Handling
LeaderInitiateSnapshot(s) ==
    /\ state[s] = "Leader"
    /\ commitIndex[s] > snapshotLastIndex[s]
    /\ LET newSnapshotIndex == commitIndex[s]
           newSnapshotTerm == log[s][newSnapshotIndex].term
    IN
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = newSnapshotIndex]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = newSnapshotTerm]
    /\ log' = [log EXCEPT ![s] = SubSeq(log[s], newSnapshotIndex + 1, Len(log[s]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, messages, nodes>>

HandleSnapshot(s, m) ==
    /\ m.type = "SnapshotReq"
    /\ m.to = s
    /\ messages' = messages \- Bag({m})
    /\ IF m.term < currentTerm[s]
       THEN UNCHANGED <<vars>>
       ELSE /\ IF m.lastIncludedIndex > commitIndex[s]
              THEN /\ state' = [state EXCEPT ![s] = "Follower"]
                   /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                   /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = m.lastIncludedIndex]
                   /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = m.lastIncludedTerm]
                   /\ commitIndex' = [commitIndex EXCEPT ![s] = m.lastIncludedIndex]
                   /\ lastApplied' = [lastApplied EXCEPT ![s] = m.lastIncludedIndex]
                   /\ log' = [log EXCEPT ![s] = << >>]
                   /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votesGranted, nodes>>
              ELSE UNCHANGED <<vars>>

\* Periodic Tasks
PeriodicHeartbeat(s) == LeaderSendAppendEntries(s)
PeriodicElectionTimeout(s) == ElectionTimeout(s)

Next ==
    \/ \E s \in Server:
        \/ ElectionTimeout(s)
        \/ BecomeCandidate(s)
        \/ BecomeLeader(s)
        \/ LeaderSendAppendEntries(s)
        \/ AdvanceCommitIndex(s)
        \/ ApplyLog(s)
        \/ LeaderInitiateSnapshot(s)
        \/ \E cmd \in Command: ClientRequest(s, cmd)
    \/ \E m \in BagToSet(messages):
        \/ HandleRequestVote(m.to, m)
        \/ HandleRequestVoteResponse(m.to, m)
        \/ HandleAppendEntries(m.to, m)
        \/ HandleAppendEntriesResponse(m.to, m)
        \/ HandleSnapshot(m.to, m)

Spec == Init /\ [][Next]_vars

====