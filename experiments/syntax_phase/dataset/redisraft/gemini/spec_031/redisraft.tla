---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Server, Value, Nil, DefaultConfig
ASSUME IsFiniteSet(Server)
ASSUME DefaultConfig \subseteq Server

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
    nodes,
    messages,
    snapshotLastIndex,
    snapshotLastTerm

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, messages, snapshotLastIndex, snapshotLastTerm>>

IsSequence(s) == TRUE
IsASetOfRecords(S) == TRUE

TypeOK ==
    /\ state \in [Server -> {"Follower", "PreCandidate", "Candidate", "Leader"}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A i \in Server: IsSequence(log[i])
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat \cup {0}]]
    /\ matchIndex \in [Server -> [Server -> Nat \cup {0}]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ nodes \in [Server -> SUBSET Server]
    /\ IsASetOfRecords(messages)
    /\ snapshotLastIndex \in [Server -> Nat]
    /\ snapshotLastTerm \in [Server -> Nat]

LastLogIndex(l) == Len(l)
LastLogTerm(l, slt) == IF Len(l) > 0 THEN l[Len(l)]["term"] ELSE slt

IsQuorum(s, serverSet) == Cardinality(s) * 2 > Cardinality(serverSet)

BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, messages, snapshotLastIndex, snapshotLastTerm>>

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ messages' = messages \cup
        {[ type |-> "RequestVote",
           term |-> currentTerm[i] + 1,
           prevote |-> TRUE,
           candidateId |-> i,
           lastLogIndex |-> snapshotLastIndex[i] + LastLogIndex(log[i]),
           lastLogTerm |-> LastLogTerm(log[i], snapshotLastTerm[i]),
           src |-> i,
           dest |-> j ] : j \in nodes[i] \ {i}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ messages' = messages \cup
        {[ type |-> "RequestVote",
           term |-> currentTerm[i] + 1,
           prevote |-> FALSE,
           candidateId |-> i,
           lastLogIndex |-> snapshotLastIndex[i] + LastLogIndex(log[i]),
           lastLogTerm |-> LastLogTerm(log[i], snapshotLastTerm[i]),
           src |-> i,
           dest |-> j ] : j \in nodes[i] \ {i}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> snapshotLastIndex[i] + LastLogIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nodes, messages, snapshotLastIndex, snapshotLastTerm>>

ElectionStart(i) ==
    /\ state[i] \in {"Follower", "Candidate"}
    /\ BecomePreCandidate(i)

ElectionTimeout(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ BecomeCandidate(i)

PeriodicHeartbeat(i) ==
    /\ state[i] = "Leader"
    /\ \E j \in nodes[i] \ {i}:
        LET prevLogIndex == nextIndex[i][j] - 1
            prevLogTerm == IF prevLogIndex > snapshotLastIndex[i]
                           THEN log[i][prevLogIndex - snapshotLastIndex[i]]["term"]
                           ELSE snapshotLastTerm[i]
        IN messages' = messages \cup
            {[ type |-> "AppendEntries",
               term |-> currentTerm[i],
               leaderId |-> i,
               prevLogIndex |-> prevLogIndex,
               prevLogTerm |-> prevLogTerm,
               entries |-> << >>,
               leaderCommit |-> commitIndex[i],
               src |-> i,
               dest |-> j ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

LogAppend(i, val, type, node) ==
    /\ state[i] = "Leader"
    /\ LET newEntry == [term |-> currentTerm[i], value |-> val, type |-> type, node |-> node]
        newLog == Append(log[i], newEntry)
    IN log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, messages, snapshotLastIndex, snapshotLastTerm>>

LogDelete(i, fromIndex) ==
    /\ LET newLog == SubSeq(log[i], 1, fromIndex - snapshotLastIndex[i] - 1)
    IN log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, messages, snapshotLastIndex, snapshotLastTerm>>

LogCommit(i) ==
    /\ state[i] = "Leader"
    /\ LET matchSet == {matchIndex[i][j] : j \in nodes[i]}
    /\ \E N \in matchSet:
        /\ N > commitIndex[i]
        /\ N > snapshotLastIndex[i]
        /\ log[i][N - snapshotLastIndex[i]]["term"] = currentTerm[i]
        /\ IsQuorum({j \in nodes[i] : matchIndex[i][j] >= N}, nodes[i])
        /\ commitIndex' = [commitIndex EXCEPT ![i] = N]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votesGranted, nodes, messages, snapshotLastIndex, snapshotLastTerm>>

ApplyConfigChange(i, entry) ==
    IF entry["type"] = "AddNode"
       THEN nodes' = [nodes EXCEPT ![i] = nodes[i] \cup {entry["node"]}]
       ELSE IF entry["type"] = "RemoveNode"
            THEN nodes' = [nodes EXCEPT ![i] = nodes[i] \ {entry["node"]}]
            ELSE UNCHANGED nodes

Apply(i) ==
    /\ commitIndex[i] > lastApplied[i]
    /\ LET applyIndex == lastApplied[i] + 1
    /\ IF applyIndex > snapshotLastIndex[i]
       THEN LET entry == log[i][applyIndex - snapshotLastIndex[i]]
            IN /\ lastApplied' = [lastApplied EXCEPT ![i] = applyIndex]
               /\ ApplyConfigChange(i, entry)
       ELSE UNCHANGED <<lastApplied, nodes>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, messages, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVote(i, m) ==
    LET logIsUpToDate ==
            \/ m["lastLogTerm"] > LastLogTerm(log[i], snapshotLastTerm[i])
            \/ /\ m["lastLogTerm"] = LastLogTerm(log[i], snapshotLastTerm[i])
               /\ m["lastLogIndex"] >= snapshotLastIndex[i] + LastLogIndex(log[i])
        grant == m["term"] >= currentTerm[i] /\
                 (votedFor[i] = Nil \/ votedFor[i] = m["candidateId"]) /\
                 logIsUpToDate
        responseTerm == IF m["term"] > currentTerm[i] THEN m["term"] ELSE currentTerm[i]
        response == [ type |-> "RequestVoteResponse",
                      term |-> responseTerm,
                      voteGranted |-> grant,
                      src |-> i,
                      dest |-> m["src"] ]
    IN
    /\ messages' = (messages \ {m}) \cup {response}
    /\ IF m["term"] > currentTerm[i]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m["candidateId"] ELSE Nil]
       ELSE /\ UNCHANGED <<currentTerm, state>>
            /\ IF grant
               THEN votedFor' = [votedFor EXCEPT ![i] = m["candidateId"]]
               ELSE UNCHANGED votedFor
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVoteResponse(i, m) ==
    /\ \/ /\ m["term"] > currentTerm[i]
          /\ state' = [state EXCEPT ![i] = "Follower"]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
          /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
          /\ messages' = messages \ {m}
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>
       \/ /\ m["term"] = currentTerm[i]
          /\ \/ /\ state[i] \in {"PreCandidate", "Candidate"}
                /\ m["voteGranted"]
                /\ LET newVotes == votesGranted[i] \cup {m["src"]}
                IN /\ \/ /\ state[i] = "PreCandidate" /\ IsQuorum(newVotes, nodes[i])
                         /\ state' = [state EXCEPT ![i] = "Candidate"]
                         /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
                         /\ votedFor' = [votedFor EXCEPT ![i] = i]
                         /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
                         /\ messages' = (messages \ {m}) \cup
                             {[ type |-> "RequestVote", term |-> currentTerm[i] + 1, prevote |-> FALSE, candidateId |-> i,
                                lastLogIndex |-> snapshotLastIndex[i] + LastLogIndex(log[i]),
                                lastLogTerm |-> LastLogTerm(log[i], snapshotLastTerm[i]),
                                src |-> i, dest |-> j ] : j \in nodes[i] \ {i}}
                         /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>
                    \/ /\ state[i] = "Candidate" /\ IsQuorum(newVotes, nodes[i])
                       /\ state' = [state EXCEPT ![i] = "Leader"]
                       /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> snapshotLastIndex[i] + LastLogIndex(log[i]) + 1]]
                       /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
                       /\ messages' = messages \ {m}
                       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>
                    \/ /\ (state[i] /= "PreCandidate" \/ ~IsQuorum(newVotes, nodes[i])) /\
                         (state[i] /= "Candidate" \/ ~IsQuorum(newVotes, nodes[i]))
                       /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                       /\ messages' = messages \ {m}
                       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>
             \/ /\ (state[i] \notin {"PreCandidate", "Candidate"} \/ ~m["voteGranted"])
                /\ messages' = messages \ {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>
       \/ /\ m["term"] < currentTerm[i]
          /\ messages' = messages \ {m}
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntries(i, m) ==
    LET responseTerm == IF m["term"] < currentTerm[i] THEN currentTerm[i] ELSE m["term"]
        logOk == \/ m["prevLogIndex"] = 0
                 \/ /\ m["prevLogIndex"] <= snapshotLastIndex[i] + LastLogIndex(log[i])
                    /\ \/ /\ m["prevLogIndex"] > snapshotLastIndex[i]
                          /\ log[i][m["prevLogIndex"] - snapshotLastIndex[i]]["term"] = m["prevLogTerm"]
                       \/ /\ m["prevLogIndex"] = snapshotLastIndex[i]
                          /\ m["prevLogTerm"] = snapshotLastTerm[i]
        success == m["term"] >= currentTerm[i] /\ logOk
        response == [ type |-> "AppendEntriesResponse", term |-> responseTerm, success |-> success,
                      matchIndex |-> IF success THEN m["prevLogIndex"] + Len(m["entries"]) ELSE 0,
                      src |-> i, dest |-> m["src"] ]
    IN
    /\ messages' = (messages \ {m}) \cup {response}
    /\ IF m["term"] >= currentTerm[i]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
            /\ IF logOk
               THEN /\ LET newLog == Append(SubSeq(log[i], 1, m["prevLogIndex"] - snapshotLastIndex[i]), m["entries"])
                    IN log' = [log EXCEPT ![i] = newLog]
                    /\ IF m["leaderCommit"] > commitIndex[i]
                       THEN commitIndex' = [commitIndex EXCEPT ![i] = Min({m["leaderCommit"], snapshotLastIndex[i] + LastLogIndex(newLog)})]
                       ELSE UNCHANGED commitIndex
               ELSE UNCHANGED <<log, commitIndex>>
       ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex>>
    /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntriesResponse(i, m) ==
    /\ messages' = messages \ {m}
    /\ \/ /\ m["term"] > currentTerm[i]
          /\ state' = [state EXCEPT ![i] = "Follower"]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
          /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>
       \/ /\ m["term"] = currentTerm[i] /\ state[i] = "Leader"
          /\ \/ /\ m["success"]
                /\ nextIndex' = [nextIndex EXCEPT ![i][m["src"]] = m["matchIndex"] + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][m["src"]] = m["matchIndex"]]
                /\ LET matchSet == {matchIndex'[i][j] : j \in nodes[i]}
                   IN \/ /\ \E N \in matchSet:
                            /\ N > commitIndex[i]
                            /\ N > snapshotLastIndex[i]
                            /\ log[i][N - snapshotLastIndex[i]]["term"] = currentTerm[i]
                            /\ IsQuorum({j \in nodes[i] : matchIndex'[i][j] >= N}, nodes[i])
                            /\ commitIndex' = [commitIndex EXCEPT ![i] = N]
                      \/ UNCHANGED commitIndex
                /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>
             \/ /\ ~m["success"]
                /\ nextIndex' = [nextIndex EXCEPT ![i][m["src"]] = Max({1, nextIndex[i][m["src"]] - 1})]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>
       \/ /\ (m["term"] < currentTerm[i]) \/ (m["term"] = currentTerm[i] /\ state[i] /= "Leader")
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

SendAppendEntries(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in nodes[i] \ {i}
    /\ snapshotLastIndex[i] + LastLogIndex(log[i]) >= nextIndex[i][j]
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > snapshotLastIndex[i]
                          THEN log[i][prevLogIndex - snapshotLastIndex[i]]["term"]
                          ELSE snapshotLastTerm[i]
           entries == SubSeq(log[i], nextIndex[i][j] - snapshotLastIndex[i], LastLogIndex(log[i]))
    IN messages' = messages \cup
        {[ type |-> "AppendEntries",
           term |-> currentTerm[i],
           leaderId |-> i,
           prevLogIndex |-> prevLogIndex,
           prevLogTerm |-> prevLogTerm,
           entries |-> entries,
           leaderCommit |-> commitIndex[i],
           src |-> i,
           dest |-> j ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

SnapshotBegin(i, index) ==
    /\ state[i] = "Leader"
    /\ index <= commitIndex[i]
    /\ index > snapshotLastIndex[i]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = index]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = log[i][index - snapshotLastIndex[i]]["term"]]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], index - snapshotLastIndex[i] + 1, LastLogIndex(log[i]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, messages>>

SnapshotEnd(i) ==
    /\ state[i] = "Leader"
    /\ UNCHANGED vars

SendSnapshot(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in nodes[i] \ {i}
    /\ nextIndex[i][j] <= snapshotLastIndex[i]
    /\ messages' = messages \cup
        {[ type |-> "InstallSnapshot",
           term |-> currentTerm[i],
           leaderId |-> i,
           lastIncludedIndex |-> snapshotLastIndex[i],
           lastIncludedTerm |-> snapshotLastTerm[i],
           src |-> i,
           dest |-> j ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

RecvSnapshot(i, m) ==
    /\ messages' = messages \ {m}
    /\ \/ /\ m["term"] < currentTerm[i]
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm, nodes>>
       \/ /\ m["term"] >= currentTerm[i]
          /\ m["lastIncludedIndex"] <= commitIndex[i]
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm, nodes>>
       \/ /\ m["term"] >= currentTerm[i]
          /\ m["lastIncludedIndex"] > commitIndex[i]
          /\ state' = [state EXCEPT ![i] = "Follower"]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
          /\ commitIndex' = [commitIndex EXCEPT ![i] = m["lastIncludedIndex"]]
          /\ lastApplied' = [lastApplied EXCEPT ![i] = m["lastIncludedIndex"]]
          /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = m["lastIncludedIndex"]]
          /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = m["lastIncludedTerm"]]
          /\ log' = [log EXCEPT ![i] = << >>]
          /\ UNCHANGED <<votedFor, nodes>>
    /\ UNCHANGED <<nextIndex, matchIndex, votesGranted>>

AddNode(i, newNode) ==
    /\ state[i] = "Leader"
    /\ newNode \notin nodes[i]
    /\ LogAppend(i, Nil, "AddNode", newNode)

RemoveNode(i, oldNode) ==
    /\ state[i] = "Leader"
    /\ oldNode \in nodes[i]
    /\ oldNode /= i
    /\ LogAppend(i, Nil, "RemoveNode", oldNode)

Receive(m) ==
    LET i == m["dest"] IN
    CASE m["type"] = "RequestVote" -> RecvRequestVote(i, m)
    [] m["type"] = "RequestVoteResponse" -> RecvRequestVoteResponse(i, m)
    [] m["type"] = "AppendEntries" -> RecvAppendEntries(i, m)
    [] m["type"] = "AppendEntriesResponse" -> RecvAppendEntriesResponse(i, m)
    [] m["type"] = "InstallSnapshot" -> RecvSnapshot(i, m)

Next ==
    \/ \E i \in Server: ElectionStart(i)
    \/ \E i \in Server: ElectionTimeout(i)
    \/ \E i \in Server: PeriodicHeartbeat(i)
    \/ \E i, j \in Server: SendAppendEntries(i, j)
    \/ \E i \in Server: Apply(i)
    \/ \E i \in Server: LogCommit(i)
    \/ \E i \in Server, v \in Value: LogAppend(i, v, "Normal", Nil)
    \/ \E i, n \in Server: AddNode(i, n)
    \/ \E i, n \in Server: RemoveNode(i, n)
    \/ \E i \in Server, idx \in 1..commitIndex[i]: SnapshotBegin(i, idx)
    \/ \E i \in Server: SnapshotEnd(i)
    \/ \E i, j \in Server: SendSnapshot(i, j)
    \/ \E m \in messages: Receive(m)

Init ==
    /\ state = [i \in Server |-> "Follower"]
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> Nil]
    /\ log = [i \in Server |-> << >>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ lastApplied = [i \in Server |-> 0]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ votesGranted = [i \in Server |-> {}]
    /\ nodes = [i \in Server |-> DefaultConfig]
    /\ messages = {}
    /\ snapshotLastIndex = [i \in Server |-> 0]
    /\ snapshotLastTerm = [i \in Server |-> 0]

Spec == Init /\ [][Next]_vars

====