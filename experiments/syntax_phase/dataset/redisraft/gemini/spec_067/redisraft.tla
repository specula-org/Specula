---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Server, Value, Nil, HeartbeatInterval, ElectionTimeoutRange

ASSUME Server = 1..3
ASSUME Cardinality(Server) > 0
ASSUME ElectionTimeoutRange = 2..3
ASSUME HeartbeatInterval = 1
ASSUME Nil \notin Server
ASSUME Nil \notin Value

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}
LogEntryTypes == {"Command", "AddNode", "RemoveNode", "NoOp"}

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    leaderId,
    nextIndex,
    matchIndex,
    electionTimer,
    electionTimeout,
    snapshotLastIndex,
    snapshotLastTerm,
    snapshotInProgress,
    config,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
          nextIndex, matchIndex, electionTimer, electionTimeout,
          snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config, messages>>

IsSeq(s) == DOMAIN s = 1..Len(s)

TypeOK ==
    /\ state \in [Server -> NodeStates]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A i \in Server: IsSeq(log[i])
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ leaderId \in [Server -> Server \cup {Nil}]
    /\ \A i \in Server: \A j \in Server: nextIndex[i][j] \in Nat
    /\ \A i \in Server: \A j \in Server: matchIndex[i][j] \in Nat
    /\ electionTimer \in [Server -> Nat]
    /\ electionTimeout \in [Server -> ElectionTimeoutRange]
    /\ snapshotLastIndex \in [Server -> Nat]
    /\ snapshotLastTerm \in [Server -> Nat]
    /\ snapshotInProgress \in [Server -> BOOLEAN]
    /\ \A i \in Server: config[i] \subseteq Server
    /\ IsBag(messages)

\* Helper operators
LastLogIndex(i) == Len(log[i])
LastLogTerm(i) == IF LastLogIndex(i) > 0 THEN log[i][LastLogIndex(i)]["term"] ELSE 0
IsQuorum(s, c) == Cardinality(s) * 2 > Cardinality(c)
IsUpToDate(myLastLogIndex, myLastLogTerm, theirLastLogIndex, theirLastLogTerm) ==
    \/ theirLastLogTerm > myLastLogTerm
    \/ (theirLastLogTerm = myLastLogTerm /\ theirLastLogIndex >= myLastLogIndex)

Init ==
    /\ state = [i \in Server |-> "Follower"]
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> Nil]
    /\ log = [i \in Server |-> << >>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ lastApplied = [i \in Server |-> 0]
    /\ leaderId = [i \in Server |-> Nil]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ electionTimer = [i \in Server |-> 0]
    /\ \E et \in [Server -> ElectionTimeoutRange] : electionTimeout = et
    /\ snapshotLastIndex = [i \in Server |-> 0]
    /\ snapshotLastTerm = [i \in Server |-> 0]
    /\ snapshotInProgress = [i \in Server |-> FALSE]
    /\ config = [i \in Server |-> Server]
    /\ messages = EmptyBag

\* State Transitions (embedded in actions)
BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ \E et \in ElectionTimeoutRange: electionTimeout' = [electionTimeout EXCEPT ![i] = et]

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ \E et \in ElectionTimeoutRange: electionTimeout' = [electionTimeout EXCEPT ![i] = et]
    /\ LET req == [ type |-> "RequestVote", from |-> i,
                    term |-> currentTerm[i] + 1, lastLogIndex |-> LastLogIndex(i),
                    lastLogTerm |-> LastLogTerm(i), prevote |-> TRUE ]
       IN messages' = messages (+) Bagify({[req EXCEPT !["to"] = j] : j \in config[i] \setminus {i}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

BecomeCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ \E et \in ElectionTimeoutRange: electionTimeout' = [electionTimeout EXCEPT ![i] = et]
    /\ LET req == [ type |-> "RequestVote", from |-> i,
                    term |-> currentTerm[i] + 1, lastLogIndex |-> LastLogIndex(i),
                    lastLogTerm |-> LastLogTerm(i), prevote |-> FALSE ]
       IN messages' = messages (+) Bagify({[req EXCEPT !["to"] = j] : j \in config[i] \setminus {i}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastLogIndex(i) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> IF j = i THEN LastLogIndex(i) ELSE 0]]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ LET noop == [term |-> currentTerm[i], type |-> "NoOp", data |-> Nil]
       IN log' = [log EXCEPT ![i] = Append(log[i], noop)]
    /\ messages' = messages
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, electionTimeout, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

\* Election Management
ElectionStart(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ BecomePreCandidate(i)

ElectionTimeout(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[i] >= electionTimeout[i]
    /\ ElectionStart(i)

\* Vote Processing
RecvRequestVote(i, m) ==
    /\ m["type"] = "RequestVote"
    /\ m["to"] = i
    /\ LET grant == NOT( \/ m["term"] < currentTerm[i]
                         \/ (m["prevote"] /\ leaderId[i] /= Nil)
                         \/ (m["term"] = currentTerm[i] /\ votedFor[i] /= Nil /\ votedFor[i] /= m["from"])
                         \/ NOT IsUpToDate(LastLogIndex(i), LastLogTerm(i), m["lastLogIndex"], m["lastLogTerm"]) )
           /\ resp == [ type |-> "RequestVoteResp", from |-> i, to |-> m["from"],
                        term |-> IF m["term"] < currentTerm[i] THEN currentTerm[i] ELSE m["term"],
                        voteGranted |-> grant, prevote |-> m["prevote"], requestTerm |-> m["term"] ]
    IN /\ messages' = (messages (-) Bagify({m})) (+) Bagify({resp})
       /\ IF m["term"] > currentTerm[i] /\ NOT m["prevote"]
          THEN /\ state' = [state EXCEPT ![i] = "Follower"]
               /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
               /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m["from"] ELSE Nil]
               /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
               /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
          ELSE /\ votedFor' = [votedFor EXCEPT ![i] = IF grant /\ NOT m["prevote"] THEN m["from"] ELSE votedFor[i]]
               /\ electionTimer' = [electionTimer EXCEPT ![i] = IF grant THEN 0 ELSE electionTimer[i]]
               /\ UNCHANGED <<state, currentTerm, leaderId>>
       /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

RecvRequestVoteResponse(i, m) ==
    /\ m["type"] = "RequestVoteResp"
    /\ m["to"] = i
    /\ IF m["term"] > currentTerm[i]
       THEN /\ BecomeFollower(i, m["term"])
            /\ messages' = messages (-) Bagify({m})
            /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>
       ELSE /\ LET isCorrectState == IF m["prevote"] THEN state[i] = "PreCandidate" ELSE state[i] = "Candidate"
                  /\ isCorrectTerm == IF m["prevote"] THEN m["requestTerm"] = currentTerm[i] + 1 ELSE m["requestTerm"] = currentTerm[i]
           IN IF isCorrectState /\ isCorrectTerm /\ m["voteGranted"]
              THEN LET votesForMe == {n \in config[i] | (n = i) \/ (n = m["from"])}
                   IN IF IsQuorum(votesForMe, config[i])
                      THEN IF state[i] = "PreCandidate"
                           THEN BecomeCandidate(i)
                           ELSE BecomeLeader(i)
                      ELSE UNCHANGED vars
              ELSE UNCHANGED vars

\* Log Replication
RecvAppendEntries(i, m) ==
    /\ m["type"] = "AppendEntries"
    /\ m["to"] = i
    /\ LET resp(success, matchIdx) == [ type |-> "AppendEntriesResp", from |-> i, to |-> m["from"],
                                        term |-> currentTerm[i], success |-> success, matchIndex |-> matchIdx ]
    IN /\ LET base_messages == (messages (-) Bagify({m}))
       IN /\ IF m["term"] < currentTerm[i]
             THEN /\ messages' = base_messages (+) Bagify({resp(FALSE, 0)})
                  /\ UNCHANGED <<vars \ {messages}>>
             ELSE /\ state' = [state EXCEPT ![i] = "Follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
                  /\ votedFor' = [votedFor EXCEPT ![i] = IF m["term"] > currentTerm[i] THEN Nil ELSE votedFor[i]]
                  /\ leaderId' = [leaderId EXCEPT ![i] = m["from"]]
                  /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
                  /\ LET prevEntryOK == \/ m["prevLogIndex"] = 0
                                        \/ (m["prevLogIndex"] <= LastLogIndex(i) /\ log[i][m["prevLogIndex"]]["term"] = m["prevLogTerm"])
                  IN IF NOT prevEntryOK
                     THEN /\ messages' = base_messages (+) Bagify({resp(FALSE, LastLogIndex(i))})
                          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>
                     ELSE /\ LET conflictIndex == CHOOSE k \in 1..Len(m["entries"]) :
                                                      m["prevLogIndex"] + k > LastLogIndex(i) \/ log[i][m["prevLogIndex"] + k]["term"] /= m["entries"][k]["term"]
                                  /\ newEntries == SubSeq(m["entries"], conflictIndex, Len(m["entries"]))
                                  /\ firstNewIndex == m["prevLogIndex"] + conflictIndex
                         IN /\ log' = [log EXCEPT ![i] = Append(SubSeq(log[i], 1, firstNewIndex - 1), newEntries)]
                            /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], Min({m["leaderCommit"], Len(log'[i])})})]
                            /\ messages' = base_messages (+) Bagify({resp(TRUE, Len(log'[i]))})
                            /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, electionTimeout, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

RecvAppendEntriesResponse(i, m) ==
    /\ m["type"] = "AppendEntriesResp"
    /\ m["to"] = i
    /\ state[i] = "Leader"
    /\ LET fromNode == m["from"]
    IN /\ IF m["term"] > currentTerm[i]
          THEN /\ BecomeFollower(i, m["term"])
               /\ messages' = messages (-) Bagify({m})
               /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>
          ELSE /\ messages' = messages (-) Bagify({m})
               /\ IF m["success"]
                  THEN /\ nextIndex' = [nextIndex EXCEPT ![i][fromNode] = m["matchIndex"] + 1]
                       /\ matchIndex' = [matchIndex EXCEPT ![i][fromNode] = m["matchIndex"]]
                       /\ LET PossibleCommits == { k \in (commitIndex[i]+1)..LastLogIndex(i) |
                                                    /\ IsQuorum({j \in config[i] | [matchIndex EXCEPT ![i][fromNode] = m["matchIndex"]][i][j] >= k} \cup {i}, config[i])
                                                    /\ log[i][k]["term"] = currentTerm[i] }
                              /\ newCommitIndex == IF PossibleCommits = {} THEN commitIndex[i] ELSE Max(PossibleCommits)
                          IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                  ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][fromNode] = Max({1, nextIndex[i][fromNode] - 1})]
                       /\ UNCHANGED <<matchIndex, commitIndex>>
               /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leaderId, electionTimer, electionTimeout, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

\* Leader Operations
SendAppendEntries(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in config[i] \setminus {i}
    /\ LET ni == nextIndex[i][j]
       IN /\ ni <= LastLogIndex(i) + 1
          /\ LET prevLogIndex == ni - 1
                 /\ prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex]["term"] ELSE 0
                 /\ entriesToSend == SubSeq(log[i], ni, LastLogIndex(i))
                 /\ msg == [ type |-> "AppendEntries", from |-> i, to |-> j,
                             term |-> currentTerm[i], leaderId |-> i,
                             prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm,
                             entries |-> entriesToSend, leaderCommit |-> commitIndex[i] ]
             IN messages' = messages (+) Bagify({msg})
          /\ UNCHANGED <<vars \ {messages}>>

SendHeartbeat(i) ==
    /\ state[i] = "Leader"
    /\ electionTimer[i] >= HeartbeatInterval
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ LET msg == [ type |-> "AppendEntries", from |-> i,
                    term |-> currentTerm[i], leaderId |-> i,
                    prevLogIndex |-> LastLogIndex(i), prevLogTerm |-> LastLogTerm(i),
                    entries |-> << >>, leaderCommit |-> commitIndex[i] ]
       IN messages' = messages (+) Bagify({[msg EXCEPT !["to"] = j] : j \in config[i] \setminus {i}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, electionTimeout, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, config>>

\* Log Management
LogAppend(i) ==
    /\ state[i] = "Leader"
    /\ \E type \in LogEntryTypes, data \in Value \cup Server:
        /\ LET newEntry == [term |-> currentTerm[i], type |-> type, data |-> data]
           IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ UNCHANGED <<vars \ {log}>>

LogCommit(i) == RecvAppendEntriesResponse(i, CHOOSE m : m["type"] = "AppendEntriesResp" /\ m["to"] = i)

LogDelete(i, idx) ==
    /\ idx > 0 /\ idx <= LastLogIndex(i)
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, idx - 1)]
    /\ UNCHANGED <<vars \ {log}>>

ApplyConfigChange(i, entry) ==
    /\ IF entry["type"] = "AddNode"
       THEN config' = [config EXCEPT ![i] = config[i] \cup {entry["data"]}]
       ELSE IF entry["type"] = "RemoveNode"
            THEN config' = [config EXCEPT ![i] = config[i] \setminus {entry["data"]}]
            ELSE config' = config

LogApply(i) ==
    /\ commitIndex[i] > lastApplied[i]
    /\ LET newApplied == lastApplied[i] + 1
           /\ entry == log[i][newApplied]
    IN /\ lastApplied' = [lastApplied EXCEPT ![i] = newApplied]
       /\ ApplyConfigChange(i, entry)
       /\ UNCHANGED <<vars \ {lastApplied, config}>>

\* Snapshot Handling
SnapshotBegin(i) ==
    /\ snapshotInProgress[i] = FALSE
    /\ commitIndex[i] > snapshotLastIndex[i]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vars \ {snapshotInProgress}>>

SnapshotEnd(i) ==
    /\ snapshotInProgress[i] = TRUE
    /\ LET newSnapshotIndex == lastApplied[i]
    IN /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = newSnapshotIndex]
       /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = IF newSnapshotIndex > 0 THEN log[i][newSnapshotIndex]["term"] ELSE 0]
       /\ log' = [log EXCEPT ![i] = SubSeq(log[i], newSnapshotIndex + 1, LastLogIndex(i))]
       /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![i] = FALSE]
       /\ UNCHANGED <<vars \ {snapshotLastIndex, snapshotLastTerm, log, snapshotInProgress}>>

SendSnapshot(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in config[i] \setminus {i}
    /\ nextIndex[i][j] <= snapshotLastIndex[i]
    /\ LET msg == [ type |-> "Snapshot", from |-> i, to |-> j,
                    term |-> currentTerm[i], lastIncludedIndex |-> snapshotLastIndex[i],
                    lastIncludedTerm |-> snapshotLastTerm[i] ]
       IN messages' = messages (+) Bagify({msg})
    /\ UNCHANGED <<vars \ {messages}>>

RecvSnapshot(i, m) ==
    /\ m["type"] = "Snapshot"
    /\ m["to"] = i
    /\ messages' = messages (-) Bagify({m})
    /\ IF m["term"] < currentTerm[i]
       THEN UNCHANGED vars
       ELSE /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ leaderId' = [leaderId EXCEPT ![i] = m["from"]]
            /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
            /\ IF m["lastIncludedIndex"] > commitIndex[i]
               THEN /\ LET newLog == IF m["lastIncludedIndex"] >= LastLogIndex(i)
                                     THEN << >>
                                     ELSE IF log[i][m["lastIncludedIndex"]]["term"] = m["lastIncludedTerm"]
                                          THEN SubSeq(log[i], m["lastIncludedIndex"] + 1, LastLogIndex(i))
                                          ELSE << >>
                  IN /\ log' = [log EXCEPT ![i] = newLog]
                     /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = m["lastIncludedIndex"]]
                     /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = m["lastIncludedTerm"]]
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = m["lastIncludedIndex"]]
                     /\ lastApplied' = [lastApplied EXCEPT ![i] = m["lastIncludedIndex"]]
               ELSE UNCHANGED <<log, snapshotLastIndex, snapshotLastTerm, commitIndex, lastApplied>>
            /\ UNCHANGED <<votedFor, nextIndex, matchIndex, electionTimeout, snapshotInProgress, config>>

\* Combined Next action
Next ==
    \/ \E i \in Server:
        \/ ElectionTimeout(i)
        \/ SendHeartbeat(i)
        \/ LogAppend(i)
        \/ LogApply(i)
        \/ SnapshotBegin(i)
        \/ SnapshotEnd(i)
        \/ \E j \in Server: SendAppendEntries(i, j)
        \/ \E j \in Server: SendSnapshot(i, j)
    \/ \E m \in BagToSet(messages): \E i \in Server:
        \/ RecvRequestVote(i, m)
        \/ RecvRequestVoteResponse(i, m)
        \/ RecvAppendEntries(i, m)
        \/ RecvAppendEntriesResponse(i, m)
        \/ RecvSnapshot(i, m)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====