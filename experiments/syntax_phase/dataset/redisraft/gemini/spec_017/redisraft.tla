---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Servers, Nil
ASSUME IsFiniteSet(Servers) /\ Servers \subseteq Nat \ {0} /\ Nil \notin Servers

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
    leaderId,
    snapshotLastIndex,
    snapshotLastTerm,
    network,
    nodes

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, network, nodes>>

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
EntryTypes == {"Normal", "AddNode", "RemoveNode", "NoOp"}
MsgTypes == {"RequestVoteReq", "RequestVoteResp", "AppendEntriesReq", "AppendEntriesResp", "SnapshotReq", "SnapshotResp"}

LogEntry(term, type, data) == [term |-> term, type |-> type, data |-> data]
LastLogIndex(l) == IF Len(l) = 0 THEN 0 ELSE Len(l)
LastLogTerm(l, sli, slt) == IF Len(l) = 0 THEN slt ELSE l[Len(l)]["term"]

Majority(nodeSet) == (Cardinality(nodeSet) \div 2) + 1

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

IsUpToDate(candLastLogTerm, candLastLogIndex, myLastLogTerm, myLastLogIndex) ==
    \/ candLastLogTerm > myLastLogTerm
    \/ (candLastLogTerm = myLastLogTerm /\ candLastLogIndex >= myLastLogIndex)

Init ==
    /\ state = [i \in Servers |-> "FOLLOWER"]
    /\ currentTerm = [i \in Servers |-> 0]
    /\ votedFor = [i \in Servers |-> Nil]
    /\ log = [i \in Servers |-> <<>>]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ lastApplied = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votesGranted = [i \in Servers |-> {}]
    /\ leaderId = [i \in Servers |-> Nil]
    /\ snapshotLastIndex = [i \in Servers |-> 0]
    /\ snapshotLastTerm = [i \in Servers |-> 0]
    /\ network = {}
    /\ nodes = Servers

\* State Transitions
BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, network, nodes>>

BecomePreCandidate(i) ==
    /\ state[i] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ LET req(j) == [type |-> "RequestVoteReq", src |-> i, dest |-> j,
                      term |-> currentTerm[i] + 1, prevote |-> TRUE,
                      lastLogIndex |-> LastLogIndex(log[i]),
                      lastLogTerm |-> LastLogTerm(log[i], snapshotLastIndex[i], snapshotLastTerm[i])]
       IN network' = network \cup {req(j) : j \in nodes \ {i}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

BecomeCandidate(i) ==
    /\ state[i] = "PRECANDIDATE"
    /\ state' = [state EXCEPT ![i] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ LET req(j) == [type |-> "RequestVoteReq", src |-> i, dest |-> j,
                      term |-> currentTerm[i] + 1, prevote |-> FALSE,
                      lastLogIndex |-> LastLogIndex(log[i]),
                      lastLogTerm |-> LastLogTerm(log[i], snapshotLastIndex[i], snapshotLastTerm[i])]
       IN network' = network \cup {req(j) : j \in nodes \ {i}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

BecomeLeader(i) ==
    /\ state[i] \in {"CANDIDATE"}
    /\ Cardinality(votesGranted[i]) >= Majority(nodes)
    /\ state' = [state EXCEPT ![i] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ LET lastIdx == LastLogIndex(log[i])
       IN nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> lastIdx + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ log' = [log EXCEPT ![i] = Append(log[i], LogEntry(currentTerm[i], "NoOp", ""))]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, network, nodes>>

\* Vote Processing
RecvRequestVote(i, msg) ==
    /\ msg["type"] = "RequestVoteReq"
    /\ msg["dest"] = i
    /\ LET myLastLogIndex == LastLogIndex(log[i])
           myLastLogTerm == LastLogTerm(log[i], snapshotLastIndex[i], snapshotLastTerm[i])
           grant == \/ msg["term"] > currentTerm[i]
                    \/ (msg["term"] = currentTerm[i] /\ (votedFor[i] = Nil \/ votedFor[i] = msg["src"]))
           upToDate == IsUpToDate(msg["lastLogTerm"], msg["lastLogIndex"], myLastLogTerm, myLastLogIndex)
           voteGranted == grant /\ upToDate
           newTerm == IF msg["term"] > currentTerm[i] THEN msg["term"] ELSE currentTerm[i]
           resp == [type |-> "RequestVoteResp", src |-> i, dest |-> msg["src"],
                    term |-> newTerm, voteGranted |-> voteGranted, prevote |-> msg["prevote"]]
    IN /\ network' = (network \ {msg}) \cup {resp}
       /\ IF msg["term"] > currentTerm[i] THEN
            /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = msg["term"]]
            /\ votedFor' = [votedFor EXCEPT ![i] = IF voteGranted /\ ~msg["prevote"] THEN msg["src"] ELSE Nil]
       ELSE
            /\ state' = state
            /\ currentTerm' = currentTerm
            /\ votedFor' = [votedFor EXCEPT ![i] = IF voteGranted /\ ~msg["prevote"] THEN msg["src"] ELSE votedFor[i]]
       /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

RecvRequestVoteResponse(i, msg) ==
    /\ msg["type"] = "RequestVoteResp"
    /\ msg["dest"] = i
    /\ network' = network \ {msg}
    /\ IF msg["term"] > currentTerm[i] THEN
        BecomeFollower(i, msg["term"])
    ELSE
        (* TLC-FIX: Removed erroneous /\ from IF/ELSE construct to form a single expression. *)
        IF msg["voteGranted"] THEN
            IF msg["prevote"] /\ state[i] = "PRECANDIDATE" /\ msg["term"] = currentTerm[i] + 1 THEN
                votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {msg["src"]}]
                /\ IF Cardinality(votesGranted'[i]) >= Majority(nodes) THEN
                    BecomeCandidate(i)
                ELSE
                    UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>
            ELSE IF ~msg["prevote"] /\ state[i] = "CANDIDATE" /\ msg["term"] = currentTerm[i] THEN
                votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {msg["src"]}]
                /\ IF Cardinality(votesGranted'[i]) >= Majority(nodes) THEN
                    BecomeLeader(i)
                ELSE
                    UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>
            ELSE
                UNCHANGED vars
        ELSE
            UNCHANGED vars

\* Log Replication
SendAppendEntries(i, j) ==
    /\ state[i] = "LEADER"
    /\ j \in nodes \ {i}
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex = 0 THEN 0
                          ELSE IF prevLogIndex = snapshotLastIndex[i] THEN snapshotLastTerm[i]
                          ELSE log[i][prevLogIndex]["term"]
           entriesToSend == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
           msg == [type |-> "AppendEntriesReq", src |-> i, dest |-> j,
                   term |-> currentTerm[i], prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm, entries |-> entriesToSend,
                   leaderCommit |-> commitIndex[i]]
    IN /\ network' = network \cup {msg}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

RecvAppendEntries(i, msg) ==
    /\ msg["type"] = "AppendEntriesReq"
    /\ msg["dest"] = i
    /\ LET resp(success, matchIdx) == [type |-> "AppendEntriesResp", src |-> i, dest |-> msg["src"],
                                       term |-> currentTerm[i], success |-> success, matchIndex |-> matchIdx]
    IN /\ IF msg["term"] < currentTerm[i] THEN
            /\ network' = (network \ {msg}) \cup {resp(FALSE, 0)}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>
       ELSE
            /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = msg["term"]]
            /\ leaderId' = [leaderId EXCEPT ![i] = msg["src"]]
            /\ LET logOK == \/ msg["prevLogIndex"] = 0
                          \/ /\ msg["prevLogIndex"] <= Len(log[i])
                             /\ log[i][msg["prevLogIndex"]]["term"] = msg["prevLogTerm"]
               IN IF logOK THEN
                    LET ConflictingIndices == {k \in 1..Len(msg["entries"]) :
                                                 msg["prevLogIndex"] + k > Len(log[i]) \/ log[i][msg["prevLogIndex"] + k]["term"] # msg["entries"][k]["term"]}
                        conflictIndex == IF ConflictingIndices = {} THEN 0 ELSE CHOOSE k \in ConflictingIndices : TRUE
                        (* TLC-FIX: Replaced non-standard AppendSeq with standard sequence concatenation operator \o *)
                        newLog == IF conflictIndex = 0 THEN
                                      log[i] \o msg["entries"]
                                  ELSE
                                      (SubSeq(log[i], 1, msg["prevLogIndex"] + conflictIndex - 1)) \o
                                      (SubSeq(msg["entries"], conflictIndex, Len(msg["entries"])))
                        newMatchIndex == msg["prevLogIndex"] + Len(msg["entries"])
                    IN log' = [log EXCEPT ![i] = newLog]
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({msg["leaderCommit"], newMatchIndex})]
                       /\ network' = (network \ {msg}) \cup {resp(TRUE, newMatchIndex)}
                ELSE
                    log' = log
                    /\ commitIndex' = commitIndex
                    /\ network' = (network \ {msg}) \cup {resp(FALSE, 0)}
            /\ UNCHANGED <<votedFor, lastApplied, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, nodes>>

RecvAppendEntriesResponse(i, msg) ==
    /\ msg["type"] = "AppendEntriesResp"
    /\ msg["dest"] = i
    /\ state[i] = "LEADER"
    /\ network' = network \ {msg}
    /\ IF msg["term"] > currentTerm[i] THEN
        BecomeFollower(i, msg["term"])
    ELSE
        /\ (IF msg["success"] THEN
            (   matchIndex' = [matchIndex EXCEPT ![i][msg["src"]] = msg["matchIndex"]]
            /\ nextIndex' = [nextIndex EXCEPT ![i][msg["src"]] = msg["matchIndex"] + 1]
            /\ LET ReplicatedBy(n) == {j \in nodes | matchIndex'[i][j] >= n} \cup {i}
                   PossibleCommits == {n \in {commitIndex[i] + 1 .. Len(log[i])} |
                                         /\ log[i][n]["term"] = currentTerm[i]
                                         /\ Cardinality(ReplicatedBy(n)) >= Majority(nodes)}
               IN commitIndex' = [commitIndex EXCEPT ![i] = IF PossibleCommits = {} THEN commitIndex[i] ELSE Max(PossibleCommits)])
        ELSE
            (   nextIndex' = [nextIndex EXCEPT ![i][msg["src"]] = Max({1, nextIndex[i][msg["src"]] - 1})]
            /\ UNCHANGED <<matchIndex, commitIndex>>))
        /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

\* Leader Operations
ClientRequest(i, type, data) ==
    /\ state[i] = "LEADER"
    /\ type \in EntryTypes
    /\ data \in IF type \in {"AddNode", "RemoveNode"} THEN Servers ELSE {""}
    /\ log' = [log EXCEPT ![i] = Append(log[i], LogEntry(currentTerm[i], type, data))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, network, nodes>>

\* Election Management
ElectionTimeout(i) ==
    /\ state[i] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ BecomePreCandidate(i)

\* Log Management
Apply(i) ==
    /\ commitIndex[i] > lastApplied[i]
    /\ LET idx == lastApplied[i] + 1
           entry == log[i][idx]
    IN /\ lastApplied' = [lastApplied EXCEPT ![i] = idx]
       /\ IF entry["type"] = "AddNode" THEN
            nodes' = nodes \cup {entry["data"]}
          ELSE IF entry["type"] = "RemoveNode" THEN
            nodes' = nodes \ {entry["data"]}
          ELSE
            nodes' = nodes
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, network>>

\* Periodic Tasks
PeriodicHeartbeat(i) ==
    /\ state[i] = "LEADER"
    /\ \E j \in nodes \ {i} : SendAppendEntries(i, j)

\* Snapshot Handling
CompactLog(i) ==
    /\ commitIndex[i] > snapshotLastIndex[i]
    /\ \E idx \in {snapshotLastIndex[i] + 1 .. commitIndex[i]} :
        /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = idx]
        /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = log[i][idx]["term"]]
        /\ log' = [log EXCEPT ![i] = SubSeq(log[i], idx + 1, Len(log[i]))]
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, network, nodes>>

SendSnapshot(i, j) ==
    /\ state[i] = "LEADER"
    /\ j \in nodes \ {i}
    /\ nextIndex[i][j] <= snapshotLastIndex[i]
    /\ LET msg == [type |-> "SnapshotReq", src |-> i, dest |-> j,
                   term |-> currentTerm[i],
                   lastIncludedIndex |-> snapshotLastIndex[i],
                   lastIncludedTerm |-> snapshotLastTerm[i]]
    IN /\ network' = network \cup {msg}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

RecvSnapshot(i, msg) ==
    /\ msg["type"] = "SnapshotReq"
    /\ msg["dest"] = i
    /\ LET resp == [type |-> "SnapshotResp", src |-> i, dest |-> msg["src"], term |-> currentTerm[i]]
    IN /\ network' = (network \ {msg}) \cup {resp}
       /\ IF msg["term"] < currentTerm[i] THEN
            UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>
       ELSE
            /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = msg["term"]]
            /\ leaderId' = [leaderId EXCEPT ![i] = msg["src"]]
            /\ IF msg["lastIncludedIndex"] > commitIndex[i] THEN
                log' = [log EXCEPT ![i] = <<>>]
                /\ commitIndex' = [commitIndex EXCEPT ![i] = msg["lastIncludedIndex"]]
                /\ lastApplied' = [lastApplied EXCEPT ![i] = msg["lastIncludedIndex"]]
                /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = msg["lastIncludedIndex"]]
                /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = msg["lastIncludedTerm"]]
            ELSE
                UNCHANGED <<log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm>>
            /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votesGranted, nodes>>

\* Network unreliability
DropMessage(msg) ==
    /\ msg \in network
    /\ network' = network \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, nodes>>

Next ==
    \/ \E i \in nodes : ElectionTimeout(i)
    \/ \E i \in nodes : PeriodicHeartbeat(i)
    \/ \E i \in nodes : Apply(i)
    \/ \E i \in nodes : CompactLog(i)
    \/ \E i, j \in nodes : SendSnapshot(i, j)
    \/ \E i \in nodes, type \in EntryTypes, data \in Servers \cup {""} : ClientRequest(i, type, data)
    \/ \E msg \in network :
        \/ \E i \in nodes : RecvRequestVote(i, msg)
        \/ \E i \in nodes : RecvRequestVoteResponse(i, msg)
        \/ \E i \in nodes : RecvAppendEntries(i, msg)
        \/ \E i \in nodes : RecvAppendEntriesResponse(i, msg)
        \/ \E i \in nodes : RecvSnapshot(i, msg)
        \/ DropMessage(msg)

Spec == Init /\ [][Next]_vars

====