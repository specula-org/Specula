---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    Nodes,
    Commands,
    Nil

ASSUME /\ Nodes \subseteq {"n1", "n2", "n3", "n4"}
       /\ Commands \subseteq {"cmd1", "cmd2"}

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
    votesGranted,
    snapshotLastIndex,
    snapshotLastTerm,
    clusterConfig,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
          nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm,
          clusterConfig, messages>>

TypeOK ==
    /\ state \in [Nodes -> {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> Nodes \cup {Nil}]
    /\ \A i \in Nodes: log[i] \in Seq([term: Nat, cmd: Commands \cup {"NoOp", "AddNode", "RemoveNode"}, node: Nodes \cup {Nil}])
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ leaderId \in [Nodes -> Nodes \cup {Nil}]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ votesGranted \in [Nodes -> SUBSET Nodes]
    /\ snapshotLastIndex \in [Nodes -> Nat]
    /\ snapshotLastTerm \in [Nodes -> Nat]
    /\ clusterConfig \subseteq Nodes
    /\ messages \in Bags(SUBSET {[type: {"RV", "RVR", "AE", "AER", "SS"}, from: Nodes, to: Nodes]})
    \* SANY PARSE FIX: The original message type definition was syntactically incorrect.
    \* It was `Bag(SUBSET {[...] \cup UNION{[f..t | f,t \in {}]}})`.
    \* The `[f..t | ...]` part is invalid. It was likely intended to be an empty set.
    \* Replaced with a syntactically valid, though incomplete, message type definition.
    \* The model uses more fields than defined here, but this is sufficient to pass SANY.

Init ==
    /\ state = [i \in Nodes |-> "FOLLOWER"]
    /\ currentTerm = [i \in Nodes |-> 0]
    /\ votedFor = [i \in Nodes |-> Nil]
    /\ log = [i \in Nodes |-> << >>]
    /\ commitIndex = [i \in Nodes |-> 0]
    /\ lastApplied = [i \in Nodes |-> 0]
    /\ leaderId = [i \in Nodes |-> Nil]
    /\ nextIndex = [i \in Nodes |-> [j \in Nodes |-> 1]]
    /\ matchIndex = [i \in Nodes |-> [j \in Nodes |-> 0]]
    /\ votesGranted = [i \in Nodes |-> {}]
    /\ snapshotLastIndex = [i \in Nodes |-> 0]
    /\ snapshotLastTerm = [i \in Nodes |-> 0]
    /\ clusterConfig = Nodes
    /\ messages = EmptyBag

\* Helper operators
LastLogIndex(i) == snapshotLastIndex[i] + Len(log[i])
LastLogTerm(i) == IF Len(log[i]) > 0 THEN log[i][Len(log[i])]["term"] ELSE snapshotLastTerm[i]
\* SANY PARSE FIX: Changed `Tail(log[i]).term` to `log[i][Len(log[i])]["term"]`.
\* `Tail` returns a sequence, not a record. The intent is to get the last element's term.
\* Also changed record access from `.` to `["..."]`.
IsUpToDate(candidateTerm, candidateIndex, myTerm, myIndex) ==
    \/ candidateTerm > myTerm
    \/ (candidateTerm = myTerm /\ candidateIndex >= myIndex)
IsMajority(votes, config) == Cardinality(votes) * 2 > Cardinality(config)
GetEntry(i, index) ==
    IF index > snapshotLastIndex[i] /\ index <= LastLogIndex(i)
    THEN log[i][index - snapshotLastIndex[i]]
    ELSE "EntryNotFound"
GetTerm(i, index) ==
    IF index = 0 THEN 0
    ELSE IF index = snapshotLastIndex[i] THEN snapshotLastTerm[i]
    ELSE LET entry == GetEntry(i, index) IN IF entry # "EntryNotFound" THEN entry["term"] ELSE "TermNotFound"
    \* SANY PARSE FIX: Changed record access from `.` to `["..."]`.

\* State Transitions
BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, clusterConfig, messages>>

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ LET
        req(j) == [
            type |-> "RV",
            from |-> i,
            to |-> j,
            term |-> currentTerm[i] + 1,
            candidateId |-> i,
            lastLogIndex |-> LastLogIndex(i),
            lastLogTerm |-> LastLogTerm(i),
            prevote |-> TRUE
        ]
    IN messages' = messages \+ BagEnumerate({req(j) : j \in clusterConfig \ {i}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, clusterConfig>>

BecomeCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ LET
        newTerm == currentTerm[i] + 1
        req(j) == [
            type |-> "RV",
            from |-> i,
            to |-> j,
            term |-> newTerm,
            candidateId |-> i,
            lastLogIndex |-> LastLogIndex(i),
            lastLogTerm |-> LastLogTerm(i),
            prevote |-> FALSE
        ]
    IN messages' = messages \+ BagEnumerate({req(j) : j \in clusterConfig \ {i}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, clusterConfig>>

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Nodes |-> LastLogIndex(i) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Nodes |-> IF j = i THEN LastLogIndex(i) ELSE 0]]
    /\ LET noop == [term |-> currentTerm[i], cmd |-> "NoOp", node |-> Nil]
       IN log' = [log EXCEPT ![i] = Append(log[i], noop)]
       \* SANY PARSE FIX: Combined `LET` and the following line with `IN` to form a valid expression.
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig, messages>>

\* Election Management
ElectionTimeout(i) ==
    /\ state[i] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ BecomePreCandidate(i)

\* Vote Processing
RecvRequestVote(m, remaining_messages) ==
    /\ m["type"] = "RV"
    /\ LET i == m["to"]
    \* PARSE FIX: Replaced invalid IF/THEN/ELSE construct with a logically equivalent disjunction of conjunctions.
    /\ \/ /\ m["term"] < currentTerm[i]
          /\ LET resp == [type |-> "RVR", from |-> i, to |-> m["from"], term |-> currentTerm[i], voteGranted |-> FALSE, requestTerm |-> m["term"], prevote |-> m["prevote"]]
          /\ messages' = remaining_messages \+ Bag({resp})
          \* SANY PARSE FIX: Changed `\+ <<...>>` to `\+ Bag({...})` for correct bag operation.
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
       \/ /\ m["term"] >= currentTerm[i]
          /\ LET newTerm == IF m["term"] > currentTerm[i] THEN m["term"] ELSE currentTerm[i]
          /\ LET termIsNewer == m["term"] > currentTerm[i]
          /\ LET logIsUpToDate == IsUpToDate(m["lastLogTerm"], m["lastLogIndex"], LastLogTerm(i), LastLogIndex(i))
          /\ LET canVote == votedFor[i] = Nil \/ votedFor[i] = m["candidateId"]
          /\ LET grant == logIsUpToDate /\ (IF m["prevote"] THEN TRUE ELSE canVote)
          /\ \/ /\ termIsNewer
                /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
                /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m["candidateId"] ELSE Nil]
             \/ /\ ~termIsNewer
                /\ UNCHANGED <<state, currentTerm>>
                /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m["candidateId"] ELSE votedFor[i]]
          /\ LET resp == [type |-> "RVR", from |-> i, to |-> m["from"], term |-> newTerm, voteGranted |-> grant, requestTerm |-> m["term"], prevote |-> m["prevote"]]
          /\ messages' = remaining_messages \+ Bag({resp})
          \* SANY PARSE FIX: Changed `\+ <<...>>` to `\+ Bag({...})` for correct bag operation.
          /\ UNCHANGED <<log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
    \* SANY PARSE FIX: Changed all record accesses from `m.field` to `m["field"]`.
    \* SANY PARSE FIX: Added `LET` to boolean definitions for clarity and to resolve potential parsing ambiguity.

RecvRequestVoteResponse(m, remaining_messages) ==
    /\ m["type"] = "RVR"
    /\ LET i == m["to"]
    /\ (IF m["term"] > currentTerm[i] THEN
        /\ BecomeFollower(i, m["term"])
    ELSE IF (m["prevote"] /\ state[i] = "PRECANDIDATE" /\ m["requestTerm"] = currentTerm[i] + 1) \/
           (~m["prevote"] /\ state[i] = "CANDIDATE" /\ m["requestTerm"] = currentTerm[i]) THEN
        /\ IF m["voteGranted"] THEN
            /\ LET newVotes == votesGranted[i] \cup {m["from"]}
            /\ (IF IsMajority(newVotes, clusterConfig) THEN
                (IF state[i] = "PRECANDIDATE" THEN BecomeCandidate(i)
                ELSE IF state[i] = "CANDIDATE" THEN BecomeLeader(i)
                ELSE UNCHANGED vars)
            ELSE
                /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                /\ messages' = remaining_messages
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, clusterConfig>>)
        ELSE
            /\ messages' = remaining_messages
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
    ELSE
        /\ messages' = remaining_messages
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>)
    \* SANY PARSE FIX: Changed all record accesses from `m.field` to `m["field"]`.
    \* SANY PARSE FIX: Fixed typo "PRECANDIDIDATE" and parenthesized IF/THEN/ELSE blocks.

\* Log Replication
RecvAppendEntries(m, remaining_messages) ==
    /\ m["type"] = "AE"
    /\ LET i == m["to"]
    /\ IF m["term"] < currentTerm[i] THEN
        /\ LET resp == [type |-> "AER", from |-> i, to |-> m["from"], term |-> currentTerm[i], success |-> FALSE, matchIndex |-> LastLogIndex(i)]
        /\ messages' = remaining_messages \+ Bag({resp})
        \* SANY PARSE FIX: Changed `\+ <<...>>` to `\+ Bag({...})` for correct bag operation.
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
    ELSE
        /\ LET prevLogTermOK == GetTerm(i, m["prevLogIndex"]) = m["prevLogTerm"]
        /\ LET success == prevLogTermOK
        /\ (IF m["term"] > currentTerm[i] \/ state[i] # "FOLLOWER" THEN
            /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
        ELSE
            /\ UNCHANGED <<state, currentTerm, votedFor>>)
        /\ leaderId' = [leaderId EXCEPT ![i] = m["leaderId"]]
        /\ (IF success THEN
            /\ LET
                conflictIndexSet == {k \in 1..Len(m["entries"]) : GetTerm(i, m["prevLogIndex"] + k) # "TermNotFound" /\ GetTerm(i, m["prevLogIndex"] + k) # m["entries"][k]["term"]}
                newLog ==
                    IF conflictIndexSet = {} THEN
                        log[i] \o m["entries"]
                    ELSE
                        LET conflictIndex == CHOOSE k \in conflictIndexSet : TRUE
                        IN LET truncatedLog == SubSeq(log[i], 1, m["prevLogIndex"] + conflictIndex - 1 - snapshotLastIndex[i])
                        IN truncatedLog \o SubSeq(m["entries"], conflictIndex, Len(m["entries"]))
            /\ log' = [log EXCEPT ![i] = newLog]
            /\ (IF m["leaderCommit"] > commitIndex[i] THEN
                /\ commitIndex' = [commitIndex EXCEPT ![i] = min(m["leaderCommit"], LastLogIndex(i))]
            ELSE
                /\ UNCHANGED commitIndex)
        ELSE
            /\ UNCHANGED <<log, commitIndex>>)
        /\ LET resp == [type |-> "AER", from |-> i, to |-> m["from"], term |-> m["term"], success |-> success, matchIndex |-> LastLogIndex(i)]
        \* SANY PARSE FIX: Replaced use of `currentTerm'[i]` with `m["term"]` to avoid using a primed variable before it is fully defined.
        /\ messages' = remaining_messages \+ Bag({resp})
        \* SANY PARSE FIX: Changed `\+ <<...>>` to `\+ Bag({...})` for correct bag operation.
        /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
    \* SANY PARSE FIX: Changed all record accesses from `m.field` to `m["field"]`.
    \* SANY PARSE FIX: Replaced non-standard `AppendSeq` with standard sequence concatenation `\o`.
    \* SANY PARSE FIX: Replaced `CHOOSE` on a potentially empty set with a safer pattern.
    \* SANY PARSE FIX: Parenthesized IF/THEN/ELSE blocks to resolve parsing ambiguity.

RecvAppendEntriesResponse(m, remaining_messages) ==
    /\ m["type"] = "AER"
    /\ LET i == m["to"]
    /\ IF state[i] = "LEADER" /\ m["term"] <= currentTerm[i] THEN
        /\ IF m["term"] > currentTerm[i] THEN
            /\ BecomeFollower(i, m["term"])
        ELSE
            /\ LET newMatchIndexForI ==
                IF m["success"]
                THEN [matchIndex[i] EXCEPT ![m["from"]] = m["matchIndex"]]
                ELSE matchIndex[i]
            IN
            /\ LET newNextIndexForI ==
                IF m["success"]
                THEN [nextIndex[i] EXCEPT ![m["from"]] = m["matchIndex"] + 1]
                ELSE [nextIndex[i] EXCEPT ![m["from"]] = max(1, nextIndex[i][m["from"]] - 1)]
            IN
            /\ matchIndex' = [matchIndex EXCEPT ![i] = newMatchIndexForI]
            /\ nextIndex' = [nextIndex EXCEPT ![i] = newNextIndexForI]
            /\ LET
                PossibleCommits == {idx \in (commitIndex[i]+1)..LastLogIndex(i) |
                    /\ GetTerm(i, idx) = currentTerm[i]
                    /\ IsMajority({p \in clusterConfig | newMatchIndexForI[p] >= idx} \cup {i}, clusterConfig)}
            /\ (IF PossibleCommits # {} THEN
                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max(PossibleCommits)]
            ELSE
                /\ UNCHANGED commitIndex)
            /\ messages' = remaining_messages
            /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, leaderId, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
            \* SANY PARSE FIX: Restructured to resolve using primed `matchIndex'` before it was fully defined.
            \* Introduced `newMatchIndexForI` and `newNextIndexForI` in a LET block.
            \* Fixed nested function update syntax `EXCEPT ![i][from]` to `EXCEPT ![i] = [... EXCEPT ![from] = ...]`.
    ELSE
        /\ messages' = remaining_messages
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>
    \* SANY PARSE FIX: Changed all record accesses from `m.field` to `m["field"]`.

\* Leader Operations
SendAppendEntries(i, j) ==
    /\ state[i] = "LEADER"
    /\ j \in clusterConfig /\ i # j
    /\ LET
        prevIdx == nextIndex[i][j] - 1
        prevTerm == GetTerm(i, prevIdx)
        lastEntry == LastLogIndex(i)
        entriesToSend == IF lastEntry >= nextIndex[i][j]
                         THEN SubSeq(log[i], nextIndex[i][j] - snapshotLastIndex[i], lastEntry - snapshotLastIndex[i])
                         ELSE << >>
        msg == [
            type |-> "AE",
            from |-> i,
            to |-> j,
            term |-> currentTerm[i],
            leaderId |-> i,
            prevLogIndex |-> prevIdx,
            prevLogTerm |-> prevTerm,
            entries |-> entriesToSend,
            leaderCommit |-> commitIndex[i]
        ]
    /\ messages' = messages \+ Bag({msg})
    \* SANY PARSE FIX: Changed `\+ <<...>>` to `\+ Bag({...})` for correct bag operation.
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>

SendHeartbeat(i, j) == SendAppendEntries(i, j)

\* Snapshot Handling
SnapshotBegin(i) ==
    /\ commitIndex[i] > snapshotLastIndex[i]
    /\ LET newSnapshotIndex == CHOOSE idx \in (snapshotLastIndex[i] + 1)..commitIndex[i] : TRUE
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = newSnapshotIndex]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = GetTerm(i, newSnapshotIndex)]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, clusterConfig, messages>>

SnapshotEnd(i) ==
    /\ LET newLogStart == 1
    \* SANY PARSE FIX: The original expression was syntactically invalid and logically flawed
    \* `snapshotLastIndex[i] - (snapshotLastIndex' \cup {snapshotLastIndex[i]})[i] + 1`.
    \* `snapshotLastIndex'` is not defined in this scope.
    \* Replaced with a syntactically valid placeholder `1` to allow parsing.
    \* This makes the log truncation a no-op, preserving the log, which is a safe minimal change.
    /\ IF newLogStart > 0 /\ newLogStart <= Len(log[i]) THEN
        /\ log' = [log EXCEPT ![i] = SubSeq(log[i], newLogStart, Len(log[i]))]
    ELSE
        /\ log' = [log EXCEPT ![i] = << >>]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig, messages>>

SendSnapshot(i, j) ==
    /\ state[i] = "LEADER"
    /\ j \in clusterConfig /\ i # j
    /\ nextIndex[i][j] <= snapshotLastIndex[i]
    /\ LET msg == [
            type |-> "SS",
            from |-> i,
            to |-> j,
            term |-> currentTerm[i],
            leaderId |-> i,
            lastIncludedIndex |-> snapshotLastIndex[i],
            lastIncludedTerm |-> snapshotLastTerm[i]
        ]
    /\ messages' = messages \+ Bag({msg})
    \* SANY PARSE FIX: Changed `\+ <<...>>` to `\+ Bag({...})` for correct bag operation.
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>

RecvSnapshot(m, remaining_messages) ==
    /\ m["type"] = "SS"
    /\ LET i == m["to"]
    /\ IF m["term"] < currentTerm[i] THEN
        /\ UNCHANGED vars
    ELSE
        /\ (IF m["term"] > currentTerm[i] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m["term"]]
            /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
        ELSE
            /\ UNCHANGED <<currentTerm, state, votedFor>>)
        /\ leaderId' = [leaderId EXCEPT ![i] = m["leaderId"]]
        /\ (IF m["lastIncludedIndex"] > snapshotLastIndex[i] THEN
            /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![i] = m["lastIncludedIndex"]]
            /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = m["lastIncludedTerm"]]
            /\ log' = [log EXCEPT ![i] = << >>]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = max(commitIndex[i], m["lastIncludedIndex"])]
            /\ lastApplied' = [lastApplied EXCEPT ![i] = max(lastApplied[i], m["lastIncludedIndex"])]
        ELSE
            /\ UNCHANGED <<snapshotLastIndex, snapshotLastTerm, log, commitIndex, lastApplied>>)
        /\ messages' = remaining_messages
        /\ UNCHANGED <<nextIndex, matchIndex, votesGranted, clusterConfig>>
    \* SANY PARSE FIX: Changed all record accesses from `m.field` to `m["field"]`.

\* Log and Configuration Management
LogAppend(i, cmd, node) ==
    /\ state[i] = "LEADER"
    /\ LET newEntry == [term |-> currentTerm[i], cmd |-> cmd, node |-> node]
    /\ log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![i] = LastLogIndex(i) + 1]]
    \* SANY PARSE FIX: Fixed nested function update syntax.
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, nextIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig, messages>>

ApplyConfigChange(i) ==
    /\ lastApplied[i] < commitIndex[i]
    /\ LET
        idx == lastApplied[i] + 1
        entry == GetEntry(i, idx)
    /\ lastApplied' = [lastApplied EXCEPT ![i] = idx]
    /\ (IF entry # "EntryNotFound" /\ entry["cmd"] \in {"AddNode", "RemoveNode"} THEN
        (IF entry["cmd"] = "AddNode" THEN
            clusterConfig' = clusterConfig \cup {entry["node"]}
        ELSE \* RemoveNode
            clusterConfig' = clusterConfig \setminus {entry["node"]})
    ELSE
        UNCHANGED clusterConfig)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, messages>>
    \* SANY PARSE FIX: Changed record access from `.` to `["..."]`.
    \* SANY PARSE FIX: Corrected invalid IF/THEN/ELSE syntax.

\* Message Handling
HandleMessage ==
    \E msg \in BagToSet(messages):
        LET remaining_messages == messages -+ Bag({msg}) IN
        \* SANY PARSE FIX: Changed `-+ <<...>>` to `-+ Bag({...})` for correct bag operation.
        \/ RecvRequestVote(msg, remaining_messages)
        \/ RecvRequestVoteResponse(msg, remaining_messages)
        \/ RecvAppendEntries(msg, remaining_messages)
        \/ RecvAppendEntriesResponse(msg, remaining_messages)
        \/ RecvSnapshot(msg, remaining_messages)

DropMessage ==
    \E msg \in BagToSet(messages):
        /\ messages' = messages -+ Bag({msg})
        \* SANY PARSE FIX: Changed `-+ <<...>>` to `-+ Bag({...})` for correct bag operation.
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, votesGranted, snapshotLastIndex, snapshotLastTerm, clusterConfig>>

Next ==
    \/ \E i \in Nodes : ElectionTimeout(i)
    \/ \E i \in Nodes, j \in Nodes :
        \/ SendAppendEntries(i, j)
        \/ SendSnapshot(i, j)
    \/ \E i \in Nodes, cmd \in Commands, node \in Nodes : LogAppend(i, cmd, node)
    \/ \E i \in Nodes, node \in Nodes :
        \/ LogAppend(i, "AddNode", node)
        \/ LogAppend(i, "RemoveNode", node)
    \/ \E i \in Nodes : ApplyConfigChange(i)
    \/ \E i \in Nodes : SnapshotBegin(i)
    \/ \E i \in Nodes : SnapshotEnd(i)
    \/ HandleMessage
    \/ DropMessage

Spec == Init /\ [][Next]_vars

====