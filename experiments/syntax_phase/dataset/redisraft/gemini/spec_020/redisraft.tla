---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags, Strings

CONSTANTS Server, Value, ConfigChangeValue, Nil

ASSUME Server \subseteq TLC!Printable
ASSUME Value \subseteq TLC!Printable
ASSUME ConfigChangeValue \subseteq Server
ASSUME Nil \notin Server

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
    preVotesGranted,
    messages,
    config,
    lastIncludedIndex,
    lastIncludedTerm

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, votesGranted, preVotesGranted, messages, config,
          lastIncludedIndex, lastIncludedTerm>>

LogEntry(term, val, type, id) == [term |-> term, value |-> val, type |-> type, id |-> id]
NoOp(term, id) == LogEntry(term, Nil, "NO_OP", id)

LastLogIndex(s) == IF Len(log[s]) = 0 THEN lastIncludedIndex[s] ELSE lastIncludedIndex[s] + Len(log[s])
LastLogTerm(s) ==
    IF Len(log[s]) = 0
    THEN lastIncludedTerm[s]
    ELSE log[s][Len(log[s])]["term"]

GetEntry(s, idx) ==
    IF idx > lastIncludedIndex[s] /\ idx <= LastLogIndex(s)
    THEN log[s][idx - lastIncludedIndex[s]]
    ELSE [term |-> 0, value |-> Nil, type |-> "NIL", id |-> 0]

IsMoreUpToDate(s, candLastLogIndex, candLastLogTerm) ==
    LET myLastLogTerm == LastLogTerm(s) IN
    LET myLastLogIndex == LastLogIndex(s) IN
    \/ candLastLogTerm > myLastLogTerm
    \/ (candLastLogTerm = myLastLogTerm /\ candLastLogIndex >= myLastLogIndex)

IsMajority(subset) == Cardinality(subset) * 2 > Cardinality(config)

TypeOK ==
    /\ state \in [Server -> {"follower", "precandidate", "candidate", "leader"}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A s \in Server: log[s] \in Seq([term: Nat, value: Value \cup ConfigChangeValue \cup {Nil}, type: String, id: Nat])
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ preVotesGranted \in [Server -> SUBSET Server]
    /\ messages \in SUBSET (
        [type: {"RequestVote"}, term: Nat, lastLogIndex: Nat, lastLogTerm: Nat, candidateId: Server, prevote: BOOLEAN, src: Server, dest: Server] \cup
        [type: {"RequestVoteResponse"}, term: Nat, requestTerm: Nat, voteGranted: BOOLEAN, prevote: BOOLEAN, src: Server, dest: Server] \cup
        [type: {"AppendEntries"}, term: Nat, leaderId: Server, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq(ANY), leaderCommit: Nat, src: Server, dest: Server] \cup
        [type: {"AppendEntriesResponse"}, term: Nat, success: BOOLEAN, matchIndex: Nat, src: Server, dest: Server] \cup
        [type: {"InstallSnapshot"}, term: Nat, leaderId: Server, lastIncludedIndex: Nat, lastIncludedTerm: Nat, src: Server, dest: Server] \cup
        [type: {"InstallSnapshotResponse"}, term: Nat, success: BOOLEAN, src: Server, dest: Server]
    )
    /\ config \in SUBSET Server
    /\ lastIncludedIndex \in [Server -> Nat]
    /\ lastIncludedTerm \in [Server -> Nat]

Init ==
    /\ state = [s \in Server |-> "follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ preVotesGranted = [s \in Server |-> {}]
    /\ messages = {}
    /\ config = Server
    /\ lastIncludedIndex = [s \in Server |-> 0]
    /\ lastIncludedTerm = [s \in Server |-> 0]

\* State Transitions
BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, config, lastIncludedIndex, lastIncludedTerm>>

BecomePreCandidate(s) ==
    /\ state[s] = "follower"
    /\ s \in config
    /\ state' = [state EXCEPT ![s] = "precandidate"]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        { [ type |-> "RequestVote",
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            candidateId |-> s,
            prevote |-> TRUE,
            src |-> s,
            dest |-> p ] : p \in config \ {s} }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, config, lastIncludedIndex, lastIncludedTerm>>

BecomeCandidate(s) ==
    /\ state[s] \in {"precandidate", "candidate"}
    /\ s \in config
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = "candidate"]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        { [ type |-> "RequestVote",
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            candidateId |-> s,
            prevote |-> FALSE,
            src |-> s,
            dest |-> p ] : p \in config \ {s} }
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>

BecomeLeader(s) ==
    /\ state[s] = "candidate"
    /\ IsMajority(votesGranted[s])
    /\ state' = [state EXCEPT ![s] = "leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ LET noop == NoOp(currentTerm[s], 0) IN
       log' = [log EXCEPT ![s] = Append(@, noop)]
    /\ messages' = messages \cup
        { [ type |-> "AppendEntries",
            term |-> currentTerm[s],
            leaderId |-> s,
            prevLogIndex |-> LastLogIndex(s),
            prevLogTerm |-> LastLogTerm(s),
            entries |-> <<noop>>,
            leaderCommit |-> commitIndex[s],
            src |-> s,
            dest |-> p ] : p \in config \ {s} }
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>

\* Vote Processing
RecvRequestVote(s, msg) ==
    LET grant == \/ /\ msg["term"] > currentTerm[s]
                  \/ /\ msg["term"] = currentTerm[s]
                     /\ votedFor[s] \in {Nil, msg["candidateId"]}
                     /\ IsMoreUpToDate(s, msg["lastLogIndex"], msg["lastLogTerm"])
    IN
    /\ msg["dest"] = s
    /\ s \in config
    /\ IF msg["term"] < currentTerm[s]
       THEN /\ messages' = messages \cup {[ type |-> "RequestVoteResponse", term |-> currentTerm[s], requestTerm |-> msg["term"], voteGranted |-> FALSE, prevote |-> msg["prevote"], src |-> s, dest |-> msg["src"] ]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>
       ELSE /\ \/ /\ grant
                  /\ messages' = messages \cup {[ type |-> "RequestVoteResponse", term |-> msg["term"], requestTerm |-> msg["term"], voteGranted |-> TRUE, prevote |-> msg["prevote"], src |-> s, dest |-> msg["src"] ]}
                  /\ IF msg["prevote"]
                     THEN UNCHANGED <<votedFor>>
                     ELSE votedFor' = [votedFor EXCEPT ![s] = msg["candidateId"]]
                  /\ state' = [state EXCEPT ![s] = "follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![s] = msg["term"]]
               \/ /\ ~grant
                  /\ messages' = messages \cup {[ type |-> "RequestVoteResponse", term |-> msg["term"], requestTerm |-> msg["term"], voteGranted |-> FALSE, prevote |-> msg["prevote"], src |-> s, dest |-> msg["src"] ]}
                  /\ state' = [state EXCEPT ![s] = "follower"]
                  /\ currentTerm' = [currentTerm EXCEPT ![s] = msg["term"]]
                  /\ UNCHANGED <<votedFor>>
            /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>

RecvRequestVoteResponse(s, msg) ==
    /\ msg["dest"] = s
    /\ \/ /\ msg["prevote"]
          /\ state[s] = "precandidate"
          /\ msg["requestTerm"] = currentTerm[s] + 1
          /\ IF msg["voteGranted"]
             THEN LET newPreVotes == preVotesGranted[s] \cup {msg["src"]} IN
                  /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = newPreVotes]
                  /\ IF IsMajority(newPreVotes)
                     THEN BecomeCandidate(s)
                     ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted, messages, log, commitIndex, lastApplied, nextIndex, matchIndex, config, lastIncludedIndex, lastIncludedTerm>>
             ELSE UNCHANGED <<preVotesGranted, state, currentTerm, votedFor, votesGranted, messages, log, commitIndex, lastApplied, nextIndex, matchIndex, config, lastIncludedIndex, lastIncludedTerm>>
       \/ /\ ~msg["prevote"]
          /\ state[s] = "candidate"
          /\ msg["requestTerm"] = currentTerm[s]
          /\ IF msg["voteGranted"]
             THEN LET newVotes == votesGranted[s] \cup {msg["src"]} IN
                  /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                  /\ IF IsMajority(newVotes)
                     THEN BecomeLeader(s)
                     ELSE UNCHANGED <<state, nextIndex, matchIndex, log, messages, currentTerm, votedFor, commitIndex, lastApplied, config, lastIncludedIndex, lastIncludedTerm>>
             ELSE UNCHANGED <<votesGranted, state, nextIndex, matchIndex, log, messages, currentTerm, votedFor, commitIndex, lastApplied, config, lastIncludedIndex, lastIncludedTerm>>
    /\ UNCHANGED <<commitIndex, lastApplied, config, lastIncludedIndex, lastIncludedTerm>>

\* Log Replication
RecvAppendEntries(s, msg) ==
    /\ msg["dest"] = s
    /\ IF msg["term"] < currentTerm[s]
       THEN /\ messages' = messages \cup {[ type |-> "AppendEntriesResponse", term |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0, src |-> s, dest |-> msg["src"] ]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>
       ELSE LET prevLogOK == \/ msg["prevLogIndex"] = 0
                             \/ /\ msg["prevLogIndex"] <= LastLogIndex(s)
                                /\ msg["prevLogIndex"] >= lastIncludedIndex[s]
                                /\ GetEntry(s, msg["prevLogIndex"])["term"] = msg["prevLogTerm"]
            IN
            /\ state' = [state EXCEPT ![s] = "follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = msg["term"]]
            /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
            /\ IF prevLogOK
               THEN /\ LET newEntries == msg["entries"] IN
                       LET conflictingIndices == {i \in 1..Len(newEntries):
                                                msg["prevLogIndex"] + i <= LastLogIndex(s) /\
                                                GetEntry(s, msg["prevLogIndex"] + i)["term"] /= newEntries[i]["term"]}
                       IN
                       log' = [log EXCEPT ![s] =
                                IF conflictingIndices = {}
                                THEN SubSeq(log[s], 1, msg["prevLogIndex"] - lastIncludedIndex[s]) \o newEntries
                                ELSE LET conflictIndex == CHOOSE i \in conflictingIndices IN
                                     SubSeq(log[s], 1, msg["prevLogIndex"] + conflictIndex - 1 - lastIncludedIndex[s]) \o
                                     SubSeq(newEntries, conflictIndex, Len(newEntries))]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = Max(commitIndex[s], Min(msg["leaderCommit"], LastLogIndex(s) + Len(msg["entries"])))]
                    /\ messages' = messages \cup {[ type |-> "AppendEntriesResponse", term |-> msg["term"], success |-> TRUE, matchIndex |-> msg["prevLogIndex"] + Len(msg["entries"]), src |-> s, dest |-> msg["src"] ]}
               ELSE /\ messages' = messages \cup {[ type |-> "AppendEntriesResponse", term |-> msg["term"], success |-> FALSE, matchIndex |-> 0, src |-> s, dest |-> msg["src"] ]}
                    /\ UNCHANGED <<log, commitIndex>>
            /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>

RecvAppendEntriesResponse(s, msg) ==
    /\ msg["dest"] = s
    /\ state[s] = "leader"
    /\ IF msg["success"]
       THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg["src"]] = msg["matchIndex"] + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![msg["src"]] = msg["matchIndex"]]]
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg["src"]] = Max(1, @ - 1)]]
            /\ UNCHANGED <<matchIndex>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, preVotesGranted, messages, config, lastIncludedIndex, lastIncludedTerm>>

\* Leader Operations
SendAppendEntries(s, p) ==
    /\ state[s] = "leader"
    /\ p \in config \ {s}
    /\ LET prevIdx == nextIndex[s][p] - 1 IN
       IF prevIdx < lastIncludedIndex[s]
       THEN /\ messages' = messages \cup
                {[ type |-> "InstallSnapshot",
                   term |-> currentTerm[s],
                   leaderId |-> s,
                   lastIncludedIndex |-> lastIncludedIndex[s],
                   lastIncludedTerm |-> lastIncludedTerm[s],
                   src |-> s,
                   dest |-> p ]}
       ELSE /\ LET entriesToSend == SubSeq(log[s], prevIdx - lastIncludedIndex[s] + 1, Len(log[s])) IN
            /\ messages' = messages \cup
                {[ type |-> "AppendEntries",
                   term |-> currentTerm[s],
                   leaderId |-> s,
                   prevLogIndex |-> prevIdx,
                   prevLogTerm |-> GetEntry(s, prevIdx)["term"],
                   entries |-> entriesToSend,
                   leaderCommit |-> commitIndex[s],
                   src |-> s,
                   dest |-> p ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>

SendHeartbeat(s) ==
    /\ state[s] = "leader"
    /\ messages' = messages \cup
        { [ type |-> "AppendEntries",
            term |-> currentTerm[s],
            leaderId |-> s,
            prevLogIndex |-> LastLogIndex(s),
            prevLogTerm |-> LastLogTerm(s),
            entries |-> << >>,
            leaderCommit |-> commitIndex[s],
            src |-> s,
            dest |-> p ] : p \in config \ {s} }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, config, lastIncludedIndex, lastIncludedTerm>>

\* Election Management
ElectionStart(s) == BecomePreCandidate(s)
ElectionTimeout(s) == BecomeCandidate(s)

\* Log Management
LogAppend(s, val, type) ==
    /\ state[s] = "leader"
    /\ LET newEntry == LogEntry(currentTerm[s], val, type, 0) IN
       log' = [log EXCEPT ![s] = Append(@, newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, config, lastIncludedIndex, lastIncludedTerm>>

LogDelete(s, idx) ==
    /\ state[s] = "follower"
    /\ idx <= LastLogIndex(s)
    /\ log' = [log EXCEPT ![s] = SubSeq(@, 1, idx - 1 - lastIncludedIndex[s])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, config, lastIncludedIndex, lastIncludedTerm>>

LogCommit(s) ==
    /\ state[s] = "leader"
    /\ LET newCommitIndex ==
           CHOOSE N \in (commitIndex[s]+1)..LastLogIndex(s):
               /\ GetEntry(s, N)["term"] = currentTerm[s]
               /\ IsMajority({p \in config : matchIndex[s][p] >= N} \cup {s})
    IN
    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, config, lastIncludedIndex, lastIncludedTerm>>

\* Periodic Tasks
PeriodicElectionTimeout(s) == BecomePreCandidate(s)
PeriodicHeartbeat(s) == SendHeartbeat(s)

\* Node Management
AddNode(s, newNode) == LogAppend(s, newNode, "ADD_NODE")
RemoveNode(s, oldNode) == LogAppend(s, oldNode, "REMOVE_NODE")

\* Snapshot Handling
SnapshotBegin(s) ==
    /\ commitIndex[s] > lastIncludedIndex[s]
    /\ LET newLastIncludedIndex == commitIndex[s] IN
       LET newLastIncludedTerm == GetEntry(s, newLastIncludedIndex)["term"] IN
       LET newLog == SubSeq(log[s], newLastIncludedIndex - lastIncludedIndex[s] + 1, Len(log[s])) IN
       /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = newLastIncludedIndex]
       /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = newLastIncludedTerm]
       /\ log' = [log EXCEPT ![s] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, config>>

SnapshotEnd(s) == UNCHANGED vars

HandleInstallSnapshot(s, msg) ==
    /\ msg["dest"] = s
    /\ IF msg["term"] < currentTerm[s]
       THEN UNCHANGED vars
       ELSE /\ state' = [state EXCEPT ![s] = "follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = msg["term"]]
            /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
            /\ IF msg["lastIncludedIndex"] > commitIndex[s]
               THEN /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = msg["lastIncludedIndex"]]
                    /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = msg["lastIncludedTerm"]]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = msg["lastIncludedIndex"]]
                    /\ lastApplied' = [lastApplied EXCEPT ![s] = msg["lastIncludedIndex"]]
                    /\ log' = [log EXCEPT ![s] = << >>]
               ELSE UNCHANGED <<lastIncludedIndex, lastIncludedTerm, commitIndex, lastApplied, log>>
            /\ messages' = messages \cup {[ type |-> "InstallSnapshotResponse", term |-> msg["term"], success |-> TRUE, src |-> s, dest |-> msg["src"] ]}
            /\ UNCHANGED <<nextIndex, matchIndex, votesGranted, preVotesGranted, config>>

HandleInstallSnapshotResponse(s, msg) ==
    /\ msg["dest"] = s
    /\ state[s] = "leader"
    /\ IF msg["success"]
       THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg["src"]] = lastIncludedIndex[s] + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![msg["src"]] = lastIncludedIndex[s]]]
       ELSE UNCHANGED <<nextIndex, matchIndex>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, preVotesGranted, messages, config, lastIncludedIndex, lastIncludedTerm>>

\* Configuration
ApplyConfigChange(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ LET idxToApply == lastApplied[s] + 1 IN
       LET entry == GetEntry(s, idxToApply) IN
       /\ lastApplied' = [lastApplied EXCEPT ![s] = idxToApply]
       /\ IF entry["type"] \in {"ADD_NODE", "REMOVE_NODE"}
          THEN config' = IF entry["type"] = "ADD_NODE"
                         THEN config \cup {entry["value"]}
                         ELSE config \ {entry["value"]}
          ELSE UNCHANGED <<config>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, lastIncludedIndex, lastIncludedTerm>>

StepDown(s, msg) ==
    /\ msg["term"] > currentTerm[s]
    /\ BecomeFollower(s, msg["term"])

Next ==
    \/ \E s \in Server:
        \/ PeriodicElectionTimeout(s)
        \/ ElectionTimeout(s)
        \/ LogCommit(s)
        \/ ApplyConfigChange(s)
        \/ SnapshotBegin(s)
        \/ PeriodicHeartbeat(s)
    \/ \E s \in Server, v \in Value: LogAppend(s, v, "NORMAL")
    \/ \E s \in Server, newNode \in ConfigChangeValue: AddNode(s, newNode)
    \/ \E s \in Server, oldNode \in ConfigChangeValue: RemoveNode(s, oldNode)
    \/ \E s, p \in Server: SendAppendEntries(s, p)
    \/ \E msg \in messages:
        LET s == msg["dest"] IN
        LET new_messages == messages \ {msg} IN
        /\ \/ /\ msg["type"] = "RequestVote"
              /\ RecvRequestVote(s, msg)
           \/ /\ msg["type"] = "RequestVoteResponse"
              /\ \/ StepDown(s, msg)
                 \/ RecvRequestVoteResponse(s, msg)
           \/ /\ msg["type"] = "AppendEntries"
              /\ \/ StepDown(s, msg)
                 \/ RecvAppendEntries(s, msg)
           \/ /\ msg["type"] = "AppendEntriesResponse"
              /\ \/ StepDown(s, msg)
                 \/ RecvAppendEntriesResponse(s, msg)
           \/ /\ msg["type"] = "InstallSnapshot"
              /\ \/ StepDown(s, msg)
                 \/ HandleInstallSnapshot(s, msg)
           \/ /\ msg["type"] = "InstallSnapshotResponse"
              /\ \/ StepDown(s, msg)
                 \/ HandleInstallSnapshotResponse(s, msg)
        /\ messages' = new_messages \cup (messages' \ messages)

Spec == Init /\ [][Next]_vars

====