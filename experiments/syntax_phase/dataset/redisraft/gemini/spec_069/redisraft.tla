---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, FiniteSetsExt, Bags, Integers

CONSTANTS Server, Command, Nil, NoOp, ConfigChangeAdd, ConfigChangeRemove

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
    leaderId,
    snapshotLastIndex,
    snapshotLastTerm,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, votesGranted, nodes, leaderId,
          snapshotLastIndex, snapshotLastTerm, messages>>

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
EntryType == Command \cup {NoOp, ConfigChangeAdd, ConfigChangeRemove}
MsgType == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "InstallSnapshot"}

TypeOK ==
    /\ state \in [Server -> NodeStates]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq([term: Nat, command: EntryType, node: Server \cup {Nil}])]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat \ {0}]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ nodes \in [Server -> SUBSET Server]
    /\ leaderId \in [Server -> Server \cup {Nil}]
    /\ snapshotLastIndex \in [Server -> Nat]
    /\ snapshotLastTerm \in [Server -> Nat]
    /\ messages \subseteq
        [ type: MsgType,
          from: Server,
          to: Server,
          term: Nat,
          prevote: BOOLEAN,
          requestTerm: Nat,
          voteGranted: BOOLEAN,
          prevLogIndex: Nat,
          prevLogTerm: Nat,
          entries: Seq([term: Nat, command: EntryType, node: Server \cup {Nil}]),
          leaderCommit: Nat,
          success: BOOLEAN,
          matchIndex: Nat,
          lastIncludedIndex: Nat,
          lastIncludedTerm: Nat
        ]

LogOK(s) ==
    /\ lastApplied[s] <= commitIndex[s]
    /\ commitIndex[s] <= snapshotLastIndex[s] + Len(log[s])
    /\ snapshotLastIndex[s] <= lastApplied[s]

LastLogIndex(s) == snapshotLastIndex[s] + Len(log[s])

LogTerm(s, idx) ==
    IF idx = 0 THEN 0
    ELSE IF idx = snapshotLastIndex[s] THEN snapshotLastTerm[s]
    ELSE log[s][idx - snapshotLastIndex[s]]["term"]

LastLogTerm(s) == LogTerm(s, LastLogIndex(s))

IsUpToDate(candidate, voter) ==
    LET candLastTerm == LastLogTerm(candidate)
        voterLastTerm == LastLogTerm(voter)
    IN
    \/ candLastTerm > voterLastTerm
    \/ (candLastTerm = voterLastTerm /\ LastLogIndex(candidate) >= LastLogIndex(voter))

Majority(s) == (Cardinality(s) \div 2) + 1

Init ==
    /\ state = [s \in Server |-> "FOLLOWER"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ nodes = [s \in Server |-> Server]
    /\ leaderId = [s \in Server |-> Nil]
    /\ snapshotLastIndex = [s \in Server |-> 0]
    /\ snapshotLastTerm = [s \in Server |-> 0]
    /\ messages = {}

\* State Transitions
BecomeFollower(s, newTerm) ==
    /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm, messages>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PRECANDIDATE"]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        {[ type |-> "RequestVote", from |-> s, to |-> p, term |-> currentTerm[s] + 1, prevote |-> TRUE,
           lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s)
         ] : p \in nodes[s] \ {s}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        {[ type |-> "RequestVote", from |-> s, to |-> p, term |-> currentTerm[s] + 1, prevote |-> FALSE,
           lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s)
         ] : p \in nodes[s] \ {s}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, nodes, snapshotLastIndex, snapshotLastTerm>>

BecomeLeader(s) ==
    LET newEntry == [term |-> currentTerm[s], command |-> NoOp, node |-> Nil]
        newLog == Append(log[s], newEntry)
        newLogIndex == LastLogIndex(s) + 1
    IN
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ log' = [log EXCEPT ![s] = newLog]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> newLogIndex + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [[p \in Server |-> 0] EXCEPT ![s] = newLogIndex]]
    /\ messages' = messages \cup
        {[ type |-> "AppendEntries", from |-> s, to |-> p, term |-> currentTerm[s],
           prevLogIndex |-> LastLogIndex(s), prevLogTerm |-> LastLogTerm(s),
           entries |-> <<newEntry>>, leaderCommit |-> commitIndex[s]
         ] : p \in nodes[s] \ {s}}
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

\* Election Management
ElectionTimeout(s) ==
    /\ state[s] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ BecomePreCandidate(s)

\* Vote Processing
RecvRequestVote(msg) ==
    LET s == msg["to"]
        candidate == msg["from"]
    IN
    /\ msg["type"] = "RequestVote"
    /\ msg["term"] <= currentTerm[s]
    /\ LET grant == /\ msg["term"] = currentTerm[s]
                    /\ (IF msg["prevote"] THEN TRUE ELSE (votedFor[s] = Nil \/ votedFor[s] = candidate))
                    /\ IsUpToDate(candidate, s)
       IN
       /\ IF grant /\ \lnot msg["prevote"]
          THEN votedFor' = [votedFor EXCEPT ![s] = candidate]
          ELSE UNCHANGED <<votedFor>>
       /\ messages' = (messages \ {msg}) \cup
           {[ type |-> "RequestVoteResponse", from |-> s, to |-> candidate, term |-> currentTerm[s],
              prevote |-> msg["prevote"], requestTerm |-> msg["term"], voteGranted |-> grant ]}
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm>>

RecvRequestVoteResponse(msg) ==
    LET s == msg["to"]
    IN
    /\ msg["type"] = "RequestVoteResponse"
    /\ msg["term"] = currentTerm[s]
    /\ \/ /\ state[s] = "PRECANDIDATE" /\ msg["prevote"] /\ msg["requestTerm"] = currentTerm[s] + 1
       \/ /\ state[s] = "CANDIDATE" /\ \lnot msg["prevote"] /\ msg["requestTerm"] = currentTerm[s]
    /\ IF msg["voteGranted"]
       THEN LET newVotes == votesGranted[s] \cup {msg["from"]}
            IN /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
               /\ IF Cardinality(newVotes) >= Majority(nodes[s])
                  THEN IF state[s] = "PRECANDIDATE"
                       THEN BecomeCandidate(s) /\ messages' = (messages \ {msg}) \cup messages'
                       ELSE IF state[s] = "CANDIDATE"
                            THEN BecomeLeader(s) /\ messages' = (messages \ {msg}) \cup messages'
                            ELSE UNCHANGED <<vars>>
                  ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotLastIndex, snapshotLastTerm, messages>>
       ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, messages>>
    /\ IF \lnot msg["voteGranted"] \/ Cardinality(votesGranted[s] \cup {msg["from"]}) < Majority(nodes[s])
       THEN messages' = messages \ {msg}
       ELSE UNCHANGED <<messages>>

\* Log Replication
RecvAppendEntries(msg) ==
    LET s == msg["to"]
    IN
    /\ msg["type"] = "AppendEntries"
    /\ msg["term"] <= currentTerm[s]
    /\ LET logOK == msg["prevLogIndex"] = 0 \/
                    (msg["prevLogIndex"] > 0 /\ LogTerm(s, msg["prevLogIndex"]) = msg["prevLogTerm"])
           success == msg["term"] = currentTerm[s] /\ logOK
       IN
       /\ IF success
          THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
               /\ leaderId' = [leaderId EXCEPT ![s] = msg["from"]]
               /\ (LET newLog == SubSeq(log[s], 1, msg["prevLogIndex"] - snapshotLastIndex[s]) \o msg["entries"]
                   IN log' = [log EXCEPT ![s] = newLog])
               /\ IF msg["leaderCommit"] > commitIndex[s]
                  THEN commitIndex' = [commitIndex EXCEPT ![s] = Min({msg["leaderCommit"], LastLogIndex(s)})]
                  ELSE UNCHANGED <<commitIndex>>
          ELSE UNCHANGED <<state, leaderId, log, commitIndex>>
       /\ messages' = (messages \ {msg}) \cup
           {[ type |-> "AppendEntriesResponse", from |-> s, to |-> msg["from"], term |-> currentTerm[s],
              success |-> success, matchIndex |-> LastLogIndex(s) ]}
    /\ UNCHANGED <<currentTerm, votedFor, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

RecvAppendEntriesResponse(msg) ==
    LET s == msg["to"]
        peer == msg["from"]
    IN
    /\ msg["type"] = "AppendEntriesResponse"
    /\ state[s] = "LEADER"
    /\ msg["term"] = currentTerm[s]
    /\ IF msg["success"]
       THEN LET newMatchIndex == msg["matchIndex"]
                newMatchIndexArray == [matchIndex[s] EXCEPT ![peer] = newMatchIndex]
                possibleCommits == { N \in (commitIndex[s] + 1)..LastLogIndex(s) :
                                       /\ LogTerm(s, N) = currentTerm[s]
                                       /\ Cardinality({p \in nodes[s] : (IF p=s THEN LastLogIndex(s) ELSE newMatchIndexArray[p]) >= N}) >= Majority(nodes[s]) }
                newCommitIndex == IF possibleCommits = {} THEN commitIndex[s] ELSE Max(possibleCommits)
            IN
            /\ matchIndex' = [matchIndex EXCEPT ![s] = newMatchIndexArray]
            /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![peer] = newMatchIndex + 1]]
            /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![peer] = nextIndex[s][peer] - 1]]
            /\ UNCHANGED <<matchIndex, commitIndex>>
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm>>

\* Leader Operations
SendAppendEntries(s) ==
    /\ state[s] = "LEADER"
    /\ \E p \in nodes[s] \ {s}:
        \/ /\ nextIndex[s][p] > snapshotLastIndex[s]
           /\ (LET prevIdx == nextIndex[s][p] - 1
                  entriesToSend == SubSeq(log[s], nextIndex[s][p] - snapshotLastIndex[s], Len(log[s]))
              IN
              messages' = messages \cup
                  {[ type |-> "AppendEntries", from |-> s, to |-> p, term |-> currentTerm[s],
                     prevLogIndex |-> prevIdx, prevLogTerm |-> LogTerm(s, prevIdx),
                     entries |-> entriesToSend, leaderCommit |-> commitIndex[s] ]})
        \/ /\ nextIndex[s][p] <= snapshotLastIndex[s]
           /\ messages' = messages \cup
               {[ type |-> "InstallSnapshot", from |-> s, to |-> p, term |-> currentTerm[s],
                  lastIncludedIndex |-> snapshotLastIndex[s],
                  lastIncludedTerm |-> snapshotLastTerm[s] ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm>>

\* Log Management
LogAppend(s) ==
    /\ state[s] = "LEADER"
    /\ \E cmd \in Command:
        (LET newEntry == [term |-> currentTerm[s], command |-> cmd, node |-> Nil]
         IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)])
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm, messages>>

ApplyLogEntry(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET idx == lastApplied[s] + 1
           entry == log[s][idx - snapshotLastIndex[s]]
       IN
       /\ lastApplied' = [lastApplied EXCEPT ![s] = idx]
       /\ IF entry["command"] = ConfigChangeAdd
          THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \cup {entry["node"]}]
          ELSE IF entry["command"] = ConfigChangeRemove
               THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \ {entry["node"]}]
               ELSE UNCHANGED <<nodes>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, leaderId, snapshotLastIndex, snapshotLastTerm, messages>>

\* Node Management
AddNode(s) ==
    /\ state[s] = "LEADER"
    /\ \E peer \in Server \ nodes[s]:
        (LET newEntry == [term |-> currentTerm[s], command |-> ConfigChangeAdd, node |-> peer]
         IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)])
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm, messages>>

RemoveNode(s) ==
    /\ state[s] = "LEADER"
    /\ \E peer \in nodes[s] \ {s}:
        (LET newEntry == [term |-> currentTerm[s], command |-> ConfigChangeRemove, node |-> peer]
         IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)])
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm, messages>>

\* Snapshot Handling
CreateSnapshot(s) ==
    /\ commitIndex[s] > snapshotLastIndex[s]
    /\ \E idxToSnapshot \in (snapshotLastIndex[s]+1)..commitIndex[s]:
        LET relativeIdx == idxToSnapshot - snapshotLastIndex[s]
            entryToSnapshot == log[s][relativeIdx]
        IN
        /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = idxToSnapshot]
        /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = entryToSnapshot["term"]]
        /\ log' = [log EXCEPT ![s] = Drop(log[s], relativeIdx)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, messages>>

RecvSnapshot(msg) ==
    LET s == msg["to"]
    IN
    /\ msg["type"] = "InstallSnapshot"
    /\ msg["term"] <= currentTerm[s]
    /\ IF msg["lastIncludedIndex"] > snapshotLastIndex[s]
       THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
            /\ leaderId' = [leaderId EXCEPT ![s] = msg["from"]]
            /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({commitIndex[s], msg["lastIncludedIndex"]})]
            /\ lastApplied' = [lastApplied EXCEPT ![s] = Max({lastApplied[s], msg["lastIncludedIndex"]})]
            /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = msg["lastIncludedIndex"]]
            /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = msg["lastIncludedTerm"]]
            /\ (LET lastLogIdx == LastLogIndex(s)
                IN IF lastLogIdx <= msg["lastIncludedIndex"]
                   THEN log' = [log EXCEPT ![s] = <<>>]
                   ELSE LET numToDrop == msg["lastIncludedIndex"] - snapshotLastIndex[s]
                        IN log' = [log EXCEPT ![s] = Drop(log[s], numToDrop)])
       ELSE UNCHANGED <<state, leaderId, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm, log>>
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<currentTerm, votedFor, nextIndex, matchIndex, votesGranted, nodes>>

\* Message Handling
StepDownOnHigherTerm(msg) ==
    /\ msg["term"] > currentTerm[msg["to"]]
    /\ BecomeFollower(msg["to"], msg["term"])
    /\ messages' = messages
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, snapshotLastIndex, snapshotLastTerm>>

HandleMsg(msg) ==
    \/ StepDownOnHigherTerm(msg)
    \/ /\ msg["term"] < currentTerm[msg["to"]]
       /\ messages' = messages \ {msg}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, nodes, leaderId, snapshotLastIndex, snapshotLastTerm>>
    \/ /\ msg["term"] = currentTerm[msg["to"]]
       /\ \/ RecvRequestVote(msg)
          \/ RecvRequestVoteResponse(msg)
          \/ RecvAppendEntries(msg)
          \/ RecvAppendEntriesResponse(msg)
          \/ RecvSnapshot(msg)

Next ==
    \/ \E s \in Server:
        \/ ElectionTimeout(s)
        \/ SendAppendEntries(s)
        \/ LogAppend(s)
        \/ AddNode(s)
        \/ RemoveNode(s)
        \/ ApplyLogEntry(s)
        \/ CreateSnapshot(s)
    \/ \E msg \in messages: HandleMsg(msg)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====