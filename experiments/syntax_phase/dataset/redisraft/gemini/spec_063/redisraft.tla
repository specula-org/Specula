---- MODULE redisraft ----
EXTENDS TLC, SequencesExt, Naturals, FiniteSets, Sequences, Bags

CONSTANTS
    Servers,
    Commands,
    NULL,
    ElectionTimeoutMin,
    ElectionTimeoutMax,
    HeartbeatInterval

ASSUME /\ ElectionTimeoutMin \in Nat
       /\ ElectionTimeoutMax \in Nat
       /\ ElectionTimeoutMin =< ElectionTimeoutMax
       /\ HeartbeatInterval \in Nat
       /\ HeartbeatInterval > 0

States == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
MsgTypes == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "Snapshot"}
LogTypes == {"NORMAL", "ADD_NODE", "REMOVE_NODE"}
ConfigChangeCommands == { [type |-> t, node |-> n] : t \in {"ADD_NODE", "REMOVE_NODE"}, n \in Servers }
NormalCommands == { [type |-> "NORMAL", command |-> c] : c \in Commands }

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nodes,
    leaderId,
    timeout_elapsed,
    election_timeout_rand,
    snapshot_last_idx,
    snapshot_last_term,
    nextIndex,
    matchIndex,
    votesGranted,
    network

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes, leaderId,
          timeout_elapsed, election_timeout_rand, snapshot_last_idx, snapshot_last_term,
          nextIndex, matchIndex, votesGranted, network>>

TypeOK ==
    /\ state \in [Servers -> States]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {NULL}]
    /\ \A s \in Servers : SequencesExt!IsSequence(log[s])
    /\ commitIndex \in [Servers -> Nat]
    /\ lastApplied \in [Servers -> Nat]
    /\ nodes \in [Servers -> SUBSET Servers]
    /\ leaderId \in [Servers -> Servers \cup {NULL}]
    /\ timeout_elapsed \in [Servers -> Nat]
    /\ election_timeout_rand \in [Servers -> Nat]
    /\ snapshot_last_idx \in [Servers -> Nat]
    /\ snapshot_last_term \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ votesGranted \in [Servers -> SUBSET Servers]

\* Helper operators
min(a, b) == IF a =< b THEN a ELSE b
max(a, b) == IF a >= b THEN a ELSE b

LastLogIndex(s) == snapshot_last_idx[s] + Len(log[s])
LastLogTerm(s) == IF Len(log[s]) > 0
                  THEN (Tail(log[s]))["term"]
                  ELSE snapshot_last_term[s]

GetEntry(s, idx) ==
    IF idx > snapshot_last_idx[s] /\ idx <= LastLogIndex(s)
    THEN log[s][idx - snapshot_last_idx[s]]
    ELSE [term |-> 0, command |-> [type |-> "NORMAL", command |-> ""]]

GetTerm(s, idx) ==
    IF idx = 0 THEN 0
    ELSE IF idx = snapshot_last_idx[s] THEN snapshot_last_term[s]
    ELSE IF idx > snapshot_last_idx[s] /\ idx <= LastLogIndex(s)
         THEN log[s][idx - snapshot_last_idx[s]]["term"]
         ELSE 0

Quorum(s) == (Cardinality(nodes[s]) \div 2) + 1

IsUpToDate(s, candidateLastLogIdx, candidateLastLogTerm) ==
    LET myLastLogTerm == LastLogTerm(s)
        myLastLogIndex == LastLogIndex(s)
    IN \/ candidateLastLogTerm > myLastLogTerm
       \/ (candidateLastLogTerm = myLastLogTerm /\ candidateLastLogIdx >= myLastLogIndex)

\* State Transitions
BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = NULL]
    /\ leaderId' = [leaderId EXCEPT ![s] = NULL]
    /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = 0]
    /\ \E rand \in ElectionTimeoutMin..ElectionTimeoutMax :
        election_timeout_rand' = [election_timeout_rand EXCEPT ![s] = rand]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted, network>>

BecomePreCandidate(s) ==
    /\ state[s] \in {"FOLLOWER", "CANDIDATE"}
    /\ state' = [state EXCEPT ![s] = "PRECANDIDATE"]
    /\ leaderId' = [leaderId EXCEPT ![s] = NULL]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = 0]
    /\ \E rand \in ElectionTimeoutMin..ElectionTimeoutMax :
        election_timeout_rand' = [election_timeout_rand EXCEPT ![s] = rand]
    /\ LET
        Request(p) == [
            type |-> "RequestVote", from |-> s, to |-> p,
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            prevote |-> TRUE
        ]
       IN network' = network (+) Bags!Bagify({Request(p) : p \in nodes[s] \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nodes,
                   snapshot_last_idx, snapshot_last_term, nextIndex, matchIndex>>

BecomeCandidate(s) ==
    /\ state[s] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ leaderId' = [leaderId EXCEPT ![s] = NULL]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = 0]
    /\ \E rand \in ElectionTimeoutMin..ElectionTimeoutMax :
        election_timeout_rand' = [election_timeout_rand EXCEPT ![s] = rand]
    /\ LET
        Request(p) == [
            type |-> "RequestVote", from |-> s, to |-> p,
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            prevote |-> FALSE
        ]
       IN network' = network (+) Bags!Bagify({Request(p) : p \in nodes[s] \ {s}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex>>

BecomeLeader(s) ==
    /\ state[s] = "CANDIDATE"
    /\ Cardinality(votesGranted[s]) >= Quorum(s)
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
    /\ LET noop_entry == [term |-> currentTerm[s], command |-> [type |-> "NORMAL", command |-> "NO-OP"]]
       IN log' = [log EXCEPT ![s] = Append(log[s], noop_entry)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, nodes,
                   snapshot_last_idx, snapshot_last_term, votesGranted, network>>

\* Vote Processing
RecvRequestVote(s, msg) ==
    /\ msg["type"] = "RequestVote"
    /\ msg["to"] = s
    /\ LET
        grant == \/ msg["term"] > currentTerm[s]
                 \/ ( /\ msg["term"] = currentTerm[s]
                      /\ votedFor[s] \in {NULL, msg["from"]}
                      /\ IsUpToDate(s, msg["lastLogIndex"], msg["lastLogTerm"]) )
        resp == [
            type |-> "RequestVoteResponse", from |-> s, to |-> msg["from"],
            term |-> IF msg["term"] > currentTerm[s] THEN msg["term"] ELSE currentTerm[s],
            voteGranted |-> grant,
            prevote |-> msg["prevote"]
        ]
       IN
        /\ IF msg["term"] > currentTerm[s]
           THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                /\ currentTerm' = [currentTerm EXCEPT ![s] = msg["term"]]
                /\ votedFor' = [votedFor EXCEPT ![s] = IF grant /\ \neg msg["prevote"] THEN msg["from"] ELSE NULL]
           ELSE /\ state' = state
                /\ currentTerm' = currentTerm
                /\ votedFor' = [votedFor EXCEPT ![s] = IF grant /\ \neg msg["prevote"] THEN msg["from"] ELSE votedFor[s]]
        /\ network' = (network (-) Bags!Bagify({msg})) (+) Bags!Bagify({resp})
        /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, leaderId, timeout_elapsed,
                       election_timeout_rand, snapshot_last_idx, snapshot_last_term,
                       nextIndex, matchIndex, votesGranted>>

RecvRequestVoteResponse(s, msg) ==
    /\ msg["type"] = "RequestVoteResponse"
    /\ msg["to"] = s
    /\ network' = network (-) Bags!Bagify({msg})
    /\ IF msg["term"] > currentTerm[s]
       THEN /\ BecomeFollower(s, msg["term"])
            /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                           snapshot_last_term, nextIndex, matchIndex, votesGranted>>
       ELSE /\ IF msg["voteGranted"]
              THEN votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {msg["from"]}]
              ELSE votesGranted' = votesGranted
            /\ IF state[s] = "PRECANDIDATE" /\ Cardinality(votesGranted'[s]) >= Quorum(s)
               THEN BecomeCandidate(s)
               ELSE IF state[s] = "CANDIDATE" /\ Cardinality(votesGranted'[s]) >= Quorum(s)
                    THEN BecomeLeader(s)
                    ELSE UNCHANGED vars

\* Log Replication
RecvAppendEntries(s, msg) ==
    /\ msg["type"] = "AppendEntries"
    /\ msg["to"] = s
    /\ LET
        termOK == msg["term"] >= currentTerm[s]
        prevLogOK == GetTerm(s, msg["prevLogIndex"]) = msg["prevLogTerm"]
        success == termOK /\ prevLogOK
        resp == [
            type |-> "AppendEntriesResponse", from |-> s, to |-> msg["from"],
            term |-> IF msg["term"] > currentTerm[s] THEN msg["term"] ELSE currentTerm[s],
            success |-> success,
            matchIndex |-> IF success THEN msg["prevLogIndex"] + Len(msg["entries"]) ELSE LastLogIndex(s)
        ]
       IN
        /\ network' = (network (-) Bags!Bagify({msg})) (+) Bags!Bagify({resp})
        /\ IF msg["term"] > currentTerm[s]
           THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                /\ currentTerm' = [currentTerm EXCEPT ![s] = msg["term"]]
                /\ votedFor' = [votedFor EXCEPT ![s] = NULL]
           ELSE /\ state' = state
                /\ currentTerm' = currentTerm
                /\ votedFor' = votedFor
        /\ IF termOK
           THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                /\ leaderId' = [leaderId EXCEPT ![s] = msg["from"]]
                /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = 0]
           ELSE /\ leaderId' = leaderId
                /\ timeout_elapsed' = timeout_elapsed
        /\ IF success
           THEN /\ LET
                    conflictSet == {i \in 1..Len(msg["entries"]) :
                                        GetTerm(s, msg["prevLogIndex"] + i) /= msg["entries"][i]["term"]}
                    conflictIndex == IF conflictSet = {} THEN 0 ELSE CHOOSE i \in conflictSet : TRUE
                    newLog == IF conflictIndex > 0
                              THEN SubSeq(log[s], 1, msg["prevLogIndex"] - snapshot_last_idx[s] + conflictIndex - 1)
                              ELSE SubSeq(log[s], 1, msg["prevLogIndex"] - snapshot_last_idx[s])
                    entriesToAppend == IF conflictIndex > 0
                                       THEN SubSeq(msg["entries"], conflictIndex, Len(msg["entries"]))
                                       ELSE msg["entries"]
                  IN log' = [log EXCEPT ![s] = newLog \o entriesToAppend]
                /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s],
                                    min(msg["leaderCommit"], msg["prevLogIndex"] + Len(msg["entries"])))]
           ELSE /\ log' = log
                /\ commitIndex' = commitIndex
        /\ UNCHANGED <<lastApplied, nodes, election_timeout_rand, snapshot_last_idx,
                       snapshot_last_term, nextIndex, matchIndex, votesGranted>>

RecvAppendEntriesResponse(s, msg) ==
    /\ msg["type"] = "AppendEntriesResponse"
    /\ msg["to"] = s
    /\ state[s] = "LEADER"
    /\ network' = network (-) Bags!Bagify({msg})
    /\ IF msg["term"] > currentTerm[s]
       THEN /\ BecomeFollower(s, msg["term"])
            /\ UNCHANGED <<log, commitIndex, lastApplied, nodes, snapshot_last_idx,
                           snapshot_last_term, nextIndex, matchIndex, votesGranted>>
       ELSE /\ IF msg["success"]
              THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg["from"]] = msg["matchIndex"] + 1]]
                   /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![msg["from"]] = msg["matchIndex"]]]
                   /\ LET
                        \* LogCommit logic
                        matchSet == {matchIndex'[s][p] : p \in nodes[s]} \cup {LastLogIndex(s)}
                        sortedMatches == SortSeq(Seq(matchSet), LAMBDA x, y : x > y)
                        majorityMatch == sortedMatches[Quorum(s)]
                      IN
                        commitIndex' = [commitIndex EXCEPT ![s] =
                                            IF majorityMatch > commitIndex[s] /\ GetTerm(s, majorityMatch) = currentTerm[s]
                                            THEN majorityMatch
                                            ELSE commitIndex[s]]
              ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg["from"]] = nextIndex[s][msg["from"]] - 1]]
                   /\ matchIndex' = matchIndex
                   /\ commitIndex' = commitIndex
            /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nodes, leaderId,
                           timeout_elapsed, election_timeout_rand, snapshot_last_idx,
                           snapshot_last_term, votesGranted>>

\* Leader Operations
SendAppendEntries(s, p) ==
    /\ state[s] = "LEADER"
    /\ p \in nodes[s] \ {s}
    /\ LET
        prevIdx == nextIndex[s][p] - 1
        entriesToSend == IF LastLogIndex(s) >= nextIndex[s][p]
                         THEN SubSeq(log[s], prevIdx - snapshot_last_idx[s] + 1, LastLogIndex(s) - snapshot_last_idx[s])
                         ELSE << >>
        msg == [
            type |-> "AppendEntries", from |-> s, to |-> p,
            term |-> currentTerm[s],
            leaderId |-> s,
            prevLogIndex |-> prevIdx,
            prevLogTerm |-> GetTerm(s, prevIdx),
            entries |-> entriesToSend,
            leaderCommit |-> commitIndex[s]
        ]
       IN network' = network (+) Bags!Bagify({msg})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes,
                   leaderId, timeout_elapsed, election_timeout_rand, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted>>

SendHeartbeat(s) ==
    /\ state[s] = "LEADER"
    /\ LET
        HeartbeatMsg(p) ==
            LET prevIdx == nextIndex[s][p] - 1
            IN [
                type |-> "AppendEntries", from |-> s, to |-> p,
                term |-> currentTerm[s],
                leaderId |-> s,
                prevLogIndex |-> prevIdx,
                prevLogTerm |-> GetTerm(s, prevIdx),
                entries |-> << >>,
                leaderCommit |-> commitIndex[s]
            ]
       IN network' = network (+) Bags!Bagify({HeartbeatMsg(p) : p \in nodes[s] \ {s}})
    /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes,
                   leaderId, election_timeout_rand, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted>>

\* Election Management
ElectionTimeout(s) ==
    /\ state[s] \in {"FOLLOWER", "CANDIDATE"}
    /\ timeout_elapsed[s] >= election_timeout_rand[s]
    /\ BecomePreCandidate(s)

\* Log Management
LogAppend(s, cmd) ==
    /\ state[s] = "LEADER"
    /\ LET entry == [term |-> currentTerm[s], command |-> cmd]
       IN log' = [log EXCEPT ![s] = Append(log[s], entry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes,
                   leaderId, timeout_elapsed, election_timeout_rand, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted, network>>

LogCommit(s) ==
    /\ state[s] = "LEADER"
    /\ LET
        matchSet == {matchIndex[s][p] : p \in nodes[s]} \cup {LastLogIndex(s)}
        sortedMatches == SortSeq(Seq(matchSet), LAMBDA x, y : x > y)
        majorityMatch == sortedMatches[Quorum(s)]
       IN
        /\ majorityMatch > commitIndex[s]
        /\ GetTerm(s, majorityMatch) = currentTerm[s]
        /\ commitIndex' = [commitIndex EXCEPT ![s] = majorityMatch]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nodes, leaderId,
                   timeout_elapsed, election_timeout_rand, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted, network>>

\* Periodic Tasks
PeriodicElectionTimeout(s) ==
    /\ state[s] \in {"FOLLOWER", "CANDIDATE", "PRECANDIDATE"}
    /\ timeout_elapsed' = [timeout_elapsed EXCEPT ![s] = timeout_elapsed[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nodes,
                   leaderId, election_timeout_rand, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted, network>>

PeriodicHeartbeat(s) ==
    /\ state[s] = "LEADER"
    /\ timeout_elapsed[s] >= HeartbeatInterval
    /\ SendHeartbeat(s)

\* Node Management and Configuration
ApplyConfigChange(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET
        idxToApply == lastApplied[s] + 1
        entry == GetEntry(s, idxToApply)
       IN
        /\ lastApplied' = [lastApplied EXCEPT ![s] = idxToApply]
        /\ IF entry["command"]["type"] = "ADD_NODE"
           THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \cup {entry["command"]["node"]}]
           ELSE IF entry["command"]["type"] = "REMOVE_NODE"
                THEN nodes' = [nodes EXCEPT ![s] = nodes[s] \ {entry["command"]["node"]}]
                ELSE nodes' = nodes
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                   timeout_elapsed, election_timeout_rand, snapshot_last_idx,
                   snapshot_last_term, nextIndex, matchIndex, votesGranted, network>>

\* Snapshot Handling
SnapshotBegin(s) ==
    /\ commitIndex[s] > snapshot_last_idx[s]
    /\ LET
        idxToSnapshot == CHOOSE i \in snapshot_last_idx[s]+1..commitIndex[s] : TRUE
        termOfSnapshot == GetTerm(s, idxToSnapshot)
        logStartIndex == idxToSnapshot - snapshot_last_idx[s]
       IN
        /\ snapshot_last_idx' = [snapshot_last_idx EXCEPT ![s] = idxToSnapshot]
        /\ snapshot_last_term' = [snapshot_last_term EXCEPT ![s] = termOfSnapshot]
        /\ log' = [log EXCEPT ![s] = SubSeq(log[s], logStartIndex + 1, Len(log[s]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nodes,
                   leaderId, timeout_elapsed, election_timeout_rand, nextIndex,
                   matchIndex, votesGranted, network>>

SnapshotEnd(s, msg) ==
    /\ msg["type"] = "Snapshot"
    /\ msg["to"] = s
    /\ network' = network (-) Bags!Bagify({msg})
    /\ IF msg["snapshot_last_idx"] > commitIndex[s]
       THEN /\ snapshot_last_idx' = [snapshot_last_idx EXCEPT ![s] = msg["snapshot_last_idx"]]
            /\ snapshot_last_term' = [snapshot_last_term EXCEPT ![s] = msg["snapshot_last_term"]]
            /\ log' = [log EXCEPT ![s] = << >>]
            /\ commitIndex' = [commitIndex EXCEPT ![s] = msg["snapshot_last_idx"]]
            /\ lastApplied' = [lastApplied EXCEPT ![s] = msg["snapshot_last_idx"]]
            /\ UNCHANGED <<state, currentTerm, votedFor, nodes, leaderId, timeout_elapsed,
                           election_timeout_rand, nextIndex, matchIndex, votesGranted>>
       ELSE UNCHANGED vars

Init ==
    /\ state = [s \in Servers |-> "FOLLOWER"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> NULL]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ lastApplied = [s \in Servers |-> 0]
    /\ nodes = [s \in Servers |-> Servers]
    /\ leaderId = [s \in Servers |-> NULL]
    /\ timeout_elapsed = [s \in Servers |-> 0]
    /\ election_timeout_rand = [s \in Servers |-> CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax : TRUE]
    /\ snapshot_last_idx = [s \in Servers |-> 0]
    /\ snapshot_last_term = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ network = EmptyBag

Next ==
    \/ \E s \in Servers : ElectionTimeout(s)
    \/ \E s \in Servers : PeriodicHeartbeat(s)
    \/ \E s \in Servers : PeriodicElectionTimeout(s)
    \/ \E s \in Servers, cmd \in NormalCommands : LogAppend(s, cmd)
    \/ \E s \in Servers, cmd \in ConfigChangeCommands : LogAppend(s, cmd)
    \/ \E s \in Servers : LogCommit(s)
    \/ \E s \in Servers : ApplyConfigChange(s)
    \/ \E s \in Servers : SnapshotBegin(s)
    \/ \E s \in Servers, p \in Servers : SendAppendEntries(s, p)
    \/ \E msg \in BagToSet(network) :
        \/ RecvRequestVote(msg["to"], msg)
        \/ RecvRequestVoteResponse(msg["to"], msg)
        \/ RecvAppendEntries(msg["to"], msg)
        \/ RecvAppendEntriesResponse(msg["to"], msg)
        \/ SnapshotEnd(msg["to"], msg)

Spec == Init /\ [][Next]_vars

====