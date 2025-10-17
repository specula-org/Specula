---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,        \* The set of server IDs
    Commands,       \* The set of possible client commands
    Nil             \* A special value for votedFor

VARIABLES
    state,          \* state[s] \in {"Follower", "PreCandidate", "Candidate", "Leader"}
    currentTerm,    \* currentTerm[s] \in Nat
    votedFor,       \* votedFor[s] \in Servers \cup {Nil}
    log,            \* log[s] is a sequence of records: [term |-> t, cmd |-> c]
    commitIndex,    \* commitIndex[s] \in Nat
    lastApplied,    \* lastApplied[s] \in Nat
    config,         \* The current server configuration (set of active servers)

    nextIndex,      \* Leader's view of the next log index to send to each server
    matchIndex,     \* Leader's view of the highest log index replicated on each server

    lastIncludedIndex, \* Index of the last entry in the most recent snapshot
    lastIncludedTerm,  \* Term of the last entry in the most recent snapshot

    votesGranted,   \* Set of servers that granted a vote to a candidate

    messages        \* A bag of messages in transit

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
          nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm,
          votesGranted, messages>>

\* --- Message Types ---
MsgType(type, src, dst, m) == [type |-> type, src |-> src, dst |-> dst, m |-> m]

RequestVote(src, dst, term, lastLogIdx, lastLogTerm, prevote) ==
    MsgType("RequestVote", src, dst, [
        term |-> term,
        lastLogIndex |-> lastLogIdx,
        lastLogTerm |-> lastLogTerm,
        prevote |-> prevote
    ])

RequestVoteResponse(src, dst, term, voteGranted) ==
    MsgType("RequestVoteResponse", src, dst, [
        term |-> term,
        voteGranted |-> voteGranted
    ])

AppendEntries(src, dst, term, prevLogIdx, prevLogTerm, entries, leaderCommit) ==
    MsgType("AppendEntries", src, dst, [
        term |-> term,
        prevLogIndex |-> prevLogIdx,
        prevLogTerm |-> prevLogTerm,
        entries |-> entries,
        leaderCommit |-> leaderCommit
    ])

AppendEntriesResponse(src, dst, term, success, matchIndex) ==
    MsgType("AppendEntriesResponse", src, dst, [
        term |-> term,
        success |-> success,
        matchIndex |-> matchIndex
    ])

InstallSnapshot(src, dst, term, lastIdx, lastTerm) ==
    MsgType("InstallSnapshot", src, dst, [
        term |-> term,
        lastIncludedIndex |-> lastIdx,
        lastIncludedTerm |-> lastTerm
    ])

InstallSnapshotResponse(src, dst, term) ==
    MsgType("InstallSnapshotResponse", src, dst, [
        term |-> term
    ])

\* --- Helper Operators ---
IsQuorum(s) == Cardinality(s) * 2 > Cardinality(config)

LastLogIndex(s) == lastIncludedIndex[s] + Len(log[s])

LastLogTerm(s) ==
    IF Len(log[s]) > 0
    THEN log[s][Len(log[s])].term
    ELSE lastIncludedTerm[s]

LogIsUpToDate(s, candLastLogTerm, candLastLogIdx) ==
    LET myLastLogTerm == LastLogTerm(s) IN
    LET myLastLogIndex == LastLogIndex(s) IN
    \/ candLastLogTerm > myLastLogTerm
    \/ (candLastLogTerm = myLastLogTerm /\ candLastLogIdx >= myLastLogIndex)

GetEntry(s, idx) ==
    IF idx > lastIncludedIndex[s] /\ idx <= LastLogIndex(s)
    THEN log[s][idx - lastIncludedIndex[s]]
    ELSE [term |-> -1, cmd |-> "InvalidIndex"]

GetTerm(s, idx) ==
    IF idx = lastIncludedIndex[s]
    THEN lastIncludedTerm[s]
    ELSE GetEntry(s, idx).term

\* --- State Transitions ---
BecomeFollower(s, newTerm) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex,
                   lastIncludedIndex, lastIncludedTerm, votesGranted, messages>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \+ Bag({ RequestVote(s, p, currentTerm[s] + 1, LastLogIndex(s), LastLogTerm(s), TRUE) : p \in config \ {s} })
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \+ Bag({ RequestVote(s, p, currentTerm[s] + 1, LastLogIndex(s), LastLogTerm(s), FALSE) : p \in config \ {s} })
    /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex,
                   lastIncludedIndex, lastIncludedTerm>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in config |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in config |-> 0]]
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], cmd |-> "NO-OP"])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, config,
                   lastIncludedIndex, lastIncludedTerm, votesGranted, messages>>

\* --- Actions ---
ElectionTimeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ BecomePreCandidate(s)

HandleRequestVote(s) ==
    \E m \in DOMAIN messages:
        /\ messages[m].type = "RequestVote"
        /\ messages[m].dst = s
        /\ LET req == messages[m].m IN
        /\ LET voteGranted ==
            IF req.term < currentTerm[s]
            THEN FALSE
            ELSE IF req.prevote
                 THEN LogIsUpToDate(s, req.lastLogTerm, req.lastLogIndex)
                 ELSE \/ votedFor[s] = Nil \/ votedFor[s] = messages[m].src
                      \/ req.term > currentTerm[s]
                      /\ LogIsUpToDate(s, req.lastLogTerm, req.lastLogIndex)
        IN
        /\ IF req.term > currentTerm[s] /\ \lnot req.prevote
           THEN /\ state' = [state EXCEPT ![s] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![s] = req.term]
                /\ votedFor' = [votedFor EXCEPT ![s] = IF voteGranted THEN messages[m].src ELSE Nil]
           ELSE /\ votedFor' = [votedFor EXCEPT ![s] = IF voteGranted /\ \lnot req.prevote THEN messages[m].src ELSE votedFor[s]]
                /\ UNCHANGED <<state, currentTerm>>
        /\ messages' = (messages \- {m}) \+ {RequestVoteResponse(s, messages[m].src, currentTerm'[s], voteGranted)}
        /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex,
                       lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleRequestVoteResponse(s) ==
    \E m \in DOMAIN messages:
        /\ messages[m].type = "RequestVoteResponse"
        /\ messages[m].dst = s
        /\ LET resp == messages[m].m IN
        /\ IF resp.term > currentTerm[s]
           THEN /\ BecomeFollower(s, resp.term)
                /\ messages' = messages \- {m}
           ELSE /\ \/ /\ state[s] = "PreCandidate"
                     /\ currentTerm[s] + 1 = resp.term
                     /\ resp.voteGranted
                     /\ LET newVotes == votesGranted[s] \cup {messages[m].src} IN
                     /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                     /\ IF IsQuorum(newVotes)
                        THEN BecomeCandidate(s) /\ messages' = messages \- {m}
                        ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                         nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, messages>>
                \/ /\ state[s] = "Candidate"
                   /\ currentTerm[s] = resp.term
                   /\ resp.voteGranted
                   /\ LET newVotes == votesGranted[s] \cup {messages[m].src} IN
                   /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                   /\ IF IsQuorum(newVotes)
                      THEN BecomeLeader(s) /\ messages' = messages \- {m}
                      ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                       nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, messages>>
                \/ /\ \lnot resp.voteGranted
                   /\ messages' = messages \- {m}
                   /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                  nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleAppendEntries(s) ==
    \E m \in DOMAIN messages:
        /\ messages[m].type = "AppendEntries"
        /\ messages[m].dst = s
        /\ LET req == messages[m].m IN
        /\ IF req.term < currentTerm[s]
           THEN /\ messages' = (messages \- {m}) \+ {AppendEntriesResponse(s, messages[m].src, currentTerm[s], FALSE, 0)}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                               nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>
           ELSE /\ \/ req.term > currentTerm[s]
                     /\ LET vars_ == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                       nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>> IN
                     /\ state' = [state EXCEPT ![s] = "Follower"]
                     /\ currentTerm' = [currentTerm EXCEPT ![s] = req.term]
                     /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                     /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex,
                                    lastIncludedIndex, lastIncludedTerm, votesGranted>>
                \/ req.term = currentTerm[s]
                   /\ state' = [state EXCEPT ![s] = "Follower"]
                   /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                  nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>
                /\ LET logOK == \/ req.prevLogIndex = 0
                                \/ /\ req.prevLogIndex <= LastLogIndex(s)
                                   /\ GetTerm(s, req.prevLogIndex) = req.prevLogTerm
                IN
                /\ IF logOK
                   THEN /\ LET newEntries == req.entries IN
                        /\ LET firstNew == req.prevLogIndex + 1 IN
                        /\ LET conflictIdx == CHOOSE i \in 1..Len(newEntries) :
                                                \/ firstNew + i - 1 > LastLogIndex(s)
                                                \/ GetTerm(s, firstNew + i - 1) /= newEntries[i].term
                        IN
                        /\ IF conflictIdx = {}
                           THEN log' = log
                           ELSE /\ LET newLogStart == firstNew + conflictIdx - 1 IN
                                /\ LET existingLogPrefix == SubSeq(log[s], 1, newLogStart - 1 - lastIncludedIndex[s]) IN
                                /\ LET entriesToAppend == SubSeq(newEntries, conflictIdx, Len(newEntries)) IN
                                /\ log' = [log EXCEPT ![s] = existingLogPrefix \o entriesToAppend]
                        /\ commitIndex' = [commitIndex EXCEPT ![s] = max({commitIndex[s], min({req.leaderCommit, LastLogIndex(s)})})]
                        /\ messages' = (messages \- {m}) \+ {AppendEntriesResponse(s, messages[m].src, currentTerm'[s], TRUE, LastLogIndex(s))}
                   ELSE /\ messages' = (messages \- {m}) \+ {AppendEntriesResponse(s, messages[m].src, currentTerm'[s], FALSE, LastLogIndex(s))}
                        /\ UNCHANGED <<log, commitIndex>>
                /\ UNCHANGED <<lastApplied, config, nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm>>

HandleAppendEntriesResponse(s) ==
    \E m \in DOMAIN messages:
        /\ messages[m].type = "AppendEntriesResponse"
        /\ messages[m].dst = s
        /\ state[s] = "Leader"
        /\ LET resp == messages[m].m IN
        /\ LET p == messages[m].src IN
        /\ IF resp.term > currentTerm[s]
           THEN /\ BecomeFollower(s, resp.term)
                /\ messages' = messages \- {m}
           ELSE /\ IF resp.success
                     THEN /\ nextIndex' = [nextIndex EXCEPT ![s][p] = resp.matchIndex + 1]
                          /\ matchIndex' = [matchIndex EXCEPT ![s][p] = resp.matchIndex]
                     ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][p] = max({1, nextIndex[s][p] - 1})]
                          /\ UNCHANGED matchIndex
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                               lastIncludedIndex, lastIncludedTerm, votesGranted>>

LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET newCommitIndex ==
        CHOOSE N \in (commitIndex[s] + 1)..LastLogIndex(s) :
            /\ GetTerm(s, N) = currentTerm[s]
            /\ IsQuorum({p \in config |-> matchIndex[s][p] >= N} \cup {s})
    IN
    /\ IF newCommitIndex /= {}
       THEN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
       ELSE UNCHANGED commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm,
                   votesGranted, messages>>

LeaderSendAppendEntries(s) ==
    /\ state[s] = "Leader"
    /\ \E p \in config \ {s}:
        /\ LET ni == nextIndex[s][p] IN
        /\ IF ni > lastIncludedIndex[s]
           THEN /\ LET prevLogIndex == ni - 1 IN
                /\ LET prevLogTerm == GetTerm(s, prevLogIndex) IN
                /\ LET entries == SubSeq(log[s], ni - lastIncludedIndex[s], Len(log[s])) IN
                /\ messages' = messages \+ {AppendEntries(s, p, currentTerm[s], prevLogIndex, prevLogTerm, entries, commitIndex[s])}
           ELSE TRUE /\ messages' = messages \* Will be handled by LeaderSendSnapshot
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

LeaderSendSnapshot(s) ==
    /\ state[s] = "Leader"
    /\ \E p \in config \ {s}:
        /\ nextIndex[s][p] <= lastIncludedIndex[s]
        /\ messages' = messages \+ {InstallSnapshot(s, p, currentTerm[s], lastIncludedIndex[s], lastIncludedTerm[s])}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleInstallSnapshot(s) ==
    \E m \in DOMAIN messages:
        /\ messages[m].type = "InstallSnapshot"
        /\ messages[m].dst = s
        /\ LET req == messages[m].m IN
        /\ IF req.term < currentTerm[s]
           THEN messages' = messages \- {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                               nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>
           ELSE /\ \/ req.term > currentTerm[s]
                     /\ LET vars_ == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                       nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>> IN
                     /\ state' = [state EXCEPT ![s] = "Follower"]
                     /\ currentTerm' = [currentTerm EXCEPT ![s] = req.term]
                     /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                \/ req.term = currentTerm[s]
                   /\ state' = [state EXCEPT ![s] = "Follower"]
                   /\ UNCHANGED <<currentTerm, votedFor>>
                /\ IF req.lastIncludedIndex > lastIncludedIndex[s]
                   THEN /\ LET newLog ==
                            CHOOSE l \in Seq(SUBSET [term: Nat, cmd: Commands \cup {"NO-OP", "ConfigChange"}]) :
                                \/ req.lastIncludedIndex >= LastLogIndex(s)
                                \/ \A i \in 1..Len(l) : l[i] = GetEntry(s, req.lastIncludedIndex + i)
                        IN
                        /\ log' = [log EXCEPT ![s] = newLog]
                        /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = req.lastIncludedIndex]
                        /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = req.lastIncludedTerm]
                        /\ lastApplied' = [lastApplied EXCEPT ![s] = max({lastApplied[s], req.lastIncludedIndex})]
                        /\ commitIndex' = [commitIndex EXCEPT ![s] = max({commitIndex[s], req.lastIncludedIndex})]
                   ELSE UNCHANGED <<log, lastIncludedIndex, lastIncludedTerm, lastApplied, commitIndex>>
                /\ messages' = (messages \- {m}) \+ {InstallSnapshotResponse(s, messages[m].src, currentTerm'[s])}
                /\ UNCHANGED <<config, nextIndex, matchIndex, votesGranted>>

HandleInstallSnapshotResponse(s) ==
    \E m \in DOMAIN messages:
        /\ messages[m].type = "InstallSnapshotResponse"
        /\ messages[m].dst = s
        /\ state[s] = "Leader"
        /\ LET resp == messages[m].m IN
        /\ LET p == messages[m].src IN
        /\ IF resp.term > currentTerm[s]
           THEN /\ BecomeFollower(s, resp.term)
                /\ messages' = messages \- {m}
           ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][p] = lastIncludedIndex[s] + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![s][p] = lastIncludedIndex[s]]
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                               lastIncludedIndex, lastIncludedTerm, votesGranted>>

ClientRequest(s, cmd) ==
    /\ state[s] = "Leader"
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], cmd |-> cmd])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm,
                   votesGranted, messages>>

Apply(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET applyIdx == lastApplied[s] + 1 IN
    /\ LET entry == GetEntry(s, applyIdx) IN
    /\ lastApplied' = [lastApplied EXCEPT ![s] = applyIdx]
    /\ IF entry.cmd.type = "ConfigChange"
       THEN config' = entry.cmd.newConfig
       ELSE UNCHANGED config
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm,
                   votesGranted, messages>>

TakeSnapshot(s) ==
    /\ commitIndex[s] > lastIncludedIndex[s]
    /\ \E idx \in (lastIncludedIndex[s] + 1)..commitIndex[s]:
        /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = idx]
        /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = GetTerm(s, idx)]
        /\ log' = [log EXCEPT ![s] = SubSeq(log[s], idx - lastIncludedIndex[s] + 1, Len(log[s]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, votesGranted, messages>>

\* --- Initial State ---
Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ lastApplied = [s \in Servers |-> 0]
    /\ config = Servers
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ lastIncludedIndex = [s \in Servers |-> 0]
    /\ lastIncludedTerm = [s \in Servers |-> 0]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ messages = EmptyBag

\* --- Next State Relation ---
Next ==
    \/ \E s \in config: ElectionTimeout(s)
    \/ \E s \in config: HandleRequestVote(s)
    \/ \E s \in config: HandleRequestVoteResponse(s)
    \/ \E s \in config: HandleAppendEntries(s)
    \/ \E s \in config: HandleAppendEntriesResponse(s)
    \/ \E s \in config: LeaderAdvanceCommitIndex(s)
    \/ \E s \in config: LeaderSendAppendEntries(s)
    \/ \E s \in config: LeaderSendSnapshot(s)
    \/ \E s \in config: HandleInstallSnapshot(s)
    \/ \E s \in config: HandleInstallSnapshotResponse(s)
    \/ \E s \in config, cmd \in Commands: ClientRequest(s, cmd)
    \/ \E s \in config: Apply(s)
    \/ \E s \in config: TakeSnapshot(s)

Spec == Init /\ [][Next]_vars

====