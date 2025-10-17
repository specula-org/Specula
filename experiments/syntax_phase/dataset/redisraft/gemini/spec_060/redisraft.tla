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

InstallSnapshotResponse(src, dst, term, lastIdx) ==
    MsgType("InstallSnapshotResponse", src, dst, [
        term |-> term,
        lastIncludedIndex |-> lastIdx
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

max(a, b) == IF a >= b THEN a ELSE b
min(a, b) == IF a <= b THEN a ELSE b
MaxSet(S) == CHOOSE x \in S : \A y \in S : y <= x

\* --- State Transitions ---
BecomeFollower(s, newTerm) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex,
                   lastIncludedIndex, lastIncludedTerm, votesGranted>>

\* --- Actions ---
ElectionTimeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \+ SetToBag({ RequestVote(s, p, currentTerm[s] + 1, LastLogIndex(s), LastLogTerm(s), TRUE) : p \in config \ {s} })
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm>>

HandleRequestVote(s) ==
    \E m \in BagToSet(messages):
        /\ m.type = "RequestVote"
        /\ m.dst = s
        /\ LET req == m.m
        /\ LET cand == m.src
        /\ LET term == currentTerm[s]
        /\ LET grant ==
               /\ req.term >= term
               /\ LogIsUpToDate(s, req.lastLogTerm, req.lastLogIndex)
               /\ (IF req.prevote
                   THEN TRUE
                   ELSE req.term > term \/ votedFor[s] = Nil \/ votedFor[s] = cand)
        /\ LET stepDown == req.term > term
        /\ state' = IF stepDown
                    THEN [state EXCEPT ![s] = "Follower"]
                    ELSE state
        /\ currentTerm' = IF stepDown
                          THEN [currentTerm EXCEPT ![s] = req.term]
                          ELSE currentTerm
        /\ votedFor' = [votedFor EXCEPT ![s] =
                         IF grant /\ \lnot req.prevote
                         THEN cand
                         ELSE IF stepDown THEN Nil ELSE votedFor[s]]
        /\ LET newTerm == IF req.term > term THEN req.term ELSE term
        /\ messages' = (messages \- SetToBag({m})) \+ SetToBag({RequestVoteResponse(s, cand, newTerm, grant)})
        /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex,
                       lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleRequestVoteResponse(s) ==
    \E m \in BagToSet(messages):
        /\ m.type = "RequestVoteResponse"
        /\ m.dst = s
        /\ LET resp == m.m
        /\ LET voter == m.src
        /\ \/ /\ resp.term > currentTerm[s]
              /\ BecomeFollower(s, resp.term)
              /\ messages' = messages \- SetToBag({m})
           \/ /\ resp.term <= currentTerm[s]
              /\ \/ /\ state[s] = "PreCandidate"
                     /\ currentTerm[s] + 1 = resp.term
                     /\ resp.voteGranted
                     /\ LET newVotes == votesGranted[s] \cup {voter}
                     /\ \/ /\ IsQuorum(newVotes)
                           /\ state' = [state EXCEPT ![s] = "Candidate"]
                           /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                           /\ votedFor' = [votedFor EXCEPT ![s] = s]
                           /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                           /\ messages' = (messages \- SetToBag({m})) \+ SetToBag({ RequestVote(s, p, currentTerm[s] + 1, LastLogIndex(s), LastLogTerm(s), FALSE) : p \in config \ {s} })
                           /\ UNCHANGED <<log, commitIndex, lastApplied, config, nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm>>
                        \/ /\ \lnot IsQuorum(newVotes)
                           /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                           /\ messages' = messages \- SetToBag({m})
                           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                          nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm>>
                 \/ /\ state[s] = "Candidate"
                    /\ currentTerm[s] = resp.term
                    /\ resp.voteGranted
                    /\ LET newVotes == votesGranted[s] \cup {voter}
                    /\ \/ /\ IsQuorum(newVotes)
                           /\ state' = [state EXCEPT ![s] = "Leader"]
                           /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in config |-> LastLogIndex(s) + 1]]
                           /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in config |-> 0]]
                           /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], cmd |-> "NO-OP"])]
                           /\ messages' = messages \- SetToBag({m})
                           /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, config,
                                          lastIncludedIndex, lastIncludedTerm, votesGranted>>
                       \/ /\ \lnot IsQuorum(newVotes)
                           /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                           /\ messages' = messages \- SetToBag({m})
                           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                          nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm>>
                 \/ /\ \lnot ( (state[s] = "PreCandidate" /\ currentTerm[s] + 1 = resp.term /\ resp.voteGranted) \/
                               (state[s] = "Candidate" /\ currentTerm[s] = resp.term /\ resp.voteGranted) )
                    /\ messages' = messages \- SetToBag({m})
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleAppendEntries(s) ==
    \E m \in BagToSet(messages):
        /\ m.type = "AppendEntries"
        /\ m.dst = s
        /\ LET req == m.m
        /\ LET leader == m.src
        /\ LET term == currentTerm[s]
        /\ LET FindConflict(idx) ==
                IF idx > Len(req.entries) \/ (req.prevLogIndex + idx) > LastLogIndex(s)
                THEN idx
                ELSE IF GetTerm(s, req.prevLogIndex + idx) /= req.entries[idx].term
                     THEN idx
                     ELSE FindConflict(idx + 1)
        IN
        /\ \/ /\ req.term < term
              /\ messages' = (messages \- SetToBag({m})) \+ SetToBag({AppendEntriesResponse(s, leader, term, FALSE, 0)})
              /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                             nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>
           \/ /\ req.term >= term
              /\ LET newTerm == req.term
              /\ state' = [state EXCEPT ![s] = "Follower"]
              /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
              /\ votedFor' = IF req.term > term THEN [votedFor EXCEPT ![s] = Nil] ELSE votedFor
              /\ LET logOK == \/ req.prevLogIndex = 0
                              \/ /\ req.prevLogIndex > 0
                                 /\ req.prevLogIndex <= LastLogIndex(s)
                                 /\ GetTerm(s, req.prevLogIndex) = req.prevLogTerm
              /\ \/ /\ logOK
                     /\ LET conflictIdx == FindConflict(1)
                           prefix == SubSeq(log[s], 1, req.prevLogIndex - lastIncludedIndex[s] + conflictIdx - 1)
                           suffix == SubSeq(req.entries, conflictIdx, Len(req.entries))
                           newLog == prefix \o suffix
                           newLastLogIndex == lastIncludedIndex[s] + Len(newLog)
                     IN
                     /\ log' = [log EXCEPT ![s] = newLog]
                     /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], min(req.leaderCommit, newLastLogIndex))]
                     /\ messages' = (messages \- SetToBag({m})) \+ SetToBag({AppendEntriesResponse(s, leader, newTerm, TRUE, newLastLogIndex)})
                 \/ /\ \lnot logOK
                     /\ messages' = (messages \- SetToBag({m})) \+ SetToBag({AppendEntriesResponse(s, leader, newTerm, FALSE, 0)})
                     /\ UNCHANGED <<log, commitIndex>>
              /\ UNCHANGED <<lastApplied, config, nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleAppendEntriesResponse(s) ==
    \E m \in BagToSet(messages):
        /\ m.type = "AppendEntriesResponse"
        /\ m.dst = s
        /\ state[s] = "Leader"
        /\ LET resp == m.m
        /\ LET p == m.src
        /\ \/ /\ resp.term > currentTerm[s]
              /\ BecomeFollower(s, resp.term)
              /\ messages' = messages \- SetToBag({m})
           \/ /\ resp.term <= currentTerm[s]
              /\ \/ /\ resp.success
                     /\ nextIndex' = [nextIndex EXCEPT ![s][p] = resp.matchIndex + 1]
                     /\ matchIndex' = [matchIndex EXCEPT ![s][p] = resp.matchIndex]
                 \/ /\ \lnot resp.success
                     /\ nextIndex' = [nextIndex EXCEPT ![s][p] = max(1, nextIndex[s][p] - 1)]
                     /\ UNCHANGED matchIndex
              /\ messages' = messages \- SetToBag({m})
              /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                             lastIncludedIndex, lastIncludedTerm, votesGranted>>

LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET PossibleCommitIndexes ==
        { N \in (commitIndex[s] + 1)..LastLogIndex(s) :
            /\ GetTerm(s, N) = currentTerm[s]
            /\ IsQuorum({p \in config : matchIndex[s][p] >= N} \cup {s})
        }
    IN
    /\ commitIndex' = IF PossibleCommitIndexes /= {}
                      THEN [commitIndex EXCEPT ![s] = MaxSet(PossibleCommitIndexes)]
                      ELSE commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm,
                   votesGranted, messages>>

LeaderSendAppendEntries(s) ==
    /\ state[s] = "Leader"
    /\ \E p \in config \ {s}:
        /\ LET ni == nextIndex[s][p] IN
        /\ ni > lastIncludedIndex[s]
        /\ LET prevLogIndex == ni - 1 IN
        /\ LET prevLogTerm == GetTerm(s, prevLogIndex) IN
        /\ LET entries == SubSeq(log[s], ni - lastIncludedIndex[s], Len(log[s])) IN
        /\ messages' = messages \+ SetToBag({AppendEntries(s, p, currentTerm[s], prevLogIndex, prevLogTerm, entries, commitIndex[s])})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

LeaderSendSnapshot(s) ==
    /\ state[s] = "Leader"
    /\ \E p \in config \ {s}:
        /\ nextIndex[s][p] <= lastIncludedIndex[s]
        /\ messages' = messages \+ SetToBag({InstallSnapshot(s, p, currentTerm[s], lastIncludedIndex[s], lastIncludedTerm[s])})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, config,
                   nextIndex, matchIndex, lastIncludedIndex, lastIncludedTerm, votesGranted>>

HandleInstallSnapshot(s) ==
    \E m \in BagToSet(messages):
        /\ m.type = "InstallSnapshot"
        /\ m.dst = s
        /\ LET req == m.m
        /\ LET leader == m.src
        /\ \/ /\ req.term < currentTerm[s]
              /\ messages' = messages \- SetToBag({m})
              /\ UNCHANGED <<vars>>
           \/ /\ req.term >= currentTerm[s]
              /\ LET newTerm == req.term
              /\ state' = [state EXCEPT ![s] = "Follower"]
              /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
              /\ votedFor' = IF req.term > currentTerm[s] THEN [votedFor EXCEPT ![s] = Nil] ELSE votedFor
              /\ \/ /\ req.lastIncludedIndex > lastIncludedIndex[s]
                     /\ LET newLog ==
                             IF req.lastIncludedIndex >= LastLogIndex(s)
                             THEN << >>
                             ELSE SubSeq(log[s], req.lastIncludedIndex - lastIncludedIndex[s] + 1, Len(log[s]))
                     /\ log' = [log EXCEPT ![s] = newLog]
                     /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = req.lastIncludedIndex]
                     /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = req.lastIncludedTerm]
                     /\ lastApplied' = [lastApplied EXCEPT ![s] = max(lastApplied[s], req.lastIncludedIndex)]
                     /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], req.lastIncludedIndex)]
                 \/ /\ req.lastIncludedIndex <= lastIncludedIndex[s]
                     /\ UNCHANGED <<log, lastIncludedIndex, lastIncludedTerm, lastApplied, commitIndex>>
              /\ messages' = (messages \- SetToBag({m})) \+ SetToBag({InstallSnapshotResponse(s, leader, newTerm, req.lastIncludedIndex)})
              /\ UNCHANGED <<config, nextIndex, matchIndex, votesGranted>>

HandleInstallSnapshotResponse(s) ==
    \E m \in BagToSet(messages):
        /\ m.type = "InstallSnapshotResponse"
        /\ m.dst = s
        /\ state[s] = "Leader"
        /\ LET resp == m.m
        /\ LET p == m.src
        /\ \/ /\ resp.term > currentTerm[s]
              /\ BecomeFollower(s, resp.term)
              /\ messages' = messages \- SetToBag({m})
           \/ /\ resp.term <= currentTerm[s]
              /\ nextIndex' = [nextIndex EXCEPT ![s][p] = max(nextIndex[s][p], resp.lastIncludedIndex + 1)]
              /\ matchIndex' = [matchIndex EXCEPT ![s][p] = max(matchIndex[s][p], resp.lastIncludedIndex)]
              /\ messages' = messages \- SetToBag({m})
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
    /\ config' = IF DOMAIN entry.cmd = {"type", "newConfig"} /\ entry.cmd.type = "ConfigChange"
                 THEN entry.cmd.newConfig
                 ELSE config
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
