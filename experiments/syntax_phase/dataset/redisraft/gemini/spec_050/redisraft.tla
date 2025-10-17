---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Value, Nil

ASSUME Server \subseteq Nat
ASSUME Nil \notin Server

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
MsgType == {"RequestVoteRequest", "RequestVoteResponse",
            "AppendEntriesRequest", "AppendEntriesResponse",
            "InstallSnapshotRequest", "InstallSnapshotResponse"}
LogEntryType == {"NORMAL", "ADD_NODE", "REMOVE_NODE"}

VARIABLES state, currentTerm, votedFor, log, commitIndex, lastApplied,
          votesGranted, nextIndex, matchIndex,
          snapshotLastIndex, snapshotLastTerm, config, msgs

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          votesGranted, nextIndex, matchIndex,
          snapshotLastIndex, snapshotLastTerm, config, msgs>>

TypeOK ==
    /\ \A s \in Server:
        /\ state[s] \in NodeStates
        /\ currentTerm[s] \in Nat
        /\ votedFor[s] \in Server \cup {Nil}
        /\ \A e \in log[s]:
            e \in [term: Nat, val: Value, type: LogEntryType]
        /\ commitIndex[s] \in Nat
        /\ lastApplied[s] \in Nat
        /\ votesGranted[s] \subseteq Server
        /\ \A p \in Server:
            /\ nextIndex[s][p] \in Nat
            /\ matchIndex[s][p] \in Nat
        /\ snapshotLastIndex[s] \in Nat
        /\ snapshotLastTerm[s] \in Nat
        /\ config[s] \subseteq Server
    /\ msgs \in Bag(
        [type: MsgType, from: Server, to: Server, mterm: Nat] \cup
        [type: MsgType, from: Server, to: Server, mterm: Nat, prevote: BOOLEAN, lastLogIndex: Nat, lastLogTerm: Nat] \cup
        [type: MsgType, from: Server, to: Server, mterm: Nat, voteGranted: BOOLEAN, prevote: BOOLEAN] \cup
        [type: MsgType, from: Server, to: Server, mterm: Nat, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq, leaderCommit: Nat] \cup
        [type: MsgType, from: Server, to: Server, mterm: Nat, success: BOOLEAN, matchIndex: Nat] \cup
        [type: MsgType, from: Server, to: Server, mterm: Nat, lastIncludedIndex: Nat, lastIncludedTerm: Nat]
    )

LastLogIndex(s) == snapshotLastIndex[s] + Len(log[s])
LastLogTerm(s) == IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE snapshotLastTerm[s]
LogTerm(s, idx) == IF idx > snapshotLastIndex[s] /\ idx <= LastLogIndex(s)
                   THEN log[s][idx - snapshotLastIndex[s]].term
                   ELSE IF idx = snapshotLastIndex[s] THEN snapshotLastTerm[s] ELSE 0
IsUpToDate(candidate, voter) ==
    \/ LastLogTerm(candidate) > LastLogTerm(voter)
    \/ /\ LastLogTerm(candidate) = LastLogTerm(voter)
       /\ LastLogIndex(candidate) >= LastLogIndex(voter)

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config, msgs>>

BecomePreCandidate(s) ==
    /\ state[s] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ state' = [state EXCEPT ![s] = "PRECANDIDATE"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config, msgs>>

BecomeCandidate(s) ==
    /\ state[s] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config, msgs>>

BecomeLeader(s) ==
    /\ state[s] = "CANDIDATE"
    /\ Cardinality(votesGranted[s]) * 2 > Cardinality(config[s])
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, config, msgs>>

ElectionTimeout(s) ==
    /\ state[s] \in {"FOLLOWER", "CANDIDATE"}
    /\ BecomePreCandidate(s)

SendRequestVote(s) ==
    LET isPreVote == state[s] = "PRECANDIDATE"
        termToSend == IF isPreVote THEN currentTerm[s] + 1 ELSE currentTerm[s]
    IN
    /\ state[s] \in {"PRECANDIDATE", "CANDIDATE"}
    /\ msgs' = msgs \+ Bag({[
            type |-> "RequestVoteRequest", from |-> s, to |-> p,
            mterm |-> termToSend, prevote |-> isPreVote,
            lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s)
        ] : p \in config[s] \ {s}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

RecvRequestVote(s) ==
    \E m \in DOMAIN msgs:
    /\ msgs[m].type = "RequestVoteRequest"
    /\ msgs[m].to = s
    /\ LET from == msgs[m].from
           mterm == msgs[m].mterm
           isPreVote == msgs[m].prevote
           candidateLog == [lastLogIndex |-> msgs[m].lastLogIndex, lastLogTerm |-> msgs[m].lastLogTerm]
           voterState == [lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s)]
           logIsUpToDate == \/ candidateLog.lastLogTerm > voterState.lastLogTerm
                            \/ /\ candidateLog.lastLogTerm = voterState.lastLogTerm
                               /\ candidateLog.lastLogIndex >= voterState.lastLogIndex
           voteGranted ==
               IF mterm < currentTerm[s] THEN FALSE
               ELSE IF isPreVote
                    THEN logIsUpToDate
                    ELSE /\ (mterm > currentTerm[s] \/ votedFor[s] \in {Nil, from})
                         /\ logIsUpToDate
    IN
    /\ IF voteGranted /\ \lnot isPreVote
       THEN /\ votedFor' = [votedFor EXCEPT ![s] = from]
            /\ IF mterm > currentTerm[s]
               THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                    /\ currentTerm' = [currentTerm EXCEPT ![s] = mterm]
               ELSE UNCHANGED <<state, currentTerm>>
       ELSE UNCHANGED <<state, currentTerm, votedFor>>
    /\ msgs' = (msgs \- Bag({m})) \+ Bag({[
            type |-> "RequestVoteResponse", from |-> s, to |-> from,
            mterm |-> currentTerm[s], voteGranted |-> voteGranted, prevote |-> isPreVote
        ]})
    /\ UNCHANGED <<log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

RecvRequestVoteResponse(s) ==
    \E m \in DOMAIN msgs:
    /\ msgs[m].type = "RequestVoteResponse"
    /\ msgs[m].to = s
    /\ LET from == msgs[m].from
           mterm == msgs[m].mterm
           isPreVote == msgs[m].prevote
           isCandidate == state[s] = "CANDIDATE"
           isPreCandidate == state[s] = "PRECANDIDATE"
    IN
    /\ IF mterm > currentTerm[s]
       THEN BecomeFollower(s, mterm)
       ELSE /\ IF msgs[m].voteGranted /\ ((isPreCandidate /\ mterm = currentTerm[s] + 1) \/ (isCandidate /\ mterm = currentTerm[s]))
              THEN /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {from}]
                   /\ IF isPreCandidate /\ Cardinality(votesGranted'[s]) * 2 > Cardinality(config[s])
                      THEN BecomeCandidate(s)
                      ELSE UNCHANGED <<state, currentTerm, votedFor, msgs>>
              ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted, msgs>>
            \* FIX: Aligned the start of expressions in the conjunction list to fix a parse error.
            /\  msgs' = msgs \- Bag({m})
            /\  UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

SendAppendEntries(s) ==
    /\ state[s] = "LEADER"
    /\ \E p \in config[s] \ {s}:
        /\ IF nextIndex[s][p] > snapshotLastIndex[s]
           THEN LET prevIdx == nextIndex[s][p] - 1
                    prevTerm == LogTerm(s, prevIdx)
                    entries == SubSeq(log[s], nextIndex[s][p] - snapshotLastIndex[s], Len(log[s]))
                IN msgs' = msgs \+ Bag({[
                    type |-> "AppendEntriesRequest", from |-> s, to |-> p,
                    mterm |-> currentTerm[s], prevLogIndex |-> prevIdx,
                    prevLogTerm |-> prevTerm, entries |-> entries,
                    leaderCommit |-> commitIndex[s]
                ]})
           ELSE msgs' = msgs \+ Bag({[
                    type |-> "InstallSnapshotRequest", from |-> s, to |-> p,
                    mterm |-> currentTerm[s],
                    lastIncludedIndex |-> snapshotLastIndex[s],
                    lastIncludedTerm |-> snapshotLastTerm[s]
                ]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

RecvAppendEntries(s) ==
    \E m \in DOMAIN msgs:
    /\ msgs[m].type = "AppendEntriesRequest"
    /\ msgs[m].to = s
    /\ LET from == msgs[m].from
           mterm == msgs[m].mterm
           prevLogIndex == msgs[m].prevLogIndex
           prevLogTerm == msgs[m].prevLogTerm
           entries == msgs[m].entries
           leaderCommit == msgs[m].leaderCommit
    IN
    /\ IF mterm < currentTerm[s]
       THEN /\ msgs' = (msgs \- Bag({m})) \+ Bag({[
                type |-> "AppendEntriesResponse", from |-> s, to |-> from,
                mterm |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0
            ]})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>
       ELSE /\ LET logOK == /\ prevLogIndex <= LastLogIndex(s)
                           /\ LogTerm(s, prevLogIndex) = prevLogTerm
            IN
            /\ IF \lnot logOK
               THEN /\ msgs' = (msgs \- Bag({m})) \+ Bag({[
                        type |-> "AppendEntriesResponse", from |-> s, to |-> from,
                        mterm |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0
                    ]})
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>
               ELSE /\ LET newLog == SubSeq(log[s], 1, prevLogIndex - snapshotLastIndex[s]) \o entries
                  IN
                  /\ log' = [log EXCEPT ![s] = newLog]
                  /\ commitIndex' = [commitIndex EXCEPT ![s] = max({commitIndex[s], min({leaderCommit, prevLogIndex + Len(entries)})})]
                  /\ msgs' = (msgs \- Bag({m})) \+ Bag({[
                        type |-> "AppendEntriesResponse", from |-> s, to |-> from,
                        mterm |-> currentTerm[s], success |-> TRUE,
                        matchIndex |-> prevLogIndex + Len(entries)
                    ]})
                  /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                  /\ currentTerm' = [currentTerm EXCEPT ![s] = mterm]
                  /\ UNCHANGED <<votedFor, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>

RecvAppendEntriesResponse(s) ==
    \E m \in DOMAIN msgs:
    /\ msgs[m].type = "AppendEntriesResponse"
    /\ msgs[m].to = s
    /\ state[s] = "LEADER"
    /\ LET from == msgs[m].from
           mterm == msgs[m].mterm
    IN
    /\ IF mterm > currentTerm[s]
       THEN /\ BecomeFollower(s, mterm)
            /\ msgs' = msgs \- Bag({m})
       ELSE /\ IF mterm = currentTerm[s]
              THEN /\ IF msgs[m].success
                     THEN /\ matchIndex' = [matchIndex EXCEPT ![s][from] = max({matchIndex[s][from], msgs[m].matchIndex})]
                          /\ nextIndex' = [nextIndex EXCEPT ![s][from] = max({nextIndex[s][from], msgs[m].matchIndex + 1})]
                     ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][from] = max({1, nextIndex[s][from] - 1})]
                          /\ UNCHANGED matchIndex
                   /\ msgs' = msgs \- Bag({m})
                   /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, snapshotLastIndex, snapshotLastTerm, config>>
              ELSE /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config>>
                   /\ msgs' = msgs \- Bag({m})

LeaderCommit(s) ==
    /\ state[s] = "LEADER"
    /\ LET possibleCIs = { i \in (commitIndex[s] + 1)..LastLogIndex(s) |
                            /\ LogTerm(s, i) = currentTerm[s]
                            /\ Cardinality({p \in config[s] | matchIndex[s][p] >= i} \cup {s}) * 2 > Cardinality(config[s])
                         }
    IN
    /\ possibleCIs /= {}
    /\ commitIndex' = [commitIndex EXCEPT ![s] = Max(possibleCIs)]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config, msgs>>

LogAppend(s) ==
    /\ state[s] = "LEADER"
    /\ \E v \in Value:
        /\ LET newEntry == [term |-> currentTerm[s], val |-> v, type |-> "NORMAL"]
        IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config, msgs>>

ApplyConfigChange(s) ==
    /\ state[s] = "LEADER"
    /\ \E newServer \in Server \ config[s]:
        /\ LET newEntry == [term |-> currentTerm[s], val |-> newServer, type |-> "ADD_NODE"]
        IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, config, msgs>>

LogCommit(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ LET applyIdx == lastApplied[s] + 1
           entry == log[s][applyIdx - snapshotLastIndex[s]]
    IN
    /\ lastApplied' = [lastApplied EXCEPT ![s] = applyIdx]
    /\ IF entry.type = "ADD_NODE"
       THEN config' = [config EXCEPT ![s] = config[s] \cup {entry.val}]
       ELSE IF entry.type = "REMOVE_NODE"
            THEN config' = [config EXCEPT ![s] = config[s] \ {entry.val}]
            ELSE UNCHANGED config
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, votesGranted, nextIndex, matchIndex, snapshotLastIndex, snapshotLastTerm, msgs>>

RecvInstallSnapshot(s) ==
    \E m \in DOMAIN msgs:
    /\ msgs[m].type = "InstallSnapshotRequest"
    /\ msgs[m].to = s
    /\ LET from == msgs[m].from
           mterm == msgs[m].mterm
           lastIdx == msgs[m].lastIncludedIndex
           lastTerm == msgs[m].lastIncludedTerm
    IN
    /\ IF mterm < currentTerm[s]
       THEN UNCHANGED <<vars, msgs>>
       ELSE /\ IF lastIdx > snapshotLastIndex[s]
              THEN /\ log' = [log EXCEPT ![s] = << >>]
                   /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = lastIdx]
                   /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = lastTerm]
                   /\ commitIndex' = [commitIndex EXCEPT ![s] = max({commitIndex[s], lastIdx})]
                   /\ lastApplied' = [lastApplied EXCEPT ![s] = max({lastApplied[s], lastIdx})]
              ELSE UNCHANGED <<log, snapshotLastIndex, snapshotLastTerm, commitIndex, lastApplied>>
            /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = mterm]
            /\ msgs' = msgs \- Bag({m})
            /\ UNCHANGED <<votedFor, votesGranted, nextIndex, matchIndex, config>>

Init ==
    /\ state = [s \in Server |-> "FOLLOWER"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ votesGranted = [s \in Server |-> {}]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ snapshotLastIndex = [s \in Server |-> 0]
    /\ snapshotLastTerm = [s \in Server |-> 0]
    /\ config = [s \in Server |-> Server]
    /\ msgs = EmptyBag

Next ==
    \/ \E s \in Server:
        \/ ElectionTimeout(s)
        \/ SendRequestVote(s)
        \/ RecvRequestVote(s)
        \/ RecvRequestVoteResponse(s)
        \/ SendAppendEntries(s)
        \/ RecvAppendEntries(s)
        \/ RecvAppendEntriesResponse(s)
        \/ LeaderCommit(s)
        \/ LogAppend(s)
        \/ ApplyConfigChange(s)
        \/ LogCommit(s)
        \/ RecvInstallSnapshot(s)
        \/ BecomeLeader(s)

Spec == Init /\ [][Next]_vars

====