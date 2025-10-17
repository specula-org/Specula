---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,
    Commands,
    Nil,
    ElectionTimeout,
    HeartbeatTimeout

ASSUME /\ ElectionTimeout > HeartbeatTimeout
       /\ TLC!Assert(IsFiniteSet(Servers), "Servers must be a finite set")
       /\ TLC!Assert(Cardinality(Servers) % 2 = 1, "Works best with an odd number of servers")

Quorum == (Cardinality(Servers) \div 2) + 1

NodeState == {"Follower", "PreCandidate", "Candidate", "Leader"}
MsgType == {"MsgPreVote", "MsgPreVoteResp",
            "MsgVote", "MsgVoteResp",
            "MsgApp", "MsgAppResp",
            "MsgProp"}

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    electionTimer,
    votesGranted,
    nextIndex,
    matchIndex,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer,
          votesGranted, nextIndex, matchIndex, messages>>

TypeOK ==
    /\ state \in [Servers -> NodeState]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ \A s \in Servers: log[s] \in Seq({[term: Nat, command: Commands]})
    /\ commitIndex \in [Servers -> Nat]
    /\ leader \in [Servers -> Servers \cup {Nil}]
    /\ electionTimer \in [Servers -> Nat]
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ \A s \in Servers: nextIndex[s] \in [Servers -> Nat]
    /\ \A s \in Servers: matchIndex[s] \in [Servers -> Nat]
    /\ IsABag(messages)

LastIndex(lg) == Len(lg)
LastTerm(lg) == IF Len(lg) > 0 THEN lg[Len(lg)].term ELSE 0

IsUpToDate(candidateLog, myLog) ==
    LET candLastTerm = LastTerm(candidateLog)
        myLastTerm = LastTerm(myLog)
    IN \/ candLastTerm > myLastTerm
       \/ /\ candLastTerm = myLastTerm
          /\ LastIndex(candidateLog) >= LastIndex(myLog)

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

StepDown(s, m) ==
    IF m.term > currentTerm[s]
    THEN BecomeFollower(s, m.term)
    ELSE UNCHANGED <<state, currentTerm, votedFor, leader, electionTimer, votesGranted>>

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ leader = [s \in Servers |-> Nil]
    /\ electionTimer = [s \in Servers |-> 0]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ messages = EmptyBag

Tick(s) ==
    /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, nextIndex, matchIndex, messages>>

Timeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[s] >= ElectionTimeout
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ LET
        nextTerm == currentTerm[s] + 1
        lastIdx == LastIndex(log[s])
        lastTrm == LastTerm(log[s])
        newMsgs == {[
            type |-> "MsgPreVote", from |-> s, to |-> peer, term |-> nextTerm,
            logTerm |-> lastTrm, index |-> lastIdx
        ] : peer \in Servers \ {s}}
       IN messages' = messages (+) Bag(newMsgs)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader, nextIndex, matchIndex>>

HandleMsgProp(s, m) ==
    /\ m.type = "MsgProp"
    /\ state[s] = "Leader"
    /\ LET newEntry == [term |-> currentTerm[s], command |-> m.command]
       IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader, electionTimer,
                   votesGranted, nextIndex, matchIndex>>

Heartbeat(s) ==
    /\ state[s] = "Leader"
    /\ electionTimer[s] >= HeartbeatTimeout
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ LET newMsgs == {[
            type |-> "MsgApp", from |-> s, to |-> peer, term |-> currentTerm[s],
            prevLogIndex |-> LastIndex(log[s]),
            prevLogTerm |-> LastTerm(log[s]),
            entries |-> << >>,
            leaderCommit |-> commitIndex[s]
        ] : peer \in Servers \ {s}}
       IN messages' = messages (+) Bag(newMsgs)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, nextIndex, matchIndex>>

ReplicateLog(s, peer) ==
    /\ state[s] = "Leader"
    /\ LET
        ni == nextIndex[s][peer]
        prevIdx == ni - 1
        prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
        newEntries == SubSeq(log[s], ni, Len(log[s]))
    IN /\ ni <= LastIndex(log[s])
       /\ messages' = messages (+) Bag({[
            type |-> "MsgApp", from |-> s, to |-> peer, term |-> currentTerm[s],
            prevLogIndex |-> prevIdx,
            prevLogTerm |-> prevTerm,
            entries |-> newEntries,
            leaderCommit |-> commitIndex[s]
        ]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer,
                   votesGranted, nextIndex, matchIndex>>

HandleMsgApp(s, m) ==
    /\ m.type = "MsgApp"
    /\ m.term >= currentTerm[s]
    /\ LET
        localPrevLogTerm == IF m.prevLogIndex > 0 /\ m.prevLogIndex <= LastIndex(log[s])
                              THEN log[s][m.prevLogIndex].term
                              ELSE 0
        logOK == /\ m.prevLogIndex <= LastIndex(log[s])
                 /\ localPrevLogTerm = m.prevLogTerm
    IN
    /\ StepDown(s, m)
    /\ leader' = [leader EXCEPT ![s] = m.from]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ IF logOK
       THEN /\ LET
                conflictIndex == CHOOSE i \in 1..Len(m.entries):
                                   /\ m.prevLogIndex + i <= Len(log[s])
                                   /\ log[s][m.prevLogIndex + i].term /= m.entries[i].term
                newLog == IF conflictIndex = NULL
                          THEN Append(log[s], m.entries)
                          ELSE Append(SubSeq(log[s], 1, m.prevLogIndex), m.entries)
              IN log' = [log EXCEPT ![s] = newLog]
            /\ commitIndex' = [commitIndex EXCEPT ![s] = max({commitIndex[s], min({m.leaderCommit, LastIndex(log'[s])})})]
            /\ messages' = (messages \ {m}) (+) Bag({[
                type |-> "MsgAppResp", from |-> s, to |-> m.from, term |-> currentTerm'[s],
                index |-> m.prevLogIndex + Len(m.entries), reject |-> FALSE
            ]})
       ELSE /\ messages' = (messages \ {m}) (+) Bag({[
                type |-> "MsgAppResp", from |-> s, to |-> m.from, term |-> currentTerm[s],
                index |-> 0, reject |-> TRUE
            ]})
            /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<votedFor, votesGranted, nextIndex, matchIndex>>

HandleMsgAppResp(s, m) ==
    /\ m.type = "MsgAppResp"
    /\ state[s] = "Leader"
    /\ m.term = currentTerm[s]
    /\ IF m.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = nextIndex[s][m.from] - 1]]
            /\ UNCHANGED <<matchIndex>>
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.index + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![m.from] = m.index]]
    /\ LET
        matchSet(idx) == {p \in Servers |-> matchIndex'[s][p] >= idx}
        committedInTerm(idx) == log[s][idx].term = currentTerm[s]
        newCommitIndex ==
            CHOOSE N \in commitIndex[s]+1 .. Len(log[s]) :
                /\ Cardinality(matchSet(N)) >= Quorum
                /\ committedInTerm(N)
                /\ \A N2 \in N+1 .. Len(log[s]) :
                    \/ Cardinality(matchSet(N2)) < Quorum
                    \/ ~committedInTerm(N2)
       IN commitIndex' = [commitIndex EXCEPT ![s] = IF newCommitIndex = NULL THEN commitIndex[s] ELSE newCommitIndex]
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, electionTimer, votesGranted>>

HandleMsgPreVote(s, m) ==
    /\ m.type = "MsgPreVote"
    /\ LET
        candidateLog == [index |-> m.index, term |-> m.logTerm]
        myLog == [index |-> LastIndex(log[s]), term |-> LastTerm(log[s])]
        grant == /\ m.term > currentTerm[s]
                 /\ IsUpToDate(candidateLog, myLog)
    IN
    /\ messages' = (messages \ {m}) (+) Bag({[
        type |-> "MsgPreVoteResp", from |-> s, to |-> m.from, term |-> m.term,
        reject |-> ~grant
    ]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer,
                   votesGranted, nextIndex, matchIndex>>

HandleMsgPreVoteResp(s, m) ==
    /\ m.type = "MsgPreVoteResp"
    /\ state[s] = "PreCandidate"
    /\ m.term = currentTerm[s] + 1
    /\ IF m.reject
       THEN UNCHANGED <<votesGranted, state, currentTerm, votedFor, messages>>
       ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.from}]
            /\ IF Cardinality(votesGranted'[s]) >= Quorum
               THEN /\ state' = [state EXCEPT ![s] = "Candidate"]
                    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                    /\ votedFor' = [votedFor EXCEPT ![s] = s]
                    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                    /\ LET
                        lastIdx == LastIndex(log[s])
                        lastTrm == LastTerm(log[s])
                        newMsgs == {[
                            type |-> "MsgVote", from |-> s, to |-> peer, term |-> currentTerm'[s],
                            logTerm |-> lastTrm, index |-> lastIdx
                        ] : peer \in Servers \ {s}}
                       IN messages' = (messages \ {m}) (+) Bag(newMsgs)
               ELSE /\ UNCHANGED <<state, currentTerm, votedFor>>
                    /\ messages' = messages \ {m}
    /\ UNCHANGED <<log, commitIndex, leader, electionTimer, nextIndex, matchIndex>>

HandleMsgVote(s, m) ==
    /\ m.type = "MsgVote"
    /\ m.term >= currentTerm[s]
    /\ LET
        candidateLog == [index |-> m.index, term |-> m.logTerm]
        myLog == [index |-> LastIndex(log[s]), term |-> LastTerm(log[s])]
        canVote == \/ votedFor[s] = Nil
                   \/ votedFor[s] = m.from
        grant == /\ canVote
                 /\ IsUpToDate(candidateLog, myLog)
    IN
    /\ StepDown(s, m)
    /\ IF grant
       THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
            /\ messages' = (messages \ {m}) (+) Bag({[
                type |-> "MsgVoteResp", from |-> s, to |-> m.from, term |-> currentTerm'[s],
                reject |-> FALSE
            ]})
       ELSE /\ messages' = (messages \ {m}) (+) Bag({[
                type |-> "MsgVoteResp", from |-> s, to |-> m.from, term |-> currentTerm[s],
                reject |-> TRUE
            ]})
            /\ UNCHANGED <<votedFor>>
    /\ UNCHANGED <<log, commitIndex, leader, electionTimer, votesGranted, nextIndex, matchIndex>>

HandleMsgVoteResp(s, m) ==
    /\ m.type = "MsgVoteResp"
    /\ state[s] = "Candidate"
    /\ m.term = currentTerm[s]
    /\ IF m.reject
       THEN UNCHANGED <<votesGranted, state, leader, nextIndex, matchIndex, messages>>
       ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.from}]
            /\ IF Cardinality(votesGranted'[s]) >= Quorum
               THEN /\ state' = [state EXCEPT ![s] = "Leader"]
                    /\ leader' = [leader EXCEPT ![s] = s]
                    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastIndex(log[s]) + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
                    /\ LET
                        emptyEntry == [term |-> currentTerm[s], command |-> "noop"]
                        log' == [log EXCEPT ![s] = Append(log[s], emptyEntry)]
                       IN UNCHANGED <<log>>
                    /\ messages' = messages \ {m}
               ELSE /\ UNCHANGED <<state, leader, nextIndex, matchIndex>>
                    /\ messages' = messages \ {m}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionTimer>>

HandleTermTooLow(s, m) ==
    /\ m.term < currentTerm[s]
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer,
                   votesGranted, nextIndex, matchIndex>>

HandleTermHigher(s, m) ==
    /\ m.term > currentTerm[s]
    /\ m.type \in {"MsgApp", "MsgVote"}
    /\ BecomeFollower(s, m.term)
    /\ messages' = messages

Receive(m) ==
    LET s == m.to IN
    \/ HandleTermTooLow(s, m)
    \/ CASE m.type = "MsgProp" -> HandleMsgProp(s, m)
        [] m.type = "MsgApp" -> HandleMsgApp(s, m)
        [] m.type = "MsgAppResp" -> HandleMsgAppResp(s, m)
        [] m.type = "MsgPreVote" -> HandleMsgPreVote(s, m)
        [] m.type = "MsgPreVoteResp" -> HandleMsgPreVoteResp(s, m)
        [] m.type = "MsgVote" -> HandleMsgVote(s, m)
        [] m.type = "MsgVoteResp" -> HandleMsgVoteResp(s, m)

Next ==
    \/ \E s \in Servers: Tick(s)
    \/ \E s \in Servers: Timeout(s)
    \/ \E s \in Servers: Heartbeat(s)
    \/ \E s \in Servers, p \in Servers: ReplicateLog(s, p)
    \/ \E m \in BagToSet(messages): Receive(m)
    \/ \E m \in BagToSet(messages): /\ messages' = messages \ {m}
                                    /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
