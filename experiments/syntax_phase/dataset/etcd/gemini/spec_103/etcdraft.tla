---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Server,
    Value,
    None,
    ElectionTimeout,
    HeartbeatTimeout

ASSUME Server \subseteq Nat
ASSUME Value \subseteq Nat
ASSUME None = 0
ASSUME ElectionTimeout > HeartbeatTimeout
ASSUME HeartbeatTimeout > 0

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    electionTimer,
    heartbeatTimer,
    messages,
    votesGranted,
    matchIndex,
    nextIndex

vars == <<state, currentTerm, votedFor, log, commitIndex, leader,
          electionTimer, heartbeatTimer, messages, votesGranted,
          matchIndex, nextIndex>>

Quorum == (Cardinality(Server) \div 2) + 1

LastLogIndex(lg) == Len(lg)
LastLogTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)].term

IsUpToDate(myLog, candLastLogTerm, candLastLogIndex) ==
    LET myLastLogTerm == LastLogTerm(myLog)
    IN (candLastLogTerm > myLastLogTerm) \/
       ((candLastLogTerm = myLastLogTerm) /\ (candLastLogIndex >= LastLogIndex(myLog)))

MsgType == {"MsgHup", "MsgProp", "MsgApp", "MsgAppResp", "MsgPreVote", "MsgPreVoteResp", "MsgVote", "MsgVoteResp"}

Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> None]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ leader = [s \in Server |-> None]
    /\ electionTimer = [s \in Server |-> 0]
    /\ heartbeatTimer = [s \in Server |-> 0]
    /\ messages = {}
    /\ votesGranted = [s \in Server |-> {}]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]

StepDown(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = None]
    /\ leader' = [leader EXCEPT ![s] = None]

HandleTerm(m) ==
    \E s \in Server:
        /\ m.to = s
        /\ m.term > currentTerm[s]
        /\ StepDown(s, m.term)
        /\ UNCHANGED <<log, commitIndex, electionTimer, heartbeatTimer, messages,
                       votesGranted, matchIndex, nextIndex>>

ClientRequest(s, v) ==
    /\ state[s] = "Leader"
    /\ LET newEntry == [term |-> currentTerm[s], value |-> v, index |-> LastLogIndex(log[s]) + 1]
    IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader,
                   electionTimer, heartbeatTimer, messages, votesGranted,
                   matchIndex, nextIndex>>

Timeout(s) ==
    /\ state[s] \in {"Follower", "Candidate", "PreCandidate"}
    /\ electionTimer[s] < ElectionTimeout
    /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   heartbeatTimer, messages, votesGranted, matchIndex, nextIndex>>

Heartbeat(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatTimer[s] < HeartbeatTimeout
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = heartbeatTimer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionTimer, messages, votesGranted, matchIndex, nextIndex>>

BecomePreCandidate(s) ==
    /\ state[s] = "Follower"
    /\ electionTimer[s] >= ElectionTimeout
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        {[ type |-> "MsgPreVote", from |-> s, to |-> p, term |-> currentTerm[s] + 1,
           lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s]) ]
           : p \in Server \ {s}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader, heartbeatTimer,
                   matchIndex, nextIndex>>

BecomeCandidate(s) ==
    /\ state[s] = "PreCandidate"
    /\ Cardinality(votesGranted[s]) >= Quorum
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        {[ type |-> "MsgVote", from |-> s, to |-> p, term |-> currentTerm'[s],
           lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s]) ]
           : p \in Server \ {s}}
    /\ UNCHANGED <<log, commitIndex, leader, heartbeatTimer, matchIndex, nextIndex>>

BecomeLeader(s) ==
    /\ state[s] = "Candidate"
    /\ Cardinality(votesGranted[s]) >= Quorum
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ leader' = [leader EXCEPT ![s] = s]
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0] WITH [s] = LastLogIndex(log[s])]
    /\ LET newEntry == [term |-> currentTerm[s], value |-> "NoOp", index |-> LastLogIndex(log[s]) + 1]
    IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
    /\ messages' = messages \cup
        {[ type |-> "MsgApp", from |-> s, to |-> p, term |-> currentTerm[s],
           prevLogIndex |-> LastLogIndex(log[s]), prevLogTerm |-> LastLogTerm(log[s]),
           entries |-> <<newEntry>>, leaderCommit |-> commitIndex[s] ]
           : p \in Server \ {s}}
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, electionTimer, votesGranted>>

LeaderSendHeartbeats(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatTimer[s] >= HeartbeatTimeout
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
    /\ messages' = messages \cup
        {[ type |-> "MsgApp", from |-> s, to |-> p, term |-> currentTerm[s],
           prevLogIndex |-> LastLogIndex(log[s]), prevLogTerm |-> LastLogTerm(log[s]),
           entries |-> << >>, leaderCommit |-> commitIndex[s] ]
           : p \in Server \ {s}}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionTimer, votesGranted, matchIndex, nextIndex>>

HandleRequestVote(m) ==
    /\ m.type \in {"MsgPreVote", "MsgVote"}
    /\ LET s == m.to
    IN \/ /\ m.term < currentTerm[s]
          /\ messages' = messages \cup {[ type |-> m.type ++ "Resp", from |-> s, to |-> m.from,
                                          term |-> currentTerm[s], granted |-> FALSE ]}
       \/ /\ m.term >= currentTerm[s]
          /\ LET grant == \/ m.type = "MsgPreVote"
                         \/ (votedFor[s] = None \/ votedFor[s] = m.from)
          IN /\ grant
             /\ IsUpToDate(log[s], m.lastLogTerm, m.lastLogIndex)
             /\ messages' = messages \cup {[ type |-> m.type ++ "Resp", from |-> s, to |-> m.from,
                                             term |-> m.term, granted |-> TRUE ]}
             /\ IF m.type = "MsgVote"
                THEN votedFor' = [votedFor EXCEPT ![s] = m.from]
                ELSE UNCHANGED votedFor
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, leader, electionTimer,
                   heartbeatTimer, votesGranted, matchIndex, nextIndex>>

HandleRequestVoteResponse(m) ==
    /\ m.type \in {"MsgPreVoteResp", "MsgVoteResp"}
    /\ LET s == m.to
    IN /\ \/ /\ m.type = "MsgPreVoteResp" /\ state[s] = "PreCandidate"
          \/ /\ m.type = "MsgVoteResp" /\ state[s] = "Candidate"
       /\ m.term = (IF state[s] = "PreCandidate" THEN currentTerm[s] + 1 ELSE currentTerm[s])
       /\ IF m.granted
          THEN votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.from}]
          ELSE UNCHANGED votesGranted
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionTimer, heartbeatTimer, messages, matchIndex, nextIndex>>

HandleAppendEntries(m) ==
    /\ m.type = "MsgApp"
    /\ LET s == m.to
    IN \/ /\ m.term < currentTerm[s]
          /\ messages' = messages \cup {[ type |-> "MsgAppResp", from |-> s, to |-> m.from,
                                          term |-> currentTerm[s], success |-> FALSE,
                                          matchIndex |-> 0 ]}
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                         electionTimer, heartbeatTimer, votesGranted, matchIndex, nextIndex>>
       \/ /\ m.term >= currentTerm[s]
          /\ state' = [state EXCEPT ![s] = "Follower"]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
          /\ leader' = [leader EXCEPT ![s] = m.from]
          /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
          /\ LET logOK == /\ m.prevLogIndex <= LastLogIndex(log[s])
                         /\ (m.prevLogIndex = 0 \/ log[s][m.prevLogIndex].term = m.prevLogTerm)
          IN \/ /\ logOK
                /\ LET newLog == SubSeq(log[s], 1, m.prevLogIndex) \o m.entries
                IN /\ log' = [log EXCEPT ![s] = newLog]
                   /\ commitIndex' = [commitIndex EXCEPT ![s] = min(m.leaderCommit, LastLogIndex(newLog))]
                   /\ messages' = messages \cup {[ type |-> "MsgAppResp", from |-> s, to |-> m.from,
                                                   term |-> currentTerm'[s], success |-> TRUE,
                                                   matchIndex |-> LastLogIndex(newLog) ]}
             \/ /\ \lnot logOK
                /\ messages' = messages \cup {[ type |-> "MsgAppResp", from |-> s, to |-> m.from,
                                                term |-> currentTerm'[s], success |-> FALSE,
                                                matchIndex |-> 0 ]}
                /\ UNCHANGED <<log, commitIndex>>
          /\ UNCHANGED <<votedFor, heartbeatTimer, votesGranted, matchIndex, nextIndex>>

HandleAppendEntriesResponse(m) ==
    /\ m.type = "MsgAppResp"
    /\ LET s == m.to
    IN /\ state[s] = "Leader"
       /\ m.term = currentTerm[s]
       /\ \/ /\ m.success
             /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.matchIndex + 1]
             /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.matchIndex]
          \/ /\ \lnot m.success
             /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = max(1, nextIndex[s][m.from] - 1)]
             /\ UNCHANGED matchIndex
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                      electionTimer, heartbeatTimer, messages, votesGranted>>

LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET
        \* The set of indices that are replicated on a quorum of servers.
        matchSet(idx) == {p \in Server |-> matchIndex[s][p] >= idx}
        \* The new commit index is the largest index replicated on a quorum
        \* for which the leader has an entry in its current term.
        newCommitIndex ==
            CHOOSE idx \in commitIndex[s]..LastLogIndex(log[s]):
                /\ Cardinality(matchSet(idx)) >= Quorum
                /\ log[s][idx].term = currentTerm[s]
                /\ \A j \in idx+1..LastLogIndex(log[s]):
                       \/ Cardinality(matchSet(j)) < Quorum
                       \/ log[s][j].term /= currentTerm[s]
    IN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, electionTimer,
                   heartbeatTimer, messages, votesGranted, matchIndex, nextIndex>>

LeaderReplicateLog(s) ==
    /\ state[s] = "Leader"
    /\ \E p \in Server \ {s}:
        LastLogIndex(log[s]) >= nextIndex[s][p]
    /\ LET p == CHOOSE p \in Server \ {s}: LastLogIndex(log[s]) >= nextIndex[s][p]
    IN LET prevIdx == nextIndex[s][p] - 1
          prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
          entriesToSend == SubSeq(log[s], nextIndex[s][p], LastLogIndex(log[s]))
       IN messages' = messages \cup
           {[ type |-> "MsgApp", from |-> s, to |-> p, term |-> currentTerm[s],
              prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
              entries |-> entriesToSend, leaderCommit |-> commitIndex[s] ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   electionTimer, heartbeatTimer, votesGranted, matchIndex, nextIndex>>

ReceiveMessage(m) ==
    \/ HandleRequestVote(m)
    \/ HandleRequestVoteResponse(m)
    \/ HandleAppendEntries(m)
    \/ HandleAppendEntriesResponse(m)

Next ==
    \/ ClientRequest(CHOOSE s \in Server: TRUE, CHOOSE v \in Value: TRUE)
    \/ \E s \in Server: Timeout(s)
    \/ \E s \in Server: Heartbeat(s)
    \/ \E s \in Server: BecomePreCandidate(s)
    \/ \E s \in Server: BecomeCandidate(s)
    \/ \E s \in Server: BecomeLeader(s)
    \/ \E s \in Server: LeaderSendHeartbeats(s)
    \/ \E s \in Server: LeaderAdvanceCommitIndex(s)
    \/ \E s \in Server: LeaderReplicateLog(s)
    \/ \E m \in messages:
        \/ HandleTerm(m)
        \/ /\ m.term <= currentTerm[m.to]
           /\ ReceiveMessage(m)
           /\ messages' = messages \ {m}

====