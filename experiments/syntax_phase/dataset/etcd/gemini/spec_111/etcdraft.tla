---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Server,
    Value,
    Nil,
    ElectionTimeout,
    HeartbeatTimeout

ASSUME Server \subseteq {"n1", "n2", "n3"}
ASSUME Value \subseteq {"v1", "v2"}
ASSUME ElectionTimeout \in Nat
ASSUME HeartbeatTimeout \in Nat
ASSUME HeartbeatTimeout < ElectionTimeout

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lead,
    votes,
    nextIndex,
    matchIndex,
    messages,
    electionElapsed,
    heartbeatElapsed

vars == <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
           nextIndex, matchIndex, messages, electionElapsed, heartbeatElapsed>>

Quorum == (Cardinality(Server) \div 2) + 1

MessageTypes == {"RequestPreVote", "RequestPreVoteResponse",
                 "RequestVote", "RequestVoteResponse",
                 "AppendEntries", "AppendEntriesResponse"}

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}

\* A dummy log entry at index 0.
DummyEntry == [term |-> 0, value |-> Nil]

\* Helper functions for log access.
LastLogIndex(s) == Len(log[s]) - 1
LastLogTerm(s) == IF LastLogIndex(s) = 0 THEN 0 ELSE log[s][LastLogIndex(s) + 1].term

\* Candidate's log is at least as up-to-date as receiver's log.
IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, myLastLogTerm, myLastLogIndex) ==
    \/ candidateLastLogTerm > myLastLogTerm
    \/ (candidateLastLogTerm = myLastLogTerm /\ candidateLastLogIndex >= myLastLogIndex)

Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<DummyEntry>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lead = [s \in Server |-> Nil]
    /\ votes = [s \in Server |-> {}]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ messages = EmptyBag
    /\ electionElapsed = [s \in Server |-> 0]
    /\ heartbeatElapsed = [s \in Server |-> 0]

\* State Transitions
BecomeFollower(s, term, l) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ lead' = [lead EXCEPT ![s] = l]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, votes, nextIndex, matchIndex, messages, heartbeatElapsed>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votes' = [votes EXCEPT ![s] = {}]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lead,
                   nextIndex, matchIndex, messages, heartbeatElapsed>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votes' = [votes EXCEPT ![s] = {s}]
    /\ lead' = [lead EXCEPT ![s] = Nil]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages, heartbeatElapsed>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ lead' = [lead EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votes, messages, electionElapsed>>

\* Actions initiated by servers

Tick(s) ==
    /\ IF state[s] \in {"Follower", "PreCandidate", "Candidate"}
       THEN electionElapsed' = [electionElapsed EXCEPT ![s] = electionElapsed[s] + 1]
       ELSE electionElapsed' = electionElapsed
    /\ IF state[s] = "Leader"
       THEN heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = heartbeatElapsed[s] + 1]
       ELSE heartbeatElapsed' = heartbeatElapsed
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                   nextIndex, matchIndex, messages>>

ElectionTimeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionElapsed[s] >= ElectionTimeout
    /\ BecomePreCandidate(s)
    /\ LET newTerm == currentTerm[s] + 1
           lastIdx == LastLogIndex(s)
           lastTerm == LastLogTerm(s)
       IN messages' = messages \union Bagify({[type |-> "RequestPreVote", from |-> s, to |-> p,
                                                 term |-> newTerm, lastLogIndex |-> lastIdx,
                                                 lastLogTerm |-> lastTerm] : p \in Server \ {s}})

HeartbeatTimeout(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatElapsed[s] >= HeartbeatTimeout
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ messages' = messages \union
        Bagify({ LET prevIdx == nextIndex[s][p] - 1
                     prevTerm == IF prevIdx >= 0 THEN log[s][prevIdx + 1].term ELSE 0
                 IN [type |-> "AppendEntries", from |-> s, to |-> p, term |-> currentTerm[s],
                     prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                     entries |-> << >>, leaderCommit |-> commitIndex[s]]
                 : p \in Server \ {s}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                   nextIndex, matchIndex, electionElapsed>>

ClientRequest(s, v) ==
    /\ state[s] = "Leader"
    /\ LET newEntry == [term |-> currentTerm[s], value |-> v]
           newLog == Append(log[s], newEntry)
       IN log' = [log EXCEPT ![s] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lead, votes,
                   nextIndex, matchIndex, messages, electionElapsed, heartbeatElapsed>>

AdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET
        PossibleCommits == {i \in (commitIndex[s]+1)..(LastLogIndex(s)) |
                                /\ log[s][i+1].term = currentTerm[s]
                                /\ Cardinality({p \in Server | matchIndex[s][p] >= i}) + 1 >= Quorum}
       IN IF PossibleCommits # {}
          THEN commitIndex' = [commitIndex EXCEPT ![s] = Max(PossibleCommits)]
          ELSE UNCHANGED commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lead, votes,
                   nextIndex, matchIndex, messages, electionElapsed, heartbeatElapsed>>

\* Message Handlers
HandleRequestPreVote(s, m) ==
    /\ LET grant == \/ m.term < currentTerm[s]
                    \/ NOT IsUpToDate(m.lastLogTerm, m.lastLogIndex, LastLogTerm(s), LastLogIndex(s))
       IN messages' = messages \-- Bagify({m}) \union
                      Bagify({[type |-> "RequestPreVoteResponse", from |-> s, to |-> m.from,
                               term |-> currentTerm[s], voteGranted |-> NOT grant]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                   nextIndex, matchIndex, electionElapsed, heartbeatElapsed>>

HandleRequestPreVoteResponse(s, m) ==
    /\ messages' = messages \-- Bagify({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term, Nil)
       ELSE IF state[s] = "PreCandidate" /\ m.voteGranted
            THEN LET newVotes == votes[s] \union {m.from}
                 IN IF Cardinality(newVotes) + 1 >= Quorum
                    THEN /\ BecomeCandidate(s)
                         /\ LET newTerm == currentTerm[s] + 1
                                lastIdx == LastLogIndex(s)
                                lastTerm == LastLogTerm(s)
                            IN messages' = messages \-- Bagify({m}) \union
                                           Bagify({[type |-> "RequestVote", from |-> s, to |-> p,
                                                    term |-> newTerm, lastLogIndex |-> lastIdx,
                                                    lastLogTerm |-> lastTerm] : p \in Server \ {s}})
                    ELSE votes' = [votes EXCEPT ![s] = newVotes]
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead,
                                        nextIndex, matchIndex, electionElapsed, heartbeatElapsed>>
            ELSE UNCHANGED vars

HandleRequestVote(s, m) ==
    /\ messages' = messages \-- Bagify({m})
    /\ IF m.term < currentTerm[s]
       THEN messages' = messages \-- Bagify({m}) \union
                        Bagify({[type |-> "RequestVoteResponse", from |-> s, to |-> m.from,
                                 term |-> currentTerm[s], voteGranted |-> FALSE]})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                           nextIndex, matchIndex, electionElapsed, heartbeatElapsed>>
       ELSE /\ IF m.term > currentTerm[s]
              THEN /\ state' = [state EXCEPT ![s] = "Follower"]
                   /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                   /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                   /\ lead' = [lead EXCEPT ![s] = Nil]
              ELSE UNCHANGED <<state, currentTerm, votedFor, lead>>
            /\ LET myLastLogTerm == LastLogTerm(s)
                   myLastLogIndex == LastLogIndex(s)
                   grant == (votedFor'[s] = Nil \/ votedFor'[s] = m.from) /\
                            IsUpToDate(m.lastLogTerm, m.lastLogIndex, myLastLogTerm, myLastLogIndex)
               IN /\ IF grant THEN votedFor'' = [votedFor' EXCEPT ![s] = m.from]
                     ELSE votedFor'' = votedFor'
                  /\ messages'' = (messages' \-- Bagify({m})) \union
                                 Bagify({[type |-> "RequestVoteResponse", from |-> s, to |-> m.from,
                                          term |-> currentTerm'[s], voteGranted |-> grant]})
                  /\ UNCHANGED <<log, commitIndex, votes, nextIndex, matchIndex,
                                 electionElapsed, heartbeatElapsed>>

HandleRequestVoteResponse(s, m) ==
    /\ messages' = messages \-- Bagify({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term, Nil)
       ELSE IF state[s] = "Candidate" /\ m.term = currentTerm[s]
            THEN IF m.voteGranted
                 THEN LET newVotes == votes[s] \union {m.from}
                      IN IF Cardinality(newVotes) >= Quorum
                         THEN /\ BecomeLeader(s)
                              /\ LET newEntry == [term |-> currentTerm[s], value |-> "NoOp"]
                                     newLog == Append(log[s], newEntry)
                                 IN log' = [log EXCEPT ![s] = newLog]
                         ELSE votes' = [votes EXCEPT ![s] = newVotes]
                              /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead,
                                             nextIndex, matchIndex, electionElapsed, heartbeatElapsed>>
                 ELSE UNCHANGED vars
            ELSE UNCHANGED vars

HandleAppendEntries(s, m) ==
    /\ messages' = messages \-- Bagify({m})
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = messages \-- Bagify({m}) \union
                          Bagify({[type |-> "AppendEntriesResponse", from |-> s, to |-> m.from,
                                   term |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0]})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                           nextIndex, matchIndex, electionElapsed, heartbeatElapsed>>
       ELSE /\ BecomeFollower(s, m.term, m.from)
            /\ LET prevLogIndex == m.prevLogIndex
                   prevLogTerm == m.prevLogTerm
                   logOk == /\ prevLogIndex <= LastLogIndex(s)
                            /\ (prevLogIndex = -1 \/ log[s][prevLogIndex + 1].term = prevLogTerm)
               IN IF logOk
                  THEN /\ LET newEntries == m.entries
                           conflictIndex == IF \E i \in 1..Len(newEntries) :
                                                 prevLogIndex + i > LastLogIndex(s) \/
                                                 log[s][prevLogIndex + i + 1].term # newEntries[i].term
                                            THEN Min({i \in 1..Len(newEntries) :
                                                        prevLogIndex + i > LastLogIndex(s) \/
                                                        log[s][prevLogIndex + i + 1].term # newEntries[i].term})
                                            ELSE 0
                        IN IF conflictIndex # 0
                           THEN log'' = [log' EXCEPT ![s] = SubSeq(log'[s], 1, prevLogIndex + conflictIndex) \o
                                                         SubSeq(newEntries, conflictIndex, Len(newEntries))]
                           ELSE log'' = [log' EXCEPT ![s] = log'[s] \o newEntries]
                       /\ IF m.leaderCommit > commitIndex'[s]
                          THEN commitIndex'' = [commitIndex' EXCEPT ![s] = Min({m.leaderCommit, LastLogIndex(s)})]
                          ELSE commitIndex'' = commitIndex'
                       /\ messages'' = (messages' \-- Bagify({m})) \union
                                      Bagify({[type |-> "AppendEntriesResponse", from |-> s, to |-> m.from,
                                               term |-> currentTerm'[s], success |-> TRUE,
                                               matchIndex |-> prevLogIndex + Len(m.entries)]})
                  ELSE /\ messages'' = (messages' \-- Bagify({m})) \union
                                      Bagify({[type |-> "AppendEntriesResponse", from |-> s, to |-> m.from,
                                               term |-> currentTerm'[s], success |-> FALSE, matchIndex |-> 0]})
                       /\ UNCHANGED <<log, commitIndex>>

HandleAppendEntriesResponse(s, m) ==
    /\ messages' = messages \-- Bagify({m})
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term, Nil)
       ELSE IF state[s] = "Leader" /\ m.term = currentTerm[s]
            THEN IF m.success
                 THEN /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.matchIndex]
                      /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.matchIndex + 1]
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                                     electionElapsed, heartbeatElapsed>>
                 ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = Max({1, nextIndex[s][m.from] - 1})]
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                                     matchIndex, electionElapsed, heartbeatElapsed>>
            ELSE UNCHANGED vars

\* The Next state relation
Next ==
    \/ \E s \in Server:
        \/ Tick(s)
        \/ ElectionTimeout(s)
        \/ HeartbeatTimeout(s)
        \/ (\E v \in Value: ClientRequest(s, v))
        \/ AdvanceCommitIndex(s)
    \/ \E m \in DOMAIN messages:
        \/ (messages[m] > 0) /\
           LET s == m.to IN
           \/ (m.type = "RequestPreVote" /\ HandleRequestPreVote(s, m))
           \/ (m.type = "RequestPreVoteResponse" /\ HandleRequestPreVoteResponse(s, m))
           \/ (m.type = "RequestVote" /\ HandleRequestVote(s, m))
           \/ (m.type = "RequestVoteResponse" /\ HandleRequestVoteResponse(s, m))
           \/ (m.type = "AppendEntries" /\ HandleAppendEntries(s, m))
           \/ (m.type = "AppendEntriesResponse" /\ HandleAppendEntriesResponse(s, m))
    \/ \E m \in DOMAIN messages: \* Message loss
        \/ (messages[m] > 0) /\
           messages' = messages \-- Bagify({m}) /\
           UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, votes,
                       nextIndex, matchIndex, electionElapsed, heartbeatElapsed>>

====
