---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS
    Server,
    Value,
    Nil

ASSUME Server \subseteq Nat
ASSUME Nil \notin Server

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    votesGranted,
    matchIndex,
    nextIndex,
    electionTimer,
    heartbeatTimer,
    network

vars == <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
          matchIndex, nextIndex, electionTimer, heartbeatTimer, network>>

NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}
MsgTypes == {"PreVoteRequest", "PreVoteResponse", "VoteRequest", "VoteResponse",
             "AppendEntriesRequest", "AppendEntriesResponse", "ClientRequest"}

Quorum == (Cardinality(Server) \div 2) + 1
ElectionTimeout == 5
HeartbeatInterval == 1

LastIndex(lg) == Len(lg)
LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)].term

IsUpToDate(candLastTerm, candLastIndex, voterLog) ==
    LET voterLastTerm == LastTerm(voterLog)
    IN IF candLastTerm /= voterLastTerm
       THEN candLastTerm > voterLastTerm
       ELSE candLastIndex >= LastIndex(voterLog)

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ leader' = [leader EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [i \in Server |-> LastIndex(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [i \in Server |-> 0]]
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = [i \in Server |-> 0]]

Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ leader = [s \in Server |-> Nil]
    /\ votesGranted = [s \in Server |-> {}]
    /\ matchIndex = [s \in Server |-> [i \in Server |-> 0]]
    /\ nextIndex = [s \in Server |-> [i \in Server |-> 1]]
    /\ electionTimer = [s \in Server |-> ElectionTimeout]
    /\ heartbeatTimer = [s \in Server |-> [i \in Server |-> HeartbeatInterval]]
    /\ network = {}

ClientRequest(s, v) ==
    /\ s \in Server
    /\ v \in Value
    /\ network' = network \cup {[type |-> "ClientRequest", to |-> s, value |-> v]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
                   matchIndex, nextIndex, electionTimer, heartbeatTimer>>

LeaderHandleClientRequest(s) ==
    \E m \in network:
        /\ m.type = "ClientRequest"
        /\ m.to = s
        /\ state[s] = "Leader"
        /\ LET newEntry == [term |-> currentTerm[s], value |-> m.value]
           IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
        /\ network' = network \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader, votesGranted,
                       matchIndex, nextIndex, electionTimer, heartbeatTimer>>

Timeout(s) ==
    /\ electionTimer[s] = 0
    /\ IF state[s] \in {"Follower", "PreCandidate"}
       THEN /\ BecomePreCandidate(s)
            /\ LET nextTerm == currentTerm[s] + 1
                   lastLogIdx == LastIndex(log[s])
                   lastLogTerm == LastTerm(log[s])
                   newMsgs == { [ type |-> "PreVoteRequest",
                                  term |-> nextTerm,
                                  from |-> s,
                                  to |-> peer,
                                  lastLogIndex |-> lastLogIdx,
                                  lastLogTerm |-> lastLogTerm ]
                                : peer \in Server \ {s} }
            IN network' = network \cup newMsgs
            /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, matchIndex, nextIndex, heartbeatTimer>>
       ELSE /\ state[s] = "Candidate"
            /\ BecomeCandidate(s)
            /\ LET lastLogIdx == LastIndex(log[s])
                   lastLogTerm == LastTerm(log[s])
                   newMsgs == { [ type |-> "VoteRequest",
                                  term |-> currentTerm'[s],
                                  from |-> s,
                                  to |-> peer,
                                  lastLogIndex |-> lastLogIdx,
                                  lastLogTerm |-> lastLogTerm ]
                                : peer \in Server }
            IN network' = network \cup newMsgs
            /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, heartbeatTimer>>

HandlePreVoteRequest(s) ==
    \E m \in network:
        /\ m.type = "PreVoteRequest"
        /\ m.to = s
        /\ LET grant == /\ m.term > currentTerm[s]
                       /\ IsUpToDate(m.lastLogTerm, m.lastLogIndex, log[s])
           IN network' = (network \ {m}) \cup
                         {[ type |-> "PreVoteResponse",
                            term |-> m.term,
                            from |-> s,
                            to |-> m.from,
                            granted |-> grant ]}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
                       matchIndex, nextIndex, electionTimer, heartbeatTimer>>

HandlePreVoteResponse(s) ==
    \E m \in network:
        /\ m.type = "PreVoteResponse"
        /\ m.to = s
        /\ state[s] = "PreCandidate"
        /\ LET nextTerm == currentTerm[s] + 1
        IN /\ m.term = nextTerm
           /\ IF m.granted
              THEN /\ LET newVotes == votesGranted[s] \cup {m.from}
                   IN /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                      /\ IF Cardinality(newVotes) >= Quorum
                         THEN /\ BecomeCandidate(s)
                              /\ LET lastLogIdx == LastIndex(log[s])
                                     lastLogTerm == LastTerm(log[s])
                                     newMsgs == { [ type |-> "VoteRequest",
                                                    term |-> currentTerm'[s],
                                                    from |-> s,
                                                    to |-> peer,
                                                    lastLogIndex |-> lastLogIdx,
                                                    lastLogTerm |-> lastLogTerm ]
                                                  : peer \in Server }
                              IN network' = (network \ {m}) \cup newMsgs
                         ELSE /\ network' = network \ {m}
                              /\ UNCHANGED <<state, currentTerm, votedFor, leader, electionTimer>>
              ELSE /\ network' = network \ {m}
                   /\ UNCHANGED <<state, currentTerm, votedFor, leader, votesGranted, electionTimer>>
           /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, heartbeatTimer>>

HandleVoteRequest(s) ==
    \E m \in network:
        /\ m.type = "VoteRequest"
        /\ m.to = s
        /\ LET grant == \/ /\ m.term < currentTerm[s]
                          /\ FALSE
                       \/ /\ m.term > currentTerm[s]
                          /\ IsUpToDate(m.lastLogTerm, m.lastLogIndex, log[s])
                       \/ /\ m.term = currentTerm[s]
                          /\ votedFor[s] \in {Nil, m.from}
                          /\ IsUpToDate(m.lastLogTerm, m.lastLogIndex, log[s])
        IN /\ IF m.term > currentTerm[s]
              THEN /\ state' = [state EXCEPT ![s] = "Follower"]
                   /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                   /\ leader' = [leader EXCEPT ![s] = Nil]
                   /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
                   /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]
                   /\ votedFor' = [votedFor EXCEPT ![s] = IF grant THEN m.from ELSE Nil]
              ELSE /\ UNCHANGED <<state, currentTerm, leader, votesGranted, electionTimer>>
                   /\ IF grant
                      THEN votedFor' = [votedFor EXCEPT ![s] = m.from]
                      ELSE UNCHANGED votedFor
           /\ network' = (network \ {m}) \cup
                         {[ type |-> "VoteResponse",
                            term |-> IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s],
                            from |-> s,
                            to |-> m.from,
                            granted |-> grant ]}
           /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, heartbeatTimer>>

HandleVoteResponse(s) ==
    \E m \in network:
        /\ m.type = "VoteResponse"
        /\ m.to = s
        /\ state[s] = "Candidate"
        /\ IF m.term > currentTerm[s]
           THEN /\ BecomeFollower(s, m.term)
                /\ network' = network \ {m}
                /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, heartbeatTimer>>
           ELSE /\ m.term = currentTerm[s]
                /\ IF m.granted
                   THEN /\ LET newVotes == votesGranted[s] \cup {m.from}
                        IN /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                           /\ IF Cardinality(newVotes) >= Quorum
                              THEN /\ BecomeLeader(s)
                                   /\ LET newEntry == [term |-> currentTerm[s], value |-> "noop"]
                                      IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
                              ELSE UNCHANGED <<state, leader, nextIndex, matchIndex, heartbeatTimer, log>>
                   ELSE UNCHANGED <<votesGranted, state, leader, nextIndex, matchIndex, heartbeatTimer, log>>
                /\ network' = network \ {m}
                /\ UNCHANGED <<currentTerm, votedFor, commitIndex, electionTimer>>

LeaderSendAppendEntries(s, peer) ==
    /\ state[s] = "Leader"
    /\ peer \in Server \ {s}
    /\ heartbeatTimer[s][peer] = 0
    /\ LET prevLogIndex == nextIndex[s][peer] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[s][prevLogIndex].term ELSE 0
           entries == SubSeq(log[s], nextIndex[s][peer], LastIndex(log[s]))
    IN /\ network' = network \cup
                     {[ type |-> "AppendEntriesRequest",
                        term |-> currentTerm[s],
                        from |-> s,
                        to |-> peer,
                        prevLogIndex |-> prevLogIndex,
                        prevLogTerm |-> prevLogTerm,
                        entries |-> entries,
                        leaderCommit |-> commitIndex[s] ]}
       /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = [heartbeatTimer[s] EXCEPT ![peer] = HeartbeatInterval]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
                   matchIndex, nextIndex, electionTimer>>

HandleAppendEntriesRequest(s) ==
    \E m \in network:
        /\ m.type = "AppendEntriesRequest"
        /\ m.to = s
        /\ LET logOK == \/ m.prevLogIndex = 0
                        \/ /\ m.prevLogIndex <= LastIndex(log[s])
                           /\ log[s][m.prevLogIndex].term = m.prevLogTerm
        IN /\ IF m.term < currentTerm[s]
              THEN /\ network' = (network \ {m}) \cup
                                 {[ type |-> "AppendEntriesResponse",
                                    term |-> currentTerm[s],
                                    from |-> s,
                                    to |-> m.from,
                                    success |-> FALSE,
                                    matchIndex |-> 0 ]}
                   /\ UNCHANGED <<vars \ {network}>>
              ELSE /\ state' = [state EXCEPT ![s] = "Follower"]
                   /\ leader' = [leader EXCEPT ![s] = m.from]
                   /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]
                   /\ IF m.term > currentTerm[s]
                      THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                           /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                      ELSE UNCHANGED <<currentTerm, votedFor>>
                   /\ IF logOK
                      THEN /\ LET newLog == SubSeq(log[s], 1, m.prevLogIndex) \o m.entries
                           IN log' = [log EXCEPT ![s] = newLog]
                           /\ commitIndex' = [commitIndex EXCEPT ![s] = min(m.leaderCommit, LastIndex(newLog))]
                      ELSE UNCHANGED <<log, commitIndex>>
                   /\ network' = (network \ {m}) \cup
                                 {[ type |-> "AppendEntriesResponse",
                                    term |-> IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s],
                                    from |-> s,
                                    to |-> m.from,
                                    success |-> logOK,
                                    matchIndex |-> IF logOK THEN m.prevLogIndex + Len(m.entries) ELSE 0 ]}
                   /\ UNCHANGED <<votesGranted, matchIndex, nextIndex, heartbeatTimer>>

HandleAppendEntriesResponse(s) ==
    \E m \in network:
        /\ m.type = "AppendEntriesResponse"
        /\ m.to = s
        /\ state[s] = "Leader"
        /\ IF m.term > currentTerm[s]
           THEN /\ BecomeFollower(s, m.term)
                /\ network' = network \ {m}
                /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, heartbeatTimer>>
           ELSE /\ m.term = currentTerm[s]
                /\ IF m.success
                   THEN /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![m.from] = m.matchIndex]]
                        /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.matchIndex + 1]]
                   ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = max(1, nextIndex[s][m.from] - 1)]]
                        /\ UNCHANGED matchIndex
                /\ network' = network \ {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, electionTimer, heartbeatTimer>>

AdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET PossibleNs == { N \in (commitIndex[s]+1)..LastIndex(log[s]) :
                            /\ log[s][N].term = currentTerm[s]
                            /\ Cardinality({i \in Server | matchIndex[s][i] >= N}) + 1 >= Quorum }
    IN /\ PossibleNs /= {}
       /\ LET newCI == Max(PossibleNs)
          IN commitIndex' = [commitIndex EXCEPT ![s] = newCI]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, votesGranted,
                      matchIndex, nextIndex, electionTimer, heartbeatTimer, network>>

Tick ==
    /\ electionTimer' = [s \in Server |-> IF state[s] # "Leader" /\ electionTimer[s] > 0 THEN electionTimer[s] - 1 ELSE electionTimer[s]]
    /\ heartbeatTimer' = [s \in Server |-> IF state[s] = "Leader" THEN [p \in Server |-> IF heartbeatTimer[s][p] > 0 THEN heartbeatTimer[s][p] - 1 ELSE 0] ELSE heartbeatTimer[s]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
                   matchIndex, nextIndex, network>>

DropMessage ==
    \E m \in network:
        /\ network' = network \ {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted,
                       matchIndex, nextIndex, electionTimer, heartbeatTimer>>

Next ==
    \/ \E s \in Server, v \in Value: ClientRequest(s, v)
    \/ \E s \in Server: LeaderHandleClientRequest(s)
    \/ \E s \in Server: Timeout(s)
    \/ \E s \in Server: HandlePreVoteRequest(s)
    \/ \E s \in Server: HandlePreVoteResponse(s)
    \/ \E s \in Server: HandleVoteRequest(s)
    \/ \E s \in Server: HandleVoteResponse(s)
    \/ \E s \in Server, p \in Server: LeaderSendAppendEntries(s, p)
    \/ \E s \in Server: HandleAppendEntriesRequest(s)
    \/ \E s \in Server: HandleAppendEntriesResponse(s)
    \/ \E s \in Server: AdvanceCommitIndex(s)
    \/ Tick
    \/ DropMessage

Spec == Init /\ [][Next]_vars

====
