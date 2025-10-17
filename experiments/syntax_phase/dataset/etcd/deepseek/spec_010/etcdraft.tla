---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, NULL

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leaderId,
    votesReceived,
    nextIndex,
    matchIndex,
    msgs,
    electionTimeout,
    electionElapsed,
    heartbeatElapsed

vars == <<state, currentTerm, votedFor, log, commitIndex, leaderId, 
          votesReceived, nextIndex, matchIndex, msgs, electionTimeout,
          electionElapsed, heartbeatElapsed>>

\* Message types
MsgHup == 0
MsgVote == 1
MsgVoteResp == 2
MsgApp == 3
MsgAppResp == 4
MsgHeartbeat == 5
MsgHeartbeatResp == 6

\* Node states
StateFollower == 0
StateCandidate == 1
StateLeader == 2
StatePreCandidate == 3

\* Type definitions
LogEntry == [term : Nat, data : Nat]

\* Initial state
Init ==
    /\ state = [s \in Server |-> StateFollower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> NULL]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ leaderId = [s \in Server |-> NULL]
    /\ votesReceived = [s \in Server |-> {}]
    /\ nextIndex = [s \in Server |-> [s2 \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [s2 \in Server |-> 0]]
    /\ msgs = EmptyBag
    /\ electionTimeout = [s \in Server |-> 3]
    /\ electionElapsed = [s \in Server |-> 0]
    /\ heartbeatElapsed = [s \in Server |-> 0]

\* Message predicates
IsVoteMsg(m) == m.type \in {MsgVote, MsgVoteResp}
IsAppMsg(m) == m.type \in {MsgApp, MsgAppResp}
IsHeartbeatMsg(m) == m.type \in {MsgHeartbeat, MsgHeartbeatResp}

\* State transitions
CanVote(server, term) ==
    /\ currentTerm[server] <= term
    /\ \/ votedFor[server] = NULL
       \/ votedFor[server] = m.from

LogUpToDate(server, lastLogIndex, lastLogTerm) ==
    LET lastIndex == Len(log[server]) IN
    IF lastLogTerm > log[server][lastIndex].term
    THEN TRUE
    ELSE /\ lastLogTerm = log[server][lastIndex].term
         /\ lastLogIndex >= lastIndex

\* Election timeout handler
HandleElectionTimeout(server) ==
    /\ electionElapsed[server] >= electionTimeout[server]
    /\ electionElapsed' = [electionElapsed EXCEPT ![server] = 0]
    /\ IF state[server] = StateFollower \/ state[server] = StateCandidate
       THEN \/ /\ state' = [state EXCEPT ![server] = StatePreCandidate]
               /\ votesReceived' = [votesReceived EXCEPT ![server] = {}]
               /\ currentTerm' = currentTerm
          \/ /\ state' = [state EXCEPT ![server] = StateCandidate]
               /\ currentTerm' = [currentTerm EXCEPT ![server] = currentTerm[server] + 1]
               /\ votedFor' = [votedFor EXCEPT ![server] = server]
               /\ votesReceived' = [votesReceived EXCEPT ![server] = {server}]
       ELSE TRUE

\* Vote request handler
HandleVoteRequest(server, m) ==
    /\ m.type = MsgVote
    /\ IF currentTerm[server] < m.term
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ votedFor' = [votedFor EXCEPT ![server] = NULL]
       ELSE TRUE
    /\ IF \/ currentTerm[server] > m.term
          \/ votedFor[server] \notin {NULL, m.from}
          \/ ~LogUpToDate(server, m.index, m.logTerm)
       THEN \/ msgs' = msgs \cup {[type |-> MsgVoteResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], reject |-> TRUE]}
       ELSE \/ msgs' = msgs \cup {[type |-> MsgVoteResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], reject |-> FALSE]}
            /\ votedFor' = [votedReceived EXCEPT ![server] = m.from]

\* Vote response handler
HandleVoteResponse(server, m) ==
    /\ m.type = MsgVoteResp
    /\ IF m.term > currentTerm[server]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ votedFor' = [votedFor EXCEPT ![server] = NULL]
       ELSE /\ IF ~m.reject
             THEN /\ votesReceived' = [votesReceived EXCEPT ![server] = @ \cup {m.from}]
                  /\ LET votes == votesReceived[server] \cup {m.from} IN
                     IF Cardinality(votes) > Cardinality(Server) \div 2
                     THEN /\ state' = [state EXCEPT ![server] = StateLeader]
                          /\ leaderId' = [leaderId EXCEPT ![server] = server]
                     ELSE TRUE
             ELSE TRUE

\* Append entries handler
HandleAppendEntries(server, m) ==
    /\ m.type = MsgApp
    /\ IF currentTerm[server] < m.term
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ leaderId' = [leaderId EXCEPT ![server] = m.from]
       ELSE TRUE
    /\ IF \/ currentTerm[server] > m.term
          \/ m.index > Len(log[server])
          \/ m.index > 0 /\ log[server][m.index].term \= m.logTerm
       THEN \/ msgs' = msgs \cup {[type |-> MsgAppResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], index |-> m.index,
                                     reject |-> TRUE]}
       ELSE \/ \* Append new entries
            /\ log' = [log EXCEPT ![server] = @ \o m.entries]
            /\ msgs' = msgs \cup {[type |-> MsgAppResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], index |-> m.index + Len(m.entries),
                                     reject |-> FALSE]}
            /\ IF m.commit > commitIndex[server]
               THEN commitIndex' = [commitIndex EXCEPT ![server] = Min(m.commit, Len(log[server]))]
               ELSE TRUE

\* Heartbeat handler
HandleHeartbeat(server, m) ==
    /\ m.type = MsgHeartbeat
    /\ electionElapsed' = [electionElapsed EXCEPT ![server] = 0]
    /\ IF currentTerm[server] < m.term
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ leaderId' = [leaderId EXCEPT ![server] = m.from]
       ELSE TRUE
    /\ msgs' = msgs \cup {[type |-> MsgHeartbeatResp, from |-> server, to |-> m.from, term |-> currentTerm[server]]}

\* Leader append entries
LeaderAppend(server) ==
    /\ state[server] = StateLeader
    /\ \forall s \in Server:
        IF s \= server
        THEN /\ LET prevIndex == nextIndex[server][s] - 1 IN
                 prevTerm == IF prevIndex > 0 THEN log[server][prevIndex].term ELSE 0
             IN
             msgs' = msgs \cup {[type |-> MsgApp, from |-> server, to |-> s,
                                 term |-> currentTerm[server], index |-> prevIndex,
                                 logTerm |-> prevTerm, entries |-> SubSeq(log[server], nextIndex[server][s], Len(log[server]))]}
        ELSE TRUE

\* Next state relation
Next ==
    \/ \E s \in Server: HandleElectionTimeout(s)
    \/ \E m \in msgs:
        \/ \E s \in Server: HandleVoteRequest(s, m) \* Vote request
        \/ \E s \in Server: HandleVoteResponse(s, m) \* Vote response
        \/ \E s \in Server: HandleAppendEntries(s, m) \* Append entries
        \/ \E s \in Server: HandleHeartbeat(s, m) \* Heartbeat
    \/ \E s \in Server: LeaderAppend(s) \* Leader sending append entries

\* Fairness and termination
Spec == Init /\ [][Next]_vars

====