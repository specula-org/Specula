---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

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

MsgHup == 0
MsgVote == 1
MsgVoteResp == 2
MsgApp == 3
MsgAppResp == 4
MsgHeartbeat == 5
MsgHeartbeatResp == 6

StateFollower == 0
StateCandidate == 1
StateLeader == 2
StatePreCandidate == 3

LogEntry == [term : Nat, data : Nat]

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
    /\ msgs = {}
    /\ electionTimeout = [s \in Server |-> 3]
    /\ electionElapsed = [s \in Server |-> 0]
    /\ heartbeatElapsed = [s \in Server |-> 0]

IsVoteMsg(m) == m.type \in {MsgVote, MsgVoteResp}
IsAppMsg(m) == m.type \in {MsgApp, MsgAppResp}
IsHeartbeatMsg(m) == m.type \in {MsgHeartbeat, MsgHeartbeatResp}

CanVote(server, term) ==
    /\ currentTerm[server] <= term
    /\ \/ votedFor[server] = NULL
       \/ votedFor[server] = term

LogUpToDate(server, lastLogIndex, lastLogTerm) ==
    LET lastIndex == Len(log[server]) IN
    IF lastIndex = 0 THEN TRUE
    ELSE IF lastLogTerm > log[server][lastIndex].term THEN TRUE
    ELSE /\ lastLogTerm = log[server][lastIndex].term
         /\ lastLogIndex >= lastIndex

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
       THEN /\ msgs' = msgs \cup {[type |-> MsgVoteResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], reject |-> TRUE]}
       ELSE /\ msgs' = msgs \cup {[type |-> MsgVoteResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], reject |-> FALSE]}
            /\ votedFor' = [votedFor EXCEPT ![server] = m.from]

HandleVoteResponse(server, m) ==
    /\ m.type = MsgVoteResp
    /\ IF m.term > currentTerm[server]
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ votedFor' = [votedFor EXCEPT ![server] = NULL]
       ELSE /\ IF ~m.reject
             THEN /\ votesReceived' = [votesReceived EXCEPT ![server] = @ \cup {m.from}]
                  /\ LET votes == votesReceived'[server] IN
                     IF Cardinality(votes) > Cardinality(Server) \div 2
                     THEN /\ state' = [state EXCEPT ![server] = StateLeader]
                          /\ leaderId' = [leaderId EXCEPT ![server] = server]
                     ELSE TRUE
             ELSE TRUE

HandleAppendEntries(server, m) ==
    /\ m.type = MsgApp
    /\ IF currentTerm[server] < m.term
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ leaderId' = [leaderId EXCEPT ![server] = m.from]
       ELSE TRUE
    /\ IF \/ currentTerm[server] > m.term
          \/ m.index > Len(log[server])
          \/ m.index > 0 /\ log[server][m.index].term # m.logTerm
       THEN /\ msgs' = msgs \cup {[type |-> MsgAppResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], index |-> m.index,
                                     reject |-> TRUE]}
       ELSE /\ log' = [log EXCEPT ![server] = @ \o m.entries]
            /\ msgs' = msgs \cup {[type |-> MsgAppResp, from |-> server, to |-> m.from,
                                     term |-> currentTerm[server], index |-> m.index + Len(m.entries),
                                     reject |-> FALSE]}
            /\ IF m.commit > commitIndex[server]
               THEN commitIndex' = [commitIndex EXCEPT ![server] = Min(m.commit, Len(log[server]))]
               ELSE TRUE

HandleHeartbeat(server, m) ==
    /\ m.type = MsgHeartbeat
    /\ electionElapsed' = [electionElapsed EXCEPT ![server] = 0]
    /\ IF currentTerm[server] < m.term
       THEN /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
            /\ state' = [state EXCEPT ![server] = StateFollower]
            /\ leaderId' = [leaderId EXCEPT ![server] = m.from]
       ELSE TRUE
    /\ msgs' = msgs \cup {[type |-> MsgHeartbeatResp, from |-> server, to |-> m.from, term |-> currentTerm[server]]}

LeaderAppend(server) ==
    /\ state[server] = StateLeader
    /\ \forall s \in Server \ {server}:
           LET prevIndex == nextIndex[server][s] - 1 IN
           LET prevTerm == IF prevIndex > 0 THEN log[server][prevIndex].term ELSE 0 IN
           msgs' = msgs \cup {[type |-> MsgApp, from |-> server, to |-> s,
                                 term |-> currentTerm[server], index |-> prevIndex,
                                 logTerm |-> prevTerm, entries |-> SubSeq(log[server], nextIndex[server][s], Len(log[server]))]}

Next ==
    \/ \E s \in Server: HandleElectionTimeout(s)
    \/ \E m \in msgs:
        \/ \E s \in Server: HandleVoteRequest(s, m)
        \/ \E s \in Server: HandleVoteResponse(s, m)
        \/ \E s \in Server: HandleAppendEntries(s, m)
        \/ \E s \in Server: HandleHeartbeat(s, m)
    \/ \E s \in Server: LeaderAppend(s)

Spec == Init /\ [][Next]_vars

====