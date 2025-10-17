---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Node, ElectionTimeoutValue, HeartbeatTimeoutValue, PreVoteEnabled

VARIABLES 
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    votesReceived,
    electionElapsed,
    heartbeatElapsed,
    msgs,
    matchIndex

vars == <<state, currentTerm, votedFor, log, commitIndex, leader, votesReceived, electionElapsed, heartbeatElapsed, msgs, matchIndex>>

NodeSet == Node

None == CHOOSE n : n \notin NodeSet

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

\* Configuration
PreVote == PreVoteEnabled

\* Helper functions
IsLeader(n) == state[n] = StateLeader
IsCandidate(n) == state[n] = StateCandidate
IsPreCandidate(n) == state[n] = StatePreCandidate
IsFollower(n) == state[n] = StateFollower

Majority == (Cardinality(NodeSet) \div 2) + 1

LastLogTerm(n) == 
    IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0

LastLogIndex(n) == Len(log[n])

LogTerm(n, i) ==
    IF i > 0 /\ i <= Len(log[n]) THEN log[n][i].term ELSE 0

MatchesLog(n, prevLogIndex, prevLogTerm) ==
    prevLogIndex = 0 \/ (prevLogIndex <= LastLogIndex(n) /\ LogTerm(n, prevLogIndex) = prevLogTerm)

GrantVote(n, candidate, candidateTerm, candidateLastLogTerm, candidateLastLogIndex) ==
    /\ votedFor[n] \in {None, candidate}
    /\ candidateLastLogTerm > LastLogTerm(n) \/ 
       (candidateLastLogTerm = LastLogTerm(n) /\ candidateLastLogIndex >= LastLogIndex(n))

ResetElectionTimeout(n) ==
    electionElapsed' = [electionElapsed EXCEPT ![n] = 0]

ResetHeartbeatTimeout(n) ==
    heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]

Max(a, b) == IF a > b THEN a ELSE b

AdvanceCommitIndex(n) ==
    LET matches == {m \in NodeSet : m /= n /\ matchIndex[m] >= commitIndex[n]}
    IN IF Cardinality(matches) + 1 >= Majority THEN
           commitIndex' = [commitIndex EXCEPT ![n] = commitIndex[n] + 1]
       ELSE UNCHANGED commitIndex

Init ==
    /\ state = [n \in NodeSet |-> StateFollower]
    /\ currentTerm = [n \in NodeSet |-> 0]
    /\ votedFor = [n \in NodeSet |-> None]
    /\ log = [n \in NodeSet |-> <<>>]
    /\ commitIndex = [n \in NodeSet |-> 0]
    /\ leader = [n \in NodeSet |-> None]
    /\ votesReceived = [n \in NodeSet |-> {}]
    /\ electionElapsed = [n \in NodeSet |-> 0]
    /\ heartbeatElapsed = [n \in NodeSet |-> 0]
    /\ msgs = {}
    /\ matchIndex = [n \in NodeSet |-> 0]

TypeInvariant ==
    /\ state \in [NodeSet -> {StateFollower, StateCandidate, StateLeader, StatePreCandidate}]
    /\ currentTerm \in [NodeSet -> Nat]
    /\ votedFor \in [NodeSet -> NodeSet \cup {None}]
    /\ commitIndex \in [NodeSet -> Nat]
    /\ leader \in [NodeSet -> NodeSet \cup {None}]
    /\ votesReceived \in [NodeSet -> SUBSET NodeSet]
    /\ electionElapsed \in [NodeSet -> Nat]
    /\ heartbeatElapsed \in [NodeSet -> Nat]
    /\ msgs \subseteq [type : {MsgHup, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp},
                       from : NodeSet,
                       to : NodeSet,
                       term : Nat,
                       logTerm : Nat,
                       index : Nat,
                       entries : Seq([term : Nat, data : {}]),
                       commit : Nat,
                       reject : BOOLEAN]
    /\ matchIndex \in [NodeSet -> Nat]

HandleMsgHup(m) ==
    /\ m.type = MsgHup
    /\ \/ IsFollower(m.to)
       \/ IsCandidate(m.to)
       \/ IsPreCandidate(m.to)
    /\ electionElapsed' = [electionElapsed EXCEPT ![m.to] = 0]
    /\ \/ PreVote /\ state' = [state EXCEPT ![m.to] = StatePreCandidate]
       \/ ~PreVote /\ state' = [state EXCEPT ![m.to] = StateCandidate]
    /\ currentTerm' = IF ~PreVote THEN [currentTerm EXCEPT ![m.to] = currentTerm[m.to] + 1] ELSE currentTerm
    /\ votedFor' = IF ~PreVote THEN [votedFor EXCEPT ![m.to] = m.to] ELSE votedFor
    /\ votesReceived' = [votesReceived EXCEPT ![m.to] = IF ~PreVote THEN {m.to} ELSE {}]
    /\ msgs' = (msgs \ {m}) \cup [type : MsgVote, from : m.to, to : {}, term : currentTerm[m.to] + IF PreVote THEN 0 ELSE 1, 
                                 logTerm : LastLogTerm(m.to), index : LastLogIndex(m.to), entries : <<>>, commit : 0, reject : FALSE]
    /\ UNCHANGED <<log, commitIndex, leader, heartbeatElapsed, matchIndex>>

HandleMsgVote(m) ==
    /\ m.type = MsgVote
    /\ \/ m.term > currentTerm[m.to]
       \/ m.term = currentTerm[m.to] /\ GrantVote(m.to, m.from, m.term, m.logTerm, m.index)
    /\ \/ m.term > currentTerm[m.to]
          /\ state' = [state EXCEPT ![m.to] = StateFollower]
          /\ currentTerm' = [currentTerm EXCEPT ![m.to] = m.term]
          /\ votedFor' = [votedFor EXCEPT ![m.to] = IF GrantVote(m.to, m.from, m.term, m.logTerm, m.index) THEN m.from ELSE None]
          /\ leader' = [leader EXCEPT ![m.to] = None]
       \/ m.term = currentTerm[m.to] 
          /\ votedFor' = [votedFor EXCEPT ![m.to] = IF GrantVote(m.to, m.from, m.term, m.logTerm, m.index) THEN m.from ELSE votedFor[m.to]]
    /\ msgs' = (msgs \ {m}) \cup [type : MsgVoteResp, from : m.to, to : m.from, term : currentTerm[m.to], 
                                 logTerm : 0, index : 0, entries : <<>>, commit : 0, reject : ~GrantVote(m.to, m.from, m.term, m.logTerm, m.index)]
    /\ ResetElectionTimeout(m.to)
    /\ UNCHANGED <<log, commitIndex, votesReceived, heartbeatElapsed, matchIndex>>

HandleMsgVoteResp(m) ==
    /\ m.type = MsgVoteResp
    /\ \/ IsCandidate(m.to) /\ m.term = currentTerm[m.to]
       \/ IsPreCandidate(m.to) /\ m.term = currentTerm[m.to] + 1
    /\ ~m.reject
    /\ votesReceived' = [votesReceived EXCEPT ![m.to] = @ \cup {m.from}]
    /\ \/ Cardinality(votesReceived'[m.to]) >= Majority /\ IsCandidate(m.to)
          /\ state' = [state EXCEPT ![m.to] = StateLeader]
          /\ leader' = [leader EXCEPT ![m.to] = m.to]
          /\ log' = [log EXCEPT ![m.to] = @ \o [term : currentTerm[m.to], data : {}]]
          /\ matchIndex' = [matchIndex EXCEPT ![m.to] = LastLogIndex(m.to)]
       \/ Cardinality(votesReceived'[m.to]) >= Majority /\ IsPreCandidate(m.to)
          /\ state' = [state EXCEPT ![m.to] = StateCandidate]
          /\ currentTerm' = [currentTerm EXCEPT ![m.to] = currentTerm[m.to] + 1]
          /\ votedFor' = [votedFor EXCEPT ![m.to] = m.to]
          /\ votesReceived' = [votesReceived EXCEPT ![m.to] = {m.to}]
          /\ msgs' = (msgs \ {m}) \cup [type : MsgVote, from : m.to, to : {}, term : currentTerm[m.to] + 1, 
                                       logTerm : LastLogTerm(m.to), index : LastLogIndex(m.to), entries : <<>>, commit : 0, reject : FALSE]
    /\ UNCHANGED <<commitIndex, heartbeatElapsed, electionElapsed>>

HandleMsgApp(m) ==
    /\ m.type = MsgApp
    /\ \/ m.term > currentTerm[m.to]
       \/ m.term = currentTerm[m.to] /\ (IsFollower(m.to) \/ IsCandidate(m.to) \/ IsPreCandidate(m.to))
    /\ \/ m.term > currentTerm[m.to]
          /\ state' = [state EXCEPT ![m.to] = StateFollower]
          /\ currentTerm' = [currentTerm EXCEPT ![m.to] = m.term]
          /\ votedFor' = [votedFor EXCEPT ![m.to] = None]
          /\ leader' = [leader EXCEPT ![m.to] = m.from]
       \/ UNCHANGED <<state, currentTerm, votedFor, leader>>
    /\ MatchesLog(m.to, m.index, m.logTerm)
    /\ log' = [log EXCEPT ![m.to] = IF m.index > 0 THEN SubSeq(log[m.to], 1, m.index) \o m.entries ELSE m.entries]
    /\ commitIndex' = [commitIndex EXCEPT ![m.to] = Max(commitIndex[m.to], Min(m.commit, LastLogIndex(m.to)))]
    /\ msgs' = (msgs \ {m}) \cup [type : MsgAppResp, from : m.to, to : m.from, term : currentTerm[m.to], 
                                 logTerm : 0, index : LastLogIndex(m.to), entries : <<>>, commit : 0, reject : FALSE]
    /\ ResetElectionTimeout(m.to)
    /\ UNCHANGED <<votesReceived, heartbeatElapsed, electionElapsed, matchIndex>>

HandleMsgAppResp(m) ==
    /\ m.type = MsgAppResp
    /\ IsLeader(m.to)
    /\ m.term = currentTerm[m.to]
    /\ ~m.reject
    /\ matchIndex' = [matchIndex EXCEPT ![m.from] = m.index]
    /\ AdvanceCommitIndex(m.to)
    /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, votesReceived, electionElapsed, heartbeatElapsed>>

HandleMsgHeartbeat(m) ==
    /\ m.type = MsgHeartbeat
    /\ \/ m.term > currentTerm[m.to]
       \/ m.term = currentTerm[m.to] /\ (IsFollower(m.to) \/ IsCandidate(m.to) \/ IsPreCandidate(m.to))
    /\ \/ m.term > currentTerm[m.to]
          /\ state' = [state EXCEPT ![m.to] = StateFollower]
          /\ currentTerm' = [currentTerm EXCEPT ![m.to] = m.term]
          /\ votedFor' = [votedFor EXCEPT ![m.to] = None]
          /\ leader' = [leader EXCEPT ![m.to] = m.from]
       \/ UNCHANGED <<state, currentTerm, votedFor, leader>>
    /\ commitIndex' = [commitIndex EXCEPT ![m.to] = Max(commitIndex[m.to], m.commit)]
    /\ msgs' = (msgs \ {m}) \cup [type : MsgHeartbeatResp, from : m.to, to : m.from, term : currentTerm[m.to], 
                                 logTerm : 0, index : 0, entries : <<>>, commit : 0, reject : FALSE]
    /\ ResetElectionTimeout(m.to)
    /\ UNCHANGED <<log, votesReceived, heartbeatElapsed, matchIndex>>

HandleMsgHeartbeatResp(m) ==
    /\ m.type = MsgHeartbeatResp
    /\ IsLeader(m.to)
    /\ m.term = currentTerm[m.to]
    /\ UNCHANGED vars

ReceiveMsg(m) ==
    \/ HandleMsgHup(m)
    \/ HandleMsgVote(m)
    \/ HandleMsgVoteResp(m)
    \/ HandleMsgApp(m)
    \/ HandleMsgAppResp(m)
    \/ HandleMsgHeartbeat(m)
    \/ HandleMsgHeartbeatResp(m)

ElectionTimeoutAction(n) ==
    /\ electionElapsed[n] >= ElectionTimeoutValue
    /\ \/ IsFollower(n)
       \/ IsCandidate(n)
       \/ IsPreCandidate(n)
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ \/ PreVote /\ state' = [state EXCEPT ![n] = StatePreCandidate]
       \/ ~PreVote /\ state' = [state EXCEPT ![n] = StateCandidate]
    /\ currentTerm' = IF ~PreVote THEN [currentTerm EXCEPT ![n] = currentTerm[n] + 1] ELSE currentTerm
    /\ votedFor' = IF ~PreVote THEN [votedFor EXCEPT ![n] = n] ELSE votedFor
    /\ votesReceived' = [votesReceived EXCEPT ![n] = IF ~PreVote THEN {n} ELSE {}]
    /\ msgs' = msgs \cup [type : MsgVote, from : n, to : {}, term : currentTerm[n] + IF PreVote THEN 0 ELSE 1, 
                          logTerm : LastLogTerm(n), index : LastLogIndex(n), entries : <<>>, commit : 0, reject : FALSE]
    /\ UNCHANGED <<log, commitIndex, leader, heartbeatElapsed, matchIndex>>

HeartbeatTimeoutAction(n) ==
    /\ IsLeader(n)
    /\ heartbeatElapsed[n] >= HeartbeatTimeoutValue
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
    /\ msgs' = msgs \cup [type : MsgHeartbeat, from : n, to : {}, term : currentTerm[n], 
                          logTerm : 0, index : 0, entries : <<>>, commit : commitIndex[n], reject : FALSE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesReceived, electionElapsed, matchIndex>>

ClientRequest(n) ==
    /\ IsLeader(n)
    /\ log' = [log EXCEPT ![n] = @ \o [term : currentTerm[n], data : {}]]
    /\ msgs' = msgs \cup [type : MsgApp, from : n, to : {}, term : currentTerm[n], 
                         logTerm : LastLogTerm(n), index : LastLogIndex(n) - 1, 
                         entries : <<[term : currentTerm[n], data : {}]>>, commit : commitIndex[n], reject : FALSE]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader, votesReceived, electionElapsed, heartbeatElapsed, matchIndex>>

Next ==
    \/ \E n \in NodeSet : ElectionTimeoutAction(n)
    \/ \E n \in NodeSet : HeartbeatTimeoutAction(n)
    \/ \E m \in msgs : ReceiveMsg(m)
    \/ \E n \in NodeSet : ClientRequest(n)

====