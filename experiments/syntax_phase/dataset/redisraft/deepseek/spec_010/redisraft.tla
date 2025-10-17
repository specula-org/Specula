---- MODULE redisraft ----
EXTENDS Sequences, Naturals, FiniteSets
CONSTANTS Servers, ElectionTimeout, RequestTimeout, None
ASSUME None \notin Servers
VARIABLES clock, state, currentTerm, votedFor, leaderId, log, commitIndex, nextIndex, matchIndex, lastElectionReset, electionTimeoutRand, lastHeartbeatReset, msgId, messages
VStates == {"Follower", "PreCandidate", "Candidate", "Leader"}
VotedFor == Servers \cup {None}
vars == <<clock, state, currentTerm, votedFor, leaderId, log, commitIndex, nextIndex, matchIndex, lastElectionReset, electionTimeoutRand, lastHeartbeatReset, msgId, messages>>
Init == 
    /\ clock = 0
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> None]
    /\ leaderId = [s \in Servers |-> None]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ lastElectionReset = [s \in Servers |-> 0]
    /\ electionTimeoutRand = [s \in Servers |-> ElectionTimeout]
    /\ lastHeartbeatReset = [s \in Servers |-> 0]
    /\ msgId = [s \in Servers |-> 0]
    /\ messages = {}
BecomeFollower(s) == 
    /\ state[s] /= "Follower"
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![s] = None]
    /\ lastElectionReset' = [lastElectionReset EXCEPT ![s] = clock]
    /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![s] = CHOOSE r \in {n \in Nat : n >= ElectionTimeout /\ n < 2*ElectionTimeout} : TRUE]
    /\ UNCHANGED <<clock, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, lastHeartbeatReset, msgId, messages>>
BecomePreCandidate(s) == 
    /\ state[s] \neq "PreCandidate"
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votedFor' = [votedFor EXCEPT ![s] = None]
    /\ leaderId' = [leaderId EXCEPT ![s] = None]
    /\ lastElectionReset' = [lastElectionReset EXCEPT ![s] = clock]
    /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![s] = CHOOSE r \in {n \in Nat : n >= ElectionTimeout /\ n < 2*ElectionTimeout} : TRUE]
    /\ messages' = messages \cup { [type |-> "RV", term |-> currentTerm[s] + 1, candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, isPrevote |-> TRUE, source |-> s, dest |-> t] : t \in Servers \ {s} }
    /\ UNCHANGED <<clock, currentTerm, log, commitIndex, nextIndex, matchIndex, lastHeartbeatReset, msgId>>
BecomeCandidate(s) == 
    /\ state[s] \neq "Candidate"
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ leaderId' = [leaderId EXCEPT ![s] = None]
    /\ lastElectionReset' = [lastElectionReset EXCEPT ![s] = clock]
    /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![s] = CHOOSE r \in {n \in Nat : n >= ElectionTimeout /\ n < 2*ElectionTimeout} : TRUE]
    /\ messages' = messages \cup { [type |-> "RV", term |-> currentTerm[s] + 1, candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, isPrevote |-> FALSE, source |-> s, dest |-> t] : t \in Servers \ {s} }
    /\ UNCHANGED <<clock, log, commitIndex, nextIndex, matchIndex, lastHeartbeatReset, msgId>>
BecomeLeader(s) == 
    /\ state[s] = "Candidate"
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Servers |-> Len(log[s]) + 1] ]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Servers |-> 0] ]
    /\ lastHeartbeatReset' = [lastHeartbeatReset EXCEPT ![s] = clock]
    /\ msgId' = [msgId EXCEPT ![s] = msgId[s] + 1]
    /\ messages' = messages \cup { [type |-> "AE", term |-> currentTerm[s], leaderId |-> s, prevLogIndex |-> Len(log[s]), prevLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, leaderCommit |-> commitIndex[s], entries |-> <<>>, msgId |-> msgId[s] + 1, source |-> s, dest |-> t] : t \in Servers \ {s} }
    /\ UNCHANGED <<clock, currentTerm, votedFor, log, commitIndex, lastElectionReset, electionTimeoutRand>>
Tick == 
    /\ clock' = clock + 1
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, log, commitIndex, nextIndex, matchIndex, lastElectionReset, electionTimeoutRand, lastHeartbeatReset, msgId, messages>>
Next == 
    \/ \E s \in Servers : BecomeFollower(s)
    \/ \E s \in Servers : BecomePreCandidate(s)
    \/ \E s \in Servers : BecomeCandidate(s)
    \/ \E s \in Servers : BecomeLeader(s)
    \/ Tick
Spec == Init /\ [][Next]_vars
====