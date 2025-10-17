---- MODULE raftkvs ----
EXTENDS Naturals, Sequences, FiniteSets, Bags, Integers
CONSTANTS NumServers, NumClients, AllStrings, LeaderTimeoutReset, ExploreFail, Debug, MaxNodeFail
ASSUME NumServers \in Nat \ {0}
ASSUME NumClients \in Nat
ASSUME LeaderTimeoutReset \in Nat
ASSUME ExploreFail \in BOOLEAN
ASSUME Debug \in BOOLEAN
ASSUME MaxNodeFail \in Nat
Node == 1..NumServers
Client == 1..NumClients
Actor == Node \cup Client
VARIABLES state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, leader, net
vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, leader, net>>
Init == 
    state = [i \in Node |-> "follower"] /\
    currentTerm = [i \in Node |-> 0] /\
    votedFor = [i \in Node |-> 0] /\
    log = [i \in Node |-> <<>>] /\
    commitIndex = [i \in Node |-> 0] /\
    nextIndex = [i \in Node |-> [j \in Node |-> 1]] /\
    matchIndex = [i \in Node |-> [j \in Node |-> 0]] /\
    votesGranted = [i \in Node |-> {}] /\
    leader = [i \in Node |-> 0] /\
    net = EmptyBag
LastTerm(seq) == IF Len(seq) > 0 THEN seq[Len(seq)].term ELSE 0
LastIndex(seq) == Len(seq)
IsQuorum(S) == Cardinality(S) > NumServers \div 2
Timeout(i) == 
    /\ state[i] \in {"follower", "candidate"}
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ LET Messages == {[type |-> "rvq", term |-> currentTerm[i] + 1, lastLogIndex |-> LastIndex(log[i]), lastLogTerm |-> LastTerm(log[i]), source |-> i, dest |-> j] : j \in Node \ {i}}
       IN net' = net \oplus [msg \in Messages |-> 1]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leader>>
RequestVoteRequest(m) == 
    /\ m \in BagToSet(net)
    /\ m.type = "rvq"
    /\ LET i == m.dest IN
       IF m.term > currentTerm[i] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
           /\ state' = [state EXCEPT ![i] = "follower"]
           /\ votedFor' = [votedFor EXCEPT ![i] = 0]
           /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
           /\ leader' = [leader EXCEPT ![i] = 0]
       ELSE
           /\ currentTerm' = currentTerm
           /\ state' = state
           /\ votedFor' = votedFor
           /\ votesGranted' = votesGranted
           /\ leader' = leader
    /\ LET i == m.dest IN
       LET grant == (m.term = currentTerm'[i]) /\ (votedFor'[i] = 0 \/ votedFor'[i] = m.source) /\ (m.lastLogTerm > LastTerm(log[i]) \/ (m.lastLogTerm = LastTerm(log[i]) /\ m.lastLogIndex >= LastIndex(log[i]))) IN
       IF grant THEN
           /\ votedFor' = [votedFor' EXCEPT ![i] = m.source]
       ELSE
           /\ votedFor' = votedFor'
    /\ LET i == m.dest IN
       net' = (net \ominus [m |-> 1]) \oplus [type |-> "rvp", term |-> currentTerm'[i], voteGranted |-> grant, source |-> i, dest |-> m.source |-> 1]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
RequestVoteResponse(m) == 
    /\ m \in BagToSet(net)
    /\ m.type = "rvp"
    /\ LET i == m.dest IN
       IF m.term > currentTerm[i] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
           /\ state' = [state EXCEPT ![i] = "follower"]
           /\ votedFor' = [votedFor EXCEPT ![i] = 0]
           /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
           /\ leader' = [leader EXCEPT ![i] = 0]
       ELSE
           /\ currentTerm' = currentTerm
           /\ state' = state
           /\ votedFor' = votedFor
           /\ votesGranted' = votesGranted
           /\ leader' = leader
    /\ LET i == m.dest IN
       IF m.term = currentTerm'[i] /\ state'[i] = "candidate" /\ m.voteGranted THEN
           /\ votesGranted' = [votesGranted' EXCEPT ![i] = votesGranted'[i] \cup {m.source}]
           /\ IF IsQuorum(votesGranted'[i]) THEN
                 /\ state' = [state' EXCEPT ![i] = "leader"]
                 /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Node |-> LastIndex(log[i]) + 1]]
                 /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Node |-> 0]]
                 /\ leader' = [leader' EXCEPT ![i] = i]
              ELSE
                 /\ state' = state'
                 /\ nextIndex' = nextIndex
                 /\ matchIndex' = matchIndex
                 /\ leader' = leader'
       ELSE
           /\ state' = state'
           /\ nextIndex' = nextIndex
           /\ matchIndex' = matchIndex
           /\ leader' = leader'
    /\ net' = net \ominus [m |-> 1]
    /\ UNCHANGED <<log, commitIndex>>
Next == 
    \/ \E i \in Node : Timeout(i)
    \/ \E m \in BagToSet(net) : RequestVoteRequest(m)
    \/ \E m \in BagToSet(net) : RequestVoteResponse(m)
Spec == Init /\ [][Next]_vars
====