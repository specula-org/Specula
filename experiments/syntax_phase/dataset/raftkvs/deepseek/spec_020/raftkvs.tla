---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Servers, Clients, Nil, Keys, Values
ASSUME Nil \notin Servers \cup Clients
Node == Servers \cup Clients
MsgType == {"RequestVoteRequest", "RequestVoteResponse", "AppendEntriesRequest", "AppendEntriesResponse", "ClientPutRequest", "ClientPutResponse", "ClientGetRequest", "ClientGetResponse"}

Message == [mtype: MsgType, mterm: Nat, msource: Node, mdest: Node, mlastLogIndex: Nat, mlastLogTerm: Nat, mvoteGranted: Bool, mprevLogIndex: Nat, mprevLogTerm: Nat, mentries: Seq(Nat), mcommitIndex: Nat, msuccess: Bool, mmatchIndex: Nat, mkey: Keys, mvalue: Values]

VARIABLES state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, msgs, votesGranted

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, msgs, votesGranted>>

Init == 
    state = [s \in Servers |-> "Follower"] /\
    currentTerm = [s \in Servers |-> 0] /\
    votedFor = [s \in Servers |-> Nil] /\
    log = [s \in Servers |-> <<>>] /\
    commitIndex = [s \in Servers |-> 0] /\
    nextIndex = [s \in Servers |-> [t \in Servers |-> 1]] /\
    matchIndex = [s \in Servers |-> [t \in Servers |-> 0]] /\
    msgs = {} /\
    votesGranted = [s \in Servers |-> {}]

IsQuorum(S) == Cardinality(S) > Cardinality(Servers) \div 2
LastTerm(logSeq) == IF Len(logSeq) > 0 THEN logSeq[Len(logSeq)] ELSE 0

ElectionTimeout(s) == 
    /\ state[s] \in {"Follower", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ msgs' = msgs \cup { [mtype |-> "RequestVoteRequest", mterm |-> currentTerm[s] + 1, msource |-> s, mdest |-> t, mlastLogIndex |-> Len(log[s]), mlastLogTerm |-> LastTerm(log[s]), mvoteGranted |-> FALSE, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 0, msuccess |-> FALSE, mmatchIndex |-> 0, mkey |-> CHOOSE k \in Keys: TRUE, mvalue |-> CHOOSE v \in Values: TRUE] : t \in Servers \ {s} }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

HandleRequestVoteRequest(m) == 
    LET s == m["mdest"]
        newTerm == m["mterm"] > currentTerm[s]
    IN
    /\ IF newTerm THEN
         state' = [state EXCEPT ![s] = "Follower"] /\
         currentTerm' = [currentTerm EXCEPT ![s] = m["mterm"]] /\
         votedFor' = [votedFor EXCEPT ![s] = Nil] /\
         votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
    /\ LET currentTermVal == IF newTerm THEN m["mterm"] ELSE currentTerm[s]
           logOK == \/ m["mlastLogTerm"] > LastTerm(log[s])
                    \/ (m["mlastLogTerm"] = LastTerm(log[s]) /\ m["mlastLogIndex"] >= Len(log[s]))
           grant == (m["mterm"] = currentTermVal /\ logOK /\ (votedFor[s] = Nil \/ votedFor[s] = m["msource"]))
       IN
       /\ IF grant THEN votedFor' = [votedFor EXCEPT ![s] = m["msource"]] ELSE UNCHANGED votedFor
       /\ msgs' = msgs \cup { [mtype |-> "RequestVoteResponse", mterm |-> currentTermVal, msource |-> s, mdest |-> m["msource"], mvoteGranted |-> grant, mlastLogIndex |-> 0, mlastLogTerm |-> 0, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 0, msuccess |-> FALSE, mmatchIndex |-> 0, mkey |-> CHOOSE k \in Keys: TRUE, mvalue |-> CHOOSE v \in Values: TRUE] }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesGranted>>

HandleRequestVoteResponse(m) == 
    LET s == m["mdest"]
        newTerm == m["mterm"] > currentTerm[s]
    IN
    /\ IF newTerm THEN
         state' = [state EXCEPT ![s] = "Follower"] /\
         currentTerm' = [currentTerm EXCEPT ![s] = m["mterm"]] /\
         votedFor' = [votedFor EXCEPT ![s] = Nil] /\
         votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
    /\ LET currentTermVal == IF newTerm THEN m["mterm"] ELSE currentTerm[s] IN
        IF m["mterm"] < currentTermVal THEN UNCHANGED <<>>
        ELSE
            /\ IF m["mvoteGranted"] THEN
                 votesGranted' = [votesGranted EXCEPT ![s] = @ \cup {m["msource"]}]
               ELSE UNCHANGED votesGranted
            /\ IF state[s] = "Candidate" /\ IsQuorum(votesGranted'[s]) THEN
                 state' = [state EXCEPT ![s] = "Leader"] /\
                 nextIndex' = [nextIndex EXCEPT ![s] = [t \in Servers |-> Len(log[s]) + 1]] /\
                 matchIndex' = [matchIndex EXCEPT ![s] = [t \in Servers |-> 0]]
               ELSE UNCHANGED <<state, nextIndex, matchIndex>>
    /\ UNCHANGED <<log, commitIndex, msgs>>

HandleAppendEntriesRequest(m) == 
    LET s == m["mdest"]
        newTerm == m["mterm"] > currentTerm[s]
    IN
    /\ IF newTerm THEN
         state' = [state EXCEPT ![s] = "Follower"] /\
         currentTerm' = [currentTerm EXCEPT ![s] = m["mterm"]] /\
         votedFor' = [votedFor EXCEPT ![s] = Nil] /\
         votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
    /\ LET currentTermVal == IF newTerm THEN m["mterm"] ELSE currentTerm[s]
           logOK == m["mprevLogIndex"] = 0 \/ (m["mprevLogIndex"] <= Len(log[s]) /\ m["mprevLogTerm"] = log[s][m["mprevLogIndex"]])
       IN
       /\ IF m["mterm"] = currentTermVal /\ state[s] = "Candidate" THEN state' = [state EXCEPT ![s] = "Follower"] ELSE UNCHANGED state
       /\ IF m["mterm"] = currentTermVal /\ logOK THEN
            /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, m["mprevLogIndex"]) \o m["mentries"]]
            /\ IF m["mcommit极"] > commitIndex[s] THEN commitIndex' = [commitIndex EXCEPT ![s] = m["mcommitIndex"]] ELSE UNCHANGED commitIndex
            /\ msgs' = msgs \cup { [mtype |-> "AppendEntriesResponse", mterm |-> currentTermVal, msource |-> s, mdest |-> m["msource"], msuccess |-> TRUE, mmatchIndex |-> m["mprevLogIndex"] + Len(m["mentries"]), mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 0, mkey |-> CHOOSE k \in Keys: TRUE, mvalue |-> CHOOSE v \in Values: TRUE] }
          ELSE
            /\ msgs' = msgs \cup { [mtype |-> "AppendEntriesResponse", mterm |-> currentTermVal, msource |-> s, mdest |-> m["msource"], msuccess |-> FALSE, mmatchIndex |-> 0, mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 极, mkey |-> CHOOSE k \in Keys: TRUE, mvalue |-> CHOOSE v \in Values: TRUE] }
    /\ UNCHANGED <<votedFor, nextIndex, matchIndex, votesGranted>>

HandleAppendEntriesResponse(m) == 
    LET s == m["mdest"]
        newTerm == m["mterm"] > currentTerm[s]
    IN
    /\ IF newTerm THEN
         state' = [state EXCEPT ![s] = "Follower"] /\
         currentTerm' = [currentTerm EXCEPT ![s] = m["mterm"]] /\
         votedFor' = [votedFor EXCEPT ![s] = Nil] /\
         votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE UNCHANGED <<state, currentTerm, voted极, votesGranted>>
    /\ IF m["mterm"] < currentTerm[s] THEN UNCHANGED <<nextIndex, matchIndex, commitIndex>>
       ELSE
         /\ IF m["msuccess"] THEN
              nextIndex' = [nextIndex EXCEPT ![s][m["msource"]] = m["mmatchIndex"] + 1] /\
              matchIndex' = [matchIndex EXCEPT ![s][m["msource"]] = m["mmatchIndex"]]
            ELSE
              nextIndex' = [nextIndex EXCEPT ![s][m["msource"]] = nextIndex[s][m["msource"]] - 1]
         /\ LET N == { i \in 1..Len(log[s]) : 
                      log[s][i] = currentTerm[s] /\ 
                      Cardinality({ t \in Servers : matchIndex[s][t] >= i }) > Cardinality(Servers) \div 2 }
            IN
            IF N # {} THEN commitIndex' = [commitIndex EXCEPT ![s] = CHOOSE n \in N : TRUE] ELSE UNCHANGED commitIndex
    /\ UNCHANGED <<state, votedFor, log, msgs, votesGranted>>

HandleClientPutRequest(m) == 
    LET s == m["mdest"] IN
    IF state[s] = "Leader" THEN
        /\ log' = [log EXCEPT ![s] = Append(log[s], currentTerm[s])]
        /\ msgs' = msgs \cup { [mtype |-> "AppendEntriesRequest", mterm |-> currentTerm[s], msource |-> s, mdest |-> t, mprevLogIndex |-> Len(log[s]), mprevLogTerm |-> LastTerm(log[s]), mentries |-> <<currentTerm[s]>>, mcommitIndex |-> commitIndex[s], mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, msuccess |-> FALSE, mmatchIndex |-> 0, mkey |-> m["mkey"], mvalue |-> m["mvalue"]] : t \in Servers \ {s} }
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, votesGranted>>
    ELSE
        /\ msgs' = msgs \cup { [mtype |-> "ClientPutResponse", mterm |-> 0, msource |-> s, mdest |-> m["msource"], msuccess |-> FALSE, mkey |-> m["mkey"], mvalue |-> CHOOSE v \in Values: TRUE, mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 0, mmatchIndex |-> 0] }
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted>>

HandleClientGetRequest(m) == 
    LET s == m["mdest"] IN
    IF state[s] = "Leader" THEN
        /\ log' = [log EXCEPT ![s] = Append(log[s], currentTerm[s])]
        /\ msgs' = msgs \cup { [mtype |-> "AppendEntriesRequest", mterm |-> currentTerm[s], msource |-> s, mdest |-> t, mprevLogIndex |-> Len(log[s]), mprevLogTerm |-> LastTerm(log[s]), mentries |-> <<currentTerm[s]>>, mcommitIndex |-> commitIndex[s], mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, msuccess |-> FALSE, mmatchIndex |-> 0, mkey |-> m["mkey"], mvalue |-> CHOOSE v \in Values: TRUE] : t \in Servers \ {s} }
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, votesGranted>>
    ELSE
        /\ msgs' = msgs \cup { [mtype |-> "ClientGetResponse", mterm |-> 0, msource |-> s, mdest |-> m["msource"], msuccess |-> FALSE, mkey |-> m["mkey"], mvalue |-> CHOOSE v \in Values: TRUE, mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 0, mmatchIndex |-> 0] }
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted>>

ClientSendRequest(c, s) == 
    /\ c \in Clients
    /\ s \in Servers
    /\ msgs' = msgs \cup { [mtype |-> "ClientPutRequest", mterm |-> 0, msource |-> c, mdest |-> s, mkey |-> CHOOSE k \in Keys: TRUE, mvalue |-> CHOOSE v \in Values: TRUE, mlastLogIndex |-> 0, mlastLogTerm |-> 0, mvoteGranted |-> FALSE, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<>>, mcommitIndex |-> 0, msuccess |-> FALSE, mmatchIndex |-> 0] }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted>>

MessageLoss(m) == 
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted>>

HandleMessage(m) == 
    IF m["mdest"] \in Servers THEN
        IF m["mtype"] = "RequestVoteRequest" THEN HandleRequestVoteRequest(m)
        ELSE IF m["mtype"] = "RequestVoteResponse" THEN HandleRequestVoteResponse(m)
        ELSE IF m["mtype"] = "AppendEntriesRequest" THEN HandleAppendEntriesRequest(m)
        ELSE IF m["mtype"] = "AppendEntriesResponse" THEN HandleAppendEntriesResponse(m)
        ELSE IF m["mtype"] = "ClientPutRequest" THEN HandleClientPutRequest(m)
        ELSE IF m["mtype"] = "ClientGetRequest" THEN HandleClientGetRequest(m)
        ELSE FALSE
    ELSE FALSE

Next == 
    \/ \E s \in Servers : ElectionTimeout(s)
    \/ \E m \in msgs : HandleMessage(m)
    \/ \E c \in Clients, s \in Servers : ClientSendRequest(c, s)
    \/ \E m \in msgs : MessageLoss(m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====