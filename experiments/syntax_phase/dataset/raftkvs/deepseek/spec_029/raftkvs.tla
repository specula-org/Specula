---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Integers
CONSTANTS NumServers, NumClients
ASSUME NumServers \in Nat \ {0}
ASSUME NumClients \in Nat
Servers == 1..NumServers
Clients == 1..NumClients
STATE_FOLLOWER == "Follower"
STATE_CANDIDATE == "Candidate"
STATE_LEADER == "Leader"
MSG_RV_REQUEST == "RequestVoteRequest"
MSG_RV_RESPONSE == "RequestVoteResponse"
MSG_AE_REQUEST == "AppendEntriesRequest"
MSG_AE_RESPONSE == "AppendEntriesResponse"
MSG_CPUT_REQUEST == "ClientPutRequest"
MSG_CPUT_RESPONSE == "ClientPutResponse"
MSG_CGET_REQUEST == "ClientGetRequest"
MSG_CGET_RESPONSE == "ClientGetResponse"
Nil == 0
Majority == (NumServers \div 2) + 1
VARIABLES currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesGranted, network
vars == <<currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesGranted, network>>
Init == 
    /\ currentTerm = [s \in Servers |-> 0]
    /\ state = [s \in Servers |-> STATE_FOLLOWER]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [f \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [f \in Servers |-> 0]]
    /\ leader = [s \in Servers |-> Nil]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ network = {}
LastTerm(seq) == IF Len(seq) = 0 THEN 0 ELSE seq[Len(seq)]
LogOk(s, lastLogTerm, lastLogIndex) == 
    \/ lastLogTerm > LastTerm(log[s])
    \/ (lastLogTerm = LastTerm(log[s]) /\ lastLogIndex >= Len(log[s]))
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b
ElectionTimeout(s) == 
    /\ state[s] = STATE_FOLLOWER \/ state[s] = STATE_CANDIDATE
    /\ state' = [state EXCEPT ![s] = STATE_CANDIDATE]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ network' = network \cup { [mtype |-> MSG_RV_REQUEST, mterm |-> currentTerm[s] + 1, mlastLogTerm |-> LastTerm(log[s]), mlastLogIndex |-> Len(log[s]), msource |-> s, mdest |-> f] : f \in Servers \ {s} }
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leader>>
ReceiveRVRequest(s, msg) == 
    /\ msg \in network
    /\ msg.mtype = MSG_RV_REQUEST
    /\ msg.mdest = s
    /\ \/ msg.mterm > currentTerm[s]
       \/ TRUE
    /\ IF msg.mterm > currentTerm[s] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![s] = msg.mterm]
           /\ state' = [state EXCEPT ![s] = STATE_FOLLOWER]
           /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
           /\ leader' = [leader EXCEPT ![s] = Nil]
           /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE
           /\ currentTerm' = currentTerm
           /\ state' = state
           /\ votedFor' = votedFor
           /\ leader' = leader
           /\ votesGranted' = votesGranted
    /\ LET newCurrentTerm == IF msg.mterm > currentTerm[s] THEN msg.mterm ELSE currentTerm[s] IN
       LET grant == /\ msg.mterm = newCurrentTerm
                    /\ LogOk(s, msg.mlastLogTerm, msg.mlastLogIndex)
                    /\ (votedFor[s] = Nil \/ votedFor[s] = msg.msource) IN
       /\ IF grant THEN
              votedFor' = [votedFor' EXCEPT ![s] = msg.msource]
          ELSE
              votedFor' = votedFor'
       /\ LET resp == [mtype |-> MSG_RV_RESPONSE, mterm |-> newCurrentTerm, mvoteGranted |-> grant, msource |-> s, mdest |-> msg.msource] IN
          network' = (network \ {msg}) \cup {resp}
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, leader, votesGranted>>
ReceiveRVResponse(s, msg) == 
    /\ msg \in network
    /\ msg.mtype = MSG_RV_RESPONSE
    /\ msg.mdest = s
    /\ \/ msg.mterm > currentTerm[s]
       \/ msg.mterm <= currentTerm[s]
    /\ IF msg.mterm > currentTerm[s] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![s] = msg.mterm]
           /\ state' = [state EXCEPT ![s] = STATE_FOLLOWER]
           /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
           /\ leader' = [leader EXCEPT ![s] = Nil]
           /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE
           /\ currentTerm' = currentTerm
           /\ state' = state
           /\ votedFor' = votedFor
           /\ leader' = leader
           /\ votesGranted' = votesGranted
    /\ LET newCurrentTerm == IF msg.mterm > currentTerm[s] THEN msg.mterm ELSE currentTerm[s] IN
       IF msg.mterm = newCurrentTerm /\ state[s] = STATE_CANDIDATE THEN
           /\ IF msg.mvoteGranted THEN
                  votesGranted' = [votesGranted' EXCEPT ![s] = votesGranted'[s] \cup {msg.msource}]
              ELSE
                  votesGranted' = votesGranted'
           /\ IF Cardinality(votesGranted'[s]) >= Majority THEN
                 /\ state' = [state' EXCEPT ![s] = STATE_LEADER]
                 /\ nextIndex' = [nextIndex EXCEPT ![s] = [f \in Servers |-> Len(log[s]) + 1]]
                 /\ matchIndex' = [matchIndex EXCEPT ![s] = [f \in Servers |-> 0]]
                 /\ leader' = [leader' EXCEPT ![s] = s]
             ELSE
                 /\ state' = state'
                 /\ nextIndex' = nextIndex
                 /\ matchIndex' = matchIndex
                 /\ leader' = leader'
       ELSE
           /\ votesGranted' = votesGranted'
           /\ state' = state'
           /\ nextIndex' = nextIndex
           /\ matchIndex' = matchIndex
           /\ leader' = leader'
    /\ network' = network \ {msg}
    /\ UNCHANGED <<log, commitIndex>>
SendAppendEntries(s) == 
    /\ state[s] = STATE_LEADER
    /\ network' = network \cup { [mtype |-> MSG_AE_REQUEST, mterm |-> currentTerm[s], mprevLogIndex |-> nextIndex[s][f] - 1, mprevLogTerm |-> IF nextIndex[s][f] > 1 THEN log[s][nextIndex[s][f] - 1] ELSE 0, mentries |-> SubSeq(log[s], nextIndex[s][f], Len(log[s])), mcommitIndex |-> commitIndex[s], msource |-> s, mdest |-> f] : f \in Servers \ {s} }
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesGranted>>
ReceiveAERequest(s, msg) == 
    /\ msg \in network
    /\ msg.mtype = MSG_AE_REQUEST
    /\ msg.mdest = s
    /\ IF msg.mterm > currentTerm[s] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![s] = msg.mterm]
           /\ state' = [state EXCEPT ![s] = STATE_FOLLOWER]
           /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
           /\ leader' = [leader EXCEPT ![s] = Nil]
           /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE
           /\ currentTerm' = currentTerm
           /\ state' = state
           /\ votedFor' = votedFor
           /\ leader' = leader
           /\ votesGranted' = votesGranted
    /\ IF msg.mterm = currentTerm'[s] /\ state[s] = STATE_CANDIDATE THEN
           /\ state' = [state' EXCEPT ![s] = STATE_FOLLOWER]
           /\ votesGranted' = [votesGranted' EXCEPT ![s] = {}]
       ELSE
           /\ state' = state'
           /\ votesGranted' = votesGranted'
    /\ IF msg.mterm = currentTerm'[s] THEN
           leader' = [leader' EXCEPT ![s] = msg.msource]
       ELSE
           leader' = leader'
    /\ LET prevLogIndex == msg.mprevLogIndex IN
       LET prevLogTerm == msg.mprevLogTerm IN
       LET logOk == \/ prevLogIndex = 0
                    \/ (prevLogIndex <= Len(log[s]) /\ log[s][prevLogIndex] = prevLogTerm) IN
       IF msg.mterm = currentTerm'[s] /\ state'[s] = STATE_FOLLOWER /\ logOk THEN
           /\ IF prevLogIndex < Len(log[s]) THEN
                  log' = [log EXCEPT ![s] = SubSeq(log[s], 1, prevLogIndex)]
              ELSE
                  log' = log
           /\ log' = [log' EXCEPT ![s] = log'[s] \o msg.mentries]
           /\ IF msg.mcommitIndex > commitIndex[s] THEN
                 commitIndex' = [commitIndex EXCEPT ![s] = Min(msg.mcommitIndex, Len(log'[s]))]
             ELSE
                 commitIndex' = commitIndex
           /\ LET newMatchIndex == prevLogIndex + Len(msg.mentries) IN
              LET resp == [mtype |-> MSG_AE_RESPONSE, mterm |-> currentTerm'[s], msuccess |-> TRUE, mmatchIndex |-> newMatchIndex, msource |-> s, mdest |-> msg.msource] IN
              network' = (network \ {msg}) \cup {resp}
       ELSE
           /\ LET resp == [mtype |-> MSG_AE_RESPONSE, mterm |-> currentTerm'[s], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> s, mdest |-> msg.msource] IN
              network' = (network \ {msg}) \cup {resp}
           /\ log' = log
           /\ commitIndex' = commitIndex
    /\ UNCHANGED <<nextIndex, matchIndex, votesGranted>>
ReceiveAEResponse(s, msg) == 
    /\ msg \in network
    /\ msg.mtype = MSG_AE_RESPONSE
    /\ msg.mdest = s
    /\ IF msg.mterm > currentTerm[s] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![s] = msg.mterm]
           /\ state' = [state EXCEPT ![s] = STATE_FOLLOWER]
           /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
           /\ leader' = [leader EXCEPT ![s] = Nil]
           /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
       ELSE
           /\ currentTerm' = currentTerm
           /\ state' = state
           /\ votedFor' = votedFor
           /\ leader' = leader
           /\ votesGranted' = votesGranted
    /\ IF msg.mterm = currentTerm'[s] /\ state[s] = STATE_LEADER THEN
           IF msg.msuccess THEN
               /\ nextIndex' = [nextIndex EXCEPT ![s][msg.msource] = msg.mmatchIndex + 1]
               /\ matchIndex' = [matchIndex EXCEPT ![s][msg.msource] = msg.mmatchIndex]
           ELSE
               /\ nextIndex' = [nextIndex EXCEPT ![s][msg.msource] = Max(1, nextIndex[s][msg.msource] - 1)]
           /\ UNCHANGED <<log, commitIndex>>
       ELSE
           UNCHANGED <<nextIndex, matchIndex, log, commitIndex>>
    /\ network' = network \ {msg}
    /\ UNCHANGED <<votedFor, votesGranted>>
AdvanceCommitIndex(s) == 
    /\ state[s] = STATE_LEADER
    /\ LET S == { n \in (commitIndex[s] + 1) .. Len(log[s]) : 
                     Cardinality({f \in Servers : matchIndex[s][f] >= n}) >= Majority
                     /\ log[s][n] = currentTerm[s] }
       IN
       S # {}
    /\ LET maxN == CHOOSE n \in S : \A m \in S : m <= n IN
       commitIndex' = [commitIndex EXCEPT ![s] = maxN]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, nextIndex, matchIndex, leader, votesGranted, network>>
MessageLoss == 
    /\ \E msg \in network : network' = network \ {msg}
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesGranted>>
ClientSendRequest(c, s, type) == 
    /\ type \in {"Put", "Get"}
    /\ network' = network \cup { [mtype |-> IF type = "Put" THEN MSG_CPUT_REQUEST ELSE MSG_CGET_REQUEST, mcmd |-> [type |-> type], msource |-> c, mdest |-> s] }
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesGranted>>
ReceiveClientRequest(s, msg) == 
    /\ msg \in network
    /\ (msg.mtype = MSG_CPUT_REQUEST \/ msg.mtype = MSG_CGET_REQUEST)
    /\ msg.mdest = s
    /\ IF state[s] = STATE_LEADER THEN
           /\ log' = [log EXCEPT ![s] = log[s] \o << currentTerm[s] >>]
           /\ network' = network \ {msg}
       ELSE
           /\ LET respType == IF msg.mtype = MSG_CPUT_REQUEST THEN MSG_CPUT_RESPONSE ELSE MSG_CGET_RESPONSE IN
              LET resp == [mtype |-> respType, msuccess |-> FALSE, mleaderHint |-> leader[s], msource |-> s, mdest |-> msg.msource] IN
              network' = (network \ {msg}) \cup {resp}
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, nextIndex, matchIndex, leader, votesGranted>>
Next == 
    \/ \E s \in Servers : ElectionTimeout(s)
    \/ \E s \in Servers, msg \in network : ReceiveRVRequest(s, msg)
    \/ \E s \in Servers, msg \in network : ReceiveRVResponse(s, msg)
    \/ \E s \in Servers : SendAppendEntries(s)
    \/ \E s \in Servers, msg \in network : ReceiveAERequest(s, msg)
    \/ \E s \in Servers, msg \in network : ReceiveAEResponse(s, msg)
    \/ \E s \in Servers : AdvanceCommitIndex(s)
    \/ MessageLoss
    \/ \E c \in Clients, s \in Servers, type \in {"Put", "Get"} : ClientSendRequest(c, s, type)
    \/ \E s \in Servers, msg \in network : ReceiveClientRequest(s, msg)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====