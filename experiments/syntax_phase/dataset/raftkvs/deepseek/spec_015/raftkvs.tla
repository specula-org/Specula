---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, AllStrings, ExploreFail, MaxNodeFail, Debug, 
          LeaderTimeoutReset, LogPop, LogConcat

VARIABLES serverState, currentTerm, votedFor, log, commitIndex, nextIndex, 
          matchIndex, votesResponded, votesGranted, leader, sm, smDomain, 
          clientLeader, clientReq, clientResp, clientReqIdx, net, netEnabled, fd

vars == <<serverState, currentTerm, votedFor, log, commitIndex, nextIndex, 
          matchIndex, votesResponded, votesGranted, leader, sm, smDomain, 
          clientLeader, clientReq, clientResp, clientReqIdx, net, netEnabled, fd>>

Server == 1..NumServers
Client == (NumServers+1)..(NumServers+NumClients)
Node == Server \union Client
Nil == 0

MessageType == {"rvq", "rvp", "apq", "app", "cpq", "cpp", "cgq", "cgp"}
Put == "put"
Get == "get"
Follower == "follower"
Candidate == "candidate"
Leader == "leader"

IsQuorum(S) == Cardinality(S) > (NumServers \div 2)
ServerSet == Server

LastTerm(log) == IF log = <<>> THEN 0 ELSE log[Len(log)].term

FindMaxAgreeIndex(log, i, matchIndex) ==
    LET S == {index \in 1..Len(log): 
               IsQuorum({i} \cup {s \in Server: matchIndex[s] >= index})}
    IN IF S = {} THEN 0 ELSE MAX(S)

ApplyLogEntry(entry, sm, smDomain) ==
    IF entry.cmd.type = Put THEN
        <<sm @@ (entry.cmd.key :> entry.cmd.value), smDomain \cup {entry.cmd.key}>>
    ELSE <<sm, smDomain>>

ApplyLog(log, start, end, sm, smDomain) ==
    IF start > end THEN <<sm, smDomain>>
    ELSE ApplyLog(log, start+1, end, 
                  ApplyLogEntry(log[start], sm, smDomain)[1],
                  ApplyLogEntry(log[start], sm, smDomain)[2])

AllReqs == 
    [type: {Put}, key: AllStrings, value: AllStrings] \cup 
    [type: {Get}, key: AllStrings]

Init == 
    /\ serverState = [s \in Server |-> Follower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesResponded = [s \in Server |-> {}]
    /\ votesGranted = [s \in Server |-> {}]
    /\ leader = [s \in Server |-> Nil]
    /\ sm = [s \in Server |-> [k \in {} |-> ""]]
    /\ smDomain = [s \in Server |-> {}]
    /\ clientLeader = [c \in Client |-> Nil]
    /\ clientReq = [c \in Client |-> [type |-> "none", key |-> "", value |-> ""]]
    /\ clientResp = [c \in Client |-> [idx |-> 0, key |-> "", value |-> "", ok |-> FALSE]]
    /\ clientReqIdx = [c \in Client |-> 0]
    /\ net = EmptyBag
    /\ netEnabled = [n \in Node |-> TRUE]
    /\ fd = [s \in Server |-> FALSE]

ServerRequestVote(s) ==
    /\ netEnabled[s] = TRUE
    /\ serverState[s] \in {Follower, Candidate}
    \* Election timeout condition
    /\ \E self \in Server: TRUE
    /\ serverState' = [serverState EXCEPT ![s] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesResponded' = [votesResponded EXCEPT ![s] = {s}]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ net' = net \cup 
        [mtype |-> "rvq", mterm |-> currentTerm[s] + 1, 
         mlastLogTerm |-> LastTerm(log[s]), mlastLogIndex |-> Len(log[s]),
         msource |-> s, mdest |-> t] : t \in Server \ {s}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain,
                  clientLeader, clientReq, clientResp, clientReqIdx, fd>>

ServerHandleRequestVoteRequest(s, m) ==
    /\ m \in net
    /\ m.mdest = s
    /\ m.mtype = "rvq"
    /\ netEnabled[s] = TRUE
    /\ IF m.mterm > currentTerm[s] THEN
        /\ serverState' = [serverState EXCEPT ![s] = Follower]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
        /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
        /\ leader' = [leader EXCEPT ![s] = Nil]
    ELSE /\ TRUE
        /\ UNCHANGED <<serverState, currentTerm, votedFor, leader>>
    /\ LET grant == 
            /\ m.mterm = currentTerm[s]
            /\ \/ votedFor[s] = Nil
               \/ votedFor[s] = m.msource
            /\ \/ m.mlastLogTerm > LastTerm(log[s])
               \/ /\ m.mlastLogTerm = LastTerm(log[s])
                  /\ m.mlastLogIndex >= Len(log[s])
       IN
       IF grant THEN
           votedFor'' = [votedFor' EXCEPT ![s] = m.msource]
       ELSE votedFor'' = votedFor'
    /\ net' = net \cup 
        [mtype |-> "rvp", mterm |-> currentTerm'[s], 
         mvoteGranted |-> grant, msource |-> s, mdest |-> m.msource]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesResponded, 
                  votesGranted, sm, smDomain, clientLeader, clientReq, 
                  clientResp, clientReqIdx, netEnabled, fd>>

ServerHandleRequestVoteResponse(s, m) ==
    /\ m \in net
    /\ m.mdest = s
    /\ m.mtype = "rvp"
    /\ netEnabled[s] = TRUE
    /\ IF m.mterm > currentTerm[s] THEN
        /\ serverState' = [serverState EXCEPT ![s] = Follower]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
        /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
        /\ leader' = [leader EXCEPT ![s] = Nil]
        /\ votesResponded' = [votesResponded EXCEPT ![s] = {}]
        /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    ELSE /\ m.mterm = currentTerm[s]
        /\ serverState[s] = Candidate
        /\ votesResponded' = [votesResponded EXCEPT ![s] = votesResponded[s] \cup {m.msource}]
        /\ IF m.mvoteGranted THEN
            votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.msource}]
        ELSE
            UNCHANGED votesGranted
        /\ IF IsQuorum(votesGranted'[s]) THEN
            /\ serverState' = [serverState EXCEPT ![s] = Leader]
            /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
            /\ leader' = [leader EXCEPT ![s] = s]
            /\ net' = net \cup 
                [mtype |-> "apq", mterm |-> currentTerm[s], 
                 mprevLogIndex |-> 0, mprevLogTerm |-> 0,
                 mentries |-> <<>>, mcommitIndex |-> commitIndex[s],
                 msource |-> s, mdest |-> t] : t \in Server \ {s}]
        ELSE
            /\ UNCHANGED <<serverState, nextIndex, matchIndex, leader, net>>
    /\ UNCHANGED <<log, commitIndex, sm, smDomain, clientLeader, clientReq, 
                  clientResp, clientReqIdx, netEnabled, fd>>

ServerHandleAppendEntriesRequest(s, m) ==
    /\ m \in net
    /\ m.mdest = s
    /\ m.mtype = "apq"
    /\ netEnabled[s] = TRUE
    /\ IF m.mterm > currentTerm[s] THEN
        /\ serverState' = [serverState EXCEPT ![s] = Follower]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
        /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
        /\ leader' = [leader EXCEPT ![s] = Nil]
    ELSE /\ TRUE
        /\ UNCHANGED <<serverState, currentTerm, votedFor, leader>>
    /\ IF m.mterm = currentTerm[s] THEN
        /\ leader'' = [leader' EXCEPT ![s] = m.msource]
        /\ IF serverState[s] = Candidate THEN
            serverState'' = [serverState' EXCEPT ![s] = Follower]
        ELSE serverState'' = serverState'
    ELSE serverState'' = serverState'
    /\ LET logOK == 
           \/ m.mprevLogIndex = 0
           \/ /\ m.mprevLogIndex > 0
              /\ m.mprevLogIndex <= Len(log[s])
              /\ m.mprevLogTerm = log[s][m.mprevLogIndex].term
       IN
       IF /\ m.mterm = currentTerm[s]
          /\ serverState''[s] = Follower
          /\ logOK
       THEN
           /\ log' = [log EXCEPT ![s] = 
                SubSeq(log[s], 1, m.mprevLogIndex) \o m.mentries]
           /\ IF m.mcommitIndex > commitIndex[s] THEN
               commitIndex' = [commitIndex EXCEPT ![s] = 
                   Min({m.mcommitIndex, Len(log'[s])})]
           ELSE UNCHANGED commitIndex
           /\ LET newSMState == 
                   ApplyLog(log'[s], commitIndex[s] + 1, commitIndex'[s], 
                           sm[s], smDomain[s])
              IN
              /\ sm' = [sm EXCEPT ![s] = newSMState[1]]
              /\ smDomain' = [smDomain EXCEPT ![s] = newSMState[2]]
           /\ net' = net \cup 
               [mtype |-> "app", mterm |-> currentTerm[s], 
                msuccess |-> TRUE, 
                mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                msource |-> s, mdest |-> m.msource]
       ELSE
           /\ UNCHANGED <<log, commitIndex, sm, smDomain>>
           /\ net' = net \cup 
               [mtype |-> "app", mterm |-> currentTerm[s], 
                msuccess |-> FALSE, mmatchIndex |-> 0,
                msource |-> s, mdest |-> m.msource]
    /\ UNCHANGED <<nextIndex, matchIndex, votesResponded, votesGranted,
                  clientLeader, clientReq, clientResp, clientReqIdx, 
                  netEnabled, fd>>

ServerHandleAppendEntriesResponse(s, m) ==
    /\ m \in net
    /\ m.mdest = s
    /\ m.mtype = "app"
    /\ netEnabled[s] = TRUE
    /\ serverState[s] = Leader
    /\ IF m.mterm > currentTerm[s] THEN
        /\ serverState' = [serverState EXCEPT ![s] = Follower]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
        /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
        /\ leader' = [leader EXCEPT ![s] = Nil]
        /\ UNCHANGED <<nextIndex, matchIndex>>
    ELSE /\ m.mterm = currentTerm[s]
        /\ IF m.msuccess THEN
            /\ nextIndex' = [nextIndex EXCEPT ![s][m.msource] = 
                   m.mmatchIndex + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![s][m.msource] = 
                   m.mmatchIndex]
        ELSE
            /\ nextIndex' = [nextIndex EXCEPT ![s][m.msource] = 
                   Max({nextIndex[s][m.msource] - 1, 1})]
            /\ UNCHANGED matchIndex
        /\ UNCHANGED <<serverState, currentTerm, votedFor, leader>>
    /\ UNCHANGED <<log, commitIndex, votesResponded, votesGranted, sm, smDomain,
                  clientLeader, clientReq, clientResp, clientReqIdx, fd>>

ServerHandleClientRequest(s, m) ==
    /\ m \in net
    /\ m.mdest = s
    /\ m.mtype \in {"cpq", "cgq"}
    /\ netEnabled[s] = TRUE
    /\ IF serverState[s] = Leader THEN
        /\ LET newEntry == [term |-> currentTerm[s], 
                           cmd |-> m.mcmd,
                           client |-> m.msource]
           IN
           /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
           /\ net' = net \cup 
               [mtype |-> "apq", mterm |-> currentTerm[s],
                mprevLogIndex |-> Len(log[s]), 
                mprevLogTerm |-> LastTerm(log[s]),
                mentries |-> <<newEntry>>, 
                mcommitIndex |-> commitIndex[s],
                msource |-> s, mdest |-> t] : t \in Server \ {s}]
    ELSE
        /\ LET respType == 
                IF m.mcmd.type = Put THEN "cpp" ELSE "cgp"
           IN
           /\ net' = net \cup 
               [mtype |-> respType, msuccess |-> FALSE,
                mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key],
                mleaderHint |-> leader[s],
                msource |-> s, mdest |-> m.msource]
        /\ UNCHANGED log
    /\ UNCHANGED <<serverState, currentTerm, votedFor, commitIndex, nextIndex,
                  matchIndex, votesResponded, votesGranted, leader, sm, 
                  smDomain, clientLeader, clientReq, clientResp, clientReqIdx,
                  netEnabled, fd>>

LeaderAdvanceCommitIndex(s) ==
    /\ serverState[s] = Leader
    /\ LET N == FindMaxAgreeIndex(log[s], s, matchIndex[s])
           IN
           IF N > commitIndex[s] /\ log[s][N].term = currentTerm[s] THEN
               /\ commitIndex' = [commitIndex EXCEPT ![s] = N]
               /\ LET newSMState == 
                       ApplyLog(log[s], commitIndex[s] + 1, N, 
                               sm[s], smDomain[s])
                  IN
                  /\ sm' = [sm EXCEPT ![s] = newSMState[1]]
                  /\ smDomain' = [smDomain EXCEPT ![s] = newSMState[2]]
           ELSE UNCHANGED <<commitIndex, sm, smDomain>>
    /\ UNCHANGED <<serverState, currentTerm, votedFor, log, nextIndex, 
                  matchIndex, votesResponded, votesGranted, leader, 
                  clientLeader, clientReq, clientResp, clientReqIdx, net, 
                  netEnabled, fd>>

ClientSendRequest(c) ==
    /\ clientReqIdx[c] = clientReqIdx[c] + 1
    /\ clientReq' = [clientReq EXCEPT ![c] = 
           [type |-> CHOOSE t \in {Put, Get}: TRUE,
            key |-> CHOOSE k \in AllStrings: TRUE,
            value |-> CHOOSE v \in AllStrings: TRUE,
            idx |-> clientReqIdx[c] + 1]]
    /\ IF clientLeader[c] = Nil THEN
        clientLeader' = [clientLeader EXCEPT ![c] = 
            CHOOSE s \in Server: TRUE]
    ELSE UNCHANGED clientLeader
    /\ net' = net \cup 
        [mtype |-> IF clientReq'[c].type = Put THEN "cpq" ELSE "cgq",
         mcmd |-> clientReq'[c],
         msource |-> c, mdest |-> clientLeader'[c]]
    /\ UNCHANGED <<serverState, currentTerm, votedFor, log, commitIndex, 
                  nextIndex, matchIndex, votesResponded, votesGranted, leader, 
                  sm, smDomain, clientResp, netEnabled, fd>>

ClientHandleResponse(c, m) ==
    /\ m \in net
    /\ m.mdest = c
    /\ m.mtype \in {"cpp", "cgp"}
    /\ clientResp' = [clientResp EXCEPT ![c] = m.mresponse]
    /\ IF m.msuccess THEN
        clientLeader' = [clientLeader EXCEPT ![c] = m.mleaderHint]
    ELSE
        clientLeader' = [clientLeader EXCEPT ![c] = Nil]
    /\ UNCHANGED <<serverState, currentTerm, votedFor, log, commitIndex, 
                  nextIndex, matchIndex, votesResponded, votesGranted, leader, 
                  sm, smDomain, clientReq, clientReqIdx, netEnabled, fd>>

Next == 
    \/ \E s \in Server: ServerRequestVote(s)
    \/ \E s \in Server, m \in net: ServerHandleRequestVoteRequest(s, m)
    \/ \E s \in Server, m \in net: ServerHandleRequestVoteResponse(s, m)
    \/ \E s \in Server, m \in net: ServerHandleAppendEntriesRequest(s, m)
    \/ \E s \in Server, m \in net: ServerHandleAppendEntriesResponse(s, m)
    \/ \E s \in Server, m \in net: ServerHandleClientRequest(s, m)
    \/ \E s \in Server: LeaderAdvanceCommitIndex(s)
    \/ \E c \in Client: ClientSendRequest(c)
    \/ \E c \in Client, m \in net: ClientHandleResponse(c, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====