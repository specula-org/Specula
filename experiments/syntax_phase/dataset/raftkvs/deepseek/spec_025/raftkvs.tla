---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, AllStrings, MaxNodeFail, LeaderTimeoutReset, ExploreFail, Debug, LogPop, LogConcat

VARIABLES
    serverState,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    leader,
    sm,
    smDomain,
    net,
    netEnabled,
    fd,
    votesResponded,
    votesGranted,
    leaderTimeout,
    appendEntriesCh,
    becomeLeaderCh,
    clientLeader,
    clientReq,
    clientResp,
    clientReqIdx,
    reqCh,
    respCh,
    timeout

vars == <<
    serverState,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    leader,
    sm,
    smDomain,
    net,
    netEnabled,
    fd,
    votesResponded,
    votesGranted,
    leaderTimeout,
    appendEntriesCh,
    becomeLeaderCh,
    clientLeader,
    clientReq,
    clientResp,
    clientReqIdx,
    reqCh,
    respCh,
    timeout
>>

ServerSet == 1..NumServers
ClientSet == (NumServers*6 + 1)..(NumServers*6 + NumClients)
NodeSet == ServerSet \union ClientSet

Nil == 0
Put == "put"
Get == "get"
Follower == "follower"
Candidate == "candidate"
Leader == "leader"
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

IsQuorum(S) == (Cardinality(S) * 2) > NumServers

LastTerm(logSeq) == IF Len(logSeq) = 0 THEN 0 ELSE logSeq[Len(logSeq)].term

FindMaxAgreeIndex(logSeq, i, matchIndexMap) ==
    LET indices == {index \in 1..Len(logSeq): 
                      IsQuorum({i} \union {s \in ServerSet: matchIndexMap[s] >= index})}
    IN IF indices = {} THEN Nil ELSE Max(indices)

ApplyLogEntry(entry, stateMachine, domain) ==
    IF entry.cmd.type = Put THEN
        <<stateMachine @@ (entry.cmd.key :> entry.cmd.value), domain \union {entry.cmd.key}>>
    ELSE <<stateMachine, domain>>

RECURSIVE ApplyLog(_, _, _, _, _)
ApplyLog(logSeq, start, end, stateMachine, domain) ==
    IF start > end THEN <<stateMachine, domain>>
    ELSE LET result == ApplyLogEntry(logSeq[start], stateMachine, domain)
         IN ApplyLog(logSeq, start+1, end, result[1], result[2])

AllReqs ==
    [type : {Put}, key : AllStrings, value : AllStrings] \union
    [type : {Get}, key : AllStrings]

TypeInvariant ==
    /\ serverState \in [ServerSet -> {Follower, Candidate, Leader}]
    /\ currentTerm \in [ServerSet -> Nat]
    /\ votedFor \in [ServerSet -> ServerSet \union {Nil}]
    /\ log \in [ServerSet -> Seq([term: Nat, cmd: AllReqs, client: ClientSet])]
    /\ commitIndex \in [ServerSet -> Nat]
    /\ nextIndex \in [ServerSet -> [ServerSet -> Nat]]
    /\ matchIndex \in [ServerSet -> [ServerSet -> Nat]]
    /\ leader \in [ServerSet -> ServerSet \union {Nil}]
    /\ sm \in [ServerSet -> [AllStrings -> AllStrings \union {Nil}]]
    /\ smDomain \in [ServerSet -> SUBSET AllStrings]
    /\ net \in [NodeSet -> Seq([mtype: {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse, ClientPutRequest, ClientPutResponse, ClientGetRequest, ClientGetResponse}, mterm: Nat, mlastLogTerm: Nat, mlastLogIndex: Nat, mprevLogIndex: Nat, mprevLogTerm: Nat, mentries: Seq({}), mcommitIndex: Nat, mvoteGranted: BOOLEAN, msuccess: BOOLEAN, mmatchIndex: Nat, mcmd: AllReqs, mresponse: [idx: Nat, key: AllStrings, value: AllStrings \union {Nil}, ok: BOOLEAN], mleaderHint: ServerSet \union {Nil}, msource: NodeSet, mdest: NodeSet])]
    /\ netEnabled \in [NodeSet -> BOOLEAN]
    /\ fd \in [NodeSet -> BOOLEAN]
    /\ votesResponded \in [ServerSet -> SUBSET ServerSet]
    /\ votesGranted \in [ServerSet -> SUBSET ServerSet]
    /\ leaderTimeout \in [ServerSet -> BOOLEAN]
    /\ appendEntriesCh \in [ServerSet -> BOOLEAN]
    /\ becomeLeaderCh \in [ServerSet -> BOOLEAN]
    /\ clientLeader \in [ClientSet -> ServerSet \union {Nil}]
    /\ clientReq \in [ClientSet -> AllReqs]
    /\ clientResp \in [ClientSet -> [idx: Nat, key: AllStrings, value: AllStrings \union {Nil}, ok: BOOLEAN]]
    /\ clientReqIdx \in [ClientSet -> Nat]
    /\ reqCh \in [ClientSet -> AllReqs]
    /\ respCh \in [ClientSet -> [idx: Nat, key: AllStrings, value: AllStrings \union {Nil}, ok: BOOLEAN]]
    /\ timeout \in [ClientSet -> BOOLEAN]

Init ==
    /\ serverState = [s \in ServerSet |-> Follower]
    /\ currentTerm = [s \in ServerSet |-> 0]
    /\ votedFor = [s \in ServerSet |-> Nil]
    /\ log = [s \in ServerSet |-> <<>>]
    /\ commitIndex = [s \in ServerSet |-> 0]
    /\ nextIndex = [s \in ServerSet |-> [t \in ServerSet |-> 1]]
    /\ matchIndex = [s \in ServerSet |-> [t \in ServerSet |-> 0]]
    /\ leader = [s \in ServerSet |-> Nil]
    /\ sm = [s \in ServerSet |-> [k \in AllStrings |-> Nil]]
    /\ smDomain = [s \in ServerSet |-> {}]
    /\ net = [n \in NodeSet |-> <<>>]
    /\ netEnabled = [n \in NodeSet |-> TRUE]
    /\ fd = [n \in NodeSet |-> FALSE]
    /\ votesResponded = [s \in ServerSet |-> {}]
    /\ votesGranted = [s \in ServerSet |-> {}]
    /\ leaderTimeout = [s \in ServerSet |-> FALSE]
    /\ appendEntriesCh = [s \in ServerSet |-> FALSE]
    /\ becomeLeaderCh = [s \in ServerSet |-> FALSE]
    /\ clientLeader = [c \in ClientSet |-> Nil]
    /\ clientReq = [c \in ClientSet |-> [type |-> Get, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil]]
    /\ clientResp = [c \in ClientSet |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE]]
    /\ clientReqIdx = [c \in ClientSet |-> 0]
    /\ reqCh = [c \in ClientSet |-> [type |-> Get, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil]]
    /\ respCh = [c \in ClientSet |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE]]
    /\ timeout = [c \in ClientSet |-> FALSE]

ServerTimeout(s) ==
    /\ serverState[s] \in {Follower, Candidate}
    /\ leaderTimeout[s]
    /\ netEnabled[s]
    /\ serverState' = [serverState EXCEPT ![s] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesResponded' = [votesResponded EXCEPT ![s] = {s}]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain, net, netEnabled, fd, appendEntriesCh, becomeLeaderCh, clientLeader, clientReq, clientResp, clientReqIdx, reqCh, respCh, timeout>>

HandleRequestVoteRequest(s, m) ==
    /\ m.mterm > currentTerm[s]
    /\ serverState' = [serverState EXCEPT ![s] = Follower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ \/ m.mlastLogTerm > LastTerm(log[s])
       \/ /\ m.mlastLogTerm = LastTerm(log[s])
          /\ m.mlastLogIndex >= Len(log[s])
    /\ votedFor' = [votedFor EXCEPT ![s] = m.msource]
    /\ net' = [net EXCEPT ![m.msource] = Append(@, [mtype |-> RequestVoteResponse, mterm |-> currentTerm[s], mvoteGranted |-> TRUE, msource |-> s, mdest |-> m.msource])]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain, netEnabled, fd, votesResponded, votesGranted, leaderTimeout, appendEntriesCh, becomeLeaderCh, clientLeader, clientReq, clientResp, clientReqIdx, reqCh, respCh, timeout>>

HandleAppendEntriesRequest(s, m) ==
    /\ m.mterm > currentTerm[s]
    /\ serverState' = [serverState EXCEPT ![s] = Follower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ m.mterm = currentTerm[s]
    /\ leader' = [leader EXCEPT ![s] = m.msource]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![s] = FALSE]
    /\ serverState[s] = Candidate
    /\ serverState' = [serverState EXCEPT ![s] = Follower]
    /\ \/ m.mprevLogIndex = 0
       \/ /\ m.mprevLogIndex > 0
          /\ m.mprevLogIndex <= Len(log[s])
          /\ m.mprevLogTerm = log[s][m.mprevLogIndex].term
    /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, m.mprevLogIndex) \o m.mentries]
    /\ commitIndex' = [commitIndex EXCEPT ![s] = IF commitIndex[s] > m.mcommitIndex THEN commitIndex[s] ELSE m.mcommitIndex]
    /\ LET result == ApplyLog(log[s], commitIndex[s] + 1, m.mcommitIndex, sm[s], smDomain[s])
        IN /\ sm' = [sm EXCEPT ![s] = result[1]]
           /\ smDomain' = [smDomain EXCEPT ![s] = result[2]]
    /\ net' = [net EXCEPT ![m.msource] = Append(@, [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[s], msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(m.mentries), msource |-> s, mdest |-> m.msource])]
    /\ UNCHANGED <<nextIndex, matchIndex, netEnabled, fd, votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh, clientLeader, clientReq, clientResp, clientReqIdx, reqCh, respCh, timeout>>

HandleClientRequest(s, m) ==
    /\ serverState[s] = Leader
    /\ LET entry == [term |-> currentTerm[s], cmd |-> m.mcmd, client |-> m.msource]
        IN log' = [log EXCEPT ![s] = Append(@, entry)]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<serverState, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, leader, sm, smDomain, net, netEnabled, fd, votesResponded, votesGranted, leaderTimeout, becomeLeaderCh, clientLeader, clientReq, clientResp, clientReqIdx, reqCh, respCh, timeout>>

Next ==
    \/ \E s \in ServerSet: ServerTimeout(s)
    \/ \E s \in ServerSet, m \in DOMAIN net[s]:
        /\ netEnabled[s]
        /\ ~fd[s]
        /\ \/ HandleRequestVoteRequest(s, net[s][m])
           \/ HandleAppendEntriesRequest(s, net[s][m])
           \/ HandleClientRequest(s, net[s][m])
    \/ \E c \in ClientSet: TRUE

Spec == Init /\ [][Next]_vars

====