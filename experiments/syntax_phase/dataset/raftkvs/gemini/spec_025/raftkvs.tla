---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    AllStrings,
    LeaderTimeoutReset,
    ExploreFail,
    MaxNodeFail,
    Debug,
    LogPop,
    LogConcat

ASSUME
    /\ NumServers \in 1..Nat
    /\ NumClients \in 1..Nat
    /\ \A s \in AllStrings : IsString(s)
    /\ LeaderTimeoutReset \in BOOLEAN
    /\ ExploreFail \in BOOLEAN
    /\ MaxNodeFail \in 0..NumServers
    /\ Debug \in BOOLEAN

Nil == 0
Min(s) == CHOOSE e \in s : \A e2 \in s : e <= e2
Max(s) == CHOOSE e \in s : \A e2 \in s : e >= e2

ServerSet == 1..NumServers
ClientSet == (NumServers + 1)..(NumServers + NumClients)
NodeSet == ServerSet \cup ClientSet

IsQuorum(s) == Cardinality(s) * 2 > NumServers

Put == "put"
Get == "get"

AllReqs ==
    {[type |-> Put, key |-> k, value |-> v] : k \in AllStrings, v \in AllStrings} \cup
    {[type |-> Get, key |-> k] : k \in AllStrings}

Follower == "follower"
Candidate == "candidate"
Leader == "leader"
ServerState == {Follower, Candidate, Leader}

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

MessageTypes == {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse,
                  ClientPutRequest, ClientPutResponse, ClientGetRequest, ClientGetResponse}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE (xlog[Len(xlog)]).term

ApplyLogEntry(xentry, xsm, xsmDomain) ==
    LET cmd == xentry.cmd IN
    IF cmd.type = Put THEN
        << [xsm EXCEPT ![cmd.key] = cmd.value], xsmDomain \cup {cmd.key} >>
    ELSE
        << xsm, xsmDomain >>

ApplyLog(xlog, start, end, xsm, xsmDomain) ==
    IF start > end THEN
        << xsm, xsmDomain >>
    ELSE
        LET result == ApplyLogEntry(xlog[start], xsm, xsmDomain) IN
        ApplyLog(xlog, start + 1, end, result[1], result[2])

FindMaxAgreeIndex(logLocal, i, matchIndex) ==
    LET Rec(index) ==
        IF index = 0 THEN Nil
        ELSE
            IF IsQuorum({i} \cup {k \in ServerSet : matchIndex[k] >= index})
            THEN index
            ELSE Rec(index - 1)
    IN Rec(Len(logLocal))

VARIABLES
    pc,
    net,
    netEnabled,
    fd,
    state,
    currentTerm,
    log,
    plog,
    commitIndex,
    nextIndex,
    matchIndex,
    votedFor,
    votesResponded,
    votesGranted,
    leader,
    sm,
    smDomain,
    leaderTimeout,
    appendEntriesCh,
    becomeLeaderCh,
    reqCh,
    respCh,
    timeout,
    m,
    idx,
    newCommitIndex,
    client_leader,
    client_req,
    client_resp,
    client_reqIdx

vars == << pc, net, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex,
           matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain,
           leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout,
           m, idx, newCommitIndex, client_leader, client_req, client_resp, client_reqIdx >>

ServerRequestVoteSet == 1..NumServers
ServerAppendEntriesSet == (NumServers + 1)..(2*NumServers)
ServerAdvanceCommitIndexSet == (2*NumServers + 1)..(3*NumServers)
ServerBecomeLeaderSet == (3*NumServers + 1)..(4*NumServers)
ServerCrasherSet == IF ExploreFail THEN (4*NumServers + 1)..(4*NumServers + MaxNodeFail) ELSE {}
ServerHandlerSet == (5*NumServers + 1)..(6*NumServers)

ProcessSet == ServerRequestVoteSet \cup ServerAppendEntriesSet \cup ServerAdvanceCommitIndexSet \cup ServerBecomeLeaderSet \cup ServerCrasherSet \cup ServerHandlerSet \cup ClientSet

MapSrvId(id) ==
    IF id \in ServerRequestVoteSet THEN id
    ELSE IF id \in ServerAppendEntriesSet THEN id - NumServers
    ELSE IF id \in ServerAdvanceCommitIndexSet THEN id - 2*NumServers
    ELSE IF id \in ServerBecomeLeaderSet THEN id - 3*NumServers
    ELSE IF id \in ServerCrasherSet THEN id - 4*NumServers
    ELSE id - 5*NumServers

Init ==
    /\ state = [i \in ServerSet |-> Follower]
    /\ currentTerm = [i \in ServerSet |-> 0]
    /\ votedFor = [i \in ServerSet |-> Nil]
    /\ log = [i \in ServerSet |-> <<>>]
    /\ plog = [i \in ServerSet |-> [cmd |-> "", entries |-> <<>>]]
    /\ commitIndex = [i \in ServerSet |-> 0]
    /\ leader = [i \in ServerSet |-> Nil]
    /\ votesResponded = [i \in ServerSet |-> {}]
    /\ votesGranted = [i \in ServerSet |-> {}]
    /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
    /\ matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]
    /\ sm = [i \in ServerSet |-> [s \in AllStrings |-> ""]]
    /\ smDomain = [i \in ServerSet |-> {}]
    /\ net = [i \in NodeSet |-> [mtype |-> "", msource |-> Nil, mdest |-> Nil]]
    /\ netEnabled = [i \in ServerSet |-> TRUE]
    /\ fd = [i \in ServerSet |-> FALSE]
    /\ leaderTimeout = TRUE
    /\ appendEntriesCh = [i \in ServerSet |-> FALSE]
    /\ becomeLeaderCh = [i \in ServerSet |-> FALSE]
    /\ reqCh = CHOOSE req \in AllReqs : req
    /\ respCh = [mtype |-> "", msuccess |-> FALSE, mresponse |-> [idx |-> 0, key |-> ""], mleaderHint |-> Nil]
    /\ timeout = FALSE
    /\ m = [i \in ServerSet |-> [mtype |-> "", msource |-> Nil, mdest |-> Nil]]
    /\ idx = [i \in ProcessSet |-> 1]
    /\ newCommitIndex = [i \in ServerSet |-> 0]
    /\ client_leader = [i \in ClientSet |-> Nil]
    /\ client_req = [i \in ClientSet |-> [type |-> "", key |-> ""]]
    /\ client_resp = [i \in ClientSet |-> [mtype |-> "", mdest |-> Nil, mresponse |-> [idx |-> 0], msuccess |-> FALSE, mleaderHint |-> Nil]]
    /\ client_reqIdx = [i \in ClientSet |-> 0]
    /\ pc = [i \in ProcessSet |->
                CASE i \in ServerHandlerSet -> "serverLoop"
                   [] i \in ServerRequestVoteSet -> "serverRequestVoteLoop"
                   [] i \in ServerAppendEntriesSet -> "serverAppendEntriesLoop"
                   [] i \in ServerAdvanceCommitIndexSet -> "serverAdvanceCommitIndexLoop"
                   [] i \in ServerBecomeLeaderSet -> "serverBecomeLeaderLoop"
                   [] i \in ClientSet -> "clientLoop"
                   [] i \in ServerCrasherSet -> "serverCrash"]

\* Server message handler
serverLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "serverLoop"
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ net[i].mdest = i
    /\ m' = [m EXCEPT ![i] = net[i]]
    /\ pc' = [pc EXCEPT ![self] = "handleMsg"]
    /\ UNCHANGED << vars EXCEPT <<pc, m>> >>

handleMsg(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "handleMsg"
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ LET msg == m[i] IN
       CASE msg.mtype = RequestVoteRequest ->
            LET
                term' = IF msg.mterm > currentTerm[i] THEN msg.mterm ELSE currentTerm[i]
                state' = IF msg.mterm > currentTerm[i] THEN Follower ELSE state[i]
                votedFor_pre' = IF msg.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
                leader' = IF msg.mterm > currentTerm[i] THEN Nil ELSE leader[i]
                logOK = \/ msg.mlastLogTerm > LastTerm(log[i])
                        \/ /\ msg.mlastLogTerm = LastTerm(log[i])
                           /\ msg.mlastLogIndex >= Len(log[i])
                grant = /\ msg.mterm = term'
                        /\ logOK
                        /\ votedFor_pre' \in {Nil, msg.msource}
                votedFor' = IF grant THEN msg.msource ELSE votedFor_pre'
                response = [mtype |-> RequestVoteResponse, mterm |-> term', mvoteGranted |-> grant, msource |-> i, mdest |-> msg.msource]
            IN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = term']
                /\ state' = [state EXCEPT ![i] = state']
                /\ votedFor' = [votedFor EXCEPT ![i] = votedFor']
                /\ leader' = [leader EXCEPT ![i] = leader']
                /\ \/ net' = [net EXCEPT ![msg.msource] = response]
                   \/ fd[msg.msource]
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                /\ UNCHANGED << vars EXCEPT <<pc, net, currentTerm, state, votedFor, leader>> >>

         [] msg.mtype = RequestVoteResponse ->
            IF msg.mterm < currentTerm[i] THEN
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                /\ UNCHANGED << vars EXCEPT <<pc>> >>
            ELSE
                LET
                    term' = IF msg.mterm > currentTerm[i] THEN msg.mterm ELSE currentTerm[i]
                    state' = IF msg.mterm > currentTerm[i] THEN Follower ELSE state[i]
                    votedFor' = IF msg.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
                    leader' = IF msg.mterm > currentTerm[i] THEN Nil ELSE leader[i]
                    votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {msg.msource}]
                    votesGranted' = IF msg.mvoteGranted THEN [votesGranted EXCEPT ![i] = votesGranted[i] \cup {msg.msource}] ELSE votesGranted
                    becomeLeader = /\ state' = Candidate
                                   /\ IsQuorum(votesGranted'[i])
                IN
                    /\ currentTerm' = [currentTerm EXCEPT ![i] = term']
                    /\ state' = [state EXCEPT ![i] = state']
                    /\ votedFor' = [votedFor EXCEPT ![i] = votedFor']
                    /\ leader' = [leader EXCEPT ![i] = leader']
                    /\ votesResponded' = votesResponded'
                    /\ votesGranted' = votesGranted'
                    /\ leaderTimeout' = IF msg.mvoteGranted THEN LeaderTimeoutReset ELSE leaderTimeout
                    /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = becomeLeader]
                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                    /\ UNCHANGED << vars EXCEPT <<pc, currentTerm, state, votedFor, leader, votesResponded, votesGranted, leaderTimeout, becomeLeaderCh>> >>

         [] msg.mtype = AppendEntriesRequest ->
            LET
                term' = IF msg.mterm > currentTerm[i] THEN msg.mterm ELSE currentTerm[i]
                state_pre' = IF msg.mterm > currentTerm[i] THEN Follower ELSE state[i]
                votedFor' = IF msg.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
                leader_pre' = IF msg.mterm > currentTerm[i] THEN Nil ELSE leader[i]
                logOK = \/ msg.mprevLogIndex = 0
                        \/ /\ msg.mprevLogIndex > 0
                           /\ msg.mprevLogIndex <= Len(log[i])
                           /\ (log[i][msg.mprevLogIndex]).term = msg.mprevLogTerm
                leader' = IF msg.mterm = term' THEN msg.msource ELSE leader_pre'
                state' = IF /\ msg.mterm = term' /\ state_pre' = Candidate THEN Follower ELSE state_pre'
                success = /\ msg.mterm = term'
                          /\ state' = Follower
                          /\ logOK
                response_term = currentTerm[i]
            IN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = term']
                /\ votedFor' = [votedFor EXCEPT ![i] = votedFor']
                /\ state' = [state EXCEPT ![i] = state']
                /\ leader' = [leader EXCEPT ![i] = leader']
                /\ leaderTimeout' = IF msg.mterm = term' THEN LeaderTimeoutReset ELSE leaderTimeout
                /\ IF success THEN
                    LET
                        newLog = SubSeq(log[i], 1, msg.mprevLogIndex) \o msg.mentries
                        newCommitIndex = Max({commitIndex[i], msg.mcommitIndex})
                        result = ApplyLog(newLog, commitIndex[i] + 1, newCommitIndex, sm[i], smDomain[i])
                    IN
                        /\ log' = [log EXCEPT ![i] = newLog]
                        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                        /\ sm' = [sm EXCEPT ![i] = result[1]]
                        /\ smDomain' = [smDomain EXCEPT ![i] = result[2]]
                        /\ LET resp = [mtype |-> AppendEntriesResponse, mterm |-> term', msuccess |-> TRUE,
                                       mmatchIndex |-> msg.mprevLogIndex + Len(msg.mentries), msource |-> i, mdest |-> msg.msource]
                           IN \/ net' = [net EXCEPT ![msg.msource] = resp]
                              \/ fd[msg.msource]
                        /\ UNCHANGED <<plog, votesResponded, votesGranted, nextIndex, matchIndex, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, m, idx, newCommitIndex, client_leader, client_req, client_resp, client_reqIdx>>
                   ELSE
                       /\ LET resp = [mtype |-> AppendEntriesResponse, mterm |-> response_term, msuccess |-> FALSE,
                                      mmatchIndex |-> 0, msource |-> i, mdest |-> msg.msource]
                          IN \/ net' = [net EXCEPT ![msg.msource] = resp]
                             \/ fd[msg.msource]
                       /\ UNCHANGED <<log, plog, commitIndex, sm, smDomain, votesResponded, votesGranted, nextIndex, matchIndex, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, m, idx, newCommitIndex, client_leader, client_req, client_resp, client_reqIdx>>
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]

         [] msg.mtype = AppendEntriesResponse ->
            IF msg.mterm < currentTerm[i] THEN
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                /\ UNCHANGED << vars EXCEPT <<pc>> >>
            ELSE
                LET
                    term' = IF msg.mterm > currentTerm[i] THEN msg.mterm ELSE currentTerm[i]
                    state' = IF msg.mterm > currentTerm[i] THEN Follower ELSE state[i]
                    votedFor' = IF msg.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
                    leader' = IF msg.mterm > currentTerm[i] THEN Nil ELSE leader[i]
                IN
                    /\ currentTerm' = [currentTerm EXCEPT ![i] = term']
                    /\ state' = [state EXCEPT ![i] = state']
                    /\ votedFor' = [votedFor EXCEPT ![i] = votedFor']
                    /\ leader' = [leader EXCEPT ![i] = leader']
                    /\ leaderTimeout' = LeaderTimeoutReset
                    /\ IF msg.msuccess THEN
                        /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![msg.msource] = msg.mmatchIndex + 1]]
                        /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![msg.msource] = msg.mmatchIndex]]
                        /\ UNCHANGED <<log, plog, commitIndex, sm, smDomain, votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, m, idx, newCommitIndex, client_leader, client_req, client_resp, client_reqIdx, net>>
                    ELSE
                        /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![msg.msource] = Max({1, nextIndex[i][msg.msource] - 1})]]
                        /\ UNCHANGED <<matchIndex, log, plog, commitIndex, sm, smDomain, votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, m, idx, newCommitIndex, client_leader, client_req, client_resp, client_reqIdx, net>>
                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]

         [] msg.mtype \in {ClientPutRequest, ClientGetRequest} ->
            IF state[i] = Leader THEN
                LET entry = [term |-> currentTerm[i], cmd |-> msg.mcmd, client |-> msg.msource] IN
                /\ log' = [log EXCEPT ![i] = Append(log[i], entry)]
                /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> <<entry>>]]
                /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                /\ UNCHANGED << vars EXCEPT <<pc, log, plog, appendEntriesCh>> >>
            ELSE
                LET
                    respType = IF msg.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
                    resp = [mtype |-> respType, msuccess |-> FALSE,
                            mresponse |-> [idx |-> msg.mcmd.idx, key |-> msg.mcmd.key],
                            mleaderHint |-> leader[i], msource |-> i, mdest |-> msg.msource]
                IN
                    /\ net' = [net EXCEPT ![msg.msource] = resp]
                    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
                    /\ UNCHANGED << vars EXCEPT <<pc, net>> >>
         [] OTHER ->
            /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
            /\ UNCHANGED << vars EXCEPT <<pc>> >>

\* Server timeout and election process
serverRequestVoteLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "serverRequestVoteLoop"
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ leaderTimeout
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ idx' = [idx EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
    /\ UNCHANGED << vars EXCEPT <<pc, state, currentTerm, votedFor, votesResponded, votesGranted, leader, idx>> >>

requestVoteLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "requestVoteLoop"
    /\ IF idx[self] <= NumServers THEN
        /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
        /\ IF idx[self] # i THEN
            /\ LET j = idx[self] IN
               LET msg = [mtype |-> RequestVoteRequest, mterm |-> currentTerm[i] + 1,
                          mlastLogTerm |-> LastTerm(log[i]), mlastLogIndex |-> Len(log[i]),
                          msource |-> i, mdest |-> j]
               IN \/ net' = [net EXCEPT ![j] = msg]
                  \/ fd[j]
        /\ ELSE
            /\ UNCHANGED <<net>>
        /\ idx' = [idx EXCEPT ![self] = idx[self] + 1]
        /\ pc' = [pc EXCEPT ![self] = "requestVoteLoop"]
        /\ UNCHANGED << vars EXCEPT <<pc, idx, net>> >>
    /\ ELSE
        /\ pc' = [pc EXCEPT ![self] = "serverRequestVoteLoop"]
        /\ UNCHANGED << vars EXCEPT <<pc>> >>

\* Server sending AppendEntries
serverAppendEntriesLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "serverAppendEntriesLoop"
    /\ appendEntriesCh[i]
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ state[i] = Leader
    /\ idx' = [idx EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
    /\ UNCHANGED << vars EXCEPT <<pc, idx>> >>

appendEntriesLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "appendEntriesLoop"
    /\ state[i] = Leader
    /\ idx[self] <= NumServers
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ IF idx[self] # i THEN
        /\ LET
            j = idx[self]
            prevLogIndex = nextIndex[i][j] - 1
            prevLogTerm = IF prevLogIndex > 0 THEN (log[i][prevLogIndex]).term ELSE 0
            entries = SubSeq(log[i], nextIndex[i][j], Len(log[i]))
            msg = [mtype |-> AppendEntriesRequest, mterm |-> currentTerm[i],
                   mprevLogIndex |-> prevLogIndex, mprevLogTerm |-> prevLogTerm,
                   mentries |-> entries, mcommitIndex |-> commitIndex[i],
                   msource |-> i, mdest |-> j]
           IN \/ net' = [net EXCEPT ![j] = msg]
              \/ fd[j]
    /\ ELSE
        /\ UNCHANGED <<net>>
    /\ idx' = [idx EXCEPT ![self] = idx[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "appendEntriesLoop"]
    /\ UNCHANGED << vars EXCEPT <<pc, idx, net>> >>

\* Server advancing commit index
serverAdvanceCommitIndexLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "serverAdvanceCommitIndexLoop"
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ state[i] = Leader
    /\ LET
        maxAgreeIndex = FindMaxAgreeIndex(log[i], i, matchIndex[i])
        nCommitIndex = IF /\ maxAgreeIndex # Nil
                          /\ (log[i][maxAgreeIndex]).term = currentTerm[i]
                       THEN maxAgreeIndex
                       ELSE commitIndex[i]
       IN newCommitIndex' = [newCommitIndex EXCEPT ![i] = nCommitIndex]
    /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
    /\ UNCHANGED << vars EXCEPT <<pc, newCommitIndex>> >>

applyLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "applyLoop"
    /\ commitIndex[i] < newCommitIndex[i]
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ LET
        newCI = commitIndex[i] + 1
        entry = log[i][newCI]
        cmd = entry.cmd
        respType = IF cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
        result = ApplyLogEntry(entry, sm[i], smDomain[i])
        reqOk = cmd.key \in result[2]
        resp = [mtype |-> respType, msuccess |-> TRUE,
                mresponse |-> [idx |-> cmd.idx, key |-> cmd.key,
                               value |-> IF reqOk THEN result[1][cmd.key] ELSE Nil,
                               ok |-> reqOk],
                mleaderHint |-> i, msource |-> i, mdest |-> entry.client]
       IN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCI]
        /\ sm' = [sm EXCEPT ![i] = result[1]]
        /\ smDomain' = [smDomain EXCEPT ![i] = result[2]]
        /\ net' = [net EXCEPT ![entry.client] = resp]
        /\ pc' = [pc EXCEPT ![self] = "applyLoop"]
        /\ UNCHANGED << vars EXCEPT <<pc, commitIndex, sm, smDomain, net>> >>

\* Server becoming leader
serverBecomeLeaderLoop(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "serverBecomeLeaderLoop"
    /\ becomeLeaderCh[i]
    /\ IF ExploreFail THEN netEnabled[i] ELSE TRUE
    /\ state[i] = Candidate
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "serverBecomeLeaderLoop"]
    /\ UNCHANGED << vars EXCEPT <<pc, state, leader, nextIndex, matchIndex, appendEntriesCh>> >>

\* Client process
clientLoop(self) ==
    /\ pc[self] = "clientLoop"
    /\ client_req' = [client_req EXCEPT ![self] = reqCh]
    /\ client_reqIdx' = [client_reqIdx EXCEPT ![self] = client_reqIdx[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "sndReq"]
    /\ UNCHANGED << vars EXCEPT <<pc, client_req, client_reqIdx>> >>

sndReq(self) ==
    /\ pc[self] = "sndReq"
    /\ LET
        leader_to_use = IF client_leader[self] = Nil
                        THEN CHOOSE s \in ServerSet : TRUE
                        ELSE client_leader[self]
        req = client_req[self]
        reqType = IF req.type = Put THEN ClientPutRequest ELSE ClientGetRequest
        cmd = IF req.type = Put
              THEN [idx |-> client_reqIdx[self], type |-> Put, key |-> req.key, value |-> req.value]
              ELSE [idx |-> client_reqIdx[self], type |-> Get, key |-> req.key]
        msg = [mtype |-> reqType, mcmd |-> cmd, msource |-> self, mdest |-> leader_to_use]
       IN
        /\ client_leader' = [client_leader EXCEPT ![self] = leader_to_use]
        /\ \/ net' = [net EXCEPT ![leader_to_use] = msg]
           \/ fd[leader_to_use]
        /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
        /\ UNCHANGED << vars EXCEPT <<pc, client_leader, net>> >>

rcvResp(self) ==
    /\ pc[self] = "rcvResp"
    /\ \/ /\ net[self].mdest = self
          /\ client_resp' = [client_resp EXCEPT ![self] = net[self]]
          /\ IF net[self].mresponse.idx # client_reqIdx[self] THEN
                /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                /\ UNCHANGED << vars EXCEPT <<pc, client_resp>> >>
             ELSE
                /\ client_leader' = [client_leader EXCEPT ![self] = net[self].mleaderHint]
                /\ IF ~net[self].msuccess THEN
                    /\ pc' = [pc EXCEPT ![self] = "sndReq"]
                    /\ UNCHANGED << vars EXCEPT <<pc, client_leader, client_resp>> >>
                ELSE
                    /\ respCh' = net[self]
                    /\ pc' = [pc EXCEPT ![self] = "clientLoop"]
                    /\ UNCHANGED << vars EXCEPT <<pc, client_leader, client_resp, respCh>> >>
       \/ /\ \/ fd[client_leader[self]]
             \/ timeout
          /\ client_leader' = [client_leader EXCEPT ![self] = Nil]
          /\ pc' = [pc EXCEPT ![self] = "sndReq"]
          /\ UNCHANGED << vars EXCEPT <<pc, client_leader>> >>

\* Server crasher process
serverCrash(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "serverCrash"
    /\ netEnabled' = [netEnabled EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "fdUpdate"]
    /\ UNCHANGED << vars EXCEPT <<pc, netEnabled>> >>

fdUpdate(self) ==
    LET i == MapSrvId(self) IN
    /\ pc[self] = "fdUpdate"
    /\ fd' = [fd EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << vars EXCEPT <<pc, fd>> >>

AServer(self) == serverLoop(self) \/ handleMsg(self)
AServerRequestVote(self) == serverRequestVoteLoop(self) \/ requestVoteLoop(self)
AServerAppendEntries(self) == serverAppendEntriesLoop(self) \/ appendEntriesLoop(self)
AServerAdvanceCommitIndex(self) == serverAdvanceCommitIndexLoop(self) \/ applyLoop(self)
AServerBecomeLeader(self) == serverBecomeLeaderLoop(self)
AClient(self) == clientLoop(self) \/ sndReq(self) \/ rcvResp(self)
AServerCrasher(self) == serverCrash(self) \/ fdUpdate(self)

Next ==
    \/ \E i \in ServerHandlerSet: AServer(i)
    \/ \E i \in ServerRequestVoteSet: AServerRequestVote(i)
    \/ \E i \in ServerAppendEntriesSet: AServerAppendEntries(i)
    \/ \E i \in ServerAdvanceCommitIndexSet: AServerAdvanceCommitIndex(i)
    \/ \E i \in ServerBecomeLeaderSet: AServerBecomeLeader(i)
    \/ \E i \in ClientSet: AClient(i)
    \/ \E i \in ServerCrasherSet: AServerCrasher(i)

Spec == Init /\ [][Next]_vars

Fairness ==
    /\ \A i \in ServerHandlerSet: WF_vars(AServer(i))
    /\ \A i \in ServerRequestVoteSet: WF_vars(AServerRequestVote(i))
    /\ \A i \in ServerAppendEntriesSet: WF_vars(AServerAppendEntries(i))
    /\ \A i \in ServerAdvanceCommitIndexSet: WF_vars(AServerAdvanceCommitIndex(i))
    /\ \A i \in ServerBecomeLeaderSet: WF_vars(AServerBecomeLeader(i))
    /\ \A i \in ClientSet: WF_vars(AClient(i))
    /\ \A i \in ServerCrasherSet: WF_vars(AServerCrasher(i))

=============================================================================
