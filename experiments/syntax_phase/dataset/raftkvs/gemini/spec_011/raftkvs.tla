---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    AllStrings,
    NilValue,
    \* Constants for KV commands
    Put, Get

ASSUME
    /\ NumServers \in 1..Nat
    /\ NumClients \in 1..Nat
    /\ Put = "put"
    /\ Get = "get"

ServerSet == 1..NumServers
ClientSet == (NumServers + 1)..(NumServers + NumClients)
NodeSet == ServerSet \cup ClientSet

StateFollower == "follower"
StateCandidate == "candidate"
StateLeader == "leader"
ServerStates == {StateFollower, StateCandidate, StateLeader}

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

MessageTypes == {
    RequestVoteRequest, RequestVoteResponse,
    AppendEntriesRequest, AppendEntriesResponse,
    ClientPutRequest, ClientPutResponse,
    ClientGetRequest, ClientGetResponse
}

\* Helper operators
IsQuorum(S) == Cardinality(S) * 2 > NumServers
LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)].term
LastIndex(lg) == Len(lg)

VARIABLES
    \* Global state
    net,
    netEnabled,
    fd,

    \* Per-server state
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    leader,

    \* Leader-specific state
    nextIndex,
    matchIndex,

    \* Candidate-specific state
    votesGranted,

    \* Per-client state
    client_leader,
    client_reqIdx,
    client_req,
    client_resp,
    client_timeout

vars == <<
    net, netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
    lastApplied, leader, nextIndex, matchIndex, votesGranted,
    client_leader, client_reqIdx, client_req, client_resp, client_timeout
>>

LogEntryType == [term: Nat, cmd: [type: {Put, Get}, key: AllStrings, value: AllStrings, idx: Nat], client: ClientSet]
MessageBodyType ==
    [mtype: {RequestVoteResponse}, mterm: Nat, mvoteGranted: BOOLEAN, msource: ServerSet, mdest: ServerSet] \cup
    [mtype: {RequestVoteRequest}, mterm: Nat, mlastLogTerm: Nat, mlastLogIndex: Nat, msource: ServerSet, mdest: ServerSet] \cup
    [mtype: {AppendEntriesRequest}, mterm: Nat, mprevLogIndex: Nat, mprevLogTerm: Nat, mentries: Seq(LogEntryType), mcommitIndex: Nat, msource: ServerSet, mdest: ServerSet] \cup
    [mtype: {AppendEntriesResponse}, mterm: Nat, msuccess: BOOLEAN, mmatchIndex: Nat, msource: ServerSet, mdest: ServerSet] \cup
    [mtype: {ClientPutRequest, ClientGetRequest}, mcmd: [type: {Put, Get}, key: AllStrings, value: AllStrings, idx: Nat], msource: ClientSet, mdest: ServerSet] \cup
    [mtype: {ClientPutResponse, ClientGetResponse}, msuccess: BOOLEAN, mresponse: [idx: Nat, key: AllStrings, value: AllStrings, ok: BOOLEAN], mleaderHint: ServerSet \cup {NilValue}, msource: ServerSet, mdest: ClientSet]

TypeOK ==
    /\ net \in [NodeSet -> Bag(MessageBodyType)]
    /\ netEnabled \in [ServerSet -> BOOLEAN]
    /\ fd \in [ServerSet -> BOOLEAN]
    /\ state \in [ServerSet -> ServerStates]
    /\ currentTerm \in [ServerSet -> Nat]
    /\ votedFor \in [ServerSet -> ServerSet \cup {NilValue}]
    /\ log \in [ServerSet -> Seq(LogEntryType)]
    /\ commitIndex \in [ServerSet -> Nat]
    /\ lastApplied \in [ServerSet -> Nat]
    /\ leader \in [ServerSet -> ServerSet \cup {NilValue}]
    /\ nextIndex \in [ServerSet -> [ServerSet -> 1..Nat]]
    /\ matchIndex \in [ServerSet -> [ServerSet -> 0..Nat]]
    /\ votesGranted \in [ServerSet -> SUBSET ServerSet]
    /\ client_leader \in [ClientSet -> ServerSet \cup {NilValue}]
    /\ client_reqIdx \in [ClientSet -> Nat]
    /\ client_req \in [ClientSet -> [type: {Put, Get}, key: AllStrings, value: AllStrings]]
    /\ client_resp \in [ClientSet -> [idx: Nat, key: AllStrings, value: AllStrings, ok: BOOLEAN]]
    /\ client_timeout \in [ClientSet -> BOOLEAN]

Init ==
    /\ net = [n \in NodeSet |-> EmptyBag]
    /\ netEnabled = [s \in ServerSet |-> TRUE]
    /\ fd = [s \in ServerSet |-> FALSE]
    /\ state = [s \in ServerSet |-> StateFollower]
    /\ currentTerm = [s \in ServerSet |-> 0]
    /\ votedFor = [s \in ServerSet |-> NilValue]
    /\ log = [s \in ServerSet |-> <<>>]
    /\ commitIndex = [s \in ServerSet |-> 0]
    /\ lastApplied = [s \in ServerSet |-> 0]
    /\ leader = [s \in ServerSet |-> NilValue]
    /\ nextIndex = [s \in ServerSet |-> [s2 \in ServerSet |-> 1]]
    /\ matchIndex = [s \in ServerSet |-> [s2 \in ServerSet |-> 0]]
    /\ votesGranted = [s \in ServerSet |-> {}]
    /\ client_leader = [c \in ClientSet |-> NilValue]
    /\ client_reqIdx = [c \in ClientSet |-> 0]
    /\ client_req = [c \in ClientSet |-> [type |-> Get, key |-> "", value |-> ""]]
    /\ client_resp = [c \in ClientSet |-> [idx |-> 0, key |-> "", value |-> "", ok |-> FALSE]]
    /\ client_timeout = [c \in ClientSet |-> FALSE]

\*-----------------------------------------------------------------------------
\* Server Actions
\*-----------------------------------------------------------------------------

Timeout(i) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ state[i] \in {StateFollower, StateCandidate}
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = NilValue]
    /\ net' = [net EXCEPT ![j] = @ \cup {[
                mtype |-> RequestVoteRequest,
                mterm |-> currentTerm[i] + 1,
                mlastLogTerm |-> LastTerm(log[i]),
                mlastLogIndex |-> LastIndex(log[i]),
                msource |-> i,
                mdest |-> j
            ]} \forall j \in ServerSet \ {i}]
    /\ UNCHANGED <<
        netEnabled, fd, log, commitIndex, lastApplied, nextIndex, matchIndex,
        client_leader, client_reqIdx, client_req, client_resp, client_timeout
    >>

HandleRequestVoteRequest(i, m) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ m.mtype = RequestVoteRequest
    /\ LET
        term' == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
        state' == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i]
        votedFor_intermediate == IF m.mterm > currentTerm[i] THEN NilValue ELSE votedFor[i]
        logOK == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= LastIndex(log[i])
        grant == /\ m.mterm <= currentTerm[i]
                 /\ logOK
                 /\ votedFor[i] \in {NilValue, m.msource}
        votedFor_final == IF grant THEN m.msource ELSE votedFor_intermediate
        resp == [
            mtype |-> RequestVoteResponse,
            mterm |-> term',
            mvoteGranted |-> grant,
            msource |-> i,
            mdest |-> m.msource
        ]
    IN
        /\ currentTerm' = [currentTerm EXCEPT ![i] = term']
        /\ state' = [state EXCEPT ![i] = state']
        /\ votedFor' = [votedFor EXCEPT ![i] = votedFor_final]
        /\ net' = [net EXCEPT ![m.msource] = @ \cup {resp}]
        /\ UNCHANGED <<
            netEnabled, fd, log, commitIndex, lastApplied, leader,
            nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx,
            client_req, client_resp, client_timeout
        >>

HandleRequestVoteResponse(i, m) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ m.mtype = RequestVoteResponse
    /\ IF m.mterm > currentTerm[i]
       THEN /\ state' = [state EXCEPT ![i] = StateFollower]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
            /\ votedFor' = [votedFor EXCEPT ![i] = NilValue]
            /\ leader' = [leader EXCEPT ![i] = NilValue]
            /\ UNCHANGED <<
                net, netEnabled, fd, log, commitIndex, lastApplied,
                nextIndex, matchIndex, votesGranted, client_leader,
                client_reqIdx, client_req, client_resp, client_timeout
            >>
       ELSE /\ m.mterm = currentTerm[i]
            /\ state[i] = StateCandidate
            /\ LET
                newVotes == IF m.mvoteGranted THEN votesGranted[i] \cup {m.msource} ELSE votesGranted[i]
            IN
                /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                /\ IF IsQuorum(newVotes)
                   THEN /\ state' = [state EXCEPT ![i] = StateLeader]
                        /\ leader' = [leader EXCEPT ![i] = i]
                        /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> LastIndex(log[i]) + 1]]
                        /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
                        /\ UNCHANGED <<
                            net, netEnabled, fd, currentTerm, votedFor, log,
                            commitIndex, lastApplied, client_leader,
                            client_reqIdx, client_req, client_resp, client_timeout
                        >>
                   ELSE /\ UNCHANGED <<
                            state, leader, nextIndex, matchIndex, net, netEnabled,
                            fd, currentTerm, votedFor, log, commitIndex,
                            lastApplied, client_leader, client_reqIdx,
                            client_req, client_resp, client_timeout
                        >>

HandleAppendEntriesRequest(i, m) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ m.mtype = AppendEntriesRequest
    /\ LET
        term' == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
        state_intermediate == IF m.mterm > currentTerm[i] THEN StateFollower
                  ELSE IF m.mterm = currentTerm[i] /\ state[i] = StateCandidate THEN StateFollower
                  ELSE state[i]
        votedFor_intermediate == IF m.mterm > currentTerm[i] THEN NilValue ELSE votedFor[i]
        leader' == IF m.mterm >= currentTerm[i] THEN m.msource ELSE leader[i]
        logOK == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ log[i][m.mprevLogIndex].term = m.mprevLogTerm
        success == m.mterm >= currentTerm[i] /\ logOK
        newLog == IF success
                  THEN SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries
                  ELSE log[i]
        newCommitIndex == IF success
                          THEN LET newLastIndex == LastIndex(newLog)
                               IN IF m.mcommitIndex > commitIndex[i]
                                  THEN IF m.mcommitIndex < newLastIndex THEN m.mcommitIndex ELSE newLastIndex
                                  ELSE commitIndex[i]
                          ELSE commitIndex[i]
        resp == [
            mtype |-> AppendEntriesResponse,
            mterm |-> term',
            msuccess |-> success,
            mmatchIndex |-> IF success THEN LastIndex(newLog) ELSE 0,
            msource |-> i,
            mdest |-> m.msource
        ]
    IN
        /\ currentTerm' = [currentTerm EXCEPT ![i] = term']
        /\ state' = [state EXCEPT ![i] = state_intermediate]
        /\ votedFor' = [votedFor EXCEPT ![i] = votedFor_intermediate]
        /\ leader' = [leader EXCEPT ![i] = leader']
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
        /\ net' = [net EXCEPT ![m.msource] = @ \cup {resp}]
        /\ UNCHANGED <<
            netEnabled, fd, lastApplied, nextIndex, matchIndex, votesGranted,
            client_leader, client_reqIdx, client_req, client_resp, client_timeout
        >>

HandleAppendEntriesResponse(i, m) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ m.mtype = AppendEntriesResponse
    /\ state[i] = StateLeader
    /\ IF m.mterm > currentTerm[i]
       THEN /\ state' = [state EXCEPT ![i] = StateFollower]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
            /\ votedFor' = [votedFor EXCEPT ![i] = NilValue]
            /\ leader' = [leader EXCEPT ![i] = NilValue]
            /\ UNCHANGED <<
                net, netEnabled, fd, log, commitIndex, lastApplied,
                nextIndex, matchIndex, votesGranted, client_leader,
                client_reqIdx, client_req, client_resp, client_timeout
            >>
       ELSE /\ m.mterm = currentTerm[i]
            /\ IF m.msuccess
               THEN /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][m.msource] = m.mmatchIndex]
                    /\ UNCHANGED <<
                        net, netEnabled, fd, state, currentTerm, votedFor, log,
                        commitIndex, lastApplied, leader, votesGranted,
                        client_leader, client_reqIdx, client_req, client_resp, client_timeout
                    >>
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] = IF @ > 1 THEN @ - 1 ELSE 1]
                    /\ UNCHANGED <<
                        net, netEnabled, fd, state, currentTerm, votedFor, log,
                        commitIndex, lastApplied, leader, matchIndex, votesGranted,
                        client_leader, client_reqIdx, client_req, client_resp, client_timeout
                    >>

HandleClientRequest(i, m) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ m.mtype \in {ClientPutRequest, ClientGetRequest}
    /\ IF state[i] = StateLeader
       THEN LET newEntry == [term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource]
            IN /\ log' = [log EXCEPT ![i] = Append(@, newEntry)]
               /\ UNCHANGED <<
                    net, netEnabled, fd, state, currentTerm, votedFor, commitIndex,
                    lastApplied, leader, nextIndex, matchIndex, votesGranted,
                    client_leader, client_reqIdx, client_req, client_resp, client_timeout
                >>
       ELSE LET respType == IF m.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
                 resp == [
                    mtype |-> respType,
                    msuccess |-> FALSE,
                    mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> "", ok |-> FALSE],
                    mleaderHint |-> leader[i],
                    msource |-> i,
                    mdest |-> m.msource
                 ]
            IN /\ net' = [net EXCEPT ![m.msource] = @ \cup {resp}]
               /\ UNCHANGED <<
                    netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
                    lastApplied, leader, nextIndex, matchIndex, votesGranted,
                    client_leader, client_reqIdx, client_req, client_resp, client_timeout
                >>

LeaderSendAppendEntries(i, j) ==
    /\ i \in ServerSet
    /\ j \in ServerSet \ {i}
    /\ netEnabled[i]
    /\ state[i] = StateLeader
    /\ LET
        prevLogIndex == nextIndex[i][j] - 1
        prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
        entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
        msg == [
            mtype |-> AppendEntriesRequest,
            mterm |-> currentTerm[i],
            mprevLogIndex |-> prevLogIndex,
            mprevLogTerm |-> prevLogTerm,
            mentries |-> entries,
            mcommitIndex |-> commitIndex[i],
            msource |-> i,
            mdest |-> j
        ]
       IN
        /\ net' = [net EXCEPT ![j] = @ \cup {msg}]
        /\ UNCHANGED <<
            netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
            lastApplied, leader, nextIndex, matchIndex, votesGranted,
            client_leader, client_reqIdx, client_req, client_resp, client_timeout
        >>

LeaderAdvanceCommitIndex(i) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ state[i] = StateLeader
    /\ LET
        \* Find the highest index N that has been replicated on a quorum
        \* and is from the current leader's term.
        AgreeingPeers(idx) == {s \in ServerSet | matchIndex[i][s] >= idx} \cup {i}
        PossibleNewCommitIndices ==
            { N \in (commitIndex[i] + 1)..Len(log[i]) |
                /\ log[i][N].term = currentTerm[i]
                /\ IsQuorum(AgreeingPeers(N))
            }
        newCommitIndex == IF PossibleNewCommitIndices = {}
                          THEN commitIndex[i]
                          ELSE CHOOSE n \in PossibleNewCommitIndices : \A n2 \in PossibleNewCommitIndices : n >= n2
       IN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
        /\ UNCHANGED <<
            net, netEnabled, fd, state, currentTerm, votedFor, log,
            lastApplied, leader, nextIndex, matchIndex, votesGranted,
            client_leader, client_reqIdx, client_req, client_resp, client_timeout
        >>

ServerApplyLog(i) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ lastApplied[i] < commitIndex[i]
    /\ LET
        idxToApply == lastApplied[i] + 1
        entry == log[i][idxToApply]
        cmd == entry.cmd
        client == entry.client
        \* This is a simplified state machine. It's not part of the spec variables.
        \* We just compute the response and send it.
        respType == IF cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
        resp == [
            mtype |-> respType,
            msuccess |-> TRUE,
            mresponse |-> [idx |-> cmd.idx, key |-> cmd.key, value |-> cmd.value, ok |-> TRUE],
            mleaderHint |-> i,
            msource |-> i,
            mdest |-> client
        ]
       IN
        /\ lastApplied' = [lastApplied EXCEPT ![i] = idxToApply]
        /\ net' = [net EXCEPT ![client] = @ \cup {resp}]
        /\ UNCHANGED <<
            netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
            leader, nextIndex, matchIndex, votesGranted,
            client_leader, client_reqIdx, client_req, client_resp, client_timeout
        >>

Crash(i) ==
    /\ i \in ServerSet
    /\ netEnabled[i]
    /\ netEnabled' = [netEnabled EXCEPT ![i] = FALSE]
    /\ fd' = [fd EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<
        net, state, currentTerm, votedFor, log, commitIndex, lastApplied,
        leader, nextIndex, matchIndex, votesGranted, client_leader,
        client_reqIdx, client_req, client_resp, client_timeout
    >>

\*-----------------------------------------------------------------------------
\* Client Actions
\*-----------------------------------------------------------------------------

ClientSendRequest(c) ==
    /\ c \in ClientSet
    /\ LET
        target == IF client_leader[c] = NilValue
                  THEN CHOOSE s \in ServerSet : TRUE
                  ELSE client_leader[c]
        reqType == IF client_req[c].type = Put THEN ClientPutRequest ELSE ClientGetRequest
        newReqIdx == client_reqIdx[c] + 1
        msg == [
            mtype |-> reqType,
            mcmd |-> [
                idx |-> newReqIdx,
                type |-> client_req[c].type,
                key |-> client_req[c].key,
                value |-> client_req[c].value
            ],
            msource |-> c,
            mdest |-> target
        ]
       IN
        /\ client_reqIdx' = [client_reqIdx EXCEPT ![c] = newReqIdx]
        /\ client_leader' = [client_leader EXCEPT ![c] = target]
        /\ net' = [net EXCEPT ![target] = @ \cup {msg}]
        /\ client_timeout' = [client_timeout EXCEPT ![c] = FALSE]
        /\ UNCHANGED <<
            netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
            lastApplied, leader, nextIndex, matchIndex, votesGranted,
            client_req, client_resp
        >>

ClientReceiveResponse(c, m) ==
    /\ c \in ClientSet
    /\ m.mdest = c
    /\ m.mtype \in {ClientPutResponse, ClientGetResponse}
    /\ m.mresponse.idx = client_reqIdx[c]
    /\ IF m.msuccess
       THEN /\ client_resp' = [client_resp EXCEPT ![c] = m.mresponse]
            /\ client_leader' = [client_leader EXCEPT ![c] = m.msource]
            /\ UNCHANGED <<
                net, netEnabled, fd, state, currentTerm, votedFor, log,
                commitIndex, lastApplied, leader, nextIndex, matchIndex,
                votesGranted, client_reqIdx, client_req, client_timeout
            >>
       ELSE /\ client_leader' = [client_leader EXCEPT ![c] = m.mleaderHint]
            /\ UNCHANGED <<
                net, netEnabled, fd, state, currentTerm, votedFor, log,
                commitIndex, lastApplied, leader, nextIndex, matchIndex,
                votesGranted, client_reqIdx, client_req, client_resp, client_timeout
            >>

ClientTimeout(c) ==
    /\ c \in ClientSet
    /\ client_timeout[c]
    /\ client_leader' = [client_leader EXCEPT ![c] = NilValue]
    /\ UNCHANGED <<
        net, netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
        lastApplied, leader, nextIndex, matchIndex, votesGranted,
        client_reqIdx, client_req, client_resp, client_timeout
    >>

\*-----------------------------------------------------------------------------
\* Network and Message Handling
\*-----------------------------------------------------------------------------

Receive(i) ==
    \E m \in DOMAIN net[i]:
        LET net == [net EXCEPT ![i] = BagDeleteOne(@, m)]
        IN \/ HandleRequestVoteRequest(i, m)
           \/ HandleRequestVoteResponse(i, m)
           \/ HandleAppendEntriesRequest(i, m)
           \/ HandleAppendEntriesResponse(i, m)
           \/ HandleClientRequest(i, m)

ReceiveClient(c) ==
    \E m \in DOMAIN net[c]:
        LET net == [net EXCEPT ![c] = BagDeleteOne(@, m)]
        IN ClientReceiveResponse(c, m)

DropMessage(n) ==
    \E m \in DOMAIN net[n]:
        /\ net' = [net EXCEPT ![n] = BagDeleteOne(@, m)]
        /\ UNCHANGED <<
            netEnabled, fd, state, currentTerm, votedFor, log, commitIndex,
            lastApplied, leader, nextIndex, matchIndex, votesGranted,
            client_leader, client_reqIdx, client_req, client_resp, client_timeout
        >>

\*-----------------------------------------------------------------------------
\* Next State Relation
\*-----------------------------------------------------------------------------

Next ==
    \/ \E i \in ServerSet:
        \/ Timeout(i)
        \/ Receive(i)
        \/ (\E j \in ServerSet \ {i}: LeaderSendAppendEntries(i, j))
        \/ LeaderAdvanceCommitIndex(i)
        \/ ServerApplyLog(i)
        \/ Crash(i)
        \/ DropMessage(i)
    \/ \E c \in ClientSet:
        \/ ClientSendRequest(c)
        \/ ReceiveClient(c)
        \/ ClientTimeout(c)
        \/ DropMessage(c)

Spec == Init /\ [][Next]_vars

Fairness ==
    /\ \A i \in ServerSet: WF_vars(Timeout(i))
    /\ \A i \in ServerSet: WF_vars(Receive(i))
    /\ \A i \in ServerSet: \A j \in ServerSet \ {i}: WF_vars(LeaderSendAppendEntries(i, j))
    /\ \A i \in ServerSet: WF_vars(LeaderAdvanceCommitIndex(i))
    /\ \A i \in ServerSet: WF_vars(ServerApplyLog(i))
    /\ \A i \in ServerSet: WF_vars(Crash(i))
    /\ \A c \in ClientSet: WF_vars(ClientSendRequest(c))
    /\ \A c \in ClientSet: WF_vars(ReceiveClient(c))
    /\ \A c \in ClientSet: WF_vars(ClientTimeout(c))
    /\ \A n \in NodeSet: WF_vars(DropMessage(n))

FairSpec == Spec /\ Fairness

====
