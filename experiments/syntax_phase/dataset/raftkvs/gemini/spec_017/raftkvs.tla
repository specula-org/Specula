---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    AllStrings,
    Nil

ServerSet == 1..NumServers
ClientSet == (NumServers + 1)..(NumServers + NumClients)
NodeSet == ServerSet \cup ClientSet

Put == "put"
Get == "get"
AllReqs ==
    [type: {{Put}}, key: AllStrings, value: AllStrings, idx: {{0}}] \cup
    [type: {{Get}}, key: AllStrings, idx: {{0}}]

Follower == "follower"
Candidate == "candidate"
Leader == "leader"
ServerStates == {{Follower, Candidate, Leader}}

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

IsQuorum(S) == Cardinality(S) * 2 > NumServers
LastTerm(lg) == IF Len(lg) = 0 THEN 0 ELSE lg[Len(lg)].term
Max(a, b) == IF a >= b THEN a ELSE b

RECURSIVE ApplyLog(_, _, _, _, _)
ApplyLog(xlog, start, end, xsm, xsmDomain) ==
    IF start > end THEN <<xsm, xsmDomain>>
    ELSE LET entry == xlog[start]
             AND cmd == entry.cmd
             AND result == IF cmd.type = Put
                       THEN << [xsm EXCEPT ![cmd.key] = cmd.value], xsmDomain \cup {{cmd.key}} >>
                       ELSE << xsm, xsmDomain >>
         IN ApplyLog(xlog, start + 1, end, result[1], result[2])

RECURSIVE FindMaxAgreeIndexRec(_, _, _, _)
FindMaxAgreeIndexRec(i, matchIdx, logLen, index) ==
    IF index = 0 THEN Nil
    ELSE IF IsQuorum({{i}} \cup {{k \in ServerSet | matchIdx[k] >= index}})
         THEN index
         ELSE FindMaxAgreeIndexRec(i, matchIdx, logLen, index - 1)

VARIABLES
    net,
    netEnabled,
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    leader,
    sm,
    smDomain,
    nextIndex,
    matchIndex,
    votesGranted,
    client_leader,
    client_reqIdx,
    respCh

vars == <<net, netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

Init ==
    /\ net = [n \in NodeSet |-> <<>>]
    /\ netEnabled = [s \in ServerSet |-> TRUE]
    /\ state = [s \in ServerSet |-> Follower]
    /\ currentTerm = [s \in ServerSet |-> 0]
    /\ votedFor = [s \in ServerSet |-> Nil]
    /\ log = [s \in ServerSet |-> <<>>]
    /\ commitIndex = [s \in ServerSet |-> 0]
    /\ lastApplied = [s \in ServerSet |-> 0]
    /\ leader = [s \in ServerSet |-> Nil]
    /\ sm = [s \in ServerSet |-> [k \in AllStrings |-> Nil]]
    /\ smDomain = [s \in ServerSet |-> {{}}]
    /\ nextIndex = [s \in ServerSet |-> [s2 \in ServerSet |-> 1]]
    /\ matchIndex = [s \in ServerSet |-> [s2 \in ServerSet |-> 0]]
    /\ votesGranted = [s \in ServerSet |-> {{}}]
    /\ client_leader = [c \in ClientSet |-> Nil]
    /\ client_reqIdx = [c \in ClientSet |-> 0]
    /\ respCh = [c \in ClientSet |-> <<>>]

UpdateTerm(i, m) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ leader' = [leader EXCEPT ![i] = Nil]

KeepTerm(i) ==
    /\ UNCHANGED <<currentTerm, state, leader>>

HandleTerm(i, m) ==
    IF m.mterm > currentTerm[i] THEN UpdateTerm(i, m) ELSE KeepTerm(i)

ServerTimeout(i) ==
    /\ netEnabled[i]
    /\ state[i] \in {{Follower, Candidate}}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {{i}}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ LET request(j) == [
            mtype       |-> RequestVoteRequest,
            mterm       |-> currentTerm'[i],
            mlastLogTerm|-> LastTerm(log[i]),
            mlastLogIndex|-> Len(log[i]),
            msource     |-> i,
            mdest       |-> j
        ]
    IN net' = [ n \in NodeSet |->
            IF n \in ServerSet \ {{i}}
            THEN net[n] \o << request(n) >>
            ELSE net[n]
       ]
    /\ UNCHANGED <<netEnabled, log, commitIndex, lastApplied, sm, smDomain, nextIndex, matchIndex, client_leader, client_reqIdx, respCh>>

HandleRequestVoteRequest(i) ==
    /\ netEnabled[i]
    /\ \E m \in net[i]:
        /\ m.mtype = RequestVoteRequest
        /\ LET new_currentTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
           AND new_votedFor == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
           AND logOK == \/ m.mlastLogTerm > LastTerm(log[i])
                        \/ /\ m.mlastLogTerm = LastTerm(log[i])
                           /\ m.mlastLogIndex >= Len(log[i])
           AND grant == /\ m.mterm = new_currentTerm
                        /\ logOK
                        /\ new_votedFor \in {{Nil, m.msource}}
           AND response == [
                   mtype        |-> RequestVoteResponse,
                   mterm        |-> new_currentTerm,
                   mvoteGranted |-> grant,
                   msource      |-> i,
                   mdest        |-> m.msource
               ]
           IN
            /\ HandleTerm(i, m)
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m.msource ELSE new_votedFor]
            /\ net' = [net EXCEPT ![i] = BagToSeq(SeqToBag(net[i]) \ {{m}}), ![m.msource] = net[m.msource] \o <<response>>]
            /\ UNCHANGED <<netEnabled, log, commitIndex, lastApplied, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

HandleRequestVoteResponse(i) ==
    /\ netEnabled[i]
    /\ \E m \in net[i]:
        /\ m.mtype = RequestVoteResponse
        /\ HandleTerm(i, m)
        /\ IF m.mterm = currentTerm[i] /\ state[i] = Candidate
           THEN /\ IF m.mvoteGranted
                   THEN votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {{m.msource}}]
                   ELSE UNCHANGED <<votesGranted>>
           ELSE UNCHANGED <<votesGranted>>
        /\ net' = [net EXCEPT ![i] = BagToSeq(SeqToBag(net[i]) \ {{m}})]
        /\ UNCHANGED <<netEnabled, votedFor, log, commitIndex, lastApplied, sm, smDomain, nextIndex, matchIndex, client_leader, client_reqIdx, respCh>>

BecomeLeader(i) ==
    /\ netEnabled[i]
    /\ state[i] = Candidate
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
    /\ LET request(j) ==
            LET prevLogIndex == nextIndex'[i][j] - 1
            AND prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
            IN [ mtype         |-> AppendEntriesRequest,
                 mterm         |-> currentTerm[i],
                 mprevLogIndex |-> prevLogIndex,
                 mprevLogTerm  |-> prevLogTerm,
                 mentries      |-> <<>>,
                 mcommitIndex  |-> commitIndex[i],
                 msource       |-> i,
                 mdest         |-> j ]
    IN net' = [ n \in NodeSet |->
            IF n \in ServerSet \ {{i}}
            THEN net[n] \o << request(n) >>
            ELSE net[n]
       ]
    /\ UNCHANGED <<netEnabled, currentTerm, votedFor, log, commitIndex, lastApplied, sm, smDomain, votesGranted, client_leader, client_reqIdx, respCh>>

LeaderSendAppendEntries(i, j) ==
    /\ netEnabled[i]
    /\ state[i] = Leader
    /\ j \in ServerSet \ {{i}}
    /\ LET prevLogIndex == nextIndex[i][j] - 1
       AND prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN log[i][prevLogIndex].term ELSE 0
       AND entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
       AND request == [ mtype         |-> AppendEntriesRequest,
                        mterm         |-> currentTerm[i],
                        mprevLogIndex |-> prevLogIndex,
                        mprevLogTerm  |-> prevLogTerm,
                        mentries      |-> entries,
                        mcommitIndex  |-> commitIndex[i],
                        msource       |-> i,
                        mdest         |-> j ]
    IN net' = [net EXCEPT ![j] = net[j] \o <<request>>]
    /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

HandleAppendEntriesRequest(i) ==
    /\ netEnabled[i]
    /\ \E m \in net[i]:
        /\ m.mtype = AppendEntriesRequest
        /\ LET new_currentTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
           AND logOK == \/ m.mprevLogIndex = 0
                        \/ /\ m.mprevLogIndex > 0
                           /\ m.mprevLogIndex <= Len(log[i])
                           /\ log[i][m.mprevLogIndex].term = m.mprevLogTerm
           AND success == /\ m.mterm >= currentTerm[i]
                          /\ logOK
           AND new_log == IF success
                          THEN SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries
                          ELSE log[i]
           AND matchIdx == IF success
                           THEN m.mprevLogIndex + Len(m.mentries)
                           ELSE 0
           AND response == [ mtype       |-> AppendEntriesResponse,
                             mterm       |-> new_currentTerm,
                             msuccess    |-> success,
                             mmatchIndex |-> matchIdx,
                             msource     |-> i,
                             mdest       |-> m.msource ]
           IN
            /\ HandleTerm(i, m)
            /\ IF m.mterm >= currentTerm[i]
               THEN /\ leader' = [leader EXCEPT ![i] = m.msource]
                    /\ IF state[i] = Candidate THEN state' = [state EXCEPT ![i] = Follower] ELSE UNCHANGED <<state>>
               ELSE UNCHANGED <<leader, state>>
            /\ log' = [log EXCEPT ![i] = new_log]
            /\ commitIndex' = IF success THEN [commitIndex EXCEPT ![i] = Max(commitIndex[i], m.mcommitIndex)] ELSE commitIndex
            /\ net' = [net EXCEPT ![i] = BagToSeq(SeqToBag(net[i]) \ {{m}}), ![m.msource] = net[m.msource] \o <<response>>]
            /\ UNCHANGED <<netEnabled, votedFor, lastApplied, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

HandleAppendEntriesResponse(i) ==
    /\ netEnabled[i]
    /\ \E m \in net[i]:
        /\ m.mtype = AppendEntriesResponse
        /\ state[i] = Leader
        /\ LET j == m.msource IN
            /\ HandleTerm(i, m)
            /\ IF m.mterm = currentTerm[i]
               THEN IF m.msuccess
                    THEN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                         /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                    ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max(1, nextIndex[i][j] - 1)]
                         /\ UNCHANGED <<matchIndex>>
               ELSE UNCHANGED <<nextIndex, matchIndex>>
            /\ net' = [net EXCEPT ![i] = BagToSeq(SeqToBag(net[i]) \ {{m}})]
            /\ UNCHANGED <<netEnabled, votedFor, log, commitIndex, lastApplied, sm, smDomain, votesGranted, client_leader, client_reqIdx, respCh>>

LeaderAdvanceCommitIndex(i) ==
    /\ netEnabled[i]
    /\ state[i] = Leader
    /\ LET maxAgreeIndex == FindMaxAgreeIndexRec(i, matchIndex[i], Len(log[i]), Len(log[i]))
       AND newCommitIndex ==
            IF maxAgreeIndex /= Nil /\ maxAgreeIndex > commitIndex[i] /\ log[i][maxAgreeIndex].term = currentTerm[i]
            THEN maxAgreeIndex
            ELSE commitIndex[i]
       IN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
        /\ UNCHANGED <<net, netEnabled, state, currentTerm, votedFor, log, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

ServerApplyEntry(i) ==
    /\ netEnabled[i]
    /\ lastApplied[i] < commitIndex[i]
    /\ LET k == lastApplied[i] + 1
       AND entry == log[i][k]
       AND cmd == entry.cmd
       AND client == entry.client
       AND new_sm_tuple == ApplyLog(log[i], k, k, sm[i], smDomain[i])
       AND reqOk == cmd.key \in new_sm_tuple[2]
       AND response == [
            mtype       |-> IF cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse,
            msuccess    |-> TRUE,
            mresponse   |-> [ idx   |-> cmd.idx,
                            key   |-> cmd.key,
                            value |-> IF reqOk THEN new_sm_tuple[1][cmd.key] ELSE Nil,
                            ok    |-> reqOk ],
            mleaderHint |-> i,
            msource     |-> i,
            mdest       |-> client
        ]
       IN
        /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
        /\ sm' = [sm EXCEPT ![i] = new_sm_tuple[1]]
        /\ smDomain' = [smDomain EXCEPT ![i] = new_sm_tuple[2]]
        /\ IF state[i] = Leader
           THEN net' = [net EXCEPT ![client] = net[client] \o <<response>>]
           ELSE UNCHANGED <<net>>
        /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, log, commitIndex, leader, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

HandleClientRequest(i) ==
    /\ netEnabled[i]
    /\ \E m \in net[i]:
        /\ m.mtype \in {{ClientPutRequest, ClientGetRequest}}
        /\ IF state[i] = Leader
           THEN /\ LET entry == [ term   |-> currentTerm[i],
                                  cmd    |-> m.mcmd,
                                  client |-> m.msource ]
                  IN log' = [log EXCEPT ![i] = Append(log[i], entry)]
                /\ net' = [net EXCEPT ![i] = BagToSeq(SeqToBag(net[i]) \ {{m}})]
                /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>
           ELSE /\ LET respType == IF m.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
                      AND response == [ mtype       |-> respType,
                                    msuccess    |-> FALSE,
                                    mresponse   |-> [ idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE ],
                                    mleaderHint |-> leader[i],
                                    msource     |-> i,
                                    mdest       |-> m.msource ]
                  IN net' = [net EXCEPT ![i] = BagToSeq(SeqToBag(net[i]) \ {{m}}), ![m.msource] = net[m.msource] \o <<response>>]
                /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

ClientRequest(c) ==
    /\ \E req \in AllReqs:
        /\ LET target == IF client_leader[c] = Nil THEN CHOOSE s \in ServerSet : TRUE ELSE client_leader[c]
           AND reqIdx == client_reqIdx[c] + 1
           AND mtype == IF req.type = Put THEN ClientPutRequest ELSE ClientGetRequest
           AND cmd == [ rcd \in DOMAIN req |-> IF rcd = "idx" THEN reqIdx ELSE req[rcd] ]
           AND msg == [ mtype   |-> mtype,
                        mcmd    |-> cmd,
                        msource |-> c,
                        mdest   |-> target ]
           IN
            /\ client_reqIdx' = [client_reqIdx EXCEPT ![c] = reqIdx]
            /\ net' = [net EXCEPT ![target] = net[target] \o <<msg>>]
            /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, respCh>>

ClientReceiveResponse(c) ==
    /\ \E m \in net[c]:
        /\ m.mtype \in {{ClientPutResponse, ClientGetResponse}}
        /\ IF m.mresponse.idx = client_reqIdx[c]
           THEN /\ client_leader' = [client_leader EXCEPT ![c] = m.mleaderHint]
                /\ IF m.msuccess
                   THEN respCh' = [respCh EXCEPT ![c] = Append(respCh[c], m)]
                   ELSE UNCHANGED <<respCh>>
           ELSE UNCHANGED <<client_leader, respCh>>
        /\ net' = [net EXCEPT ![c] = BagToSeq(SeqToBag(net[c]) \ {{m}})]
        /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_reqIdx>>

ClientTimeout(c) ==
    /\ client_leader' = [client_leader EXCEPT ![c] = Nil]
    /\ UNCHANGED <<net, netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_reqIdx, respCh>>

Crash(i) ==
    /\ netEnabled[i]
    /\ netEnabled' = [netEnabled EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<net, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

Recover(i) ==
    /\ ~netEnabled[i]
    /\ netEnabled' = [netEnabled EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<net, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

DropMessage(n) ==
    /\ \E m \in net[n]:
        /\ net' = [net EXCEPT ![n] = BagToSeq(SeqToBag(net[n]) \ {{m}})]
        /\ UNCHANGED <<netEnabled, state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, sm, smDomain, nextIndex, matchIndex, votesGranted, client_leader, client_reqIdx, respCh>>

Next ==
    \/ \E i \in ServerSet:
        \/ ServerTimeout(i)
        \/ HandleRequestVoteRequest(i)
        \/ HandleRequestVoteResponse(i)
        \/ BecomeLeader(i)
        \/ \E j \in ServerSet: LeaderSendAppendEntries(i, j)
        \/ HandleAppendEntriesRequest(i)
        \/ HandleAppendEntriesResponse(i)
        \/ LeaderAdvanceCommitIndex(i)
        \/ ServerApplyEntry(i)
        \/ HandleClientRequest(i)
        \/ Crash(i)
        \/ Recover(i)
    \/ \E c \in ClientSet:
        \/ ClientRequest(c)
        \/ ClientReceiveResponse(c)
        \/ ClientTimeout(c)
    \/ \E n \in NodeSet: DropMessage(n)

Spec == Init /\ [][Next]_vars

Fairness ==
    /\ \A i \in ServerSet: WF_vars(ServerTimeout(i))
    /\ \A i \in ServerSet: WF_vars(HandleRequestVoteRequest(i))
    /\ \A i \in ServerSet: WF_vars(HandleRequestVoteResponse(i))
    /\ \A i \in ServerSet: WF_vars(BecomeLeader(i))
    /\ \A i, j \in ServerSet: WF_vars(LeaderSendAppendEntries(i, j))
    /\ \A i \in ServerSet: WF_vars(HandleAppendEntriesRequest(i))
    /\ \A i \in ServerSet: WF_vars(HandleAppendEntriesResponse(i))
    /\ \A i \in ServerSet: WF_vars(LeaderAdvanceCommitIndex(i))
    /\ \A i \in ServerSet: WF_vars(ServerApplyEntry(i))
    /\ \A i \in ServerSet: WF_vars(HandleClientRequest(i))
    /\ \A c \in ClientSet: WF_vars(ClientRequest(c))
    /\ \A c \in ClientSet: WF_vars(ClientReceiveResponse(c))
    /\ \A c \in ClientSet: WF_vars(ClientTimeout(c))
    /\ \A n \in NodeSet: WF_vars(DropMessage(n))

FairSpec == Spec /\ Fairness

====
