---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS NumServers, NumClients, AllStrings, LeaderTimeoutReset, MaxNodeFail, ExploreFail, Debug, LogPop, LogConcat

VARIABLES
    net, netLen, netEnabled, fd,
    state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
    votedFor, votesResponded, votesGranted, leader, sm, smDomain,
    leaderTimeout, appendEntriesCh, becomeLeaderCh,
    reqCh, respCh, timeout,
    req, resp, reqIdx, leaderHint

vars == <<net, netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
          votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh,
          becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

Server == 1..NumServers
Client == (6 * NumServers + 1)..(6 * NumServers + NumClients)
Node == Server \union Client

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

IsQuorum(S) == Cardinality(S) * 2 > NumServers

LastTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term

FindMaxAgreeIndex(log, i, matchIndex) ==
    LET Recursive(max) ==
        IF max = 0 THEN Nil
        ELSE IF IsQuorum({s \in Server: matchIndex[s] >= max} \union {i})
             THEN max
             ELSE Recursive(max - 1)
    IN Recursive(Len(log))

ApplyLogEntry(entry, sm, smDomain) ==
    IF entry.cmd.type = Put THEN
        <<sm @@ (entry.cmd.key :> entry.cmd.value), smDomain \union {entry.cmd.key}>>
    ELSE <<sm, smDomain>>

ApplyLog(log, start, end, sm, smDomain) ==
    IF start > end THEN <<sm, smDomain>>
    ELSE LET result == ApplyLogEntry(log[start], sm, smDomain)
         IN ApplyLog(log, start + 1, end, result[1], result[2])

AllReqs ==
    [type : {Put}, key : AllStrings, value : AllStrings] \union
    [type : {Get}, key : AllStrings]

Init ==
    /\ net = [n \in Node |-> <<>>]
    /\ netLen = [n \in Node |-> 0]
    /\ netEnabled = [n \in Node |-> TRUE]
    /\ fd = [n \in Node |-> FALSE]
    /\ state = [s \in Server |-> Follower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ log = [s \in Server |-> <<>>]
    /\ plog = [s \in Server |-> [cmd |-> "init", entries |-> <<>>]]
    /\ commitIndex = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votedFor = [s \in Server |-> Nil]
    /\ votesResponded = [s \in Server |-> {}]
    /\ votesGranted = [s \in Server |-> {}]
    /\ leader = [s \in Server |-> Nil]
    /\ sm = [s \in Server |-> [k \in {} |-> ""]]
    /\ smDomain = [s \in Server |-> {}]
    /\ leaderTimeout = [s \in Server |-> LeaderTimeoutReset]
    /\ appendEntriesCh = [s \in Server |-> FALSE]
    /\ becomeLeaderCh = [s \in Server |-> FALSE]
    /\ reqCh = [c \in Client |-> [type : {Put, Get}, key : "", value : ""]]
    /\ respCh = [c \in Client |-> [success : FALSE, response : [idx : 0, key : "", value : "", ok : FALSE]]]
    /\ timeout = [c \in Client |-> FALSE]
    /\ req = [c \in Client |-> [type : {Put, Get}, key : "", value : ""]]
    /\ resp = [c \in Client |-> [success : FALSE, response : [idx : 0, key : "", value : "", ok : FALSE]]]
    /\ reqIdx = [c \in Client |-> 0]
    /\ leaderHint = [c \in Client |-> Nil]

ServerLoop(s) ==
    /\ netEnabled[s]
    /\ netLen[s] > 0
    /\ LET m == Head(net[s]) IN
        /\ m.mdest = s
        /\ \/ HandleRequestVoteRequest(s, m)
           \/ HandleRequestVoteResponse(s, m)
           \/ HandleAppendEntriesRequest(s, m)
           \/ HandleAppendEntriesResponse(s, m)
           \/ HandleClientRequest(s, m)
    /\ net' = [net EXCEPT ![s] = Tail(@)]
    /\ netLen' = [netLen EXCEPT ![s] = @ - 1]
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

HandleRequestVoteRequest(s, m) ==
    /\ m.mtype = RequestVoteRequest
    /\ \/ m.mterm > currentTerm[s]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
          /\ state' = [state EXCEPT ![s] = Follower]
          /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
          /\ leader' = [leader EXCEPT ![s] = Nil]
       \/ TRUE
          /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
    /\ LET logOK == \/ m.mlastLogTerm > LastTerm(log[s])
                   \/ /\ m.mlastLogTerm = LastTerm(log[s])
                      /\ m.mlastLogIndex >= Len(log[s])
        grant == /\ m.mterm = currentTerm[s]
                 /\ logOK
                 /\ votedFor[s] \in {Nil, m.msource}
    IN
        /\ m.mterm <= currentTerm[s]
        /\ IF grant THEN
               votedFor' = [votedFor EXCEPT ![s] = m.msource]
           ELSE UNCHANGED votedFor
        /\ \/ /\ netEnabled[m.msource]
              /\ net' = [net EXCEPT ![m.msource] = Append(@, 
                    [mtype |-> RequestVoteResponse, mterm |-> currentTerm[s],
                     mvoteGranted |-> grant, msource |-> s, mdest |-> m.msource])]
              /\ netLen' = [netLen EXCEPT ![m.msource] = @ + 1]
           \/ ~netEnabled[m.msource]
              /\ UNCHANGED <<net, netLen>>
        /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, nextIndex, matchIndex,
                       votesResponded, votesGranted, sm, smDomain, leaderTimeout,
                       appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

HandleRequestVoteResponse(s, m) ==
    /\ m.mtype = RequestVoteResponse
    /\ \/ m.mterm > currentTerm[s]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
          /\ state' = [state EXCEPT ![s] = Follower]
          /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
          /\ leader' = [leader EXCEPT ![s] = Nil]
       \/ TRUE
          /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
    /\ IF m.mterm < currentTerm[s] THEN
          UNCHANGED <<votesResponded, votesGranted, leaderTimeout, becomeLeaderCh>>
       ELSE
          /\ votesResponded' = [votesResponded EXCEPT ![s] = @ \union {m.msource}]
          /\ IF m.mvoteGranted THEN
                 /\ leaderTimeout' = [leaderTimeout EXCEPT ![s] = LeaderTimeoutReset]
                 /\ votesGranted' = [votesGranted EXCEPT ![s] = @ \union {m.msource}]
                 /\ IF state[s] = Candidate /\ IsQuorum(votesGranted[s] \union {m.msource}) THEN
                        becomeLeaderCh' = [becomeLeaderCh EXCEPT ![s] = TRUE]
                    ELSE UNCHANGED becomeLeaderCh
             ELSE UNCHANGED <<leaderTimeout, votesGranted, becomeLeaderCh>>
    /\ UNCHANGED <<netEnabled, fd, net, netLen, log, plog, commitIndex, nextIndex, matchIndex,
                   sm, smDomain, appendEntriesCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

HandleAppendEntriesRequest(s, m) ==
    /\ m.mtype = AppendEntriesRequest
    /\ \/ m.mterm > currentTerm[s]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
          /\ state' = [state EXCEPT ![s] = Follower]
          /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
          /\ leader' = [leader EXCEPT ![s] = Nil]
       \/ TRUE
          /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
    /\ IF m.mterm = currentTerm[s] THEN
          /\ leader' = [leader EXCEPT ![s] = m.msource]
          /\ leaderTimeout' = [leaderTimeout EXCEPT ![s] = LeaderTimeoutReset]
          /\ IF state[s] = Candidate THEN
                 state' = [state EXCEPT ![s] = Follower]
             ELSE UNCHANGED state
       ELSE UNCHANGED <<leader, leaderTimeout, state>>
    /\ LET logOK == \/ m.mprevLogIndex = 0
                   \/ /\ m.mprevLogIndex > 0
                      /\ m.mprevLogIndex <= Len(log[s])
                      /\ m.mprevLogTerm = log[s][m.mprevLogIndex].term
    IN
        IF m.mterm < currentTerm[s] \/ (m.mterm = currentTerm[s] /\ state[s] = Follower /\ ~logOK) THEN
            \/ /\ netEnabled[m.msource]
               /\ net' = [net EXCEPT ![m.msource] = Append(@,
                     [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[s],
                      msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> s, mdest |-> m.msource])]
               /\ netLen' = [netLen EXCEPT ![m.msource] = @ + 1]
            \/ ~netEnabled[m.msource]
               /\ UNCHANGED <<net, netLen>>
        ELSE
            /\ m.mterm = currentTerm[s]
            /\ state[s] = Follower
            /\ logOK
            /\ LET newLog == SubSeq(log[s], 1, m.mprevLogIndex) \o m.mentries
               newCommitIndex == Max({commitIndex[s], m.mcommitIndex})
               applied == ApplyLog(newLog, commitIndex[s] + 1, m.mcommitIndex, sm[s], smDomain[s])
            IN
                /\ log' = [log EXCEPT ![s] = newLog]
                /\ plog' = [plog EXCEPT ![s] = [cmd |-> LogConcat, entries |-> m.mentries]]
                /\ sm' = [sm EXCEPT ![s] = applied[1]]
                /\ smDomain' = [smDomain EXCEPT ![s] = applied[2]]
                /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                /\ \/ /\ netEnabled[m.msource]
                      /\ net' = [net EXCEPT ![m.msource] = Append(@,
                            [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[s],
                             msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                             msource |-> s, mdest |-> m.msource])]
                      /\ netLen' = [netLen EXCEPT ![m.msource] = @ + 1]
                   \/ ~netEnabled[m.msource]
                      /\ UNCHANGED <<net, netLen>>
    /\ UNCHANGED <<netEnabled, fd, votedFor, votesResponded, votesGranted, nextIndex, matchIndex,
                   appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

HandleAppendEntriesResponse(s, m) ==
    /\ m.mtype = AppendEntriesResponse
    /\ \/ m.mterm > currentTerm[s]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
          /\ state' = [state EXCEPT ![s] = Follower]
          /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
          /\ leader' = [leader EXCEPT ![s] = Nil]
       \/ TRUE
          /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
    /\ IF m.mterm < currentTerm[s] THEN
          UNCHANGED <<nextIndex, matchIndex, leaderTimeout>>
       ELSE
          /\ leaderTimeout' = [leaderTimeout EXCEPT ![s] = LeaderTimeoutReset]
          /\ IF m.msuccess THEN
                 /\ nextIndex' = [nextIndex EXCEPT ![s][m.msource] = m.mmatchIndex + 1]
                 /\ matchIndex' = [matchIndex EXCEPT ![s][m.msource] = m.mmatchIndex]
             ELSE
                 /\ nextIndex' = [nextIndex EXCEPT ![s][m.msource] = Max({nextIndex[s][m.msource] - 1, 1})]
                 /\ UNCHANGED matchIndex
    /\ UNCHANGED <<netEnabled, fd, net, netLen, log, plog, commitIndex, votedFor, votesResponded,
                   votesGranted, sm, smDomain, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

HandleClientRequest(s, m) ==
    /\ \/ m.mtype = ClientPutRequest
       \/ m.mtype = ClientGetRequest
    /\ IF state[s] = Leader THEN
          /\ LET entry == [term |-> currentTerm[s], cmd |-> m.mcmd, client |-> m.msource]
          IN
              /\ log' = [log EXCEPT ![s] = Append(@, entry)]
              /\ plog' = [plog EXCEPT ![s] = [cmd |-> LogConcat, entries |-> <<entry>>]]
              /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![s] = TRUE]
       ELSE
          /\ LET respType == IF m.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
          IN
              \/ /\ netEnabled[m.msource]
                 /\ net' = [net EXCEPT ![m.msource] = Append(@,
                       [mtype |-> respType, msuccess |-> FALSE,
                        mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key],
                        mleaderHint |-> leader[s], msource |-> s, mdest |-> m.msource])]
                 /\ netLen' = [netLen EXCEPT ![m.msource] = @ + 1]
              \/ ~netEnabled[m.msource]
                 /\ UNCHANGED <<net, netLen>>
          /\ UNCHANGED <<log, plog, appendEntriesCh>>
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, commitIndex, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

ServerRequestVote(s) ==
    /\ netEnabled[s]
    /\ leaderTimeout[s] = 0
    /\ netLen[s] = 0
    /\ state[s] \in {Follower, Candidate}
    /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
    /\ state' = [state EXCEPT ![s] = Candidate]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesResponded' = [votesResponded EXCEPT ![s] = {s}]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![s] = LeaderTimeoutReset]
    /\ \A t \in Server \ {s}:
           \/ ~netEnabled[t]
           \/ /\ netEnabled[t]
              /\ net' = [net EXCEPT ![t] = Append(@,
                    [mtype |-> RequestVoteRequest, mterm |-> currentTerm[s] + 1,
                     mlastLogTerm |-> LastTerm(log[s]), mlastLogIndex |-> Len(log[s]),
                     msource |-> s, mdest |-> t])]
              /\ netLen' = [netLen EXCEPT ![t] = @ + 1]
    /\ UNCHANGED <<fd, log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain,
                   appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

ServerAppendEntries(s) ==
    /\ netEnabled[s]
    /\ appendEntriesCh[s]
    /\ state[s] = Leader
    /\ \A t \in Server:
           \/ t = s
           \/ ~netEnabled[t]
           \/ LET prevLogIndex == nextIndex[s][t] - 1
                 prevLogTerm == IF prevLogIndex > 0 THEN log[s][prevLogIndex].term ELSE 0
                 entries == SubSeq(log[s], nextIndex[s][t], Len(log[s]))
              IN
                 /\ net' = [net EXCEPT ![t] = Append(@,
                       [mtype |-> AppendEntriesRequest, mterm |-> currentTerm[s],
                        mprevLogIndex |-> prevLogIndex, mprevLogTerm |-> prevLogTerm,
                        mentries |-> entries, mcommitIndex |-> commitIndex[s],
                        msource |-> s, mdest |-> t])]
                 /\ netLen' = [netLen EXCEPT ![t] = @ + 1]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

ServerAdvanceCommitIndex(s) ==
    /\ netEnabled[s]
    /\ state[s] = Leader
    /\ LET newCommitIndex ==
           LET N == FindMaxAgreeIndex(log[s], s, matchIndex[s])
           IN IF N # Nil /\ log[s][N].term = currentTerm[s] THEN N ELSE commitIndex[s]
       IN
           /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
           /\ LET applied == ApplyLog(log[s], commitIndex[s] + 1, newCommitIndex, sm[s], smDomain[s])
              IN
                  /\ sm' = [sm EXCEPT ![s] = applied[1]]
                  /\ smDomain' = [smDomain EXCEPT ![s] = applied[2]]
    /\ UNCHANGED <<netEnabled, fd, net, netLen, state, currentTerm, log, plog, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, leaderTimeout, appendEntriesCh,
                   becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

ServerBecomeLeader(s) ==
    /\ netEnabled[s]
    /\ becomeLeaderCh[s]
    /\ state[s] = Candidate
    /\ IsQuorum(votesGranted[s])
    /\ state' = [state EXCEPT ![s] = Leader]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
    /\ leader' = [leader EXCEPT ![s] = s]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![s] = TRUE]
    /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<netEnabled, fd, net, netLen, currentTerm, log, plog, commitIndex, votedFor,
                   votesResponded, votesGranted, sm, smDomain, leaderTimeout, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

ClientLoop(c) ==
    /\ req' = [req EXCEPT ![c] = reqCh[c]]
    /\ reqIdx' = [reqIdx EXCEPT ![c] = @ + 1]
    /\ UNCHANGED <<net, netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex,
                   matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain,
                   leaderTimeout, appendEntriesCh, becomeLeaderCh, respCh, timeout, resp, leaderHint>>

ClientSndReq(c) ==
    /\ LET s == IF leaderHint[c] = Nil THEN CHOOSE t \in Server : TRUE ELSE leaderHint[c]
           m == IF req[c].type = Put THEN
                    [mtype |-> ClientPutRequest, mcmd |-> [idx |-> reqIdx[c], type |-> Put,
                            key |-> req[c].key, value |-> req[c].value], msource |-> c, mdest |-> s]
                ELSE [mtype |-> ClientGetRequest, mcmd |-> [idx |-> reqIdx[c], type |-> Get,
                            key |-> req[c].key], msource |-> c, mdest |-> s]
       IN
           \/ /\ netEnabled[s]
              /\ net' = [net EXCEPT ![s] = Append(@, m)]
              /\ netLen' = [netLen EXCEPT ![s] = @ + 1]
           \/ ~netEnabled[s]
              /\ UNCHANGED <<net, netLen>>
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

ClientRcvResp(c) ==
    /\ netLen[c] > 0
    /\ LET m == Head(net[c]) IN
        /\ m.mdest = c
        /\ resp' = [resp EXCEPT ![c] = m]
        /\ leaderHint' = [leaderHint EXCEPT ![c] = m.mleaderHint]
        /\ IF m.msuccess THEN
               respCh' = [respCh EXCEPT ![c] = m]
           ELSE UNCHANGED respCh
    /\ net' = [net EXCEPT ![c] = Tail(@)]
    /\ netLen' = [netLen EXCEPT ![c] = @ - 1]
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   appendEntriesCh, becomeLeaderCh, reqCh, timeout, req, reqIdx>>

ServerCrasher(s) ==
    /\ ExploreFail
    /\ netEnabled[s]
    /\ netEnabled' = [netEnabled EXCEPT ![s] = FALSE]
    /\ fd' = [fd EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<net, netLen, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex,
                   votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout, req, resp, reqIdx, leaderHint>>

Next ==
    \/ \E s \in Server: ServerLoop(s)
    \/ \E s \in Server: ServerRequestVote(s)
    \/ \E s \in Server: ServerAppendEntries(s)
    \/ \E s \in Server: ServerAdvanceCommitIndex(s)
    \/ \E s \in Server: ServerBecomeLeader(s)
    \/ \E c \in Client: ClientLoop(c)
    \/ \E c \in Client: ClientSndReq(c)
    \/ \E c \in Client: ClientRcvResp(c)
    \/ \E s \in Server: ServerCrasher(s)

Spec == Init /\ [][Next]_vars

====