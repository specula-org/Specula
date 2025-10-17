---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS ServerSet, ClientSet, AllStrings, NumServers, NumClients, MaxNodeFail, LeaderTimeoutReset, ExploreFail, Debug, LogPop, LogConcat

VARIABLES
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
    timeout

vars == <<net, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

Nil == 0
ServerSet == 1..NumServers
ClientSet == (NumServers * 6 + 1)..(NumServers * 6 + NumClients)
NodeSet == ServerSet \union ClientSet

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

Min(S) ==
    CHOOSE x \in S : \A y \in S : x <= y

Max(S) ==
    CHOOSE x \in S : \A y \in S : x >= y

ApplyLogEntry(entry, sm, smDomain) ==
    LET cmd == entry.cmd IN
    IF cmd.type = Put THEN
        <<sm @@ (cmd.key :> cmd.value), smDomain \union {cmd.key}>>
    ELSE <<sm, smDomain>>

RECURSIVE ApplyLog(_, _, _, _, _)
ApplyLog(log, start, end, sm, smDomain) ==
    IF start > end THEN <<sm, smDomain>>
    ELSE LET result == ApplyLogEntry(log[start], sm, smDomain)
         IN ApplyLog(log, start+1, end, result[1], result[2])

RECURSIVE FindMaxAgreeIndex(_, _, _)
FindMaxAgreeIndex(logLocal, i, matchIndex) ==
    LET FindMaxAgreeIndexRec(index) ==
        IF index = 0 THEN Nil
        ELSE IF IsQuorum({i} \union {k \in ServerSet: matchIndex[k] >= index})
             THEN index
             ELSE FindMaxAgreeIndexRec(index-1)
    IN FindMaxAgreeIndexRec(Len(logLocal))

AllReqs ==
    [type : {Put}, key : AllStrings, value : AllStrings] \union
    [type : {Get}, key : AllStrings]

Init ==
    /\ net = [n \in NodeSet |-> <<>>]
    /\ netEnabled = [n \in NodeSet |-> TRUE]
    /\ fd = [n \in NodeSet |-> TRUE]
    /\ state = [n \in ServerSet |-> Follower]
    /\ currentTerm = [n \in ServerSet |-> 0]
    /\ log = [n \in ServerSet |-> <<>>]
    /\ plog = [n \in ServerSet |-> [cmd |-> "empty", entries |-> <<>>]]
    /\ commitIndex = [n \in ServerSet |-> 0]
    /\ nextIndex = [n \in ServerSet |-> [s \in ServerSet |-> 1]]
    /\ matchIndex = [n \in ServerSet |-> [s \in ServerSet |-> 0]]
    /\ votedFor = [n \in ServerSet |-> Nil]
    /\ votesResponded = [n \in ServerSet |-> {}]
    /\ votesGranted = [n \in ServerSet |-> {}]
    /\ leader = [n \in ServerSet |-> Nil]
    /\ sm = [n \in ServerSet |-> [x \in {} |-> 0]]
    /\ smDomain = [n \in ServerSet |-> {}]
    /\ leaderTimeout = [n \in ServerSet |-> LeaderTimeoutReset]
    /\ appendEntriesCh = [n \in ServerSet |-> FALSE]
    /\ becomeLeaderCh = [n \in ServerSet |-> FALSE]
    /\ reqCh = [c \in ClientSet |-> [type |-> "none"]]
    /\ respCh = [c \in ClientSet |-> [type |-> "none"]]
    /\ timeout = [c \in ClientSet |-> FALSE]

ServerRequestVote(i) ==
    /\ netEnabled[i]
    /\ leaderTimeout[i] = 0
    /\ Cardinality(net[i]) = 0
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ \E j \in ServerSet \ {i}:
        net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> RequestVoteRequest,
                                               mterm |-> currentTerm[i],
                                               mlastLogTerm |-> LastTerm(log[i]),
                                               mlastLogIndex |-> Len(log[i]),
                                               msource |-> i,
                                               mdest |-> j])]
    /\ UNCHANGED <<log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleRequestVoteRequest(i, j) ==
    /\ netEnabled[i]
    /\ \E msg \in net[i]:
        /\ msg.mtype = RequestVoteRequest
        /\ msg.mdest = i
        /\ msg.mterm <= currentTerm[i]
        /\ LET logOK == \/ msg.mlastLogTerm > LastTerm(log[i])
                       \/ /\ msg.mlastLogTerm = LastTerm(log[i])
                          /\ msg.mlastLogIndex >= Len(log[i])
           grant == /\ msg.mterm = currentTerm[i]
                   /\ logOK
                   /\ votedFor[i] \in {Nil, j}
        IN
        /\ IF msg.mterm > currentTerm[i] THEN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
           ELSE UNCHANGED <<currentTerm, state, votedFor, leader>>
        /\ IF grant THEN votedFor' = [votedFor EXCEPT ![i] = j] ELSE UNCHANGED votedFor
        /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> RequestVoteResponse,
                                                mterm |-> currentTerm[i],
                                                mvoteGranted |-> grant,
                                                msource |-> i,
                                                mdest |-> j])]
        /\ net' = [net' EXCEPT ![i] = Delete(net[i], msg)]
    /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleRequestVoteResponse(i, j) ==
    /\ netEnabled[i]
    /\ \E msg \in net[i]:
        /\ msg.mtype = RequestVoteResponse
        /\ msg.mdest = i
        /\ msg.mterm <= currentTerm[i]
        /\ IF msg.mterm > currentTerm[i] THEN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
           ELSE UNCHANGED <<currentTerm, state, votedFor, leader>>
        /\ IF msg.mterm = currentTerm[i] THEN
             /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \union {j}]
             /\ IF msg.mvoteGranted THEN
                  /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = LeaderTimeoutReset]
                  /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \union {j}]
                  /\ IF state[i] = Candidate /\ IsQuorum(votesGranted[i] \union {j}) THEN
                       becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = TRUE]
                    ELSE UNCHANGED becomeLeaderCh
                ELSE UNCHANGED <<leaderTimeout, votesGranted, becomeLeaderCh>>
           ELSE UNCHANGED <<votesResponded, votesGranted, leaderTimeout, becomeLeaderCh>>
        /\ net' = [net EXCEPT ![i] = Delete(net[i], msg)]
    /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain, appendEntriesCh, reqCh, respCh, timeout>>

HandleAppendEntriesRequest(i, j) ==
    /\ netEnabled[i]
    /\ \E msg \in net[i]:
        /\ msg.mtype = AppendEntriesRequest
        /\ msg.mdest = i
        /\ msg.mterm <= currentTerm[i]
        /\ LET logOK == \/ msg.mprevLogIndex = 0
                       \/ /\ msg.mprevLogIndex > 0
                          /\ msg.mprevLogIndex <= Len(log[i])
                          /\ msg.mprevLogTerm = log[i][msg.mprevLogIndex].term
           IN
        /\ IF msg.mterm > currentTerm[i] THEN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
           ELSE UNCHANGED <<currentTerm, state, votedFor, leader>>
        /\ IF msg.mterm = currentTerm[i] THEN
             /\ leader' = [leader EXCEPT ![i] = j]
             /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = LeaderTimeoutReset]
             /\ IF state[i] = Candidate THEN state' = [state EXCEPT ![i] = Follower] ELSE UNCHANGED state
           ELSE UNCHANGED <<leader, leaderTimeout, state>>
        /\ IF \/ msg.mterm < currentTerm[i]
              \/ /\ msg.mterm = currentTerm[i]
                 /\ state[i] = Follower
                 /\ ~logOK
           THEN
             /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> AppendEntriesResponse,
                                                     mterm |-> currentTerm[i],
                                                     msuccess |-> FALSE,
                                                     mmatchIndex |-> 0,
                                                     msource |-> i,
                                                     mdest |-> j])]
             /\ net' = [net' EXCEPT ![i] = Delete(net[i], msg)]
           ELSE 
             /\ LET newLog == SubSeq(log[i], 1, msg.mprevLogIndex) \o msg.mentries
                result == ApplyLog(newLog, commitIndex[i]+1, msg.mcommitIndex, sm[i], smDomain[i])
             IN
             /\ log' = [log EXCEPT ![i] = newLog]
             /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> msg.mentries]]
             /\ sm' = [sm EXCEPT ![i] = result[1]]
             /\ smDomain' = [smDomain EXCEPT ![i] = result[2]]
             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], msg.mcommitIndex})]
             /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> AppendEntriesResponse,
                                                     mterm |-> currentTerm[i],
                                                     msuccess |-> TRUE,
                                                     mmatchIndex |-> msg.mprevLogIndex + Len(msg.mentries),
                                                     msource |-> i,
                                                     mdest |-> j])]
             /\ net' = [net' EXCEPT ![i] = Delete(net[i], msg)]
    /\ UNCHANGED <<netEnabled, fd, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleAppendEntriesResponse(i, j) ==
    /\ netEnabled[i]
    /\ \E msg \in net[i]:
        /\ msg.mtype = AppendEntriesResponse
        /\ msg.mdest = i
        /\ msg.mterm <= currentTerm[i]
        /\ IF msg.mterm > currentTerm[i] THEN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
           ELSE UNCHANGED <<currentTerm, state, votedFor, leader>>
        /\ IF msg.mterm = currentTerm[i] THEN
             /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = LeaderTimeoutReset]
             /\ IF msg.msuccess THEN
                  /\ nextIndex' = [nextIndex EXCEPT ![i][j] = msg.mmatchIndex + 1]
                  /\ matchIndex' = [matchIndex EXCEPT ![i][j] = msg.mmatchIndex]
                ELSE
                  /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
                  /\ UNCHANGED matchIndex
           ELSE UNCHANGED <<leaderTimeout, nextIndex, matchIndex>>
        /\ net' = [net EXCEPT ![i] = Delete(net[i], msg)]
    /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, votedFor, votesResponded, votesGranted, sm, smDomain, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

BecomeLeader(i) ==
    /\ becomeLeaderCh[i]
    /\ netEnabled[i]
    /\ state[i] = Candidate
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [s \in ServerSet |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [s \in ServerSet |-> 0]]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
    /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<net, netEnabled, fd, currentTerm, log, plog, commitIndex, votedFor, votesResponded, votesGranted, sm, smDomain, leaderTimeout, reqCh, respCh, timeout>>

AdvanceCommitIndex(i) ==
    /\ netEnabled[i]
    /\ state[i] = Leader
    /\ LET N == FindMaxAgreeIndex(log[i], i, matchIndex[i])
       newCommitIndex == IF N # Nil /\ log[i][N].term = currentTerm[i] THEN N ELSE commitIndex[i]
       IN
       /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<net, netEnabled, fd, state, currentTerm, log, plog, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

ApplyCommittedEntries(i) ==
    /\ commitIndex[i] > 0
    /\ \E k \in 1..commitIndex[i]:
        k > commitIndex[i]
    /\ UNCHANGED vars

ClientSendRequest(c) ==
    /\ netEnabled[c]
    /\ reqCh[c] # [type |-> "none"]
    /\ LET leaderHint == IF leader[c] = Nil THEN CHOOSE s \in ServerSet: TRUE ELSE leader[c]
       IN
       /\ net' = [net EXCEPT ![leaderHint] = Append(net[leaderHint], [mtype |-> IF reqCh[c].type = Put THEN ClientPutRequest ELSE ClientGetRequest,
                                                            mcmd |-> [idx |-> c, type |-> reqCh[c].type, key |-> reqCh[c].key, value |-> reqCh[c].value],
                                                            msource |-> c,
                                                            mdest |-> leaderHint])]
    /\ reqCh' = [reqCh EXCEPT ![c] = [type |-> "none"]]
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, respCh, timeout>>

ClientHandleResponse(c) ==
    /\ netEnabled[c]
    /\ \E msg \in net[c]:
        /\ msg.mtype \in {ClientPutResponse, ClientGetResponse}
        /\ msg.mdest = c
        /\ respCh' = [respCh EXCEPT ![c] = msg]
        /\ net' = [net EXCEPT ![c] = Delete(net[c], msg)]
    /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, timeout>>

Next ==
    \/ \E i \in ServerSet: ServerRequestVote(i)
    \/ \E i \in ServerSet: \E j \in ServerSet: HandleRequestVoteRequest(i, j)
    \/ \E i \in ServerSet: \E j \in ServerSet: HandleRequestVoteResponse(i, j)
    \/ \E i \in ServerSet: \E j \in ServerSet: HandleAppendEntriesRequest(i, j)
    \/ \E i \in ServerSet: \E j \in ServerSet: HandleAppendEntriesResponse(i, j)
    \/ \E i \in ServerSet: BecomeLeader(i)
    \/ \E i \in ServerSet: AdvanceCommitIndex(i)
    \/ \E i \in ServerSet: ApplyCommittedEntries(i)
    \/ \E c \in ClientSet: ClientSendRequest(c)
    \/ \E c \in ClientSet: ClientHandleResponse(c)

Spec == Init /\ [][Next]_vars

====