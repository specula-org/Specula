---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, MaxNodeFail, ExploreFail, Debug, LeaderTimeoutReset, AllStrings, LogPop, LogConcat

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    votesResponded,
    votesGranted,
    leader,
    sm,
    smDomain,
    leaderTimeout,
    appendEntriesCh,
    becomeLeaderCh,
    net,
    netLen,
    netEnabled,
    fd,
    plog,
    reqCh,
    respCh,
    timeout

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, 
          votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
          appendEntriesCh, becomeLeaderCh, net, netLen, netEnabled, fd, plog,
          reqCh, respCh, timeout>>

Nil == 0
ServerSet == 1..NumServers
ClientSet == (6*NumServers+1)..(6*NumServers+NumClients)
NodeSet == ServerSet \cup ClientSet

StateFollower == "follower"
StateCandidate == "candidate"
StateLeader == "leader"

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

Put == "put"
Get == "get"

IsQuorum(s) == Cardinality(s) * 2 > NumServers

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

RECURSIVE ApplyLog(_, _, _, _, _)

Init ==
    /\ state = [i \in ServerSet |-> StateFollower]
    /\ currentTerm = [i \in ServerSet |-> 0]
    /\ votedFor = [i \in ServerSet |-> Nil]
    /\ log = [i \in ServerSet |-> <<>>]
    /\ commitIndex = [i \in ServerSet |-> 0]
    /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
    /\ matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]
    /\ votesResponded = [i \in ServerSet |-> {}]
    /\ votesGranted = [i \in ServerSet |-> {}]
    /\ leader = [i \in ServerSet |-> Nil]
    /\ sm = [i \in ServerSet |-> [k \in {} |-> Nil]]
    /\ smDomain = [i \in ServerSet |-> {}]
    /\ leaderTimeout = FALSE
    /\ appendEntriesCh = [i \in ServerSet |-> FALSE]
    /\ becomeLeaderCh = [i \in ServerSet |-> FALSE]
    /\ net = [i \in NodeSet |-> <<>>]
    /\ netLen = [i \in NodeSet |-> 0]
    /\ netEnabled = [i \in NodeSet |-> TRUE]
    /\ fd = [i \in NodeSet |-> FALSE]
    /\ plog = [i \in ServerSet |-> [cmd |-> "", entries |-> <<>>, cnt |-> 0]]
    /\ reqCh = <<>>
    /\ respCh = <<>>
    /\ timeout = FALSE

LeaderTimeout ==
    /\ leaderTimeout = FALSE
    /\ \E i \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ netLen[i] = 0
        /\ state[i] \in {StateFollower, StateCandidate}
        /\ state' = [state EXCEPT ![i] = StateCandidate]
        /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
        /\ votedFor' = [votedFor EXCEPT ![i] = i]
        /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
        /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
        /\ leader' = [leader EXCEPT ![i] = Nil]
        /\ leaderTimeout' = TRUE
        /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain,
                      appendEntriesCh, becomeLeaderCh, net, netLen, netEnabled, 
                      fd, plog, reqCh, respCh, timeout>>

RequestVoteRequest(i, j) ==
    /\ netEnabled[i] = TRUE
    /\ state[i] = StateCandidate
    /\ i # j
    /\ \/ /\ fd[j] = FALSE
          /\ net' = [net EXCEPT ![j] = Append(net[j], 
                [mtype |-> RequestVoteRequest,
                 mterm |-> currentTerm[i],
                 mlastLogTerm |-> LastTerm(log[i]),
                 mlastLogIndex |-> Len(log[i]),
                 msource |-> i,
                 mdest |-> j])]
          /\ netLen' = [netLen EXCEPT ![j] = netLen[j] + 1]
       \/ /\ fd[j] = TRUE
          /\ UNCHANGED <<net, netLen>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex,
                  matchIndex, votesResponded, votesGranted, leader, sm, smDomain,
                  leaderTimeout, appendEntriesCh, becomeLeaderCh, netEnabled, fd,
                  plog, reqCh, respCh, timeout>>

RequestVoteResponse(i) ==
    /\ netEnabled[i] = TRUE
    /\ netLen[i] > 0
    /\ LET m == Head(net[i])
       IN /\ m.mdest = i
          /\ m.mtype = RequestVoteRequest
          /\ IF m.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ LET logOK == \/ m.mlastLogTerm > LastTerm(log[i])
                          \/ /\ m.mlastLogTerm = LastTerm(log[i])
                             /\ m.mlastLogIndex >= Len(log[i])
                 grant == /\ m.mterm = currentTerm'[i]
                          /\ logOK
                          /\ votedFor'[i] \in {Nil, m.msource}
             IN /\ IF grant
                   THEN votedFor' = [votedFor' EXCEPT ![i] = m.msource]
                   ELSE UNCHANGED votedFor'
                /\ \/ /\ fd[m.msource] = FALSE
                      /\ net' = [net EXCEPT ![m.msource] = Append(net[m.msource],
                            [mtype |-> RequestVoteResponse,
                             mterm |-> currentTerm'[i],
                             mvoteGranted |-> grant,
                             msource |-> i,
                             mdest |-> m.msource])]
                      /\ netLen' = [netLen EXCEPT ![m.msource] = netLen[m.msource] + 1]
                   \/ /\ fd[m.msource] = TRUE
                      /\ UNCHANGED <<net, netLen>>
          /\ net' = [net' EXCEPT ![i] = Tail(net'[i])]
          /\ netLen' = [netLen' EXCEPT ![i] = netLen'[i] - 1]
          /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesResponded,
                        votesGranted, sm, smDomain, leaderTimeout, appendEntriesCh,
                        becomeLeaderCh, netEnabled, fd, plog, reqCh, respCh, timeout>>

HandleRequestVoteResponse(i) ==
    /\ netEnabled[i] = TRUE
    /\ netLen[i] > 0
    /\ LET m == Head(net[i])
       IN /\ m.mdest = i
          /\ m.mtype = RequestVoteResponse
          /\ IF m.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ IF m.mterm < currentTerm'[i]
             THEN /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                  /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
                  /\ UNCHANGED <<votesResponded, votesGranted, leaderTimeout, becomeLeaderCh>>
             ELSE /\ m.mterm = currentTerm'[i]
                  /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {m.msource}]
                  /\ IF m.mvoteGranted
                     THEN /\ leaderTimeout' = LeaderTimeoutReset
                          /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {m.msource}]
                          /\ IF /\ state'[i] = StateCandidate
                                /\ IsQuorum(votesGranted'[i])
                             THEN becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = TRUE]
                             ELSE UNCHANGED becomeLeaderCh
                     ELSE /\ UNCHANGED <<leaderTimeout, votesGranted, becomeLeaderCh>>
                  /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                  /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
          /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain,
                        appendEntriesCh, netEnabled, fd, plog, reqCh, respCh, timeout>>

AppendEntriesRequest(i, j) ==
    /\ netEnabled[i] = TRUE
    /\ state[i] = StateLeader
    /\ i # j
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
           entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
       IN /\ \/ /\ fd[j] = FALSE
                /\ net' = [net EXCEPT ![j] = Append(net[j],
                      [mtype |-> AppendEntriesRequest,
                       mterm |-> currentTerm[i],
                       mprevLogIndex |-> prevLogIndex,
                       mprevLogTerm |-> prevLogTerm,
                       mentries |-> entries,
                       mcommitIndex |-> commitIndex[i],
                       msource |-> i,
                       mdest |-> j])]
                /\ netLen' = [netLen EXCEPT ![j] = netLen[j] + 1]
             \/ /\ fd[j] = TRUE
                /\ UNCHANGED <<net, netLen>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex,
                  matchIndex, votesResponded, votesGranted, leader, sm, smDomain,
                  leaderTimeout, appendEntriesCh, becomeLeaderCh, netEnabled, fd,
                  plog, reqCh, respCh, timeout>>

AppendEntriesResponse(i) ==
    /\ netEnabled[i] = TRUE
    /\ netLen[i] > 0
    /\ LET m == Head(net[i])
       IN /\ m.mdest = i
          /\ m.mtype = AppendEntriesRequest
          /\ IF m.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ IF m.mterm = currentTerm'[i]
             THEN /\ leader' = [leader' EXCEPT ![i] = m.msource]
                  /\ leaderTimeout' = LeaderTimeoutReset
             ELSE /\ UNCHANGED <<leader', leaderTimeout>>
          /\ IF /\ m.mterm = currentTerm'[i]
                /\ state'[i] = StateCandidate
             THEN state' = [state' EXCEPT ![i] = StateFollower]
             ELSE UNCHANGED state'
          /\ LET logOK == \/ m.mprevLogIndex = 0
                          \/ /\ m.mprevLogIndex > 0
                             /\ m.mprevLogIndex <= Len(log[i])
                             /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
             IN IF \/ m.mterm < currentTerm'[i]
                   \/ /\ m.mterm = currentTerm'[i]
                      /\ state'[i] = StateFollower
                      /\ ~logOK
                THEN /\ \/ /\ fd[m.msource] = FALSE
                           /\ net' = [net EXCEPT ![m.msource] = Append(net[m.msource],
                                 [mtype |-> AppendEntriesResponse,
                                  mterm |-> currentTerm'[i],
                                  msuccess |-> FALSE,
                                  mmatchIndex |-> 0,
                                  msource |-> i,
                                  mdest |-> m.msource])]
                           /\ netLen' = [netLen EXCEPT ![m.msource] = netLen[m.msource] + 1]
                        \/ /\ fd[m.msource] = TRUE
                           /\ UNCHANGED <<net, netLen>>
                     /\ net' = [net' EXCEPT ![i] = Tail(net'[i])]
                     /\ netLen' = [netLen' EXCEPT ![i] = netLen'[i] - 1]
                     /\ UNCHANGED <<log, commitIndex, sm, smDomain, plog>>
                ELSE /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries]
                     /\ LET result == ApplyLog(log'[i], commitIndex[i] + 1, m.mcommitIndex, sm[i], smDomain[i])
                        IN /\ sm' = [sm EXCEPT ![i] = result[1]]
                           /\ smDomain' = [smDomain EXCEPT ![i] = result[2]]
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], m.mcommitIndex})]
                     /\ \/ /\ fd[m.msource] = FALSE
                           /\ net' = [net EXCEPT ![m.msource] = Append(net[m.msource],
                                 [mtype |-> AppendEntriesResponse,
                                  mterm |-> currentTerm'[i],
                                  msuccess |-> TRUE,
                                  mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                                  msource |-> i,
                                  mdest |-> m.msource])]
                           /\ netLen' = [netLen EXCEPT ![m.msource] = netLen[m.msource] + 1]
                        \/ /\ fd[m.msource] = TRUE
                           /\ UNCHANGED <<net, netLen>>
                     /\ net' = [net' EXCEPT ![i] = Tail(net'[i])]
                     /\ netLen' = [netLen' EXCEPT ![i] = netLen'[i] - 1]
                     /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> m.mentries]]
          /\ UNCHANGED <<votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh,
                        netEnabled, fd, reqCh, respCh, timeout>>

HandleAppendEntriesResponse(i) ==
    /\ netEnabled[i] = TRUE
    /\ netLen[i] > 0
    /\ LET m == Head(net[i])
       IN /\ m.mdest = i
          /\ m.mtype = AppendEntriesResponse
          /\ IF m.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ IF m.mterm < currentTerm'[i]
             THEN /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                  /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
                  /\ UNCHANGED <<nextIndex, matchIndex, leaderTimeout>>
             ELSE /\ leaderTimeout' = LeaderTimeoutReset
                  /\ IF m.msuccess
                     THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.msource] = m.mmatchIndex + 1]]
                          /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![m.msource] = m.mmatchIndex]]
                     ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.msource] = Max({nextIndex[i][m.msource] - 1, 1})]]
                          /\ UNCHANGED matchIndex
                  /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                  /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
          /\ UNCHANGED <<log, commitIndex, votesResponded, votesGranted, sm, smDomain,
                        appendEntriesCh, becomeLeaderCh, netEnabled, fd, plog, reqCh, respCh, timeout>>

BecomeLeader(i) ==
    /\ netEnabled[i] = TRUE
    /\ becomeLeaderCh[i] = TRUE
    /\ state[i] = StateCandidate
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesResponded,
                  votesGranted, sm, smDomain, leaderTimeout, becomeLeaderCh,
                  net, netLen, netEnabled, fd, plog, reqCh, respCh, timeout>>

ClientRequest(i) ==
    /\ netEnabled[i] = TRUE
    /\ state[i] = StateLeader
    /\ \E c \in ClientSet :
        /\ netLen[c] > 0
        /\ LET m == Head(net[c])
           IN /\ m.mdest = i
              /\ m.mtype \in {ClientPutRequest, ClientGetRequest}
              /\ LET entry == [term |-> currentTerm[i],
                              cmd |-> m.mcmd,
                              client |-> m.msource]
                 IN /\ log' = [log EXCEPT ![i] = Append(log[i], entry)]
                    /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> <<entry>>]]
                    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
              /\ net' = [net EXCEPT ![c] = Tail(net[c])]
              /\ netLen' = [netLen EXCEPT ![c] = netLen[c] - 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex,
                  votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                  becomeLeaderCh, netEnabled, fd, reqCh, respCh, timeout>>

AdvanceCommitIndex(i) ==
    /\ netEnabled[i] = TRUE
    /\ state[i] = StateLeader
    /\ \E newCommitIndex \in (commitIndex[i] + 1)..Len(log[i]) :
        /\ log[i][newCommitIndex].term = currentTerm[i]
        /\ IsQuorum({i} \cup {j \in ServerSet : matchIndex[i][j] >= newCommitIndex})
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
        /\ LET entry == log[i][newCommitIndex]
               cmd == entry.cmd
               respType == IF cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
           IN /\ IF cmd.type = Put
                 THEN /\ sm' = [sm EXCEPT ![i] = sm[i] @@ (cmd.key :> cmd.value)]
                      /\ smDomain' = [smDomain EXCEPT ![i] = smDomain[i] \cup {cmd.key}]
                 ELSE UNCHANGED <<sm, smDomain>>
              /\ LET reqOK == cmd.key \in smDomain'[i]
                 IN /\ net' = [net EXCEPT ![entry.client] = Append(net[entry.client],
                          [mtype |-> respType,
                           msuccess |-> TRUE,
                           mresponse |-> [idx |-> cmd.idx,
                                         key |-> cmd.key,
                                         value |-> IF reqOK THEN sm'[i][cmd.key] ELSE Nil,
                                         ok |-> reqOK],
                           mleaderHint |-> i,
                           msource |-> i,
                           mdest |-> entry.client])]
                    /\ netLen' = [netLen EXCEPT ![entry.client] = netLen[entry.client] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex,
                  votesResponded, votesGranted, leader, leaderTimeout,
                  appendEntriesCh, becomeLeaderCh, netEnabled, fd, plog, reqCh, respCh, timeout>>

ApplyLog(xlog, start, end, xsm, xsmDomain) ==
    IF start > end
    THEN <<xsm, xsmDomain>>
    ELSE LET entry == xlog[start]
             cmd == entry.cmd
             result == IF cmd.type = Put
                      THEN <<xsm @@ (cmd.key :> cmd.value), xsmDomain \cup {cmd.key}>>
                      ELSE <<xsm, xsmDomain>>
         IN ApplyLog(xlog, start + 1, end, result[1], result[2])

Max(s) == CHOOSE x \in s : \A y \in s : x >= y

Next ==
    \/ LeaderTimeout
    \/ \E i, j \in ServerSet : RequestVoteRequest(i, j)
    \/ \E i \in ServerSet : RequestVoteResponse(i)
    \/ \E i \in ServerSet : HandleRequestVoteResponse(i)
    \/ \E i, j \in ServerSet : AppendEntriesRequest(i, j)
    \/ \E i \in ServerSet : AppendEntriesResponse(i)
    \/ \E i \in ServerSet : HandleAppendEntriesResponse(i)
    \/ \E i \in ServerSet : BecomeLeader(i)
    \/ \E i \in ServerSet : ClientRequest(i)
    \/ \E i \in ServerSet : AdvanceCommitIndex(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====