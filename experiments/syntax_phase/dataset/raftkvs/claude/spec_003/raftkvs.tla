---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, MaxNodeFail, LeaderTimeoutReset, AllStrings

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
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex,
          votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
          appendEntriesCh, becomeLeaderCh, net, netLen, netEnabled, fd, messages>>

ServerSet == 1..NumServers
ClientSet == (NumServers * 6 + 1)..(NumServers * 6 + NumClients)
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
Nil == 0

IsQuorum(s) == Cardinality(s) * 2 > NumServers

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

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
    /\ sm = [i \in ServerSet |-> [k \in {} |-> ""]]
    /\ smDomain = [i \in ServerSet |-> {}]
    /\ leaderTimeout = TRUE
    /\ appendEntriesCh = [i \in ServerSet |-> FALSE]
    /\ becomeLeaderCh = [i \in ServerSet |-> FALSE]
    /\ net = [i \in NodeSet |-> <<>>]
    /\ netLen = [i \in NodeSet |-> 0]
    /\ netEnabled = [i \in NodeSet |-> TRUE]
    /\ fd = [i \in NodeSet |-> FALSE]
    /\ messages = {}

LeaderTimeout(i) ==
    /\ i \in ServerSet
    /\ leaderTimeout
    /\ netLen[i] = 0
    /\ state[i] \in {StateFollower, StateCandidate}
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain,
                   leaderTimeout, appendEntriesCh, becomeLeaderCh, net, netLen,
                   netEnabled, fd, messages>>

RequestVote(i, j) ==
    /\ i \in ServerSet
    /\ j \in ServerSet
    /\ i # j
    /\ state[i] = StateCandidate
    /\ LET msg == [mtype |-> RequestVoteRequest,
                   mterm |-> currentTerm[i],
                   mlastLogTerm |-> LastTerm(log[i]),
                   mlastLogIndex |-> Len(log[i]),
                   msource |-> i,
                   mdest |-> j]
       IN /\ net' = [net EXCEPT ![j] = Append(net[j], msg)]
          /\ netLen' = [netLen EXCEPT ![j] = netLen[j] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex,
                   matchIndex, votesResponded, votesGranted, leader, sm, smDomain,
                   leaderTimeout, appendEntriesCh, becomeLeaderCh, netEnabled, fd, messages>>

HandleRequestVoteRequest(i) ==
    /\ i \in ServerSet
    /\ netLen[i] > 0
    /\ LET msg == Head(net[i])
       IN /\ msg.mtype = RequestVoteRequest
          /\ msg.mdest = i
          /\ IF msg.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ LET logOK == \/ msg.mlastLogTerm > LastTerm(log[i])
                          \/ /\ msg.mlastLogTerm = LastTerm(log[i])
                             /\ msg.mlastLogIndex >= Len(log[i])
                 grant == /\ msg.mterm = currentTerm'[i]
                          /\ logOK
                          /\ votedFor'[i] \in {Nil, msg.msource}
             IN /\ IF grant
                   THEN votedFor' = [votedFor' EXCEPT ![i] = msg.msource]
                   ELSE UNCHANGED votedFor'
                /\ LET response == [mtype |-> RequestVoteResponse,
                                    mterm |-> currentTerm'[i],
                                    mvoteGranted |-> grant,
                                    msource |-> i,
                                    mdest |-> msg.msource]
                   IN /\ net' = [net EXCEPT ![msg.msource] = Append(net[msg.msource], response),
                                            ![i] = Tail(net[i])]
                      /\ netLen' = [netLen EXCEPT ![msg.msource] = netLen[msg.msource] + 1,
                                                  ![i] = netLen[i] - 1]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votesResponded,
                   votesGranted, sm, smDomain, leaderTimeout, appendEntriesCh,
                   becomeLeaderCh, netEnabled, fd, messages>>

HandleRequestVoteResponse(i) ==
    /\ i \in ServerSet
    /\ netLen[i] > 0
    /\ LET msg == Head(net[i])
       IN /\ msg.mtype = RequestVoteResponse
          /\ msg.mdest = i
          /\ IF msg.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ IF msg.mterm = currentTerm'[i]
             THEN /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {msg.msource}]
                  /\ IF msg.mvoteGranted
                     THEN /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {msg.msource}]
                          /\ IF /\ state'[i] = StateCandidate
                                /\ IsQuorum(votesGranted'[i])
                             THEN becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = TRUE]
                             ELSE UNCHANGED becomeLeaderCh
                     ELSE /\ UNCHANGED <<votesGranted, becomeLeaderCh>>
             ELSE /\ UNCHANGED <<votesResponded, votesGranted, becomeLeaderCh>>
          /\ net' = [net EXCEPT ![i] = Tail(net[i])]
          /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, sm, smDomain,
                   leaderTimeout, appendEntriesCh, netEnabled, fd, messages>>

BecomeLeader(i) ==
    /\ i \in ServerSet
    /\ becomeLeaderCh[i]
    /\ state[i] = StateCandidate
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
    /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesResponded,
                   votesGranted, sm, smDomain, leaderTimeout, net, netLen,
                   netEnabled, fd, messages>>

AppendEntries(i, j) ==
    /\ i \in ServerSet
    /\ j \in ServerSet
    /\ i # j
    /\ state[i] = StateLeader
    /\ appendEntriesCh[i]
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
           entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
           msg == [mtype |-> AppendEntriesRequest,
                   mterm |-> currentTerm[i],
                   mprevLogIndex |-> prevLogIndex,
                   mprevLogTerm |-> prevLogTerm,
                   mentries |-> entries,
                   mcommitIndex |-> commitIndex[i],
                   msource |-> i,
                   mdest |-> j]
       IN /\ net' = [net EXCEPT ![j] = Append(net[j], msg)]
          /\ netLen' = [netLen EXCEPT ![j] = netLen[j] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex,
                   matchIndex, votesResponded, votesGranted, leader, sm, smDomain,
                   leaderTimeout, appendEntriesCh, becomeLeaderCh, netEnabled, fd, messages>>

HandleAppendEntriesRequest(i) ==
    /\ i \in ServerSet
    /\ netLen[i] > 0
    /\ LET msg == Head(net[i])
       IN /\ msg.mtype = AppendEntriesRequest
          /\ msg.mdest = i
          /\ IF msg.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ IF msg.mterm = currentTerm'[i]
             THEN /\ leader' = [leader' EXCEPT ![i] = msg.msource]
                  /\ IF state'[i] = StateCandidate
                     THEN state' = [state' EXCEPT ![i] = StateFollower]
                     ELSE UNCHANGED state'
             ELSE /\ UNCHANGED <<state', leader'>>
          /\ LET logOK == \/ msg.mprevLogIndex = 0
                          \/ /\ msg.mprevLogIndex > 0
                             /\ msg.mprevLogIndex <= Len(log[i])
                             /\ msg.mprevLogTerm = log[i][msg.mprevLogIndex].term
             IN /\ IF /\ msg.mterm = currentTerm'[i]
                      /\ state'[i] = StateFollower
                      /\ logOK
                   THEN /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, msg.mprevLogIndex) \o msg.mentries]
                        /\ commitIndex' = [commitIndex EXCEPT ![i] = 
                                          IF msg.mcommitIndex <= Len(log'[i])
                                          THEN msg.mcommitIndex
                                          ELSE commitIndex[i]]
                        /\ LET response == [mtype |-> AppendEntriesResponse,
                                            mterm |-> currentTerm'[i],
                                            msuccess |-> TRUE,
                                            mmatchIndex |-> msg.mprevLogIndex + Len(msg.mentries),
                                            msource |-> i,
                                            mdest |-> msg.msource]
                           IN /\ net' = [net EXCEPT ![msg.msource] = Append(net[msg.msource], response),
                                                    ![i] = Tail(net[i])]
                              /\ netLen' = [netLen EXCEPT ![msg.msource] = netLen[msg.msource] + 1,
                                                          ![i] = netLen[i] - 1]
                   ELSE /\ LET response == [mtype |-> AppendEntriesResponse,
                                            mterm |-> currentTerm'[i],
                                            msuccess |-> FALSE,
                                            mmatchIndex |-> 0,
                                            msource |-> i,
                                            mdest |-> msg.msource]
                           IN /\ net' = [net EXCEPT ![msg.msource] = Append(net[msg.msource], response),
                                                    ![i] = Tail(net[i])]
                              /\ netLen' = [netLen EXCEPT ![msg.msource] = netLen[msg.msource] + 1,
                                                          ![i] = netLen[i] - 1]
                        /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<votesResponded, votesGranted, sm, smDomain, leaderTimeout,
                   appendEntriesCh, becomeLeaderCh, netEnabled, fd, messages>>

HandleAppendEntriesResponse(i) ==
    /\ i \in ServerSet
    /\ netLen[i] > 0
    /\ LET msg == Head(net[i])
       IN /\ msg.mtype = AppendEntriesResponse
          /\ msg.mdest = i
          /\ IF msg.mterm > currentTerm[i]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.mterm]
                  /\ state' = [state EXCEPT ![i] = StateFollower]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ leader' = [leader EXCEPT ![i] = Nil]
             ELSE /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
          /\ IF msg.mterm = currentTerm'[i]
             THEN /\ IF msg.msuccess
                     THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![msg.msource] = msg.mmatchIndex + 1]]
                          /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![msg.msource] = msg.mmatchIndex]]
                     ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![msg.msource] = 
                                          IF nextIndex[i][msg.msource] > 1
                                          THEN nextIndex[i][msg.msource] - 1
                                          ELSE 1]]
                          /\ UNCHANGED matchIndex
             ELSE /\ UNCHANGED <<nextIndex, matchIndex>>
          /\ net' = [net EXCEPT ![i] = Tail(net[i])]
          /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
    /\ UNCHANGED <<log, commitIndex, votesResponded, votesGranted, sm, smDomain,
                   leaderTimeout, appendEntriesCh, becomeLeaderCh, netEnabled, fd, messages>>

ClientRequest(i, cmd) ==
    /\ i \in ServerSet
    /\ state[i] = StateLeader
    /\ LET entry == [term |-> currentTerm[i], cmd |-> cmd, client |-> i]
       IN /\ log' = [log EXCEPT ![i] = Append(log[i], entry)]
          /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex,
                   votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout,
                   becomeLeaderCh, net, netLen, netEnabled, fd, messages>>

AdvanceCommitIndex(i) ==
    /\ i \in ServerSet
    /\ state[i] = StateLeader
    /\ \E index \in (commitIndex[i] + 1)..Len(log[i]) :
        /\ log[i][index].term = currentTerm[i]
        /\ IsQuorum({i} \cup {j \in ServerSet : matchIndex[i][j] >= index})
        /\ commitIndex' = [commitIndex EXCEPT ![i] = index]
        /\ IF log[i][index].cmd.type = Put
           THEN /\ sm' = [sm EXCEPT ![i] = (sm[i] @@ (log[i][index].cmd.key :> log[i][index].cmd.value))]
                /\ smDomain' = [smDomain EXCEPT ![i] = smDomain[i] \cup {log[i][index].cmd.key}]
           ELSE UNCHANGED <<sm, smDomain>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex,
                   votesResponded, votesGranted, leader, leaderTimeout,
                   appendEntriesCh, becomeLeaderCh, net, netLen, netEnabled, fd, messages>>

Next ==
    \/ \E i \in ServerSet : LeaderTimeout(i)
    \/ \E i, j \in ServerSet : RequestVote(i, j)
    \/ \E i \in ServerSet : HandleRequestVoteRequest(i)
    \/ \E i \in ServerSet : HandleRequestVoteResponse(i)
    \/ \E i \in ServerSet : BecomeLeader(i)
    \/ \E i, j \in ServerSet : AppendEntries(i, j)
    \/ \E i \in ServerSet : HandleAppendEntriesRequest(i)
    \/ \E i \in ServerSet : HandleAppendEntriesResponse(i)
    \/ \E i \in ServerSet, cmd \in [type : {Put, Get}, key : AllStrings, value : AllStrings] : ClientRequest(i, cmd)
    \/ \E i \in ServerSet : AdvanceCommitIndex(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====