---- MODULE raftkvs ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, MaxNodeFail, ExploreFail, Debug, LeaderTimeoutReset, LogPop, LogConcat, AllStrings

VARIABLES net, netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout

Vars == <<net, netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

Nil == 0

Min(s) == 
  LET e == CHOOSE element \in s : TRUE
  IN MinAcc(s \ {e}, e)

MinAcc(s, e) ==
  IF s = {} THEN e
  ELSE LET e2 == CHOOSE element \in s : TRUE
       IN MinAcc(s \ {e2}, IF e2 < e THEN e2 ELSE e)

Max(s) ==
  LET e == CHOOSE element \in s : TRUE
  IN MaxAcc(s \ {e}, e)

MaxAcc(s, e) ==
  IF s = {} THEN e
  ELSE LET e2 == CHOOSE element \in s : TRUE
       IN MaxAcc(s \ {e2}, IF e2 > e THEN e2 ELSE e)

IsQuorum(s) == Cardinality(s) * 2 > NumServers

ServerSet == 1..NumServers

FindMaxAgreeIndex(logLocal, i, matchIndex) ==
  FindMaxAgreeIndexRec(logLocal, i, matchIndex, Len(logLocal))

FindMaxAgreeIndexRec(logLocal, i, matchIndex, index) ==
  IF index = 0 THEN Nil
  ELSE IF IsQuorum({i} \cup {k \in ServerSet : matchIndex[k] >= index})
       THEN index
       ELSE FindMaxAgreeIndexRec(logLocal, i, matchIndex, index - 1)

Put == "put"
Get == "get"

ApplyLogEntry(xentry, xsm, xsmDomain) ==
  LET cmd == xentry.cmd
  IN IF cmd.type = Put
     THEN <<xsm @@ (cmd.key :> cmd.value), xsmDomain \cup {cmd.key}>>
     ELSE <<xsm, xsmDomain>>

ApplyLog(xlog, start, end, xsm, xsmDomain) ==
  IF start > end THEN <<xsm, xsmDomain>>
  ELSE LET result == ApplyLogEntry(xlog[start], xsm, xsmDomain)
       IN ApplyLog(xlog, start + 1, end, result[1], result[2])

AllReqs == [type : {Put}, key : AllStrings, value : AllStrings] \cup
           [type : {Get}, key : AllStrings]

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

LastTerm(xlog) ==
  IF Len(xlog) = 0 THEN 0
  ELSE xlog[Len(xlog)].term

ServerRequestVoteSet == (1 * NumServers + 1)..(2 * NumServers)
ServerAppendEntriesSet == (2 * NumServers + 1)..(3 * NumServers)
ServerAdvanceCommitIndexSet == (3 * NumServers + 1)..(4 * NumServers)
ServerBecomeLeaderSet == (4 * NumServers + 1)..(5 * NumServers)

ServerCrasherSet ==
  IF ExploreFail THEN (5 * NumServers + 1)..(5 * NumServers + MaxNodeFail)
  ELSE {}

ClientSet == (6 * NumServers + 1)..(6 * NumServers + NumClients)

NodeSet == ServerSet \cup ClientSet

KeySet == {}

TypeOK ==
  /\ net \in [NodeSet -> Seq([mtype : STRING, msource : NodeSet, mdest : NodeSet])]
  /\ netLen \in [NodeSet -> Nat]
  /\ netEnabled \in [NodeSet -> BOOLEAN]
  /\ fd \in [NodeSet -> BOOLEAN]
  /\ state \in [ServerSet -> {StateFollower, StateCandidate, StateLeader}]
  /\ currentTerm \in [ServerSet -> Nat]
  /\ log \in [ServerSet -> Seq([term : Nat, cmd : [type : STRING, key : STRING]])]
  /\ commitIndex \in [ServerSet -> Nat]
  /\ nextIndex \in [ServerSet -> [ServerSet -> Nat]]
  /\ matchIndex \in [ServerSet -> [ServerSet -> Nat]]
  /\ votedFor \in [ServerSet -> ServerSet \cup {Nil}]
  /\ votesResponded \in [ServerSet -> SUBSET ServerSet]
  /\ votesGranted \in [ServerSet -> SUBSET ServerSet]
  /\ leader \in [ServerSet -> ServerSet \cup {Nil}]
  /\ sm \in [ServerSet -> [STRING -> STRING]]
  /\ smDomain \in [ServerSet -> SUBSET STRING]
  /\ leaderTimeout \in BOOLEAN
  /\ appendEntriesCh \in [ServerSet -> BOOLEAN]
  /\ becomeLeaderCh \in [ServerSet -> BOOLEAN]

Init ==
  /\ net = [i \in NodeSet |-> <<>>]
  /\ netLen = [i \in NodeSet |-> 0]
  /\ netEnabled = [i \in NodeSet |-> TRUE]
  /\ fd = [i \in NodeSet |-> FALSE]
  /\ state = [i \in ServerSet |-> StateFollower]
  /\ currentTerm = [i \in ServerSet |-> 0]
  /\ log = [i \in ServerSet |-> <<>>]
  /\ plog = [i \in ServerSet |-> [cmd |-> "", entries |-> <<>>]]
  /\ commitIndex = [i \in ServerSet |-> 0]
  /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
  /\ matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]
  /\ votedFor = [i \in ServerSet |-> Nil]
  /\ votesResponded = [i \in ServerSet |-> {}]
  /\ votesGranted = [i \in ServerSet |-> {}]
  /\ leader = [i \in ServerSet |-> Nil]
  /\ sm = [i \in ServerSet |-> [k \in {} |-> ""]]
  /\ smDomain = [i \in ServerSet |-> {}]
  /\ leaderTimeout = FALSE
  /\ appendEntriesCh = [i \in ServerSet |-> FALSE]
  /\ becomeLeaderCh = [i \in ServerSet |-> FALSE]
  /\ reqCh = <<>>
  /\ respCh = <<>>
  /\ timeout = FALSE

SendMessage(dest, msg) ==
  /\ net' = [net EXCEPT ![dest] = Append(@, msg)]
  /\ netLen' = [netLen EXCEPT ![dest] = @ + 1]

HandleRequestVoteRequest(i, m) ==
  /\ LET newCurrentTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
         newState == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i]
         newVotedFor == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
         newLeader == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i]
     IN /\ currentTerm' = [currentTerm EXCEPT ![i] = newCurrentTerm]
        /\ state' = [state EXCEPT ![i] = newState]
        /\ votedFor' = [votedFor EXCEPT ![i] = newVotedFor]
        /\ leader' = [leader EXCEPT ![i] = newLeader]
  /\ LET j == m.msource
         logOK == \/ m.mlastLogTerm > LastTerm(log[i])
                  \/ /\ m.mlastLogTerm = LastTerm(log[i])
                     /\ m.mlastLogIndex >= Len(log[i])
         grant == /\ m.mterm = currentTerm'[i]
                  /\ logOK
                  /\ votedFor'[i] \in {Nil, j}
     IN /\ IF grant
           THEN votedFor' = [votedFor' EXCEPT ![i] = j]
           ELSE UNCHANGED votedFor'
        /\ SendMessage(j, [mtype |-> RequestVoteResponse,
                          mterm |-> currentTerm'[i],
                          mvoteGranted |-> grant,
                          msource |-> i,
                          mdest |-> j])
  /\ UNCHANGED <<log, plog, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh>>

HandleRequestVoteResponse(i, m) ==
  /\ LET newCurrentTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
         newState == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i]
         newVotedFor == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
         newLeader == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i]
     IN /\ currentTerm' = [currentTerm EXCEPT ![i] = newCurrentTerm]
        /\ state' = [state EXCEPT ![i] = newState]
        /\ votedFor' = [votedFor EXCEPT ![i] = newVotedFor]
        /\ leader' = [leader EXCEPT ![i] = newLeader]
  /\ IF m.mterm < currentTerm'[i]
     THEN UNCHANGED <<votesResponded, votesGranted, leaderTimeout, becomeLeaderCh>>
     ELSE LET j == m.msource
          IN /\ votesResponded' = [votesResponded EXCEPT ![i] = @ \cup {j}]
             /\ IF m.mvoteGranted
                THEN /\ leaderTimeout' = LeaderTimeoutReset
                     /\ votesGranted' = [votesGranted EXCEPT ![i] = @ \cup {j}]
                     /\ IF /\ state'[i] = StateCandidate
                           /\ IsQuorum(votesGranted'[i])
                        THEN becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = TRUE]
                        ELSE UNCHANGED becomeLeaderCh
                ELSE UNCHANGED <<leaderTimeout, votesGranted, becomeLeaderCh>>
  /\ UNCHANGED <<log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain, appendEntriesCh>>

HandleAppendEntriesRequest(i, m) ==
  /\ LET newCurrentTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
         newState == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i]
         newVotedFor == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
         newLeader == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i]
     IN /\ currentTerm' = [currentTerm EXCEPT ![i] = newCurrentTerm]
        /\ state' = [state EXCEPT ![i] = newState]
        /\ votedFor' = [votedFor EXCEPT ![i] = newVotedFor]
        /\ leader' = [leader EXCEPT ![i] = newLeader]
  /\ LET j == m.msource
         logOK == \/ m.mprevLogIndex = 0
                  \/ /\ m.mprevLogIndex > 0
                     /\ m.mprevLogIndex <= Len(log[i])
                     /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
     IN /\ IF m.mterm = currentTerm'[i]
           THEN /\ leader' = [leader' EXCEPT ![i] = m.msource]
                /\ leaderTimeout' = LeaderTimeoutReset
           ELSE /\ UNCHANGED leader'
                /\ UNCHANGED leaderTimeout
        /\ IF /\ m.mterm = currentTerm'[i]
              /\ state'[i] = StateCandidate
           THEN state' = [state' EXCEPT ![i] = StateFollower]
           ELSE UNCHANGED state'
        /\ IF \/ m.mterm < currentTerm'[i]
              \/ /\ m.mterm = currentTerm'[i]
                 /\ state'[i] = StateFollower
                 /\ ~logOK
           THEN /\ SendMessage(j, [mtype |-> AppendEntriesResponse,
                                  mterm |-> currentTerm'[i],
                                  msuccess |-> FALSE,
                                  mmatchIndex |-> 0,
                                  msource |-> i,
                                  mdest |-> j])
                /\ UNCHANGED <<log, plog, commitIndex, sm, smDomain>>
           ELSE /\ LET index == m.mprevLogIndex + 1
                   IN /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogPop, cnt |-> Len(log[i]) - m.mprevLogIndex]]
                      /\ log' = [log EXCEPT ![i] = SubSeq(@, 1, m.mprevLogIndex)]
                      /\ plog' = [plog' EXCEPT ![i] = [cmd |-> LogConcat, entries |-> m.mentries]]
                      /\ log' = [log' EXCEPT ![i] = @ \o m.mentries]
                /\ LET result == ApplyLog(log'[i], commitIndex[i] + 1, m.mcommitIndex, sm[i], smDomain[i])
                   IN /\ sm' = [sm EXCEPT ![i] = result[1]]
                      /\ smDomain' = [smDomain EXCEPT ![i] = result[2]]
                /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({@, m.mcommitIndex})]
                /\ SendMessage(j, [mtype |-> AppendEntriesResponse,
                                  mterm |-> currentTerm'[i],
                                  msuccess |-> TRUE,
                                  mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                                  msource |-> i,
                                  mdest |-> j])
  /\ UNCHANGED <<nextIndex, matchIndex, votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh>>

HandleAppendEntriesResponse(i, m) ==
  /\ LET newCurrentTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i]
         newState == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i]
         newVotedFor == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i]
         newLeader == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i]
     IN /\ currentTerm' = [currentTerm EXCEPT ![i] = newCurrentTerm]
        /\ state' = [state EXCEPT ![i] = newState]
        /\ votedFor' = [votedFor EXCEPT ![i] = newVotedFor]
        /\ leader' = [leader EXCEPT ![i] = newLeader]
  /\ IF m.mterm < currentTerm'[i]
     THEN UNCHANGED <<nextIndex, matchIndex, leaderTimeout>>
     ELSE /\ leaderTimeout' = LeaderTimeoutReset
          /\ LET j == m.msource
             IN IF m.msuccess
                THEN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                     /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({@ - 1, 1})]
                     /\ UNCHANGED matchIndex
  /\ UNCHANGED <<log, plog, commitIndex, votesResponded, votesGranted, sm, smDomain, appendEntriesCh, becomeLeaderCh>>

HandleClientRequest(i, m) ==
  IF state[i] = StateLeader
  THEN /\ LET entry == [term |-> currentTerm[i],
                       cmd |-> m.mcmd,
                       client |-> m.msource]
          IN /\ log' = [log EXCEPT ![i] = Append(@, entry)]
             /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> <<entry>>]]
       /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
       /\ UNCHANGED <<currentTerm, state, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, becomeLeaderCh>>
  ELSE /\ LET j == m.msource
              respType == IF m.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
          IN SendMessage(j, [mtype |-> respType,
                            msuccess |-> FALSE,
                            mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key],
                            mleaderHint |-> leader[i],
                            msource |-> i,
                            mdest |-> j])
       /\ UNCHANGED <<currentTerm, state, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh>>

HandleMessage(i) ==
  /\ netLen[i] > 0
  /\ LET m == Head(net[i])
     IN /\ net' = [net EXCEPT ![i] = Tail(@)]
        /\ netLen' = [netLen EXCEPT ![i] = @ - 1]
        /\ IF m.mtype = RequestVoteRequest
           THEN HandleRequestVoteRequest(i, m)
           ELSE IF m.mtype = RequestVoteResponse
                THEN HandleRequestVoteResponse(i, m)
                ELSE IF m.mtype = AppendEntriesRequest
                     THEN HandleAppendEntriesRequest(i, m)
                     ELSE IF m.mtype = AppendEntriesResponse
                          THEN HandleAppendEntriesResponse(i, m)
                          ELSE IF m.mtype \in {ClientPutRequest, ClientGetRequest}
                               THEN HandleClientRequest(i, m)
                               ELSE UNCHANGED <<state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh>>

LeaderTimeout ==
  /\ leaderTimeout
  /\ \E i \in ServerSet :
       /\ netLen[i] = 0
       /\ state[i] \in {StateFollower, StateCandidate}
       /\ state' = [state EXCEPT ![i] = StateCandidate]
       /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
       /\ votedFor' = [votedFor EXCEPT ![i] = i]
       /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
       /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
       /\ leader' = [leader EXCEPT ![i] = Nil]
       /\ \A j \in ServerSet \ {i} :
            SendMessage(j, [mtype |-> RequestVoteRequest,
                           mterm |-> currentTerm'[i],
                           mlastLogTerm |-> LastTerm(log[i]),
                           mlastLogIndex |-> Len(log[i]),
                           msource |-> i,
                           mdest |-> j])
  /\ UNCHANGED <<log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh>>

BecomeLeader ==
  /\ \E i \in ServerSet :
       /\ becomeLeaderCh[i]
       /\ state[i] = StateCandidate
       /\ IsQuorum(votesGranted[i])
       /\ state' = [state EXCEPT ![i] = StateLeader]
       /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> Len(log[i]) + 1]]
       /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
       /\ leader' = [leader EXCEPT ![i] = i]
       /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
       /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<net, netLen, netEnabled, fd, currentTerm, log, plog, commitIndex, votedFor, votesResponded, votesGranted, sm, smDomain, leaderTimeout>>

AppendEntries ==
  /\ \E i \in ServerSet :
       /\ appendEntriesCh[i]
       /\ state[i] = StateLeader
       /\ \A j \in ServerSet \ {i} :
            LET prevLogIndex == nextIndex[i][j] - 1
                prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
                entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
            IN SendMessage(j, [mtype |-> AppendEntriesRequest,
                             mterm |-> currentTerm[i],
                             mprevLogIndex |-> prevLogIndex,
                             mprevLogTerm |-> prevLogTerm,
                             mentries |-> entries,
                             mcommitIndex |-> commitIndex[i],
                             msource |-> i,
                             mdest |-> j])
       /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, becomeLeaderCh>>

AdvanceCommitIndex ==
  /\ \E i \in ServerSet :
       /\ state[i] = StateLeader
       /\ LET maxAgreeIndex == FindMaxAgreeIndex(log[i], i, matchIndex[i])
              nCommitIndex == IF /\ maxAgreeIndex # Nil
                                 /\ log[i][maxAgreeIndex].term = currentTerm[i]
                              THEN maxAgreeIndex
                              ELSE commitIndex[i]
          IN /\ nCommitIndex >= commitIndex[i]
             /\ IF nCommitIndex > commitIndex[i]
                THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = nCommitIndex]
                     /\ LET newEntries == SubSeq(log[i], commitIndex[i] + 1, nCommitIndex)
                        IN \A k \in DOMAIN newEntries :
                             LET entry == newEntries[k]
                                 cmd == entry.cmd
                                 respType == IF cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
                             IN /\ IF cmd.type = Put
                                   THEN /\ sm' = [sm EXCEPT ![i] = @ @@ (cmd.key :> cmd.value)]
                                        /\ smDomain' = [smDomain EXCEPT ![i] = @ \cup {cmd.key}]
                                   ELSE UNCHANGED <<sm, smDomain>>
                                /\ LET reqOk == cmd.key \in smDomain'[i]
                                   IN SendMessage(entry.client, [mtype |-> respType,
                                                               msuccess |-> TRUE,
                                                               mresponse |-> [idx |-> cmd.idx,
                                                                            key |-> cmd.key,
                                                                            value |-> IF reqOk THEN sm'[i][cmd.key] ELSE Nil,
                                                                            ok |-> reqOk],
                                                               mleaderHint |-> i,
                                                               msource |-> i,
                                                               mdest |-> entry.client])
                ELSE UNCHANGED <<commitIndex, sm, smDomain>>
  /\ UNCHANGED <<netLen, netEnabled, fd, state, currentTerm, log, plog, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, leaderTimeout, appendEntriesCh, becomeLeaderCh>>

ClientRequest ==
  /\ \E req \in AllReqs :
       /\ reqCh' = Append(reqCh, req)
  /\ UNCHANGED <<net, netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, respCh, timeout>>

Next ==
  \/ \E i \in ServerSet : HandleMessage(i)
  \/ LeaderTimeout
  \/ BecomeLeader
  \/ AppendEntries
  \/ AdvanceCommitIndex
  \/ ClientRequest

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====