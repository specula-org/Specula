---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, AllStrings

Servers == 1..NumServers
Clients == (NumServers + 1)..(NumServers + NumClients)
Nodes == Servers \cup Clients

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

AllReqs ==
  { [type |-> Put, key |-> k, value |-> v, idx |-> n] : k \in AllStrings, v \in AllStrings, n \in Nat } \cup
  { [type |-> Get, key |-> k, value |-> Nil, idx |-> n] : k \in AllStrings, n \in Nat }

LogEntrySet ==
  { [term |-> t, cmd |-> cmd, client |-> c] : t \in Nat, cmd \in AllReqs, c \in Clients }

Messages ==
  { [ mtype |-> RequestVoteRequest,
      mterm |-> t, mlastLogTerm |-> tl, mlastLogIndex |-> il,
      msource |-> i, mdest |-> j ] :
    t \in Nat /\ tl \in Nat /\ il \in Nat /\ i \in Servers /\ j \in Servers } \cup
  { [ mtype |-> RequestVoteResponse,
      mterm |-> t, mvoteGranted |-> g,
      msource |-> i, mdest |-> j ] :
    t \in Nat /\ g \in BOOLEAN /\ i \in Servers /\ j \in Servers } \cup
  { [ mtype |-> AppendEntriesRequest,
      mterm |-> t, mprevLogIndex |-> pi, mprevLogTerm |-> pt,
      mentries |-> es, mcommitIndex |-> ci,
      msource |-> i, mdest |-> j ] :
    t \in Nat /\ pi \in Nat /\ pt \in Nat /\ es \in Seq(LogEntrySet) /\ ci \in Nat /\ i \in Servers /\ j \in Servers } \cup
  { [ mtype |-> AppendEntriesResponse,
      mterm |-> t, msuccess |-> s, mmatchIndex |-> mi,
      msource |-> j, mdest |-> i ] :
    t \in Nat /\ s \in BOOLEAN /\ mi \in Nat /\ i \in Servers /\ j \in Servers } \cup
  { [ mtype |-> ClientPutRequest,
      mcmd |-> cmd, msource |-> c, mdest |-> i ] :
    cmd \in { r \in AllReqs : r.type = Put } /\ c \in Clients /\ i \in Servers } \cup
  { [ mtype |-> ClientGetRequest,
      mcmd |-> cmd, msource |-> c, mdest |-> i ] :
    cmd \in { r \in AllReqs : r.type = Get } /\ c \in Clients /\ i \in Servers } \cup
  { [ mtype |-> ClientPutResponse,
      msuccess |-> s, mresponse |-> r, mleaderHint |-> lh,
      msource |-> i, mdest |-> c ] :
    s \in BOOLEAN /\ r \in [ idx: Nat, key: AllStrings, value: AllStrings \cup {Nil}, ok: BOOLEAN ] /\
    lh \in (Servers \cup {Nil}) /\ i \in Servers /\ c \in Clients } \cup
  { [ mtype |-> ClientGetResponse,
      msuccess |-> s, mresponse |-> r, mleaderHint |-> lh,
      msource |-> i, mdest |-> c ] :
    s \in BOOLEAN /\ r \in [ idx: Nat, key: AllStrings, value: AllStrings \cup {Nil}, ok: BOOLEAN ] /\
    lh \in (Servers \cup {Nil}) /\ i \in Servers /\ c \in Clients }

IsQuorum(S) == 2 * Cardinality(S) > NumServers

Max(a, b) == IF a >= b THEN a ELSE b

LastTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

ApplyLogEntry(entry, sm, dom) ==
  IF entry.cmd.type = Put
  THEN << [sm EXCEPT ![entry.cmd.key] = entry.cmd.value], dom \cup {entry.cmd.key} >>
  ELSE << sm, dom >>

RECURSIVE ApplyLogRange(_, _, _, _, _)
ApplyLogRange(log, start, end, sm, dom) ==
  IF start > end THEN << sm, dom >>
  ELSE
    LET res == ApplyLogEntry(log[start], sm, dom) IN
      ApplyLogRange(log, start + 1, end, res[1], res[2])

RECURSIVE FindMaxAgreeIndexRec(_, _, _, _)
FindMaxAgreeIndexRec(logi, i, matchi, idx) ==
  IF idx = 0 THEN Nil
  ELSE
    LET agree == { i } \cup { k \in Servers : matchi[k] >= idx } IN
      IF IsQuorum(agree) THEN idx ELSE FindMaxAgreeIndexRec(logi, i, matchi, idx - 1)

FindMaxAgreeIndex(logi, i, matchi) == FindMaxAgreeIndexRec(logi, i, matchi, Len(logi))

VARIABLES
  state, currentTerm, votedFor, leader,
  log, commitIndex, nextIndex, matchIndex,
  votesResponded, votesGranted, leaderTimeout,
  sm, smDomain,
  Net,
  leaderHint, reqIdx, clientOutstanding

Vars ==
  << state, currentTerm, votedFor, leader,
     log, commitIndex, nextIndex, matchIndex,
     votesResponded, votesGranted, leaderTimeout,
     sm, smDomain,
     Net,
     leaderHint, reqIdx, clientOutstanding >>

Init ==
  /\ state = [i \in Servers |-> Follower]
  /\ currentTerm = [i \in Servers |-> 0]
  /\ votedFor = [i \in Servers |-> Nil]
  /\ leader = [i \in Servers |-> Nil]
  /\ log = [i \in Servers |-> << >>]
  /\ commitIndex = [i \in Servers |-> 0]
  /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
  /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
  /\ votesResponded = [i \in Servers |-> {}]
  /\ votesGranted = [i \in Servers |-> {}]
  /\ leaderTimeout = [i \in Servers |-> FALSE]
  /\ sm = [i \in Servers |-> [k \in AllStrings |-> Nil]]
  /\ smDomain = [i \in Servers |-> {}]
  /\ Net \subseteq Messages
  /\ Net = {}
  /\ leaderHint = [c \in Clients |-> Nil]
  /\ reqIdx = [c \in Clients |-> 0]
  /\ clientOutstanding = [c \in Clients |-> FALSE]

Tick(i) ==
  /\ i \in Servers
  /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = TRUE]
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex,
                  nextIndex, matchIndex, votesResponded, votesGranted,
                  sm, smDomain, Net, leaderHint, reqIdx, clientOutstanding >>

Timeout(i) ==
  /\ i \in Servers
  /\ leaderTimeout[i]
  /\ state[i] \in {Follower, Candidate}
  /\ state' = [state EXCEPT ![i] = Candidate]
  /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
  /\ votedFor' = [votedFor EXCEPT ![i] = i]
  /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
  /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
  /\ leader' = [leader EXCEPT ![i] = Nil]
  /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
  /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDomain, Net, leaderHint, reqIdx, clientOutstanding >>

RequestVoteSend(i, j) ==
  /\ i \in Servers /\ j \in Servers /\ i # j
  /\ state[i] = Candidate
  /\ LET m ==
       [ mtype |-> RequestVoteRequest,
         mterm |-> currentTerm[i],
         mlastLogTerm |-> LastTerm(log[i]),
         mlastLogIndex |-> Len(log[i]),
         msource |-> i, mdest |-> j ]
     IN
     /\ Net' = Net \cup { m }
     /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex,
                     nextIndex, matchIndex, votesResponded, votesGranted, leaderTimeout,
                     sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

RequestVoteRecv(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
       /\ m.mdest = i /\ m.mtype = RequestVoteRequest
       /\ LET i0 == i IN
          LET j == m.msource IN
          LET cur == currentTerm[i0] IN
          LET newTerm == m.mterm IN
          LET cur2 == IF newTerm > cur THEN newTerm ELSE cur IN
          LET state2 == IF newTerm > cur THEN Follower ELSE state[i0] IN
          LET voted2 == IF newTerm > cur THEN Nil ELSE votedFor[i0] IN
          LET leader2 == IF newTerm > cur THEN Nil ELSE leader[i0] IN
          LET myLog == log[i0] IN
          LET logOK ==
                ( m.mlastLogTerm > LastTerm(myLog) )
             \/ ( m.mlastLogTerm = LastTerm(myLog) /\ m.mlastLogIndex >= Len(myLog) ) IN
          LET grant == ( (m.mterm = cur2) /\ logOK /\ (voted2 \in {Nil, j}) ) IN
          /\ Net' =
               (Net \ {m}) \cup
               { [ mtype |-> RequestVoteResponse,
                   mterm |-> cur2,
                   mvoteGranted |-> grant,
                   msource |-> i0, mdest |-> j ] }
          /\ currentTerm' = [currentTerm EXCEPT ![i0] = cur2]
          /\ state' = [state EXCEPT ![i0] = state2]
          /\ votedFor' = [votedFor EXCEPT ![i0] = IF grant THEN j ELSE voted2]
          /\ leader' = [leader EXCEPT ![i0] = leader2]
          /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, leaderTimeout,
                          sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

RequestVoteRespRecv(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
       /\ m.mdest = i /\ m.mtype = RequestVoteResponse
       /\ LET i0 == i IN
          LET j == m.msource IN
          LET cur == currentTerm[i0] IN
          LET newTerm == m.mterm IN
          LET stepped == (newTerm > cur) IN
          LET cur2 == IF stepped THEN newTerm ELSE cur IN
          LET state2 == IF stepped THEN Follower ELSE state[i0] IN
          LET voted2 == IF stepped THEN Nil ELSE votedFor[i0] IN
          LET leader2 == IF stepped THEN Nil ELSE leader[i0] IN
          /\ Net' = Net \ {m}
          /\ currentTerm' = [currentTerm EXCEPT ![i0] = cur2]
          /\ state' = [state EXCEPT ![i0] = state2]
          /\ votedFor' = [votedFor EXCEPT ![i0] = voted2]
          /\ leader' = [leader EXCEPT ![i0] = leader2]
          /\ votesResponded' = [votesResponded EXCEPT ![i0] = votesResponded[i0] \cup { j }]
          /\ votesGranted' =
               [votesGranted EXCEPT ![i0] =
                 IF (m.mvoteGranted /\ ~stepped /\ m.mterm = cur2)
                 THEN votesGranted[i0] \cup { j }
                 ELSE votesGranted[i0] ]
          /\ leaderTimeout' =
               [leaderTimeout EXCEPT ![i0] =
                 IF (m.mvoteGranted /\ ~stepped /\ m.mterm = cur2)
                 THEN FALSE ELSE leaderTimeout[i0] ]
          /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

BecomeLeader(i) ==
  /\ i \in Servers
  /\ state[i] = Candidate
  /\ IsQuorum(votesGranted[i])
  /\ state' = [state EXCEPT ![i] = Leader]
  /\ leader' = [leader EXCEPT ![i] = i]
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> Len(log[i]) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, votesResponded, votesGranted, leaderTimeout,
                  sm, smDomain, Net, leaderHint, reqIdx, clientOutstanding >>

LeaderSendAppendEntries(i, j) ==
  /\ i \in Servers /\ j \in Servers /\ i # j
  /\ state[i] = Leader
  /\ LET ni == nextIndex[i][j] IN
     LET prevIdx == ni - 1 IN
     LET prevTerm == IF prevIdx = 0 THEN 0 ELSE log[i][prevIdx].term IN
     LET entries == SubSeq(log[i], ni, Len(log[i])) IN
     LET m ==
       [ mtype |-> AppendEntriesRequest,
         mterm |-> currentTerm[i],
         mprevLogIndex |-> prevIdx,
         mprevLogTerm |-> prevTerm,
         mentries |-> entries,
         mcommitIndex |-> commitIndex[i],
         msource |-> i, mdest |-> j ]
     IN
     /\ Net' = Net \cup { m }
     /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
                     votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

AppendEntriesRecv(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
       /\ m.mdest = i /\ m.mtype = AppendEntriesRequest
       /\ LET i0 == i IN
          LET j == m.msource IN
          LET cur == currentTerm[i0] IN
          LET stepped == (m.mterm > cur) IN
          LET cur2 == IF stepped THEN m.mterm ELSE cur IN
          LET state2 == IF stepped THEN Follower ELSE state[i0] IN
          LET voted2 == IF stepped THEN Nil ELSE votedFor[i0] IN
          LET myLog == log[i0] IN
          LET prevOK ==
                (m.mprevLogIndex = 0)
             \/ (m.mprevLogIndex > 0 /\ m.mprevLogIndex <= Len(myLog) /\
                 m.mprevLogTerm = myLog[m.mprevLogIndex].term) IN
          /\ currentTerm' = [currentTerm EXCEPT ![i0] = cur2]
          /\ state' = [state EXCEPT ![i0] =
                         IF (m.mterm = cur2 /\ state2 = Candidate) THEN Follower ELSE state2]
          /\ votedFor' = [votedFor EXCEPT ![i0] = voted2]
          /\ leader' = [leader EXCEPT ![i0] = IF m.mterm = cur2 THEN j ELSE leader[i0]]
          /\ leaderTimeout' = [leaderTimeout EXCEPT ![i0] = IF m.mterm = cur2 THEN FALSE ELSE leaderTimeout[i0]]
          /\ IF ( (m.mterm < cur2) \/ (m.mterm = cur2 /\ state'[i0] = Follower /\ ~prevOK) )
             THEN
               /\ Net' = (Net \ {m}) \cup
                         { [ mtype |-> AppendEntriesResponse,
                             mterm |-> cur2, msuccess |-> FALSE, mmatchIndex |-> 0,
                             msource |-> i0, mdest |-> j ] }
               /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted,
                               sm, smDomain, leaderHint, reqIdx, clientOutstanding >>
             ELSE
               LET trunc == SubSeq(myLog, 1, m.mprevLogIndex) IN
               LET newLog == trunc \o m.mentries IN
               LET commitNew == IF m.mcommitIndex <= Len(newLog) THEN m.mcommitIndex ELSE Len(newLog) IN
               LET appRes == ApplyLogRange(newLog, commitIndex[i0] + 1, commitNew, sm[i0], smDomain[i0]) IN
               /\ Net' = (Net \ {m}) \cup
                         { [ mtype |-> AppendEntriesResponse,
                             mterm |-> cur2, msuccess |-> TRUE,
                             mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                             msource |-> i0, mdest |-> j ] }
               /\ log' = [log EXCEPT ![i0] = newLog]
               /\ commitIndex' = [commitIndex EXCEPT ![i0] = Max(commitIndex[i0], commitNew)]
               /\ sm' = [sm EXCEPT ![i0] = appRes[1]]
               /\ smDomain' = [smDomain EXCEPT ![i0] = appRes[2]]
               /\ UNCHANGED << nextIndex, matchIndex, votesResponded, votesGranted, leaderHint, reqIdx, clientOutstanding >>

AppendEntriesRespRecv(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
       /\ m.mdest = i /\ m.mtype = AppendEntriesResponse
       /\ LET i0 == i IN
          LET j == m.msource IN
          LET cur == currentTerm[i0] IN
          LET stepped == (m.mterm > cur) IN
          LET cur2 == IF stepped THEN m.mterm ELSE cur IN
          LET state2 == IF stepped THEN Follower ELSE state[i0] IN
          LET voted2 == IF stepped THEN Nil ELSE votedFor[i0] IN
          LET leader2 == IF stepped THEN Nil ELSE leader[i0] IN
          /\ Net' = Net \ {m}
          /\ currentTerm' = [currentTerm EXCEPT ![i0] = cur2]
          /\ state' = [state EXCEPT ![i0] = state2]
          /\ votedFor' = [votedFor EXCEPT ![i0] = voted2]
          /\ leader' = [leader EXCEPT ![i0] = leader2]
          /\ leaderTimeout' = [leaderTimeout EXCEPT ![i0] = FALSE]
          /\ IF (~stepped /\ m.mterm = cur2 /\ state2 = Leader /\ m.msuccess)
             THEN
               /\ nextIndex' = [nextIndex EXCEPT ![i0] = [nextIndex[i0] EXCEPT ![j] = m.mmatchIndex + 1]]
               /\ matchIndex' = [matchIndex EXCEPT ![i0] = [matchIndex[i0] EXCEPT ![j] = m.mmatchIndex]]
             ELSE
               IF (~stepped /\ m.mterm = cur2 /\ state2 = Leader /\ ~m.msuccess)
               THEN
                 /\ nextIndex' = [nextIndex EXCEPT ![i0] = [nextIndex[i0] EXCEPT ![j] = Max(nextIndex[i0][j] - 1, 1)]]
                 /\ UNCHANGED matchIndex
               ELSE
                 /\ UNCHANGED << nextIndex, matchIndex >>
          /\ UNCHANGED << log, commitIndex, votesResponded, votesGranted, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

AdvanceCommit(i) ==
  /\ i \in Servers
  /\ state[i] = Leader
  /\ LET n == FindMaxAgreeIndex(log[i], i, matchIndex[i]) IN
     LET n2 == IF n # Nil /\ (n > commitIndex[i]) /\ (log[i][n].term = currentTerm[i]) THEN n ELSE commitIndex[i] IN
     /\ n2 >= commitIndex[i]
     /\ IF n2 > commitIndex[i]
        THEN
          LET appRes == ApplyLogRange(log[i], commitIndex[i] + 1, n2, sm[i], smDomain[i]) IN
          LET smAfter == [sm EXCEPT ![i] = appRes[1]] IN
          LET smDomAfter == [smDomain EXCEPT ![i] = appRes[2]] IN
          /\ commitIndex' = [commitIndex EXCEPT ![i] = n2]
          /\ sm' = smAfter
          /\ smDomain' = smDomAfter
          /\ Net' = Net \cup
                    { [ mtype |-> IF log[i][k].cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse,
                        msuccess |-> TRUE,
                        mresponse |-> [ idx |-> log[i][k].cmd.idx,
                                        key |-> log[i][k].cmd.key,
                                        value |-> smAfter[i][log[i][k].cmd.key],
                                        ok |-> log[i][k].cmd.key \in smDomAfter[i] ],
                        mleaderHint |-> i,
                        msource |-> i, mdest |-> log[i][k].client ] :
                      k \in (commitIndex[i] + 1)..n2 }
          /\ UNCHANGED << state, currentTerm, votedFor, leader, log, nextIndex, matchIndex, votesResponded, votesGranted, leaderTimeout, leaderHint, reqIdx, clientOutstanding >>
        ELSE
          /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, leaderTimeout, sm, smDomain, Net, leaderHint, reqIdx, clientOutstanding >>

ClientPutRecv(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
       /\ m.mdest = i /\ m.mtype = ClientPutRequest
       /\ IF state[i] = Leader
          THEN
            /\ log' = [log EXCEPT ![i] = Append(log[i], [term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource])]
            /\ Net' = Net \ {m}
            /\ UNCHANGED << state, currentTerm, votedFor, leader, commitIndex, nextIndex, matchIndex,
                            votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>
          ELSE
            /\ Net' = (Net \ {m}) \cup
                      { [ mtype |-> ClientPutResponse,
                          msuccess |-> FALSE,
                          mresponse |-> [ idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE ],
                          mleaderHint |-> leader[i],
                          msource |-> i, mdest |-> m.msource ] }
            /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
                            votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

ClientGetRecv(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
       /\ m.mdest = i /\ m.mtype = ClientGetRequest
       /\ IF state[i] = Leader
          THEN
            /\ log' = [log EXCEPT ![i] = Append(log[i], [term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource])]
            /\ Net' = Net \ {m}
            /\ UNCHANGED << state, currentTerm, votedFor, leader, commitIndex, nextIndex, matchIndex,
                            votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>
          ELSE
            /\ Net' = (Net \ {m}) \cup
                      { [ mtype |-> ClientGetResponse,
                          msuccess |-> FALSE,
                          mresponse |-> [ idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE ],
                          mleaderHint |-> leader[i],
                          msource |-> i, mdest |-> m.msource ] }
            /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
                            votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

ClientSend(c) ==
  /\ c \in Clients
  /\ ~clientOutstanding[c]
  /\ LET srv == IF leaderHint[c] = Nil THEN CHOOSE s \in Servers : TRUE ELSE leaderHint[c] IN
     LET idx == reqIdx[c] + 1 IN
     LET req == CHOOSE r \in AllReqs : TRUE IN
     LET msg ==
          IF req.type = Put
          THEN [ mtype |-> ClientPutRequest,
                 mcmd |-> [req EXCEPT !.idx = idx],
                 msource |-> c, mdest |-> srv ]
          ELSE [ mtype |-> ClientGetRequest,
                 mcmd |-> [req EXCEPT !.idx = idx],
                 msource |-> c, mdest |-> srv ]
     IN
     /\ Net' = Net \cup { msg }
     /\ reqIdx' = [reqIdx EXCEPT ![c] = idx]
     /\ clientOutstanding' = [clientOutstanding EXCEPT ![c] = TRUE]
     /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
                     votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint >>

ClientRcvResp(c) ==
  /\ c \in Clients
  /\ \E m \in Net :
       /\ m.mdest = c /\ m.mtype \in {ClientPutResponse, ClientGetResponse}
       /\ Net' = Net \ {m}
       /\ leaderHint' = [leaderHint EXCEPT ![c] = m.mleaderHint]
       /\ clientOutstanding' = [clientOutstanding EXCEPT ![c] = IF m.msuccess THEN FALSE ELSE clientOutstanding[c]]
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
                       votesResponded, votesGranted, leaderTimeout, sm, smDomain, reqIdx >>

Drop ==
  /\ \E m \in Net : TRUE
  /\ Net' = Net \ { m }
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
                  votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderHint, reqIdx, clientOutstanding >>

ServerDeliver(i) == RequestVoteRecv(i) \/ RequestVoteRespRecv(i) \/ AppendEntriesRecv(i) \/ AppendEntriesRespRecv(i)
ClientDeliver(c) == ClientRcvResp(c)

Next ==
  \/ \E i \in Servers : Tick(i)
  \/ \E i \in Servers : Timeout(i)
  \/ \E i, j \in Servers : RequestVoteSend(i, j)
  \/ \E i \in Servers : ServerDeliver(i)
  \/ \E i, j \in Servers : LeaderSendAppendEntries(i, j)
  \/ \E i \in Servers : AdvanceCommit(i)
  \/ \E i \in Servers : ClientPutRecv(i)
  \/ \E i \in Servers : ClientGetRecv(i)
  \/ \E c \in Clients : ClientSend(c)
  \/ \E c \in Clients : ClientDeliver(c)
  \/ Drop

Spec ==
  Init /\ [][Next]_Vars /\
  WF_Vars(\E i \in Servers : Timeout(i)) /\
  WF_Vars(\E i, j \in Servers : RequestVoteSend(i, j)) /\
  WF_Vars(\E i \in Servers : ServerDeliver(i)) /\
  WF_Vars(\E i, j \in Servers : LeaderSendAppendEntries(i, j)) /\
  WF_Vars(\E i \in Servers : AdvanceCommit(i)) /\
  WF_Vars(\E c \in Clients : ClientSend(c)) /\
  WF_Vars(\E c \in Clients : ClientDeliver(c))

====