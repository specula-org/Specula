---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumServers, NumClients, AllStrings

SetsEqual(S,T) == /\ S \subseteq T /\ T \subseteq S

Servers == 1..NumServers
Clients == 1..NumClients

Nil == 0

StateFollower == "follower"
StateCandidate == "candidate"
StateLeader == "leader"

Put == "put"
Get == "get"

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

Cmd ==
  [ type : {Put, Get},
    idx  : Nat,
    key  : AllStrings,
    value: AllStrings \cup {Nil}
  ]

LogEntry ==
  [ term  : Nat,
    cmd   : Cmd,
    client: Clients
  ]

Msg ==
  [ mtype        : {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse, ClientPutRequest, ClientPutResponse, ClientGetRequest, ClientGetResponse},
    mterm        : Nat,
    msource      : Servers \cup Clients,
    mdest        : Servers \cup Clients,
    mlastLogTerm : Nat,
    mlastLogIndex: Nat,
    mvoteGranted : BOOLEAN,
    mprevLogIndex: Nat,
    mprevLogTerm : Nat,
    mentries     : Seq(LogEntry),
    mcommitIndex : Nat,
    msuccess     : BOOLEAN,
    mmatchIndex  : Nat,
    mcmd         : Cmd,
    mresponse    : [ idx: Nat, key: AllStrings, value: AllStrings \cup {Nil}, ok: BOOLEAN ],
    mleaderHint  : Servers \cup {Nil}
  ]

IsQuorum(S) == 2 * Cardinality(S) > NumServers

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

ApplyLogEntry(entry, xsm, xdom) ==
  IF entry.cmd.type = Put THEN
    LET newDom == xdom \cup {entry.cmd.key} IN
      << [ k \in newDom |->
           IF k = entry.cmd.key THEN entry.cmd.value ELSE xsm[k] ],
         newDom >>
  ELSE
    << xsm, xdom >>

ApplyLog(xlog, start, stop, xsm, xdom) ==
  IF start > stop THEN << xsm, xdom >>
  ELSE
    LET res == ApplyLogEntry(xlog[start], xsm, xdom) IN
      ApplyLog(xlog, start + 1, stop, res[1], res[2])

MaxNat(S) ==
  IF S = {} THEN 0
  ELSE CHOOSE n \in S: \A m \in S: m <= n

VARIABLES
  state,
  currentTerm,
  votedFor,
  log,
  commitIndex,
  nextIndex,
  matchIndex,
  leader,
  sm,
  smDom,
  votesResponded,
  votesGranted,
  leaderTimeout,
  Net,
  clientLeader,
  clientReqIdx

Vars == << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, Net, clientLeader, clientReqIdx >>

TypeOK ==
  /\ state \in [Servers -> {StateFollower, StateCandidate, StateLeader}]
  /\ currentTerm \in [Servers -> Nat]
  /\ votedFor \in [Servers -> (Servers \cup {Nil})]
  /\ log \in [Servers -> Seq(LogEntry)]
  /\ commitIndex \in [Servers -> Nat]
  /\ nextIndex \in [Servers -> [Servers -> Nat]]
  /\ matchIndex \in [Servers -> [Servers -> Nat]]
  /\ leader \in [Servers -> (Servers \cup {Nil})]
  /\ smDom \in [Servers -> SUBSET AllStrings]
  /\ sm \in [Servers -> [AllStrings -> AllStrings]]
  /\ votesResponded \in [Servers -> SUBSET Servers]
  /\ votesGranted \in [Servers -> SUBSET Servers]
  /\ leaderTimeout \in [Servers -> BOOLEAN]
  /\ Net \subseteq Msg
  /\ clientLeader \in [Clients -> (Servers \cup {Nil})]
  /\ clientReqIdx \in [Clients -> Nat]
  /\ \A i \in Servers: commitIndex[i] <= Len(log[i])
  /\ \A i \in Servers: \A j \in Servers: nextIndex[i][j] \in 1..(Len(log[i]) + 1)
  /\ \A i \in Servers: \A j \in Servers: matchIndex[i][j] \in 0..Len(log[i])
  /\ \A i \in Servers: sm[i] = [ k \in smDom[i] |->
                                 sm[i][k] ] \cup
                               [ k \in (AllStrings \ {k \in AllStrings: k \in smDom[i]}) |->
                                 CHOOSE v \in AllStrings: TRUE ]

Init ==
  /\ state = [ i \in Servers |-> StateFollower ]
  /\ currentTerm = [ i \in Servers |-> 0 ]
  /\ votedFor = [ i \in Servers |-> Nil ]
  /\ log = [ i \in Servers |-> << >> ]
  /\ commitIndex = [ i \in Servers |-> 0 ]
  /\ nextIndex = [ i \in Servers |-> [ j \in Servers |-> 1 ] ]
  /\ matchIndex = [ i \in Servers |-> [ j \in Servers |-> 0 ] ]
  /\ leader = [ i \in Servers |-> Nil ]
  /\ smDom = [ i \in Servers |-> {} ]
  /\ sm = [ i \in Servers |-> [ k \in AllStrings |-> CHOOSE v \in AllStrings: TRUE ] ]
  /\ votesResponded = [ i \in Servers |-> {} ]
  /\ votesGranted = [ i \in Servers |-> {} ]
  /\ leaderTimeout = [ i \in Servers |-> FALSE ]
  /\ Net = {}
  /\ clientLeader = [ c \in Clients |-> Nil ]
  /\ clientReqIdx = [ c \in Clients |-> 0 ]
  /\ TypeOK

Tick(i) ==
  /\ i \in Servers
  /\ state[i] # StateLeader
  /\ leaderTimeout' = [ leaderTimeout EXCEPT ![i] = TRUE ]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, Net, clientLeader, clientReqIdx >>

ElectionTimeout(i) ==
  /\ i \in Servers
  /\ leaderTimeout[i]
  /\ state[i] \in {StateFollower, StateCandidate}
  /\ LET newTerm == currentTerm[i] + 1 IN
     /\ state' = [ state EXCEPT ![i] = StateCandidate ]
     /\ currentTerm' = [ currentTerm EXCEPT ![i] = newTerm ]
     /\ votedFor' = [ votedFor EXCEPT ![i] = i ]
     /\ votesResponded' = [ votesResponded EXCEPT ![i] = {i} ]
     /\ votesGranted' = [ votesGranted EXCEPT ![i] = {i} ]
     /\ leader' = [ leader EXCEPT ![i] = Nil ]
     /\ leaderTimeout' = [ leaderTimeout EXCEPT ![i] = FALSE ]
     /\ Net' = Net \cup { [ mtype |-> RequestVoteRequest,
                           mterm |-> newTerm,
                           msource |-> i,
                           mdest |-> j,
                           mlastLogTerm |-> LastTerm(log[i]),
                           mlastLogIndex |-> Len(log[i]),
                           mvoteGranted |-> FALSE,
                           mprevLogIndex |-> 0,
                           mprevLogTerm |-> 0,
                           mentries |-> << >>,
                           mcommitIndex |-> 0,
                           msuccess |-> FALSE,
                           mmatchIndex |-> 0,
                           mcmd |-> [type |-> Get, idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil],
                           mresponse |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE],
                           mleaderHint |-> Nil ]
                        : j \in Servers \ {i} }
     /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDom, clientLeader, clientReqIdx >>

HandleRequestVoteRequest(i, m) ==
  /\ i \in Servers
  /\ m \in Net
  /\ m.mtype = RequestVoteRequest
  /\ m.mdest = i
  /\ LET newTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
     LET becameFollower == m.mterm > currentTerm[i] IN
     LET logOK == (m.mlastLogTerm > LastTerm(log[i]))
                   \/ (m.mlastLogTerm = LastTerm(log[i]) /\ m.mlastLogIndex >= Len(log[i])) IN
     LET grant == (m.mterm = newTerm) /\ logOK /\ (votedFor[i] = Nil \/ votedFor[i] = m.msource) IN
     /\ currentTerm' = [ currentTerm EXCEPT ![i] = newTerm ]
     /\ state' = [ state EXCEPT ![i] = IF becameFollower THEN StateFollower ELSE state[i] ]
     /\ votedFor' = [ votedFor EXCEPT ![i] = IF grant THEN m.msource ELSE IF becameFollower THEN Nil ELSE votedFor[i] ]
     /\ leader' = [ leader EXCEPT ![i] = IF becameFollower THEN Nil ELSE leader[i] ]
     /\ Net' = (Net \ {m}) \cup { [ mtype |-> RequestVoteResponse,
                                    mterm |-> newTerm,
                                    msource |-> i,
                                    mdest |-> m.msource,
                                    mlastLogTerm |-> 0,
                                    mlastLogIndex |-> 0,
                                    mvoteGranted |-> grant,
                                    mprevLogIndex |-> 0,
                                    mprevLogTerm |-> 0,
                                    mentries |-> << >>,
                                    mcommitIndex |-> 0,
                                    msuccess |-> FALSE,
                                    mmatchIndex |-> 0,
                                    mcmd |-> [type |-> Get, idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil],
                                    mresponse |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE],
                                    mleaderHint |-> Nil ] }
     /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

HandleRequestVoteResponse(i, m) ==
  /\ i \in Servers
  /\ m \in Net
  /\ m.mtype = RequestVoteResponse
  /\ m.mdest = i
  /\ IF m.mterm > currentTerm[i] THEN
       /\ currentTerm' = [ currentTerm EXCEPT ![i] = m.mterm ]
       /\ state' = [ state EXCEPT ![i] = StateFollower ]
       /\ votedFor' = [ votedFor EXCEPT ![i] = Nil ]
       /\ leader' = [ leader EXCEPT ![i] = Nil ]
       /\ Net' = Net \ {m}
       /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>
     ELSE IF m.mterm < currentTerm[i] THEN
       /\ Net' = Net \ {m}
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>
     ELSE
       /\ state[i] = StateCandidate
       /\ votesResponded' = [ votesResponded EXCEPT ![i] = votesResponded[i] \cup {m.msource} ]
       /\ votesGranted' = [ votesGranted EXCEPT ![i] = IF m.mvoteGranted THEN votesGranted[i] \cup {m.msource} ELSE votesGranted[i] ]
       /\ leaderTimeout' = [ leaderTimeout EXCEPT ![i] = IF m.mvoteGranted THEN FALSE ELSE leaderTimeout[i] ]
       /\ Net' = Net \ {m}
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, clientLeader, clientReqIdx >>

BecomeLeader(i) ==
  /\ i \in Servers
  /\ state[i] = StateCandidate
  /\ IsQuorum(votesGranted[i])
  /\ state' = [ state EXCEPT ![i] = StateLeader ]
  /\ leader' = [ leader EXCEPT ![i] = i ]
  /\ nextIndex' = [ nextIndex EXCEPT ![i] = [ j \in Servers |->
                     Len(log[i]) + 1 ] ]
  /\ matchIndex' = [ matchIndex EXCEPT ![i] = [ j \in Servers |-> 0 ] ]
  /\ Net' = Net \cup { [ mtype |-> AppendEntriesRequest,
                         mterm |-> currentTerm[i],
                         msource |-> i,
                         mdest |-> j,
                         mlastLogTerm |-> 0,
                         mlastLogIndex |-> 0,
                         mvoteGranted |-> FALSE,
                         mprevLogIndex |-> IF nextIndex[i][j] = 0 THEN 0 ELSE nextIndex[i][j] - 1,
                         mprevLogTerm |-> IF nextIndex[i][j] = 1 THEN 0
                                          ELSE IF nextIndex[i][j] - 1 > 0 THEN log[i][nextIndex[i][j] - 1].term ELSE 0,
                         mentries |-> << >>,
                         mcommitIndex |-> commitIndex[i],
                         msuccess |-> FALSE,
                         mmatchIndex |-> 0,
                         mcmd |-> [type |-> Get, idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil],
                         mresponse |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE],
                         mleaderHint |-> Nil ] : j \in Servers \ {i} }
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

LeaderSendAppendEntries(i, j) ==
  /\ i \in Servers
  /\ j \in Servers
  /\ i # j
  /\ state[i] = StateLeader
  /\ LET prevIndex == nextIndex[i][j] - 1 IN
     LET prevTerm == IF prevIndex = 0 THEN 0 ELSE log[i][prevIndex].term IN
     LET entries == SubSeq(log[i], nextIndex[i][j], Len(log[i])) IN
     /\ Net' = Net \cup { [ mtype |-> AppendEntriesRequest,
                            mterm |-> currentTerm[i],
                            msource |-> i,
                            mdest |-> j,
                            mlastLogTerm |-> 0,
                            mlastLogIndex |-> 0,
                            mvoteGranted |-> FALSE,
                            mprevLogIndex |-> prevIndex,
                            mprevLogTerm |-> prevTerm,
                            mentries |-> entries,
                            mcommitIndex |-> commitIndex[i],
                            msuccess |-> FALSE,
                            mmatchIndex |-> 0,
                            mcmd |-> [type |-> Get, idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil],
                            mresponse |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE],
                            mleaderHint |-> Nil ] }
     /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

HandleAppendEntriesRequest(i, m) ==
  /\ i \in Servers
  /\ m \in Net
  /\ m.mtype = AppendEntriesRequest
  /\ m.mdest = i
  /\ LET newTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
     LET becameFollower == m.mterm > currentTerm[i] IN
     LET logOK == (m.mprevLogIndex = 0)
                   \/ (m.mprevLogIndex > 0 /\ m.mprevLogIndex <= Len(log[i])
                       /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term) IN
     /\ currentTerm' = [ currentTerm EXCEPT ![i] = newTerm ]
     /\ state' = [ state EXCEPT ![i] =
           IF (m.mterm = newTerm /\ state[i] = StateCandidate) \/ becameFollower THEN StateFollower ELSE state[i] ]
     /\ leader' = [ leader EXCEPT ![i] = IF m.mterm = newTerm THEN m.msource ELSE
                                       IF becameFollower THEN Nil ELSE leader[i] ]
     /\ leaderTimeout' = [ leaderTimeout EXCEPT ![i] = IF m.mterm = newTerm THEN FALSE ELSE leaderTimeout[i] ]
     /\ IF m.mterm < newTerm \/ ~logOK THEN
          /\ Net' = (Net \ {m}) \cup { [ mtype |-> AppendEntriesResponse,
                                         mterm |-> newTerm,
                                         msource |-> i,
                                         mdest |-> m.msource,
                                         mlastLogTerm |-> 0,
                                         mlastLogIndex |-> 0,
                                         mvoteGranted |-> FALSE,
                                         mprevLogIndex |-> 0,
                                         mprevLogTerm |-> 0,
                                         mentries |-> << >>,
                                         mcommitIndex |-> 0,
                                         msuccess |-> FALSE,
                                         mmatchIndex |-> 0,
                                         mcmd |-> [type |-> Get, idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil],
                                         mresponse |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE],
                                         mleaderHint |-> Nil ] }
          /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDom, votedFor, votesResponded, votesGranted, clientLeader, clientReqIdx >>
        ELSE
          /\ LET newLog == SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries IN
             /\ log' = [ log EXCEPT ![i] = newLog ]
             /\ commitIndex' = [ commitIndex EXCEPT ![i] =
                   IF m.mcommitIndex <= Len(newLog) THEN
                     Max({commitIndex[i], m.mcommitIndex})
                   ELSE
                     commitIndex[i] ]
             /\ LET upto == commitIndex'[i] IN
                LET applied == ApplyLog(newLog, commitIndex[i] + 1, upto, sm[i], smDom[i]) IN
                /\ sm' = [ sm EXCEPT ![i] = applied[1] ]
                /\ smDom' = [ smDom EXCEPT ![i] = applied[2] ]
             /\ Net' = (Net \ {m}) \cup { [ mtype |-> AppendEntriesResponse,
                                            mterm |-> newTerm,
                                            msource |-> i,
                                            mdest |-> m.msource,
                                            mlastLogTerm |-> 0,
                                            mlastLogIndex |-> 0,
                                            mvoteGranted |-> FALSE,
                                            mprevLogIndex |-> 0,
                                            mprevLogTerm |-> 0,
                                            mentries |-> << >>,
                                            mcommitIndex |-> 0,
                                            msuccess |-> TRUE,
                                            mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                                            mcmd |-> [type |-> Get, idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil],
                                            mresponse |-> [idx |-> 0, key |-> CHOOSE k \in AllStrings: TRUE, value |-> Nil, ok |-> FALSE],
                                            mleaderHint |-> Nil ] }
             /\ UNCHANGED << nextIndex, matchIndex, votedFor, votesResponded, votesGranted, clientLeader, clientReqIdx >>

HandleAppendEntriesResponse(i, m) ==
  /\ i \in Servers
  /\ m \in Net
  /\ m.mtype = AppendEntriesResponse
  /\ m.mdest = i
  /\ IF m.mterm > currentTerm[i] THEN
       /\ currentTerm' = [ currentTerm EXCEPT ![i] = m.mterm ]
       /\ state' = [ state EXCEPT ![i] = StateFollower ]
       /\ votedFor' = [ votedFor EXCEPT ![i] = Nil ]
       /\ leader' = [ leader EXCEPT ![i] = Nil ]
       /\ Net' = Net \ {m}
       /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>
     ELSE IF m.mterm < currentTerm[i] THEN
       /\ Net' = Net \ {m}
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>
     ELSE
       /\ state[i] = StateLeader
       /\ leaderTimeout' = [ leaderTimeout EXCEPT ![i] = FALSE ]
       /\ IF m.msuccess THEN
            /\ nextIndex' = [ nextIndex EXCEPT ![i][m.msource] = m.mmatchIndex + 1 ]
            /\ matchIndex' = [ matchIndex EXCEPT ![i][m.msource] = m.mmatchIndex ]
          ELSE
            /\ nextIndex' = [ nextIndex EXCEPT ![i][m.msource] = Max(1, nextIndex[i][m.msource] - 1) ]
            /\ matchIndex' = matchIndex
       /\ Net' = Net \ {m}
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader, sm, smDom, votesResponded, votesGranted, clientLeader, clientReqIdx >>

LeaderAdvanceCommit(i) ==
  /\ i \in Servers
  /\ state[i] = StateLeader
  /\ LET Agree(k) == IsQuorum({i} \cup { s \in Servers : matchIndex[i][s] >= k }) IN
     LET K == { k \in 1..Len(log[i]) : /\ k > commitIndex[i]
                                   /\ Agree(k)
                                   /\ log[i][k].term = currentTerm[i] } IN
     /\ K # {}
     /\ commitIndex' = [ commitIndex EXCEPT ![i] = commitIndex[i] + 1 ]
     /\ commitIndex'[i] <= MaxNat(K)
     /\ LET k == commitIndex'[i] IN
        LET entry == log[i][k] IN
        LET apply == ApplyLog( log[i], k, k, sm[i], smDom[i] ) IN
        /\ sm' = [ sm EXCEPT ![i] = apply[1] ]
        /\ smDom' = [ smDom EXCEPT ![i] = apply[2] ]
        /\ Net' = Net \cup
            { [ mtype |-> IF entry.cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse,
                mterm |-> currentTerm[i],
                msource |-> i,
                mdest |-> entry.client,
                mlastLogTerm |-> 0,
                mlastLogIndex |-> 0,
                mvoteGranted |-> FALSE,
                mprevLogIndex |-> 0,
                mprevLogTerm |-> 0,
                mentries |-> << >>,
                mcommitIndex |-> 0,
                msuccess |-> TRUE,
                mmatchIndex |-> 0,
                mcmd |-> entry.cmd,
                mresponse |-> [ idx |-> entry.cmd.idx,
                                 key |-> entry.cmd.key,
                                 value |-> IF entry.cmd.type = Get
                                           THEN IF entry.cmd.key \in smDom'[i] THEN sm'[i][entry.cmd.key] ELSE Nil
                                           ELSE IF entry.cmd.key \in smDom'[i] THEN sm'[i][entry.cmd.key] ELSE entry.cmd.value,
                                 ok |-> (entry.cmd.type = Put) \/ (entry.cmd.key \in smDom'[i]) ],
                mleaderHint |-> i ] }
     /\ UNCHANGED << state, currentTerm, votedFor, log, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

HandleClientRequestAtLeader(i, m) ==
  /\ i \in Servers
  /\ m \in Net
  /\ m.mdest = i
  /\ state[i] = StateLeader
  /\ (m.mtype = ClientPutRequest \/ m.mtype = ClientGetRequest)
  /\ LET e == [ term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource ] IN
     /\ log' = [ log EXCEPT ![i] = Append(log[i], e) ]
     /\ Net' = Net \ {m}
     /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

HandleClientRequestAtFollower(i, m) ==
  /\ i \in Servers
  /\ m \in Net
  /\ m.mdest = i
  /\ state[i] # StateLeader
  /\ (m.mtype = ClientPutRequest \/ m.mtype = ClientGetRequest)
  /\ Net' = (Net \ {m}) \cup
     { [ mtype |-> IF m.mtype = ClientPutRequest THEN ClientPutResponse ELSE ClientGetResponse,
         mterm |-> currentTerm[i],
         msource |-> i,
         mdest |-> m.msource,
         mlastLogTerm |-> 0,
         mlastLogIndex |-> 0,
         mvoteGranted |-> FALSE,
         mprevLogIndex |-> 0,
         mprevLogTerm |-> 0,
         mentries |-> << >>,
         mcommitIndex |-> 0,
         msuccess |-> FALSE,
         mmatchIndex |-> 0,
         mcmd |-> m.mcmd,
         mresponse |-> [ idx |-> m.mcmd.idx,
                          key |-> m.mcmd.key,
                          value |-> Nil,
                          ok |-> FALSE ],
         mleaderHint |-> leader[i] ] }
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

ClientSend(c) ==
  /\ c \in Clients
  /\ LET dest == IF clientLeader[c] = Nil THEN CHOOSE s \in Servers: TRUE ELSE clientLeader[c] IN
     /\ LET newIdx == clientReqIdx[c] + 1 IN
        /\ \E t \in {Put, Get}:
           LET cmd == [ type |-> t,
                        idx |-> newIdx,
                        key |-> CHOOSE k \in AllStrings: TRUE,
                        value |-> CHOOSE v \in AllStrings: TRUE ] IN
           /\ Net' = Net \cup
               { [ mtype |-> IF t = Put THEN ClientPutRequest ELSE ClientGetRequest,
                   mterm |-> 0,
                   msource |-> c,
                   mdest |-> dest,
                   mlastLogTerm |-> 0,
                   mlastLogIndex |-> 0,
                   mvoteGranted |-> FALSE,
                   mprevLogIndex |-> 0,
                   mprevLogTerm |-> 0,
                   mentries |-> << >>,
                   mcommitIndex |-> 0,
                   msuccess |-> FALSE,
                   mmatchIndex |-> 0,
                   mcmd |-> cmd,
                   mresponse |-> [ idx |-> 0, key |-> cmd.key, value |-> Nil, ok |-> FALSE ],
                   mleaderHint |-> Nil ] }
           /\ clientLeader' = [ clientLeader EXCEPT ![c] = dest ]
           /\ clientReqIdx' = [ clientReqIdx EXCEPT ![c] = newIdx ]
           /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout >>

ClientReceive(c, m) ==
  /\ c \in Clients
  /\ m \in Net
  /\ m.mdest = c
  /\ m.mtype \in {ClientPutResponse, ClientGetResponse}
  /\ clientLeader' = [ clientLeader EXCEPT ![c] = m.mleaderHint ]
  /\ IF ~m.msuccess THEN
       /\ Net' = Net \ {m}
       /\ UNCHANGED clientReqIdx
     ELSE
       /\ IF m.mresponse.idx # clientReqIdx[c] THEN
            /\ Net' = Net \ {m}
            /\ UNCHANGED clientReqIdx
          ELSE
            /\ Net' = Net \ {m}
            /\ UNCHANGED clientReqIdx
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout >>

ClientTimeout(c) ==
  /\ c \in Clients
  /\ clientLeader' = [ clientLeader EXCEPT ![c] = Nil ]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, Net, clientReqIdx >>

Drop(m) ==
  /\ m \in Net
  /\ Net' = Net \ {m}
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, sm, smDom, votesResponded, votesGranted, leaderTimeout, clientLeader, clientReqIdx >>

Next ==
  \/ \E i \in Servers: Tick(i)
  \/ \E i \in Servers: ElectionTimeout(i)
  \/ \E i \in Servers, m \in Net: HandleRequestVoteRequest(i, m)
  \/ \E i \in Servers, m \in Net: HandleRequestVoteResponse(i, m)
  \/ \E i, j \in Servers: LeaderSendAppendEntries(i, j)
  \/ \E i \in Servers, m \in Net: HandleAppendEntriesRequest(i, m)
  \/ \E i \in Servers, m \in Net: HandleAppendEntriesResponse(i, m)
  \/ \E i \in Servers: BecomeLeader(i)
  \/ \E i \in Servers: LeaderAdvanceCommit(i)
  \/ \E i \in Servers, m \in Net: HandleClientRequestAtLeader(i, m)
  \/ \E i \in Servers, m \in Net: HandleClientRequestAtFollower(i, m)
  \/ \E c \in Clients: ClientSend(c)
  \/ \E c \in Clients, m \in Net: ClientReceive(c, m)
  \/ \E c \in Clients: ClientTimeout(c)
  \/ \E m \in Net: Drop(m)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A i \in Servers: WF_Vars(ElectionTimeout(i))
  /\ \A i, j \in Servers: WF_Vars(LeaderSendAppendEntries(i,j))
  /\ \A i \in Servers: WF_Vars(BecomeLeader(i))
  /\ \A i \in Servers: WF_Vars(LeaderAdvanceCommit(i))
  /\ \A i \in Servers: WF_Vars(\E m \in Net: HandleRequestVoteRequest(i, m))
  /\ \A i \in Servers: WF_Vars(\E m \in Net: HandleRequestVoteResponse(i, m))
  /\ \A i \in Servers: WF_Vars(\E m \in Net: HandleAppendEntriesRequest(i, m))
  /\ \A i \in Servers: WF_Vars(\E m \in Net: HandleAppendEntriesResponse(i, m))
  /\ \A c \in Clients: WF_Vars(ClientSend(c))
  /\ \A c \in Clients: WF_Vars(\E m \in Net: ClientReceive(c, m))

====
