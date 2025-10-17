---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    AllStrings

Servers == 1..NumServers
Clients == 1..NumClients
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
    UNION {
      { [type |-> Put, key |-> k, value |-> v] : k \in AllStrings, v \in AllStrings },
      { [type |-> Get, key |-> k] : k \in AllStrings }
    }

IsQuorum(S) == 2*Cardinality(S) > NumServers

Min(S) ==
  CHOOSE m \in S : \A x \in S : m <= x

Max(S) ==
  CHOOSE m \in S : \A x \in S : m >= x

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

ApplyLogEntry(xentry, xsm, xsmDom) ==
  IF xentry.cmd.type = Put THEN
    << [xsm EXCEPT ![xentry.cmd.key] = xentry.cmd.value], xsmDom \cup {xentry.cmd.key} >>
  ELSE
    << xsm, xsmDom >>

ApplyRange(xlog, k, end, xsm, xsmDom) ==
  IF k > end THEN << xsm, xsmDom >>
  ELSE
    LET step == ApplyLogEntry(xlog[k], xsm, xsmDom) IN
      ApplyRange(xlog, k+1, end, step[1], step[2])

FindMaxAgreeIndex(logLocal, i, matchIndex) ==
  LET Agree(k) == IsQuorum({i} \cup { j \in Servers : matchIndex[j] >= k }) IN
    IF \E k \in 1..Len(logLocal) : Agree(k) THEN
      Max({ k \in 1..Len(logLocal) : Agree(k) })
    ELSE
      Nil

VARIABLES
    state,
    currentTerm,
    votedFor,
    leader,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votesResponded,
    votesGranted,
    sm,
    smDom,
    Net,
    leaderHint,
    req,
    reqIdx,
    waiting

Vars == << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, Net, leaderHint, req, reqIdx, waiting >>

Init ==
  /\ state = [ i \in Servers |-> Follower ]
  /\ currentTerm = [ i \in Servers |-> 0 ]
  /\ votedFor = [ i \in Servers |-> Nil ]
  /\ leader = [ i \in Servers |-> Nil ]
  /\ log = [ i \in Servers |-> << >> ]
  /\ commitIndex = [ i \in Servers |-> 0 ]
  /\ lastApplied = [ i \in Servers |-> 0 ]
  /\ nextIndex = [ i \in Servers |-> [ j \in Servers |-> 1 ] ]
  /\ matchIndex = [ i \in Servers |-> [ j \in Servers |-> 0 ] ]
  /\ votesResponded = [ i \in Servers |-> {} ]
  /\ votesGranted = [ i \in Servers |-> {} ]
  /\ sm = [ i \in Servers |-> [ k \in {} |-> Nil ] ]
  /\ smDom = [ i \in Servers |-> {} ]
  /\ Net = {}
  /\ leaderHint = [ c \in Clients |-> Nil ]
  /\ req = [ c \in Clients |-> [type |-> Get, key |-> CHOOSE x \in AllStrings : TRUE, idx |-> 0] ]
  /\ reqIdx = [ c \in Clients |-> 0 ]
  /\ waiting = [ c \in Clients |-> FALSE ]

ElectionTimeout(i) ==
  /\ i \in Servers
  /\ state[i] \in {Follower, Candidate}
  /\ LET t == currentTerm[i] + 1 IN
       /\ state' = [state EXCEPT ![i] = Candidate]
       /\ currentTerm' = [currentTerm EXCEPT ![i] = t]
       /\ votedFor' = [votedFor EXCEPT ![i] = i]
       /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
       /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
       /\ leader' = [leader EXCEPT ![i] = Nil]
       /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, sm, smDom, leaderHint, req, reqIdx, waiting >>
       /\ Net' =
            Net \cup
            { [ mtype |-> RequestVoteRequest,
                mterm |-> t,
                mlastLogTerm |-> LastTerm(log[i]),
                mlastLogIndex |-> Len(log[i]),
                msource |-> i,
                mdest |-> j ] : j \in Servers \ {i} }

AppendSend(i, j) ==
  /\ i \in Servers /\ j \in Servers /\ i # j
  /\ state[i] = Leader
  /\ LET pidx == nextIndex[i][j] - 1 IN
     LET pterm == IF pidx > 0 THEN log[i][pidx].term ELSE 0 IN
     LET entries == SubSeq(log[i], nextIndex[i][j], Len(log[i])) IN
       /\ Net' = Net \cup {
          [ mtype |-> AppendEntriesRequest,
            mterm |-> currentTerm[i],
            mprevLogIndex |-> pidx,
            mprevLogTerm |-> pterm,
            mentries |-> entries,
            mcommitIndex |-> commitIndex[i],
            msource |-> i,
            mdest |-> j ] }
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>

HandleRequestVoteRequest(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
        /\ m.mdest = i /\ m.mtype = RequestVoteRequest
        /\ LET newTerm == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
           LET becameFollower ==
               m.mterm > currentTerm[i] IN
           LET logOK ==
               (m.mlastLogTerm > LastTerm(log[i]))
               \/ (m.mlastLogTerm = LastTerm(log[i]) /\ m.mlastLogIndex >= Len(log[i])) IN
           LET curTermAfter ==
               IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
           LET votedForAfter ==
               IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i] IN
           LET grant ==
               (m.mterm = curTermAfter)
               /\ logOK
               /\ (votedForAfter \in {Nil, m.msource}) IN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = curTermAfter]
             /\ state' = [state EXCEPT ![i] = IF becameFollower THEN Follower ELSE @]
             /\ votedFor' =
                  [votedFor EXCEPT
                     ![i] = IF grant THEN m.msource ELSE votedForAfter]
             /\ leader' = [leader EXCEPT ![i] = IF becameFollower THEN Nil ELSE @]
             /\ Net' =
                  (Net \ {m})
                  \cup
                  { [ mtype |-> RequestVoteResponse,
                      mterm |-> curTermAfter,
                      mvoteGranted |-> grant,
                      msource |-> i,
                      mdest |-> m.msource ] }
             /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>

HandleRequestVoteResponse(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
        /\ m.mdest = i /\ m.mtype = RequestVoteResponse
        /\ IF m.mterm > currentTerm[i] THEN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
             /\ Net' = Net \ {m}
             /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>
           ELSE IF m.mterm < currentTerm[i] THEN
             /\ Net' = Net \ {m}
             /\ UNCHANGED Vars
           ELSE
             LET resped == votesResponded[i] \cup {m.msource} IN
             LET granted == IF m.mvoteGranted THEN votesGranted[i] \cup {m.msource} ELSE votesGranted[i] IN
             LET becomeLdr == state[i] = Candidate /\ IsQuorum(granted) IN
               /\ votesResponded' = [votesResponded EXCEPT ![i] = resped]
               /\ votesGranted' = [votesGranted EXCEPT ![i] = granted]
               /\ state' = [state EXCEPT ![i] = IF becomeLdr THEN Leader ELSE @]
               /\ leader' = [leader EXCEPT ![i] = IF becomeLdr THEN i ELSE @]
               /\ nextIndex' =
                    [nextIndex EXCEPT
                       ![i] = IF becomeLdr THEN [ j \in Servers |-> Len(log[i]) + 1 ] ELSE @]
               /\ matchIndex' =
                    [matchIndex EXCEPT
                       ![i] = IF becomeLdr THEN [ j \in Servers |-> 0 ] ELSE @]
               /\ Net' = Net \ {m}
               /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, sm, smDom, leaderHint, req, reqIdx, waiting >>

HandleAppendEntriesRequest(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
        /\ m.mdest = i /\ m.mtype = AppendEntriesRequest
        /\ LET stepDown == m.mterm > currentTerm[i] IN
           LET curTermAfter == IF stepDown THEN m.mterm ELSE currentTerm[i] IN
           LET logOK ==
             (m.mprevLogIndex = 0)
             \/ (m.mprevLogIndex > 0
                 /\ m.mprevLogIndex <= Len(log[i])
                 /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term) IN
           /\ currentTerm' = [currentTerm EXCEPT ![i] = curTermAfter]
           /\ state' = [state EXCEPT ![i] = IF stepDown THEN Follower ELSE IF (m.mterm = curTermAfter /\ state[i] = Candidate) THEN Follower ELSE @]
           /\ leader' = [leader EXCEPT ![i] = IF (m.mterm = curTermAfter) THEN m.msource ELSE IF stepDown THEN Nil ELSE @]
           /\ votedFor' = [votedFor EXCEPT ![i] = IF stepDown THEN Nil ELSE @]
           /\ IF m.mterm < curTermAfter \/ ~logOK THEN
                /\ Net' =
                    (Net \ {m})
                    \cup
                    { [ mtype |-> AppendEntriesResponse,
                        mterm |-> curTermAfter,
                        msuccess |-> FALSE,
                        mmatchIndex |-> 0,
                        msource |-> i,
                        mdest |-> m.msource ] }
                /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>
              ELSE
                LET newLog == SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries IN
                LET newCommit == IF m.mcommitIndex > commitIndex[i] THEN m.mcommitIndex ELSE commitIndex[i] IN
                  /\ log' = [log EXCEPT ![i] = newLog]
                  /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommit]
                  /\ Net' =
                      (Net \ {m})
                      \cup
                      { [ mtype |-> AppendEntriesResponse,
                          mterm |-> curTermAfter,
                          msuccess |-> TRUE,
                          mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                          msource |-> i,
                          mdest |-> m.msource ] }
                  /\ UNCHANGED << nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, lastApplied, leaderHint, req, reqIdx, waiting >>

HandleAppendEntriesResponse(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
        /\ m.mdest = i /\ m.mtype = AppendEntriesResponse
        /\ LET j == m.msource IN
           IF m.mterm > currentTerm[i] THEN
             /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
             /\ Net' = Net \ {m}
             /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>
           ELSE IF m.mterm < currentTerm[i] THEN
             /\ Net' = Net \ {m}
             /\ UNCHANGED Vars
           ELSE
             /\ nextIndex' =
                  [nextIndex EXCEPT
                     ![i][j] = IF m.msuccess THEN m.mmatchIndex + 1 ELSE Max({1, nextIndex[i][j] - 1})]
             /\ matchIndex' =
                  [matchIndex EXCEPT
                     ![i][j] = IF m.msuccess THEN m.mmatchIndex ELSE @]
             /\ Net' = Net \ {m}
             /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>

HandleClientRequest(i) ==
  /\ i \in Servers
  /\ \E m \in Net :
        /\ m.mdest = i /\ m.mtype \in {ClientPutRequest, ClientGetRequest}
        /\ IF state[i] = Leader THEN
             LET entry ==
               [ term |-> currentTerm[i],
                 cmd |-> m.mcmd,
                 client |-> m.msource ] IN
               /\ log' = [log EXCEPT ![i] = Append(log[i], entry)]
               /\ Net' = Net \ {m}
               /\ UNCHANGED << state, currentTerm, votedFor, leader, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint, req, reqIdx, waiting >>
           ELSE
             LET respType == IF m.mtype = ClientPutRequest THEN ClientPutResponse ELSE ClientGetResponse IN
             LET resp ==
               [ mtype |-> respType,
                 msuccess |-> FALSE,
                 mresponse |-> IF m.mtype = ClientPutRequest
                                THEN [ idx |-> m.mcmd.idx, key |-> m.mcmd.key ]
                                ELSE [ idx |-> m.mcmd.idx, key |-> m.mcmd.key ],
                 mleaderHint |-> leader[i],
                 msource |-> i,
                 mdest |-> m.msource ] IN
               /\ Net' = (Net \ {m}) \cup { resp }
               /\ UNCHANGED Vars

AdvanceCommit(i) ==
  /\ i \in Servers
  /\ state[i] = Leader
  /\ LET N == FindMaxAgreeIndex(log[i], i, matchIndex[i]) IN
     /\ N # Nil
     /\ log[i][N].term = currentTerm[i]
     /\ N > commitIndex[i]
     /\ commitIndex' = [commitIndex EXCEPT ![i] = N]
     /\ UNCHANGED << state, currentTerm, votedFor, leader, log, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, Net, leaderHint, req, reqIdx, waiting >>

ApplyOne(i) ==
  /\ i \in Servers
  /\ lastApplied[i] < commitIndex[i]
  /\ LET k == lastApplied[i] + 1 IN
     LET e == log[i][k] IN
     LET smStep ==
          IF e.cmd.type = Put
          THEN << [sm[i] EXCEPT ![e.cmd.key] = e.cmd.value], smDom[i] \cup {e.cmd.key} >>
          ELSE << sm[i], smDom[i] >> IN
     LET newSm == smStep[1] IN
     LET newDom == smStep[2] IN
     LET mayResp == state[i] = Leader IN
     LET respSet ==
       IF mayResp THEN
         { IF e.cmd.type = Put THEN
             [ mtype |-> ClientPutResponse,
               msuccess |-> TRUE,
               mresponse |-> [ idx |-> e.cmd.idx, key |-> e.cmd.key ],
               mleaderHint |-> i,
               msource |-> i,
               mdest |-> e.client ]
           ELSE
             [ mtype |-> ClientGetResponse,
               msuccess |-> TRUE,
               mresponse |-> [ idx |-> e.cmd.idx,
                               key |-> e.cmd.key,
                               value |-> (IF e.cmd.key \in DOMAIN newSm THEN newSm[e.cmd.key] ELSE Nil),
                               ok |-> e.cmd.key \in DOMAIN newSm ],
               mleaderHint |-> i,
               msource |-> i,
               mdest |-> e.client ] }
       ELSE {} IN
     /\ sm' = [sm EXCEPT ![i] = newSm]
     /\ smDom' = [smDom EXCEPT ![i] = newDom]
     /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
     /\ Net' = Net \cup respSet
     /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, leaderHint, req, reqIdx, waiting >>

ClientSend(c) ==
  /\ c \in Clients
  /\ ~waiting[c]
  /\ LET lh == leaderHint[c] IN
     LET srv == IF lh = Nil THEN CHOOSE s \in Servers : TRUE ELSE lh IN
     LET newIdx == reqIdx[c] + 1 IN
     /\ \E r \in AllReqs :
          LET cmd ==
            IF r.type = Put
            THEN [ idx |-> newIdx, type |-> Put, key |-> r.key, value |-> r.value ]
            ELSE [ idx |-> newIdx, type |-> Get, key |-> r.key ] IN
          LET msg ==
            IF r.type = Put THEN
              [ mtype |-> ClientPutRequest,
                mcmd |-> cmd,
                msource |-> c,
                mdest |-> srv ]
            ELSE
              [ mtype |-> ClientGetRequest,
                mcmd |-> cmd,
                msource |-> c,
                mdest |-> srv ] IN
          /\ req' = [req EXCEPT ![c] = cmd]
          /\ reqIdx' = [reqIdx EXCEPT ![c] = newIdx]
          /\ waiting' = [waiting EXCEPT ![c] = TRUE]
          /\ Net' = Net \cup { msg }
          /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, leaderHint >>

HandleClientResponse(c) ==
  /\ c \in Clients
  /\ \E m \in Net :
        /\ m.mdest = c
        /\ m.mtype \in {ClientPutResponse, ClientGetResponse}
        /\ IF m.mresponse.idx # reqIdx[c] THEN
             /\ Net' = Net \ {m}
             /\ UNCHANGED Vars
           ELSE
             /\ leaderHint' = [leaderHint EXCEPT ![c] = m.mleaderHint]
             /\ waiting' = [waiting EXCEPT ![c] = FALSE]
             /\ Net' = Net \ {m}
             /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDom, req, reqIdx >>

DropMessage ==
  /\ Net # {}
  /\ \E m \in Net :
       /\ Net' = Net \ {m}
       /\ UNCHANGED Vars

NetDeliverServer == \E i \in Servers :
  HandleRequestVoteRequest(i) \/ HandleRequestVoteResponse(i) \/ HandleAppendEntriesRequest(i) \/ HandleAppendEntriesResponse(i) \/ HandleClientRequest(i)

NetDeliverClient == \E c \in Clients : HandleClientResponse(c)

ElectionTimeoutSome == \E i \in Servers : ElectionTimeout(i)
AppendSendSome == \E i \in Servers : \E j \in Servers \ {i} : AppendSend(i, j)
AdvanceCommitSome == \E i \in Servers : AdvanceCommit(i)
ApplyOneSome == \E i \in Servers : ApplyOne(i)
ClientSendSome == \E c \in Clients : ClientSend(c)
NetDeliverSome == NetDeliverServer \/ NetDeliverClient
DropMessageSome == DropMessage

Next ==
  ElectionTimeoutSome
  \/ AppendSendSome
  \/ NetDeliverSome
  \/ AdvanceCommitSome
  \/ ApplyOneSome
  \/ ClientSendSome
  \/ DropMessageSome

Spec ==
  Init /\ [][Next]_Vars
  /\ WF_Vars(ElectionTimeoutSome)
  /\ WF_Vars(NetDeliverSome)
  /\ WF_Vars(AppendSendSome)
  /\ WF_Vars(AdvanceCommitSome)
  /\ WF_Vars(ApplyOneSome)
  /\ WF_Vars(ClientSendSome)

====