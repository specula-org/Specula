---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    Servers,
    Clients,
    Keys,
    Values,
    Nil

Nodes == Servers \cup Clients
NumServers == Cardinality(Servers)
Nat1 == Nat \ {0}

RVQ == "rvq"
RVP == "rvp"
APQ == "apq"
APP == "app"
CPQ == "cpq"
CPP == "cpp"
CGQ == "cgq"
CGP == "cgp"

Put == "put"
Get == "get"

IsQuorum(S) == 2*Cardinality(S) > NumServers

Max2(a,b) == IF a >= b THEN a ELSE b
Min2(a,b) == IF a <= b THEN a ELSE b

RemoveAt(s,k) == SubSeq(s, 1, k - 1) \o SubSeq(s, k + 1, Len(s))

Entry == [term: Nat, cmd: Cmd, client: Clients]
Cmd == [idx: Nat, type: {Put,Get}, key: Keys, value: Values \cup {Nil}]

RVQMsg ==
  [ mtype: {RVQ},
    mterm: Nat,
    mlastLogTerm: Nat,
    mlastLogIndex: Nat,
    msource: Servers,
    mdest: Servers ]

RVPMsg ==
  [ mtype: {RVP},
    mterm: Nat,
    mvoteGranted: BOOLEAN,
    msource: Servers,
    mdest: Servers ]

APQMsg ==
  [ mtype: {APQ},
    mterm: Nat,
    mprevLogIndex: Nat,
    mprevLogTerm: Nat,
    mentries: Seq(Entry),
    mcommitIndex: Nat,
    msource: Servers,
    mdest: Servers ]

APPMsg ==
  [ mtype: {APP},
    mterm: Nat,
    msuccess: BOOLEAN,
    mmatchIndex: Nat,
    msource: Servers,
    mdest: Servers ]

ClientQMsg ==
  [ mtype: {CPQ,CGQ},
    mcmd: Cmd,
    msource: Clients,
    mdest: Servers ]

ClientPMsg ==
  [ mtype: {CPP,CGP},
    msuccess: BOOLEAN,
    mresponse: [ idx: Nat, key: Keys, value: Values \cup {Nil}, ok: BOOLEAN ],
    mleaderHint: (Servers \cup {Nil}),
    msource: Servers,
    mdest: Clients ]

Msg == RVQMsg \cup RVPMsg \cup APQMsg \cup APPMsg \cup ClientQMsg \cup ClientPMsg

LastTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

UpToDate(mlastTerm, mlastIndex, li) ==
    \/ mlastTerm > LastTerm(li)
    \/ /\ mlastTerm = LastTerm(li)
       /\ mlastIndex >= Len(li)

PrevOK(mpIdx, mpTerm, li) ==
    \/ mpIdx = 0
    \/ /\ mpIdx > 0
       /\ mpIdx <= Len(li)
       /\ li[mpIdx].term = mpTerm

EligibleCommit(i) ==
    { n \in 0..Len(log[i]) :
        IsQuorum({i} \cup { k \in Servers : matchIndex[i][k] >= n})
    }

MaxNat(S) ==
    IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x

MaxAgreeIndex(i) == MaxNat(EligibleCommit(i))

VARIABLES
    state,
    currentTerm,
    votedFor,
    leader,
    log,
    commitIndex,
    nextIndex,
    matchIndex,
    votesResponded,
    votesGranted,
    electionTimer,
    appliedIndex,
    sm,
    smDom,
    leaderHint,
    reqIdx,
    Net

vars == << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex,
           votesResponded, votesGranted, electionTimer, appliedIndex, sm, smDom,
           leaderHint, reqIdx, Net >>

Init ==
    /\ state = [i \in Servers |-> "follower"]
    /\ currentTerm = [i \in Servers |-> 0]
    /\ votedFor = [i \in Servers |-> Nil]
    /\ leader = [i \in Servers |-> Nil]
    /\ log = [i \in Servers |-> << >>]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votesResponded = [i \in Servers |-> {}]
    /\ votesGranted = [i \in Servers |-> {}]
    /\ electionTimer = [i \in Servers |-> FALSE]
    /\ appliedIndex = [i \in Servers |-> 0]
    /\ sm = [i \in Servers |-> [k \in {} |-> CHOOSE v \in Values : TRUE]]
    /\ smDom = [i \in Servers |-> {}]
    /\ leaderHint = [c \in Clients |-> Nil]
    /\ reqIdx = [c \in Clients |-> 0]
    /\ Net = [n \in Nodes |-> << >>]

Tick(i) ==
    /\ i \in Servers
    /\ electionTimer[i] = FALSE
    /\ electionTimer' = [electionTimer EXCEPT ![i] = TRUE]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                    matchIndex, votesResponded, votesGranted, appliedIndex, sm, smDom,
                    leaderHint, reqIdx, Net >>

LeaderTimeout(i) ==
    /\ i \in Servers
    /\ electionTimer[i] = TRUE
    /\ state[i] \in {"follower","candidate"}
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = FALSE]
    /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, appliedIndex, sm, smDom,
                    leaderHint, reqIdx, Net >>

SendRVQ(i,j) ==
    /\ i \in Servers /\ j \in Servers /\ i # j
    /\ state[i] = "candidate"
    LET m == [ mtype |-> RVQ,
               mterm |-> currentTerm[i],
               mlastLogTerm |-> LastTerm(log[i]),
               mlastLogIndex |-> Len(log[i]),
               msource |-> i,
               mdest |-> j ] IN
    /\ Net' = [Net EXCEPT ![j] = Append(@, m)]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                    matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                    sm, smDom, leaderHint, reqIdx >>

SendAppendEntries(i,j) ==
    /\ i \in Servers /\ j \in Servers /\ i # j
    /\ state[i] = "leader"
    LET nidx == nextIndex[i][j] IN
    LET prevIdx == nidx - 1 IN
    LET prevTerm == IF prevIdx = 0 THEN 0 ELSE log[i][prevIdx].term IN
    LET ents == SubSeq(log[i], nidx, Len(log[i])) IN
    LET m == [ mtype |-> APQ,
               mterm |-> currentTerm[i],
               mprevLogIndex |-> prevIdx,
               mprevLogTerm |-> prevTerm,
               mentries |-> ents,
               mcommitIndex |-> commitIndex[i],
               msource |-> i,
               mdest |-> j ] IN
    /\ Net' = [Net EXCEPT ![j] = Append(@, m)]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                    matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                    sm, smDom, leaderHint, reqIdx >>

BecomeLeader(i) ==
    /\ i \in Servers
    /\ state[i] = "candidate"
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = "leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, votesResponded, votesGranted,
                    electionTimer, appliedIndex, sm, smDom, leaderHint, reqIdx, Net >>

AdvanceCommit(i) ==
    /\ i \in Servers
    /\ state[i] = "leader"
    LET N == MaxAgreeIndex(i) IN
    /\ commitIndex' =
         IF /\ N > commitIndex[i]
            /\ N > 0
            /\ log[i][N].term = currentTerm[i]
         THEN [commitIndex EXCEPT ![i] = N]
         ELSE commitIndex
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, nextIndex,
                    matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                    sm, smDom, leaderHint, reqIdx, Net >>

ApplyOne(i) ==
    /\ i \in Servers
    /\ appliedIndex[i] < commitIndex[i]
    LET k == appliedIndex[i] + 1 IN
    LET e == log[i][k] IN
    LET cmd == e.cmd IN
    LET isPut == cmd.type = Put IN
    LET key == cmd.key IN
    LET val == cmd.value IN
    LET smi == sm[i] IN
    LET smDomI == smDom[i] IN
    LET smi1 == IF isPut THEN [smi EXCEPT ![key] = val] ELSE smi IN
    LET smDom1 == IF isPut THEN smDomI \cup {key} ELSE smDomI IN
    LET okv == (cmd.type = Get) /\ key \in smDom1 IN
    LET gval == IF okv THEN smi1[key] ELSE Nil IN
    LET respType == IF cmd.type = Put THEN CPP ELSE CGP IN
    LET resp == [ mtype |-> respType,
                  msource |-> i,
                  mdest |-> e.client,
                  msuccess |-> TRUE,
                  mresponse |-> [idx |-> cmd.idx, key |-> key, value |-> gval, ok |-> (IF cmd.type = Get THEN okv ELSE TRUE)],
                  mleaderHint |-> i ] IN
    /\ sm' = [sm EXCEPT ![i] = smi1]
    /\ smDom' = [smDom EXCEPT ![i] = smDom1]
    /\ appliedIndex' = [appliedIndex EXCEPT ![i] = k]
    /\ Net' =
         IF state[i] = "leader"
         THEN [Net EXCEPT ![e.client] = Append(@, resp)]
         ELSE Net
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                    matchIndex, votesResponded, votesGranted, electionTimer, leaderHint, reqIdx >>

ClientSendPut(c) ==
    /\ c \in Clients
    LET iHint == leaderHint[c] IN
    LET j == IF iHint \in Servers THEN iHint ELSE CHOOSE s \in Servers : TRUE IN
    \E k \in Keys, v \in Values:
      LET idx == reqIdx[c] + 1 IN
      LET cmd == [idx |-> idx, type |-> Put, key |-> k, value |-> v] IN
      LET m == [ mtype |-> CPQ,
                 mcmd |-> cmd,
                 msource |-> c,
                 mdest |-> j ] IN
      /\ Net' = [Net EXCEPT ![j] = Append(@, m)]
      /\ reqIdx' = [reqIdx EXCEPT ![c] = idx]
      /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                      matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                      sm, smDom, leaderHint >>

ClientSendGet(c) ==
    /\ c \in Clients
    LET iHint == leaderHint[c] IN
    LET j == IF iHint \in Servers THEN iHint ELSE CHOOSE s \in Servers : TRUE IN
    \E k \in Keys:
      LET idx == reqIdx[c] + 1 IN
      LET cmd == [idx |-> idx, type |-> Get, key |-> k, value |-> Nil] IN
      LET m == [ mtype |-> CGQ,
                 mcmd |-> cmd,
                 msource |-> c,
                 mdest |-> j ] IN
      /\ Net' = [Net EXCEPT ![j] = Append(@, m)]
      /\ reqIdx' = [reqIdx EXCEPT ![c] = idx]
      /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                      matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                      sm, smDom, leaderHint >>

Drop(d,k) ==
    /\ d \in Nodes
    /\ k \in 1..Len(Net[d])
    /\ Net' = [Net EXCEPT ![d] = RemoveAt(@, k)]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                    matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                    sm, smDom, leaderHint, reqIdx >>

Deliver(d,k) ==
    LET m == Net[d][k] IN
    /\ d \in Nodes
    /\ k \in 1..Len(Net[d])
    /\ m.mdest = d
    /\ IF d \in Servers THEN
         LET i == d IN
         CASE m.mtype = RVQ ->
                LET j == m.msource IN
                LET newTerm == Max2(currentTerm[i], m.mterm) IN
                LET madeHigher == m.mterm > currentTerm[i] IN
                LET state1 == IF madeHigher THEN [state EXCEPT ![i] = "follower"] ELSE state IN
                LET votedFor1 == IF madeHigher THEN [votedFor EXCEPT ![i] = Nil] ELSE votedFor IN
                LET leader1 == IF madeHigher THEN [leader EXCEPT ![i] = Nil] ELSE leader IN
                LET grant ==
                      /\ m.mterm = newTerm
                      /\ UpToDate(m.mlastLogTerm, m.mlastLogIndex, log[i])
                      /\ votedFor1[i] \in {Nil, j}
                IN
                /\ Net' =
                     [Net EXCEPT
                        ![i] = RemoveAt(@, k),
                        ![j] = Append(@, [ mtype |-> RVP,
                                           mterm |-> newTerm,
                                           mvoteGranted |-> grant,
                                           msource |-> i,
                                           mdest |-> j ])]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
                /\ state' = state1
                /\ votedFor' = IF grant THEN [votedFor1 EXCEPT ![i] = j] ELSE votedFor1
                /\ leader' = leader1
                /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted,
                                electionTimer, appliedIndex, sm, smDom, leaderHint, reqIdx >>
           [] m.mtype = RVP ->
                LET j == m.msource IN
                LET newTerm == Max2(currentTerm[i], m.mterm) IN
                LET madeHigher == m.mterm > currentTerm[i] IN
                LET state1 == IF madeHigher THEN [state EXCEPT ![i] = "follower"] ELSE state IN
                LET votedFor1 == IF madeHigher THEN [votedFor EXCEPT ![i] = Nil] ELSE votedFor IN
                LET leader1 == IF madeHigher THEN [leader EXCEPT ![i] = Nil] ELSE leader IN
                /\ Net' = [Net EXCEPT ![i] = RemoveAt(@, k)]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
                /\ state' = state1
                /\ votedFor' = votedFor1
                /\ leader' = leader1
                /\ IF /\ m.mterm = newTerm
                      /\ state1[i] = "candidate"
                   THEN
                     /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
                     /\ votesGranted' =
                         IF m.mvoteGranted
                         THEN [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                         ELSE votesGranted
                     /\ electionTimer' =
                         IF m.mvoteGranted
                         THEN [electionTimer EXCEPT ![i] = FALSE]
                         ELSE electionTimer
                   ELSE
                     /\ votesResponded' = votesResponded
                     /\ votesGranted' = votesGranted
                     /\ electionTimer' = electionTimer
                /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, appliedIndex, sm, smDom, leaderHint, reqIdx >>
           [] m.mtype = APQ ->
                LET j == m.msource IN
                LET newTerm == Max2(currentTerm[i], m.mterm) IN
                LET madeHigher == m.mterm > currentTerm[i] IN
                LET state1 == IF madeHigher THEN [state EXCEPT ![i] = "follower"] ELSE state IN
                LET votedFor1 == IF madeHigher THEN [votedFor EXCEPT ![i] = Nil] ELSE votedFor IN
                LET leader1a == IF madeHigher THEN [leader EXCEPT ![i] = Nil] ELSE leader IN
                LET equalTerm == (m.mterm = newTerm) IN
                LET state2 == IF (equalTerm /\ state1[i] = "candidate") THEN [state1 EXCEPT ![i] = "follower"] ELSE state1 IN
                LET leader2 == IF equalTerm THEN [leader1a EXCEPT ![i] = j] ELSE leader1a IN
                LET timer2 == IF equalTerm THEN [electionTimer EXCEPT ![i] = FALSE] ELSE electionTimer IN
                LET lOK == PrevOK(m.mprevLogIndex, m.mprevLogTerm, log[i]) IN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
                /\ state' = state2
                /\ votedFor' = votedFor1
                /\ leader' = leader2
                /\ IF \/ m.mterm < newTerm
                      \/ /\ equalTerm /\ ~lOK
                   THEN
                     /\ Net' =
                          [Net EXCEPT
                             ![i] = RemoveAt(@, k),
                             ![j] = Append(@, [ mtype |-> APP,
                                                mterm |-> newTerm,
                                                msuccess |-> FALSE,
                                                mmatchIndex |-> 0,
                                                msource |-> i,
                                                mdest |-> j ])]
                     /\ log' = log
                     /\ commitIndex' = commitIndex
                   ELSE
                     LET newLog == SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries IN
                     LET newCommit == Max2(commitIndex[i], Min2(m.mcommitIndex, Len(newLog))) IN
                     /\ log' = [log EXCEPT ![i] = newLog]
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommit]
                     /\ Net' =
                          [Net EXCEPT
                             ![i] = RemoveAt(@, k),
                             ![j] = Append(@, [ mtype |-> APP,
                                                mterm |-> newTerm,
                                                msuccess |-> TRUE,
                                                mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                                                msource |-> i,
                                                mdest |-> j ])]
                /\ electionTimer' = timer2
                /\ UNCHANGED << nextIndex, matchIndex, votesResponded, votesGranted, appliedIndex, sm, smDom, leaderHint, reqIdx >>
           [] m.mtype = APP ->
                LET j == m.msource IN
                LET newTerm == Max2(currentTerm[i], m.mterm) IN
                LET madeHigher == m.mterm > currentTerm[i] IN
                LET state1 == IF madeHigher THEN [state EXCEPT ![i] = "follower"] ELSE state IN
                LET votedFor1 == IF madeHigher THEN [votedFor EXCEPT ![i] = Nil] ELSE votedFor IN
                LET leader1 == IF madeHigher THEN [leader EXCEPT ![i] = Nil] ELSE leader IN
                /\ Net' = [Net EXCEPT ![i] = RemoveAt(@, k)]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
                /\ state' = state1
                /\ votedFor' = votedFor1
                /\ leader' = leader1
                /\ IF m.mterm = newTerm
                   THEN
                     /\ electionTimer' = [electionTimer EXCEPT ![i] = FALSE]
                     /\ IF m.msuccess
                        THEN
                          /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = m.mmatchIndex + 1]]
                          /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![j] = m.mmatchIndex]]
                        ELSE
                          /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = Max2(nextIndex[i][j] - 1, 1)]]
                          /\ matchIndex' = matchIndex
                   ELSE
                     /\ electionTimer' = electionTimer
                     /\ nextIndex' = nextIndex
                     /\ matchIndex' = matchIndex
                /\ UNCHANGED << log, commitIndex, votesResponded, votesGranted, appliedIndex, sm, smDom, leaderHint, reqIdx >>
           [] m.mtype \in {CPQ,CGQ} ->
                /\ currentTerm' = currentTerm
                /\ votesResponded' = votesResponded
                /\ votesGranted' = votesGranted
                /\ electionTimer' = electionTimer
                /\ appliedIndex' = appliedIndex
                /\ commitIndex' = commitIndex
                /\ nextIndex' = nextIndex
                /\ matchIndex' = matchIndex
                /\ sm' = sm
                /\ smDom' = smDom
                /\ leader' = leader
                /\ state' = state
                /\ votedFor' = votedFor
                /\ leaderHint' = leaderHint
                /\ reqIdx' = reqIdx
                /\ IF state[i] = "leader"
                   THEN
                     LET entry == [term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource] IN
                     /\ log' = [log EXCEPT ![i] = Append(@, entry)]
                     /\ Net' = [Net EXCEPT ![i] = RemoveAt(@, k)]
                   ELSE
                     LET respType == IF m.mtype = CPQ THEN CPP ELSE CGP IN
                     LET resp == [ mtype |-> respType,
                                   msource |-> i,
                                   mdest |-> m.msource,
                                   msuccess |-> FALSE,
                                   mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE],
                                   mleaderHint |-> leader[i] ] IN
                     /\ log' = log
                     /\ Net' = [Net EXCEPT ![i] = RemoveAt(@, k), ![m.msource] = Append(@, resp)]
           [] OTHER ->
                FALSE
       ELSE
         CASE m.mtype \in {CPP,CGP} ->
                /\ Net' = [Net EXCEPT ![d] = RemoveAt(@, k)]
                /\ leaderHint' = [leaderHint EXCEPT ![d] = m.mleaderHint]
                /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex,
                                matchIndex, votesResponded, votesGranted, electionTimer, appliedIndex,
                                sm, smDom, reqIdx >>
           [] OTHER -> FALSE

AdvanceCommitAny == \E i \in Servers : AdvanceCommit(i)
ApplyOneAny == \E i \in Servers : ApplyOne(i)
LeaderTimeoutAny == \E i \in Servers : LeaderTimeout(i)
SendRVQAny == \E i,j \in Servers : SendRVQ(i,j)
SendAppendEntriesAny == \E i,j \in Servers : SendAppendEntries(i,j)
DeliverAny == \E d \in Nodes, k \in 1..Len(Net[d]) : Deliver(d,k)
DropAny == \E d \in Nodes, k \in 1..Len(Net[d]) : Drop(d,k)
ClientSendAny ==
    \E c \in Clients :
        ClientSendPut(c) \/ ClientSendGet(c)
TickAny == \E i \in Servers : Tick(i)
BecomeLeaderAny == \E i \in Servers : BecomeLeader(i)

Next ==
    \/ TickAny
    \/ LeaderTimeoutAny
    \/ SendRVQAny
    \/ SendAppendEntriesAny
    \/ BecomeLeaderAny
    \/ AdvanceCommitAny
    \/ ApplyOneAny
    \/ ClientSendAny
    \/ DeliverAny
    \/ DropAny

Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(DeliverAny)
    /\ WF_vars(LeaderTimeoutAny)
    /\ WF_vars(SendRVQAny)
    /\ WF_vars(SendAppendEntriesAny)
    /\ WF_vars(AdvanceCommitAny)
    /\ WF_vars(ApplyOneAny)
    /\ WF_vars(ClientSendAny)
    /\ WF_vars(TickAny)

====