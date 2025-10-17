---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS NumServers, NumClients, AllStrings

Nil == 0

Server == 1..NumServers
Client == (NumServers+1)..(NumServers+NumClients)
Node == Server \cup Client

Put == "put"
Get == "get"

Follower == "follower"
Candidate == "candidate"
Leader == "leader"

RVQ == "rvq"
RVP == "rvp"
APQ == "apq"
APP == "app"
CPQ == "cpq"
CPP == "cpp"
CGQ == "cgq"
CGP == "cgp"

CmdPut(idx, key, val) == [idx |-> idx, type |-> Put, key |-> key, value |-> val]
CmdGet(idx, key) == [idx |-> idx, type |-> Get, key |-> key]

AllReqs ==
  { [type |-> Put, key |-> k, value |-> v] : k \in AllStrings, v \in AllStrings } \cup
  { [type |-> Get, key |-> k] : k \in AllStrings }

LogEntry(cmd, term, client) == [term |-> term, cmd |-> cmd, client |-> client]

RespRec(idx, key, val, ok) == [idx |-> idx, key |-> key, value |-> val, ok |-> ok]

IsQuorum(S) == 2*Cardinality(S) > NumServers

LastTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term

Max2(a, b) == IF a >= b THEN a ELSE b
Min2(a, b) == IF a <= b THEN a ELSE b

RECURSIVE ApplyLogEntry(_,_ ,_)
ApplyLogEntry(entry, sm, dom) ==
  IF entry.cmd.type = Put
  THEN << [sm EXCEPT ![entry.cmd.key] = entry.cmd.value], dom \cup {entry.cmd.key} >>
  ELSE << sm, dom >>

RECURSIVE ApplyLog(_,_ ,_ ,_ ,_)
ApplyLog(xlog, start, end, xsm, xdom) ==
  IF start > end
  THEN << xsm, xdom >>
  ELSE
    LET res == ApplyLogEntry(xlog[start], xsm, xdom) IN
      ApplyLog(xlog, start+1, end, res[1], res[2])

Messages ==
  { m \in [mtype : {RVQ},
           mterm : Nat,
           mlastLogTerm : Nat,
           mlastLogIndex : Nat,
           msource : Server,
           mdest : Server] } \cup
  { m \in [mtype : {RVP},
           mterm : Nat,
           mvoteGranted : BOOLEAN,
           msource : Server,
           mdest : Server] } \cup
  { m \in [mtype : {APQ},
           mterm : Nat,
           mprevLogIndex : Nat,
           mprevLogTerm : Nat,
           mentries : Seq([term : Nat, cmd : [idx : Nat, type : {Put,Get}, key : AllStrings, value : AllStrings \cup {Nil}], client : Client]),
           mcommitIndex : Nat,
           msource : Server,
           mdest : Server] } \cup
  { m \in [mtype : {APP},
           mterm : Nat,
           msuccess : BOOLEAN,
           mmatchIndex : Nat,
           msource : Server,
           mdest : Server] } \cup
  { m \in [mtype : {CPQ},
           mcmd : [idx : Nat, type : {Put}, key : AllStrings, value : AllStrings],
           msource : Client,
           mdest : Server] } \cup
  { m \in [mtype : {CGQ},
           mcmd : [idx : Nat, type : {Get}, key : AllStrings],
           msource : Client,
           mdest : Server] } \cup
  { m \in [mtype : {CPP},
           msuccess : BOOLEAN,
           mresponse : [idx : Nat, key : AllStrings, value : AllStrings \cup {Nil}, ok : BOOLEAN],
           mleaderHint : Server \cup {Nil},
           msource : Server,
           mdest : Client] } \cup
  { m \in [mtype : {CGP},
           msuccess : BOOLEAN,
           mresponse : [idx : Nat, key : AllStrings, value : AllStrings \cup {Nil}, ok : BOOLEAN],
           mleaderHint : Server \cup {Nil},
           msource : Server,
           mdest : Client] }

VARIABLES
  state,
  currentTerm,
  votedFor,
  log,
  commitIndex,
  nextIndex,
  matchIndex,
  leader,
  votesResponded,
  votesGranted,
  leaderTimeout,
  sm,
  smDomain,
  net,
  leaderC,
  reqIdxC,
  pending,
  waiting

vars ==
  << state,
     currentTerm,
     votedFor,
     log,
     commitIndex,
     nextIndex,
     matchIndex,
     leader,
     votesResponded,
     votesGranted,
     leaderTimeout,
     sm,
     smDomain,
     net,
     leaderC,
     reqIdxC,
     pending,
     waiting >>

Init ==
  /\ state = [i \in Server |-> Follower]
  /\ currentTerm = [i \in Server |-> 0]
  /\ votedFor = [i \in Server |-> Nil]
  /\ log = [i \in Server |-> << >>]
  /\ commitIndex = [i \in Server |-> 0]
  /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
  /\ leader = [i \in Server |-> Nil]
  /\ votesResponded = [i \in Server |-> {}]
  /\ votesGranted = [i \in Server |-> {}]
  /\ leaderTimeout = [i \in Server |-> FALSE]
  /\ sm = [i \in Server |-> [k \in AllStrings |-> Nil]]
  /\ smDomain = [i \in Server |-> {}]
  /\ net = {}
  /\ leaderC = [c \in Client |-> Nil]
  /\ reqIdxC = [c \in Client |-> 0]
  /\ pending = [c \in Client |-> CHOOSE r \in AllReqs : TRUE]
  /\ waiting = [c \in Client |-> FALSE]

SetTimeout(i) ==
  /\ i \in Server
  /\ leaderTimeout[i] = FALSE
  /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = TRUE]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, sm, smDomain, net, leaderC, reqIdxC, pending, waiting >>

ResetTimeout(i) ==
  /\ i \in Server
  /\ leaderTimeout[i] = TRUE
  /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, sm, smDomain, net, leaderC, reqIdxC, pending, waiting >>

StartElection(i) ==
  /\ i \in Server
  /\ state[i] \in {Follower, Candidate}
  /\ leaderTimeout[i] = TRUE
  /\ LET newTerm == currentTerm[i] + 1 IN
     /\ state' = [state EXCEPT ![i] = Candidate]
     /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
     /\ votedFor' = [votedFor EXCEPT ![i] = i]
     /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
     /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
     /\ leader' = [leader EXCEPT ![i] = Nil]
     /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
     /\ net' = net \cup { [mtype |-> RVQ,
                          mterm |-> newTerm,
                          mlastLogTerm |-> LastTerm(log[i]),
                          mlastLogIndex |-> Len(log[i]),
                          msource |-> i,
                          mdest |-> j] : j \in Server \ {i} }
     /\ UNCHANGED << log, commitIndex, nextIndex, matchIndex, sm, smDomain, leaderC, reqIdxC, pending, waiting >>

BecomeLeader(i) ==
  /\ i \in Server
  /\ state[i] = Candidate
  /\ IsQuorum(votesGranted[i])
  /\ state' = [state EXCEPT ![i] = Leader]
  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
  /\ leader' = [leader EXCEPT ![i] = i]
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, votesResponded, votesGranted, leaderTimeout, sm, smDomain, net, leaderC, reqIdxC, pending, waiting >>

SendAppendEntries(i, j) ==
  /\ i \in Server
  /\ j \in Server
  /\ i # j
  /\ state[i] = Leader
  /\ nextIndex[i][j] \in Nat
  /\ LET prevIdx == nextIndex[i][j] - 1 IN
     LET prevTerm == IF prevIdx > 0 THEN log[i][prevIdx].term ELSE 0 IN
     LET entries == SubSeq(log[i], nextIndex[i][j], Len(log[i])) IN
     /\ net' = net \cup {
           [mtype |-> APQ,
            mterm |-> currentTerm[i],
            mprevLogIndex |-> prevIdx,
            mprevLogTerm |-> prevTerm,
            mentries |-> entries,
            mcommitIndex |-> commitIndex[i],
            msource |-> i,
            mdest |-> j] }
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderC, reqIdxC, pending, waiting >>

FindMaxAgreeIndex(logLocal, i, matchIdx) ==
  Len(logLocal)

AdvanceCommitIndex(i) ==
  /\ i \in Server
  /\ state[i] = Leader
  /\ LET k == FindMaxAgreeIndex(log[i], i, matchIndex[i]) IN
     /\ k >= commitIndex[i]
     /\ (k = commitIndex[i] \/
         (k > commitIndex[i] /\ log[i][k].term = currentTerm[i]))
     /\ LET newCI == IF k > commitIndex[i] /\ log[i][k].term = currentTerm[i] THEN k ELSE commitIndex[i] IN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCI]
        /\ LET res == ApplyLog(log[i], commitIndex[i] + 1, newCI, sm[i], smDomain[i]) IN
           /\ sm' = [sm EXCEPT ![i] = res[1]]
           /\ smDomain' = [smDomain EXCEPT ![i] = res[2]]
           /\ net' =
                net \cup
                { [mtype |-> IF log[i][k0].cmd.type = Put THEN CPP ELSE CGP,
                   msuccess |-> TRUE,
                   mresponse |-> [idx |-> log[i][k0].cmd.idx,
                                   key |-> log[i][k0].cmd.key,
                                   value |-> IF log[i][k0].cmd.type = Get /\ (log[i][k0].cmd.key \in res[2])
                                             THEN res[1][log[i][k0].cmd.key] ELSE
                                              IF log[i][k0].cmd.type = Put
                                              THEN res[1][log[i][k0].cmd.key] ELSE Nil,
                                   ok |-> (log[i][k0].cmd.key \in res[2])],
                   mleaderHint |-> i,
                   msource |-> i,
                   mdest |-> log[i][k0].client] :
                  k0 \in (commitIndex[i] + 1)..newCI }
  /\ UNCHANGED << state, currentTerm, votedFor, log, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, leaderC, reqIdxC, pending, waiting >>

HandleServerMessage(i, m) ==
  /\ i \in Server
  /\ m \in net
  /\ m.mdest = i
  /\ CASE
    m.mtype = RVQ ->
      LET stepDown ==
        IF m.mterm > currentTerm[i]
        THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
             /\ leader' = [leader EXCEPT ![i] = Nil]
        ELSE /\ currentTerm' = currentTerm
             /\ state' = state
             /\ votedFor' = votedFor
             /\ leader' = leader
      IN
      /\ stepDown
      /\ LET logOK ==
            (m.mlastLogTerm > LastTerm(log[i])) \/
            (m.mlastLogTerm = LastTerm(log[i]) /\ m.mlastLogIndex >= Len(log[i]))
         IN
         LET grant == (m.mterm = currentTerm'[i] /\ logOK /\ (votedFor'[i] \in {Nil, m.msource})) IN
         /\ net' = (net \ {m}) \cup { [mtype |-> RVP,
                                      mterm |-> currentTerm'[i],
                                      mvoteGranted |-> grant,
                                      msource |-> i,
                                      mdest |-> m.msource] }
         /\ votesResponded' = votesResponded
         /\ votesGranted' = votesGranted
         /\ commitIndex' = commitIndex
         /\ nextIndex' = nextIndex
         /\ matchIndex' = matchIndex
         /\ leaderTimeout' = leaderTimeout
         /\ sm' = sm
         /\ smDomain' = smDomain

  [] m.mtype = RVP ->
      LET stp ==
        IF m.mterm > currentTerm[i]
        THEN << [state EXCEPT ![i] = Follower],
               [currentTerm EXCEPT ![i] = m.mterm],
               [votedFor EXCEPT ![i] = Nil],
               [leader EXCEPT ![i] = Nil] >>
        ELSE << state, currentTerm, votedFor, leader >>
      IN
      /\ state' = stp[1]
      /\ currentTerm' = stp[2]
      /\ votedFor' = stp[3]
      /\ leader' = stp[4]
      /\ IF m.mterm < currentTerm'[i]
         THEN /\ net' = net \ {m}
              /\ votesResponded' = votesResponded
              /\ votesGranted' = votesGranted
              /\ leaderTimeout' = leaderTimeout
         ELSE
           /\ votesResponded' = [votesResponded EXCEPT ![i] = @ \cup {m.msource}]
           /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = IF m.mvoteGranted THEN FALSE ELSE leaderTimeout[i]]
           /\ votesGranted' =
                [votesGranted EXCEPT ![i] = IF m.mvoteGranted THEN @ \cup {m.msource} ELSE @]
           /\ net' = net \ {m}
      /\ commitIndex' = commitIndex
      /\ nextIndex' = nextIndex
      /\ matchIndex' = matchIndex
      /\ sm' = sm
      /\ smDomain' = smDomain

  [] m.mtype = APQ ->
      LET stp ==
        IF m.mterm > currentTerm[i]
        THEN << [state EXCEPT ![i] = Follower],
               [currentTerm EXCEPT ![i] = m.mterm],
               [votedFor EXCEPT ![i] = Nil],
               [leader EXCEPT ![i] = Nil] >>
        ELSE << state, currentTerm, votedFor, leader >>
      IN
      LET logOK ==
            (m.mprevLogIndex = 0) \/
            (m.mprevLogIndex > 0 /\ m.mprevLogIndex <= Len(log[i]) /\
             log[i][m.mprevLogIndex].term = m.mprevLogTerm)
      IN
      /\ state' = stp[1]
      /\ currentTerm' = stp[2]
      /\ votedFor' = stp[3]
      /\ leader' = [stp[4] EXCEPT ![i] = IF m.mterm = currentTerm'[i] THEN m.msource ELSE @]
      /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = IF m.mterm = currentTerm'[i] THEN FALSE ELSE @]
      /\ IF (m.mterm < currentTerm'[i]) \/ (~logOK)
         THEN
           /\ net' = (net \ {m}) \cup
                     { [mtype |-> APP,
                        mterm |-> currentTerm'[i],
                        msuccess |-> FALSE,
                        mmatchIndex |-> 0,
                        msource |-> i,
                        mdest |-> m.msource] }
           /\ log' = log
           /\ commitIndex' = commitIndex
           /\ sm' = sm
           /\ smDomain' = smDomain
         ELSE
           /\ LET newLog == [log EXCEPT ![i] = Append(SubSeq(@, 1, m.mprevLogIndex), m.mentries)] IN
              LET ciNew == Max2(commitIndex[i], Min2(Len(newLog[i]), m.mcommitIndex)) IN
              LET res == ApplyLog(newLog[i], commitIndex[i] + 1, ciNew, sm[i], smDomain[i]) IN
              /\ log' = newLog
              /\ commitIndex' = [commitIndex EXCEPT ![i] = ciNew]
              /\ sm' = [sm EXCEPT ![i] = res[1]]
              /\ smDomain' = [smDomain EXCEPT ![i] = res[2]]
           /\ net' = (net \ {m}) \cup
                     { [mtype |-> APP,
                        mterm |-> currentTerm'[i],
                        msuccess |-> TRUE,
                        mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                        msource |-> i,
                        mdest |-> m.msource] }
      /\ votesResponded' = votesResponded
      /\ votesGranted' = votesGranted
      /\ nextIndex' = nextIndex
      /\ matchIndex' = matchIndex

  [] m.mtype = APP ->
      LET stp ==
        IF m.mterm > currentTerm[i]
        THEN << [state EXCEPT ![i] = Follower],
               [currentTerm EXCEPT ![i] = m.mterm],
               [votedFor EXCEPT ![i] = Nil],
               [leader EXCEPT ![i] = Nil] >>
        ELSE << state, currentTerm, votedFor, leader >>
      IN
      /\ state' = stp[1]
      /\ currentTerm' = stp[2]
      /\ votedFor' = stp[3]
      /\ leader' = stp[4]
      /\ IF m.mterm < currentTerm'[i]
         THEN /\ net' = net \ {m}
              /\ nextIndex' = nextIndex
              /\ matchIndex' = matchIndex
              /\ leaderTimeout' = leaderTimeout
         ELSE
           /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
           /\ IF m.msuccess
              THEN /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] = m.mmatchIndex + 1]
                   /\ matchIndex' = [matchIndex EXCEPT ![i][m.msource] = m.mmatchIndex]
              ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] = Max2(1, nextIndex[i][m.msource] - 1)]
                   /\ matchIndex' = matchIndex
           /\ net' = net \ {m}
      /\ votesResponded' = votesResponded
      /\ votesGranted' = votesGranted
      /\ log' = log
      /\ commitIndex' = commitIndex
      /\ sm' = sm
      /\ smDomain' = smDomain

  [] m.mtype \in {CPQ, CGQ} ->
      /\ state' = state
      /\ currentTerm' = currentTerm
      /\ votedFor' = votedFor
      /\ leader' = leader
      /\ votesResponded' = votesResponded
      /\ votesGranted' = votesGranted
      /\ leaderTimeout' = leaderTimeout
      /\ commitIndex' = commitIndex
      /\ nextIndex' = nextIndex
      /\ matchIndex' = matchIndex
      /\ sm' = sm
      /\ smDomain' = smDomain
      /\ IF state[i] = Leader
         THEN
           LET entry ==
                 [term |-> currentTerm[i],
                  cmd |-> IF m.mtype = CPQ
                          THEN [idx |-> m.mcmd.idx, type |-> Put, key |-> m.mcmd.key, value |-> m.mcmd.value]
                          ELSE [idx |-> m.mcmd.idx, type |-> Get, key |-> m.mcmd.key],
                  client |-> m.msource]
           IN
           /\ log' = [log EXCEPT ![i] = Append(@, entry)]
           /\ net' = net \ {m}
         ELSE
           LET respType == IF m.mtype = CPQ THEN CPP ELSE CGP IN
           LET resp == [mtype |-> respType,
                        msuccess |-> FALSE,
                        mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE],
                        mleaderHint |-> leader[i],
                        msource |-> i,
                        mdest |-> m.msource] IN
           /\ log' = log
           /\ net' = (net \ {m}) \cup {resp}

  OTHER ->
      FALSE

ClientSend(c) ==
  /\ c \in Client
  /\ waiting[c] = FALSE
  /\ LET dest == IF leaderC[c] = Nil THEN CHOOSE s \in Server : TRUE ELSE leaderC[c] IN
     LET idx == reqIdxC[c] + 1 IN
     LET rq == CHOOSE r \in AllReqs : TRUE IN
     LET m ==
       IF rq.type = Put
       THEN [mtype |-> CPQ,
             mcmd |-> [idx |-> idx, type |-> Put, key |-> rq.key, value |-> rq.value],
             msource |-> c, mdest |-> dest]
       ELSE [mtype |-> CGQ,
             mcmd |-> [idx |-> idx, type |-> Get, key |-> rq.key],
             msource |-> c, mdest |-> dest]
  /\ net' = net \cup {m}
  /\ reqIdxC' = [reqIdxC EXCEPT ![c] = idx]
  /\ leaderC' = [leaderC EXCEPT ![c] = dest]
  /\ pending' = [pending EXCEPT ![c] = rq]
  /\ waiting' = [waiting EXCEPT ![c] = TRUE]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, sm, smDomain >>

ClientRcv(c, m) ==
  /\ c \in Client
  /\ m \in net
  /\ m.mdest = c
  /\ m.mtype \in {CPP, CGP}
  /\ leaderC' = [leaderC EXCEPT ![c] = m.mleaderHint]
  /\ IF ~m.msuccess
     THEN /\ waiting' = [waiting EXCEPT ![c] = FALSE]
          /\ pending' = pending
     ELSE /\ m.mresponse.idx = reqIdxC[c]
          /\ m.mresponse.key = pending[c].key
          /\ waiting' = [waiting EXCEPT ![c] = FALSE]
          /\ pending' = pending
  /\ net' = net \ {m}
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, sm, smDomain, reqIdxC >>

ClientTimeout(c) ==
  /\ c \in Client
  /\ waiting[c] = TRUE
  /\ \A mm \in net : mm.mdest # c
  /\ leaderC' = [leaderC EXCEPT ![c] = Nil]
  /\ waiting' = [waiting EXCEPT ![c] = FALSE]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, sm, smDomain, net, reqIdxC, pending >>

Drop ==
  /\ net # {}
  /\ \E m \in net : net' = net \ {m}
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesResponded, votesGranted, leaderTimeout, sm, smDomain, leaderC, reqIdxC, pending, waiting >>

Next ==
  \/ \E i \in Server : SetTimeout(i)
  \/ \E i \in Server : ResetTimeout(i)
  \/ \E i \in Server : StartElection(i)
  \/ \E i \in Server : BecomeLeader(i)
  \/ \E i, j \in Server : SendAppendEntries(i, j)
  \/ \E i \in Server, m \in net : HandleServerMessage(i, m)
  \/ \E i \in Server : AdvanceCommitIndex(i)
  \/ \E c \in Client : ClientSend(c)
  \/ \E c \in Client, m \in net : ClientRcv(c, m)
  \/ \E c \in Client : ClientTimeout(c)
  \/ Drop

Spec ==
  Init /\ [][Next]_vars /\
  WF_vars(\E i \in Server : StartElection(i)) /\
  WF_vars(\E i \in Server, j \in Server : SendAppendEntries(i,j)) /\
  WF_vars(\E i \in Server, m \in net : HandleServerMessage(i, m)) /\
  WF_vars(\E c \in Client, m \in net : ClientRcv(c, m))

====