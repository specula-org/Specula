---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumServers, NumClients, AllStrings

Nil == 0

Server == 1..NumServers
Client == 1..NumClients

Key == AllStrings
Value == AllStrings
ValueOrNil == Value \cup {Nil}

ReqType == {"put","get"}

MsgType == {"rvq","rvp","apq","app","cpq","cgq","cpp","cgp"}

ServerOrNil == Server \cup {Nil}

Entry == [term: Nat, cmd: [idx: Nat, type: ReqType, key: Key, value: ValueOrNil], client: Client]

ReqPut(c, idx, k, v) == [idx |-> idx, type |-> "put", key |-> k, value |-> v]
ReqGet(c, idx, k) == [idx |-> idx, type |-> "get", key |-> k]

LastTerm(s) == IF Len(s) = 0 THEN 0 ELSE s[Len(s)].term

IsQuorum(S) == 2*Cardinality(S) > NumServers

MaxNat(S) == CHOOSE x \in S: \A y \in S: y <= x

Max2(a,b) == IF a >= b THEN a ELSE b

AddMsg(b,m) == [b EXCEPT ![m] = IF m \in DOMAIN b THEN b[m] + 1 ELSE 1]
RemMsg(b,m) == [b EXCEPT ![m] = b[m] - 1]

FindMaxAgreeIndex(log, i, matchIndex) ==
  LET idxs == 0..Len(log) IN
    MaxNat({ n \in idxs: IsQuorum({i} \cup { j \in Server: matchIndex[j] >= n})})

RVQ(m) == m.mtype = "rvq"
RVP(m) == m.mtype = "rvp"
APQ(m) == m.mtype = "apq"
APP(m) == m.mtype = "app"
CPQ(m) == m.mtype = "cpq"
CGQ(m) == m.mtype = "cgq"
CPP(m) == m.mtype = "cpp"
CGP(m) == m.mtype = "cgp"

VARIABLES
  state, currentTerm, votedFor, leader,
  log, commitIndex, appliedIndex,
  nextIndex, matchIndex,
  votesResponded, votesGranted,
  sm, smDomain,
  Timeout,
  Net,
  leaderOf, reqIdx

TypeInv ==
  /\ state \in [Server -> {"follower","candidate","leader"}]
  /\ currentTerm \in [Server -> Nat]
  /\ votedFor \in [Server -> ServerOrNil]
  /\ leader \in [Server -> ServerOrNil]
  /\ log \in [Server -> Seq(Entry)]
  /\ commitIndex \in [Server -> Nat]
  /\ appliedIndex \in [Server -> Nat]
  /\ nextIndex \in [Server -> [Server -> Nat]]
  /\ matchIndex \in [Server -> [Server -> Nat]]
  /\ votesResponded \in [Server -> SUBSET Server]
  /\ votesGranted \in [Server -> SUBSET Server]
  /\ sm \in [Server -> [Key -> ValueOrNil]]
  /\ smDomain \in [Server -> SUBSET Key]
  /\ Timeout \in [Server -> BOOLEAN]
  /\ Net \in Bags
  /\ leaderOf \in [Client -> ServerOrNil]
  /\ reqIdx \in [Client -> Nat]

Init ==
  /\ state = [i \in Server |-> "follower"]
  /\ currentTerm = [i \in Server |-> 0]
  /\ votedFor = [i \in Server |-> Nil]
  /\ leader = [i \in Server |-> Nil]
  /\ log = [i \in Server |-> << >>]
  /\ commitIndex = [i \in Server |-> 0]
  /\ appliedIndex = [i \in Server |-> 0]
  /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
  /\ votesResponded = [i \in Server |-> {}]
  /\ votesGranted = [i \in Server |-> {}]
  /\ sm = [i \in Server |-> [k \in Key |-> Nil]]
  /\ smDomain = [i \in Server |-> {}]
  /\ Timeout = [i \in Server |-> FALSE]
  /\ Net = [m \in {} |-> 0]
  /\ leaderOf = [c \in Client |-> Nil]
  /\ reqIdx = [c \in Client |-> 0]

TimerExpire(i) ==
  /\ i \in Server
  /\ ~Timeout[i]
  /\ Timeout' = [Timeout EXCEPT ![i] = TRUE]
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                 nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Net,
                 leaderOf, reqIdx >>

CandidateStart(i) ==
  /\ i \in Server
  /\ Timeout[i]
  /\ state[i] \in {"follower","candidate"}
  /\ state' = [state EXCEPT ![i] = "candidate"]
  /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
  /\ votedFor' = [votedFor EXCEPT ![i] = i]
  /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
  /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
  /\ leader' = [leader EXCEPT ![i] = Nil]
  /\ Timeout' = [Timeout EXCEPT ![i] = FALSE]
  /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex, sm, smDomain, Net, leaderOf, reqIdx >>

SendRequestVote(i,j) ==
  /\ i \in Server /\ j \in Server /\ i # j
  /\ state[i] = "candidate"
  /\ LET m == [
        mtype |-> "rvq",
        mterm |-> currentTerm[i],
        mlastLogTerm |-> LastTerm(log[i]),
        mlastLogIndex |-> Len(log[i]),
        msource |-> i,
        mdest |-> j
     ]
     IN Net' = AddMsg(Net, m)
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                 nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout,
                 leaderOf, reqIdx >>

SendAppendEntries(i,j) ==
  /\ i \in Server /\ j \in Server /\ i # j
  /\ state[i] = "leader"
  /\ LET pidx == nextIndex[i][j] - 1 IN
     LET pterm == IF pidx > 0 THEN log[i][pidx].term ELSE 0 IN
     LET ents == SubSeq(log[i], nextIndex[i][j], Len(log[i])) IN
     LET m == [
        mtype |-> "apq",
        mterm |-> currentTerm[i],
        mprevLogIndex |-> pidx,
        mprevLogTerm |-> pterm,
        mentries |-> ents,
        mcommitIndex |-> commitIndex[i],
        msource |-> i,
        mdest |-> j
     ]
     IN Net' = AddMsg(Net, m)
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                 nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout,
                 leaderOf, reqIdx >>

Deliver ==
  \E m \in DOMAIN Net :
    /\ Net[m] > 0
    /\ IF RVQ(m) THEN
         LET i == m.mdest IN
         LET j == m.msource IN
         LET ct == currentTerm[i] IN
         LET lt == LastTerm(log[i]) IN
         LET logOK == (m.mlastLogTerm > lt) \/
                       (m.mlastLogTerm = lt /\ m.mlastLogIndex >= Len(log[i])) IN
         LET newTerm == IF m.mterm > ct THEN m.mterm ELSE ct IN
         LET newState == IF m.mterm > ct THEN "follower" ELSE state[i] IN
         LET newVotedFor == IF m.mterm > ct THEN Nil ELSE votedFor[i] IN
         LET newLeader == IF m.mterm > ct THEN Nil ELSE leader[i] IN
         LET grant == (m.mterm = newTerm) /\ logOK /\ (newVotedFor \in {Nil, j}) IN
         /\ Net' = AddMsg(RemMsg(Net, m),
                          [mtype |-> "rvp",
                           mterm |-> newTerm,
                           mvoteGranted |-> grant,
                           msource |-> i,
                           mdest |-> j])
         /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
         /\ state' = [state EXCEPT ![i] = newState]
         /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE newVotedFor]
         /\ leader' = [leader EXCEPT ![i] = newLeader]
         /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex,
                        votesResponded, votesGranted, sm, smDomain, Timeout, leaderOf, reqIdx >>
       ELSE IF RVP(m) THEN
         LET i == m.mdest IN
         LET j == m.msource IN
         LET ct == currentTerm[i] IN
         /\ IF m.mterm > ct THEN
              /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
              /\ state' = [state EXCEPT ![i] = "follower"]
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ leader' = [leader EXCEPT ![i] = Nil]
              /\ votesResponded' = votesResponded
              /\ votesGranted' = votesGranted
              /\ Timeout' = Timeout
            ELSE
              /\ currentTerm' = currentTerm
              /\ state' = state
              /\ votedFor' = votedFor
              /\ leader' = leader
              /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
              /\ votesGranted' = [votesGranted EXCEPT ![i] =
                    IF m.mvoteGranted THEN votesGranted[i] \cup {j} ELSE votesGranted[i]]
              /\ Timeout' = [Timeout EXCEPT ![i] = IF m.mvoteGranted THEN FALSE ELSE Timeout[i]]
         /\ LET becomeLeader ==
                (state'[i] = "candidate") /\ IsQuorum(votesGranted'[i]) IN
            /\ IF becomeLeader THEN
                 /\ state'' = [state' EXCEPT ![i] = "leader"]
                 /\ nextIndex' = [nextIndex EXCEPT ![i] = [k \in Server |-> Len(log[i]) + 1]]
                 /\ matchIndex' = [matchIndex EXCEPT ![i] = [k \in Server |-> 0]]
                 /\ leader'' = [leader' EXCEPT ![i] = i]
               ELSE
                 /\ state'' = state'
                 /\ nextIndex' = nextIndex
                 /\ matchIndex' = matchIndex
                 /\ leader'' = leader'
         /\ Net' = RemMsg(Net, m)
         /\ UNCHANGED << log, commitIndex, appliedIndex, sm, smDomain, leaderOf, reqIdx >>
         /\ state'' = state'
         /\ leader'' = leader'
       ELSE IF APQ(m) THEN
         LET i == m.mdest IN
         LET j == m.msource IN
         LET ct == currentTerm[i] IN
         LET st == state[i] IN
         LET newTerm == IF m.mterm > ct THEN m.mterm ELSE ct IN
         LET newState == IF m.mterm > ct THEN "follower" ELSE st IN
         LET newVotedFor == IF m.mterm > ct THEN Nil ELSE votedFor[i] IN
         LET newLeader == IF m.mterm > ct THEN Nil ELSE leader[i] IN
         LET eqTerm == (m.mterm = newTerm) IN
         LET leaderNow == IF eqTerm THEN j ELSE newLeader IN
         LET stateNow == IF eqTerm /\ newState = "candidate" THEN "follower" ELSE newState IN
         LET logOK == (m.mprevLogIndex = 0) \/
                       (m.mprevLogIndex > 0 /\ m.mprevLogIndex <= Len(log[i]) /\
                        log[i][m.mprevLogIndex].term = m.mprevLogTerm) IN
         /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
         /\ state' = [state EXCEPT ![i] = stateNow]
         /\ votedFor' = [votedFor EXCEPT ![i] = newVotedFor]
         /\ leader' = [leader EXCEPT ![i] = leaderNow]
         /\ Timeout' = [Timeout EXCEPT ![i] = IF eqTerm THEN FALSE ELSE Timeout[i]]
         /\ IF ~logOK THEN
              /\ Net' = AddMsg(RemMsg(Net, m),
                               [mtype |-> "app",
                                mterm |-> newTerm,
                                msuccess |-> FALSE,
                                mmatchIndex |-> 0,
                                msource |-> i,
                                mdest |-> j])
              /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex,
                               votesResponded, votesGranted, sm, smDomain, leaderOf, reqIdx >>
            ELSE
              LET newLog == SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries IN
              LET newCommit == Max2(commitIndex[i], Min(Len(newLog), m.mcommitIndex)) IN
              /\ log' = [log EXCEPT ![i] = newLog]
              /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommit]
              /\ Net' = AddMsg(RemMsg(Net, m),
                               [mtype |-> "app",
                                mterm |-> newTerm,
                                msuccess |-> TRUE,
                                mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                                msource |-> i,
                                mdest |-> j])
              /\ UNCHANGED << appliedIndex, nextIndex, matchIndex, votesResponded, votesGranted,
                              sm, smDomain, leaderOf, reqIdx >>
       ELSE IF APP(m) THEN
         LET i == m.mdest IN
         LET j == m.msource IN
         LET ct == currentTerm[i] IN
         /\ IF m.mterm > ct THEN
              /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
              /\ state' = [state EXCEPT ![i] = "follower"]
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ leader' = [leader EXCEPT ![i] = Nil]
              /\ Timeout' = Timeout
              /\ nextIndex' = nextIndex
              /\ matchIndex' = matchIndex
            ELSE
              /\ currentTerm' = currentTerm
              /\ state' = state
              /\ votedFor' = votedFor
              /\ leader' = leader
              /\ Timeout' = [Timeout EXCEPT ![i] = FALSE]
              /\ nextIndex' =
                   IF m.msuccess
                     THEN [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = m.mmatchIndex + 1]]
                     ELSE [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = Max2(nextIndex[i][j] - 1, 1)]]
              /\ matchIndex' =
                   IF m.msuccess
                     THEN [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![j] = m.mmatchIndex]]
                     ELSE matchIndex
         /\ Net' = RemMsg(Net, m)
         /\ UNCHANGED << log, commitIndex, appliedIndex, votesResponded, votesGranted, sm, smDomain, leaderOf, reqIdx >>
       ELSE IF CPQ(m) \/ CGQ(m) THEN
         LET i == m.mdest IN
         LET c == m.msource IN
         LET cmd == m.mcmd IN
         /\ IF state[i] = "leader" THEN
              LET val == IF "value" \in DOMAIN cmd THEN cmd.value ELSE Nil IN
              LET entry == [term |-> currentTerm[i],
                            cmd |-> [idx |-> cmd.idx, type |-> cmd.type, key |-> cmd.key, value |-> val],
                            client |-> c] IN
              /\ log' = [log EXCEPT ![i] = log[i] \o << entry >>]
              /\ Net' = RemMsg(Net, m)
              /\ UNCHANGED << state, currentTerm, votedFor, leader, commitIndex, appliedIndex,
                              nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain,
                              Timeout, leaderOf, reqIdx >>
            ELSE
              LET respType == IF CPQ(m) THEN "cpp" ELSE "cgp" IN
              LET resp == [
                   mtype |-> respType,
                   msuccess |-> FALSE,
                   mresponse |-> [idx |-> cmd.idx, key |-> cmd.key, value |-> Nil, ok |-> FALSE],
                   mleaderHint |-> leader[i],
                   msource |-> i,
                   mdest |-> c
                 ] IN
              /\ Net' = AddMsg(RemMsg(Net, m), resp)
              /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                              nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain,
                              Timeout, leaderOf, reqIdx >>
       ELSE IF CPP(m) \/ CGP(m) THEN
         LET c == m.mdest IN
         /\ leaderOf' = [leaderOf EXCEPT ![c] = m.mleaderHint]
         /\ reqIdx' = [reqIdx EXCEPT ![c] = IF m.msuccess /\ m.mresponse.idx = reqIdx[c] + 1 THEN reqIdx[c] + 1 ELSE reqIdx[c]]
         /\ Net' = RemMsg(Net, m)
         /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                         nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout >>
       ELSE FALSE

AdvanceCommitIndex(i) ==
  /\ i \in Server
  /\ state[i] = "leader"
  /\ LET candidate == FindMaxAgreeIndex(log[i], i, matchIndex[i]) IN
     LET nci == IF candidate > 0 /\ log[i][candidate].term = currentTerm[i]
                THEN Max2(commitIndex[i], candidate) ELSE commitIndex[i] IN
     /\ commitIndex' = [commitIndex EXCEPT ![i] = nci]
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, appliedIndex,
                 nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout, Net, leaderOf, reqIdx >>

ApplyEntries(i) ==
  /\ i \in Server
  /\ appliedIndex[i] < commitIndex[i]
  /\ LET k == appliedIndex[i] + 1 IN
     LET e == log[i][k] IN
     LET cmd == e.cmd IN
     LET isPut == cmd.type = "put" IN
     LET sm1 == IF isPut THEN [sm[i] EXCEPT ![cmd.key] = cmd.value] ELSE sm[i] IN
     LET dom1 == IF isPut THEN smDomain[i] \cup {cmd.key} ELSE smDomain[i] IN
     /\ sm' = [sm EXCEPT ![i] = sm1]
     /\ smDomain' = [smDomain EXCEPT ![i] = dom1]
     /\ appliedIndex' = [appliedIndex EXCEPT ![i] = k]
     /\ IF state[i] = "leader" THEN
          LET respType == IF cmd.type = "put" THEN "cpp" ELSE "cgp" IN
          LET ok == (cmd.key \in dom1) IN
          LET val == IF ok THEN sm1[cmd.key] ELSE Nil IN
          LET resp == [
               mtype |-> respType,
               msuccess |-> TRUE,
               mresponse |-> [idx |-> cmd.idx, key |-> cmd.key, value |-> val, ok |-> ok],
               mleaderHint |-> i,
               msource |-> i,
               mdest |-> e.client
             ] IN
          /\ Net' = AddMsg(Net, resp)
          /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex,
                         nextIndex, matchIndex, votesResponded, votesGranted, Timeout, leaderOf, reqIdx >>
        ELSE
          /\ Net' = Net
          /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex,
                         nextIndex, matchIndex, votesResponded, votesGranted, Timeout, leaderOf, reqIdx >>

ClientSend(c) ==
  /\ c \in Client
  /\ LET idx == reqIdx[c] + 1 IN
     LET k \in Key IN
     LET v \in Value IN
     LET choosePut \in BOOLEAN IN
     LET srv == IF leaderOf[c] \in Server THEN leaderOf[c] ELSE CHOOSE s \in Server: TRUE IN
     LET msg == IF choosePut
                THEN [mtype |-> "cpq",
                      mcmd |-> ReqPut(c, idx, k, v),
                      msource |-> c, mdest |-> srv]
                ELSE [mtype |-> "cgq",
                      mcmd |-> ReqGet(c, idx, k),
                      msource |-> c, mdest |-> srv]
     IN Net' = AddMsg(Net, msg)
  /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                 nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout,
                 leaderOf, reqIdx >>

Drop ==
  \E m \in DOMAIN Net :
    /\ Net[m] > 0
    /\ Net' = RemMsg(Net, m)
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout,
                   leaderOf, reqIdx >>

Next ==
  \/ \E i \in Server: TimerExpire(i)
  \/ \E i \in Server: CandidateStart(i)
  \/ \E i \in Server: \E j \in Server: SendRequestVote(i,j)
  \/ \E i \in Server: \E j \in Server: SendAppendEntries(i,j)
  \/ Deliver
  \/ \E i \in Server: AdvanceCommitIndex(i)
  \/ \E i \in Server: ApplyEntries(i)
  \/ \E c \in Client: ClientSend(c)
  \/ Drop

Spec ==
  Init /\ [][Next]_<< state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
               nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout, Net, leaderOf, reqIdx >>
  /\ WF_<< state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
            nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout, Net, leaderOf, reqIdx >>(Deliver)
  /\ WF_<< state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
            nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout, Net, leaderOf, reqIdx >>(\E i \in Server: TimerExpire(i))
  /\ WF_<< state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
            nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout, Net, leaderOf, reqIdx >>(\E i \in Server: ApplyEntries(i))
  /\ WF_<< state, currentTerm, votedFor, leader, log, commitIndex, appliedIndex,
            nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Timeout, Net, leaderOf, reqIdx >>(\E c \in Client: ClientSend(c))

====