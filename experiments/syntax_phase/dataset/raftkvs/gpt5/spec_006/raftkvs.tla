---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NumServers,
    NumClients,
    Keys,
    Values,
    DefaultValue

MType == {"rvq","rvp","apq","app","cpq","cgq","cpp","cgp"}
StateType == {"follower","candidate","leader"}
CmdType == {"put","get"}

Server == 1..NumServers
Client == 1..NumClients
Node == Server \cup Client

Nil == 0

KeyAny == CHOOSE k \in Keys : TRUE
ValAny == CHOOSE v \in Values : TRUE

Cmd == [type: CmdType, key: Keys, value: Values \cup {Nil}, idx: NAT]
Entry == [term: NAT, cmd: Cmd, client: Client]

Msg ==
    [ mtype: MType,
      mterm: NAT,
      mlastLogTerm: NAT,
      mlastLogIndex: NAT,
      mvoteGranted: BOOLEAN,
      mprevLogIndex: NAT,
      mprevLogTerm: NAT,
      mentries: Seq(Entry),
      mcommitIndex: NAT,
      msuccess: BOOLEAN,
      mmatchIndex: NAT,
      msource: Node,
      mdest: Node,
      mcmd: Cmd,
      mresponse: [idx: NAT, key: Keys, value: Values \cup {Nil}, ok: BOOLEAN],
      mleaderHint: Server \cup {Nil}
    ]

IsQuorum(S) == 2 * Cardinality(S) > NumServers

LastTerm(s) == IF Len(s) = 0 THEN 0 ELSE s[Len(s)].term

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(x, y) == IF x <= y THEN x ELSE y

RECURSIVE ApplyLogRange(_,_,_,_,_)
ApplyLogRange(theLog, start, end, sm0, dom0) ==
    IF start > end THEN <<sm0, dom0>>
    ELSE
        LET e == theLog[start] IN
        LET upd == IF e.cmd.type = "put"
                   THEN << [sm0 EXCEPT ![e.cmd.key] = e.cmd.value], dom0 \cup {e.cmd.key} >>
                   ELSE << sm0, dom0 >>
        IN ApplyLogRange(theLog, start+1, end, upd[1], upd[2])

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
    smDomain,
    leaderTimeout,
    Net,
    leaderHint,
    creqIdx

vars == << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, Net, leaderHint, creqIdx >>

Init ==
    /\ state \in [Server -> StateType]
    /\ \A i \in Server : state[i] = "follower"
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor \in [Server -> (Server \cup {Nil})]
    /\ \A i \in Server : votedFor[i] = Nil
    /\ leader \in [Server -> (Server \cup {Nil})]
    /\ \A i \in Server : leader[i] = Nil
    /\ log \in [Server -> Seq(Entry)]
    /\ \A i \in Server : log[i] = <<>>
    /\ commitIndex = [i \in Server |-> 0]
    /\ lastApplied = [i \in Server |-> 0]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ votesResponded \in [Server -> SUBSET Server]
    /\ \A i \in Server : votesResponded[i] = {}
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ \A i \in Server : votesGranted[i] = {}
    /\ sm \in [Server -> [Keys -> Values]]
    /\ \A i \in Server : sm[i] = [k \in Keys |-> DefaultValue]
    /\ smDomain \in [Server -> SUBSET Keys]
    /\ \A i \in Server : smDomain[i] = {}
    /\ leaderTimeout \in [Server -> BOOLEAN]
    /\ \A i \in Server : leaderTimeout[i] = FALSE
    /\ Net \subseteq Msg
    /\ Net = {}
    /\ leaderHint \in [Client -> (Server \cup {Nil})]
    /\ \A c \in Client : leaderHint[c] = Nil
    /\ creqIdx = [c \in Client |-> 0]

LeaderTimeoutAction(i) ==
    /\ i \in Server
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, Net, leaderHint, creqIdx >>

StartElection(i) ==
    /\ i \in Server
    /\ leaderTimeout[i] = TRUE
    /\ state[i] \in {"follower","candidate"}
    /\ state' = [state EXCEPT ![i] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, sm, smDomain, Net, leaderHint, creqIdx >>

SendRequestVote(i,j) ==
    /\ i \in Server /\ j \in Server /\ i # j
    /\ state[i] = "candidate"
    /\ LET m == [ mtype |-> "rvq",
                  mterm |-> currentTerm[i],
                  mlastLogTerm |-> LastTerm(log[i]),
                  mlastLogIndex |-> Len(log[i]),
                  mvoteGranted |-> FALSE,
                  mprevLogIndex |-> 0,
                  mprevLogTerm |-> 0,
                  mentries |-> <<>>,
                  mcommitIndex |-> 0,
                  msuccess |-> FALSE,
                  mmatchIndex |-> 0,
                  msource |-> i,
                  mdest |-> j,
                  mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
                  mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
                  mleaderHint |-> Nil
                ] IN
       Net' = Net \cup {m}
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint, creqIdx >>

RcvRVQ(i,m) ==
    /\ m \in Net
    /\ m.mtype = "rvq"
    /\ i \in Server
    /\ m.mdest = i
    /\ LET ct == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET st == IF m.mterm > currentTerm[i] THEN "follower" ELSE state[i] IN
       LET vf == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i] IN
       LET ld == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i] IN
       LET vresp == IF m.mterm > currentTerm[i] THEN {} ELSE votesResponded[i] IN
       LET vgrantSet == IF m.mterm > currentTerm[i] THEN {} ELSE votesGranted[i] IN
       LET logOK == (m.mlastLogTerm > LastTerm(log[i]))
                    \/ (m.mlastLogTerm = LastTerm(log[i]) /\ m.mlastLogIndex >= Len(log[i])) IN
       LET grant == (m.mterm = ct) /\ logOK /\ (vf = Nil \/ vf = m.msource) IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = ct]
       /\ state' = [state EXCEPT ![i] = st]
       /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m.msource ELSE vf]
       /\ leader' = [leader EXCEPT ![i] = ld]
       /\ votesResponded' = [votesResponded EXCEPT ![i] = vresp]
       /\ votesGranted' = [votesGranted EXCEPT ![i] = vgrantSet]
       /\ leaderTimeout' = leaderTimeout
       /\ Net' =
            (Net \ {m})
            \cup { [ mtype |-> "rvp",
                     mterm |-> ct,
                     mlastLogTerm |-> 0,
                     mlastLogIndex |-> 0,
                     mvoteGranted |-> grant,
                     mprevLogIndex |-> 0,
                     mprevLogTerm |-> 0,
                     mentries |-> <<>>,
                     mcommitIndex |-> 0,
                     msuccess |-> FALSE,
                     mmatchIndex |-> 0,
                     msource |-> i,
                     mdest |-> m.msource,
                     mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
                     mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
                     mleaderHint |-> Nil
                   ] }
       /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, sm, smDomain, leaderHint, creqIdx >>

RcvRVP(i,m) ==
    /\ m \in Net
    /\ m.mtype = "rvp"
    /\ i \in Server
    /\ m.mdest = i
    /\ LET ct == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET becameFollower == m.mterm > currentTerm[i] IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = ct]
       /\ state' = [state EXCEPT ![i] = IF becameFollower THEN "follower" ELSE state[i]]
       /\ votedFor' = [votedFor EXCEPT ![i] = IF becameFollower THEN Nil ELSE votedFor[i]]
       /\ leader' = [leader EXCEPT ![i] = IF becameFollower THEN Nil ELSE leader[i]]
       /\ IF (m.mterm = ct) /\ (state[i] = "candidate")
          THEN /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {m.msource}]
               /\ votesGranted' = [votesGranted EXCEPT ![i] = IF m.mvoteGranted THEN votesGranted[i] \cup {m.msource} ELSE votesGranted[i]]
               /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = IF m.mvoteGranted THEN FALSE ELSE leaderTimeout[i]]
          ELSE /\ votesResponded' = votesResponded
               /\ votesGranted' = votesGranted
               /\ leaderTimeout' = leaderTimeout
       /\ Net' = Net \ {m}
       /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, sm, smDomain, leaderHint, creqIdx >>

BecomeLeader(i) ==
    /\ i \in Server
    /\ state[i] = "candidate"
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = "leader"]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, votesResponded, votesGranted, sm, smDomain, Net, leaderHint, creqIdx >>

SendAppendEntries(i,j) ==
    /\ i \in Server /\ j \in Server /\ i # j
    /\ state[i] = "leader"
    /\ LET pIdx == nextIndex[i][j] - 1 IN
       LET pTerm == IF pIdx > 0 /\ pIdx <= Len(log[i]) THEN log[i][pIdx].term ELSE 0 IN
       LET ents == SubSeq(log[i], nextIndex[i][j], Len(log[i])) IN
       /\ Net' =
            Net \cup { [ mtype |-> "apq",
                         mterm |-> currentTerm[i],
                         mlastLogTerm |-> 0,
                         mlastLogIndex |-> 0,
                         mvoteGranted |-> FALSE,
                         mprevLogIndex |-> pIdx,
                         mprevLogTerm |-> pTerm,
                         mentries |-> ents,
                         mcommitIndex |-> commitIndex[i],
                         msuccess |-> FALSE,
                         mmatchIndex |-> 0,
                         msource |-> i,
                         mdest |-> j,
                         mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
                         mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
                         mleaderHint |-> i
                       ] }
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint, creqIdx >>

RcvAPQ(i,m) ==
    /\ m \in Net
    /\ m.mtype = "apq"
    /\ i \in Server
    /\ m.mdest = i
    /\ LET ct == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET becameFollower == m.mterm > currentTerm[i] IN
       LET st == IF becameFollower THEN "follower" ELSE state[i] IN
       LET vf == IF becameFollower THEN Nil ELSE votedFor[i] IN
       LET ld0 == IF m.mterm = ct THEN m.msource ELSE IF becameFollower THEN Nil ELSE leader[i] IN
       LET logOK ==
            (m.mprevLogIndex = 0)
            \/ (m.mprevLogIndex > 0
                /\ m.mprevLogIndex <= Len(log[i])
                /\ log[i][m.mprevLogIndex].term = m.mprevLogTerm) IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = ct]
       /\ state' = [state EXCEPT ![i] = IF (m.mterm = ct) /\ (st = "candidate") THEN "follower" ELSE st]
       /\ votedFor' = [votedFor EXCEPT ![i] = vf]
       /\ leader' = [leader EXCEPT ![i] = IF m.mterm = ct THEN m.msource ELSE ld0]
       /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = IF m.mterm = ct THEN FALSE ELSE leaderTimeout[i]]
       /\ IF (m.mterm < ct) \/ ((m.mterm = ct) /\ (state[i] = "follower") /\ ~logOK)
          THEN /\ Net' =
                    (Net \ {m})
                    \cup { [ mtype |-> "app",
                             mterm |-> ct,
                             mlastLogTerm |-> 0,
                             mlastLogIndex |-> 0,
                             mvoteGranted |-> FALSE,
                             mprevLogIndex |-> 0,
                             mprevLogTerm |-> 0,
                             mentries |-> <<>>,
                             mcommitIndex |-> 0,
                             msuccess |-> FALSE,
                             mmatchIndex |-> 0,
                             msource |-> i,
                             mdest |-> m.msource,
                             mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
                             mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
                             mleaderHint |-> ld0
                           ] }
               /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderHint, creqIdx >>
          ELSE
            /\ LET newLog == SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries IN
               LET oldCI == commitIndex[i] IN
               LET newCI == Max({oldCI, Min(m.mcommitIndex, Len(newLog))}) IN
               LET apRes == ApplyLogRange(newLog, oldCI+1, newCI, sm[i], smDomain[i]) IN
               /\ log' = [log EXCEPT ![i] = newLog]
               /\ commitIndex' = [commitIndex EXCEPT ![i] = newCI]
               /\ lastApplied' = lastApplied
               /\ sm' = [sm EXCEPT ![i] = apRes[1]]
               /\ smDomain' = [smDomain EXCEPT ![i] = apRes[2]]
               /\ Net' =
                    (Net \ {m})
                    \cup { [ mtype |-> "app",
                             mterm |-> ct,
                             mlastLogTerm |-> 0,
                             mlastLogIndex |-> 0,
                             mvoteGranted |-> FALSE,
                             mprevLogIndex |-> 0,
                             mprevLogTerm |-> 0,
                             mentries |-> <<>>,
                             mcommitIndex |-> 0,
                             msuccess |-> TRUE,
                             mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                             msource |-> i,
                             mdest |-> m.msource,
                             mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
                             mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
                             mleaderHint |-> ld0
                           ] }
               /\ UNCHANGED << nextIndex, matchIndex, votesResponded, votesGranted, leaderHint, creqIdx >>

RcvAPP(i,m) ==
    /\ m \in Net
    /\ m.mtype = "app"
    /\ i \in Server
    /\ m.mdest = i
    /\ LET ct == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET becameFollower == m.mterm > currentTerm[i] IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = ct]
       /\ state' = [state EXCEPT ![i] = IF becameFollower THEN "follower" ELSE state[i]]
       /\ votedFor' = [votedFor EXCEPT ![i] = IF becameFollower THEN Nil ELSE votedFor[i]]
       /\ leader' = [leader EXCEPT ![i] = IF becameFollower THEN Nil ELSE leader[i]]
       /\ IF (m.mterm = ct) /\ (state[i] = "leader")
          THEN
            /\ leaderTimeout' = [leaderTimeout EXCEPT ![i] = FALSE]
            /\ nextIndex' =
                 [nextIndex EXCEPT ![i] =
                    [nextIndex[i] EXCEPT
                       ![m.msource] = IF m.msuccess
                                      THEN m.mmatchIndex + 1
                                      ELSE Max({ nextIndex[i][m.msource] - 1, 1 })]]
            /\ matchIndex' =
                 [matchIndex EXCEPT ![i] =
                    [matchIndex[i] EXCEPT
                       ![m.msource] = IF m.msuccess
                                      THEN m.mmatchIndex
                                      ELSE matchIndex[i][m.msource]]]
          ELSE
            /\ leaderTimeout' = leaderTimeout
            /\ nextIndex' = nextIndex
            /\ matchIndex' = matchIndex
       /\ Net' = Net \ {m}
       /\ UNCHANGED << log, commitIndex, lastApplied, votesResponded, votesGranted, sm, smDomain, leaderHint, creqIdx >>

HandleClientAtServer(i,m) ==
    /\ m \in Net
    /\ i \in Server
    /\ m.mdest = i
    /\ m.mtype \in {"cpq","cgq"}
    /\ IF state[i] = "leader"
       THEN
         /\ log' = [log EXCEPT ![i] = Append(log[i], [term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource])]
         /\ Net' = Net \ {m}
         /\ UNCHANGED << state, currentTerm, votedFor, leader, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint, creqIdx >>
       ELSE
         /\ LET rtype == IF m.mtype = "cpq" THEN "cpp" ELSE "cgp" IN
            LET resp == [ mtype |-> rtype,
                          mterm |-> currentTerm[i],
                          mlastLogTerm |-> 0,
                          mlastLogIndex |-> 0,
                          mvoteGranted |-> FALSE,
                          mprevLogIndex |-> 0,
                          mprevLogTerm |-> 0,
                          mentries |-> <<>>,
                          mcommitIndex |-> 0,
                          msuccess |-> FALSE,
                          mmatchIndex |-> 0,
                          msource |-> i,
                          mdest |-> m.msource,
                          mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
                          mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE],
                          mleaderHint |-> leader[i]
                        ] IN
            /\ Net' = (Net \ {m}) \cup {resp}
            /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint, creqIdx >>

AdvanceCommitIndex(i) ==
    /\ i \in Server
    /\ state[i] = "leader"
    /\ LET AgreeSet == { k \in 0..Len(log[i]) :
                           IsQuorum({i} \cup { j \in Server : matchIndex[i][j] >= k }) } IN
       LET newK == IF AgreeSet = {} THEN commitIndex[i] ELSE Max(AgreeSet) IN
       /\ commitIndex' =
            [commitIndex EXCEPT ![i] =
               IF newK > commitIndex[i] /\ newK > 0 /\ log[i][newK].term = currentTerm[i]
               THEN newK ELSE commitIndex[i]]
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, Net, leaderHint, creqIdx >>

ApplyOneCommitted(i) ==
    /\ i \in Server
    /\ state[i] = "leader"
    /\ lastApplied[i] < commitIndex[i]
    /\ LET k == lastApplied[i] + 1 IN
       LET e == log[i][k] IN
       LET newSM == IF e.cmd.type = "put"
                    THEN [sm[i] EXCEPT ![e.cmd.key] = e.cmd.value]
                    ELSE sm[i] IN
       LET newDom == IF e.cmd.type = "put"
                     THEN smDomain[i] \cup {e.cmd.key}
                     ELSE smDomain[i] IN
       /\ sm' = [sm EXCEPT ![i] = newSM]
       /\ smDomain' = [smDomain EXCEPT ![i] = newDom]
       /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
       /\ Net' = Net \cup {
             [ mtype |-> IF e.cmd.type = "put" THEN "cpp" ELSE "cgp",
               mterm |-> currentTerm[i],
               mlastLogTerm |-> 0,
               mlastLogIndex |-> 0,
               mvoteGranted |-> FALSE,
               mprevLogIndex |-> 0,
               mprevLogTerm |-> 0,
               mentries |-> <<>>,
               mcommitIndex |-> 0,
               msuccess |-> TRUE,
               mmatchIndex |-> 0,
               msource |-> i,
               mdest |-> e.client,
               mcmd |-> [type |-> "get", key |-> KeyAny, value |-> ValAny, idx |-> 0],
               mresponse |-> [idx |-> e.cmd.idx,
                              key |-> e.cmd.key,
                              value |-> IF e.cmd.type = "get" /\ e.cmd.key \in newDom THEN newSM[e.cmd.key] ELSE IF e.cmd.type = "put" THEN e.cmd.value ELSE Nil,
                              ok |-> IF e.cmd.type = "get" THEN e.cmd.key \in newDom ELSE TRUE],
               mleaderHint |-> i
             ] }
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, leaderTimeout, leaderHint, creqIdx >>

ClientSendPut(c) ==
    /\ c \in Client
    /\ LET srv == IF leaderHint[c] \in Server THEN leaderHint[c] ELSE CHOOSE s \in Server : TRUE IN
       /\ creqIdx' = [creqIdx EXCEPT ![c] = creqIdx[c] + 1]
       /\ Net' = Net \cup {
            [ mtype |-> "cpq",
              mterm |-> 0,
              mlastLogTerm |-> 0,
              mlastLogIndex |-> 0,
              mvoteGranted |-> FALSE,
              mprevLogIndex |-> 0,
              mprevLogTerm |-> 0,
              mentries |-> <<>>,
              mcommitIndex |-> 0,
              msuccess |-> FALSE,
              mmatchIndex |-> 0,
              msource |-> c,
              mdest |-> srv,
              mcmd |-> [type |-> "put", key |-> KeyAny, value |-> ValAny, idx |-> creqIdx'[c]],
              mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
              mleaderHint |-> Nil
            ] }
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint >>

ClientSendGet(c) ==
    /\ c \in Client
    /\ LET srv == IF leaderHint[c] \in Server THEN leaderHint[c] ELSE CHOOSE s \in Server : TRUE IN
       /\ creqIdx' = [creqIdx EXCEPT ![c] = creqIdx[c] + 1]
       /\ Net' = Net \cup {
            [ mtype |-> "cgq",
              mterm |-> 0,
              mlastLogTerm |-> 0,
              mlastLogIndex |-> 0,
              mvoteGranted |-> FALSE,
              mprevLogIndex |-> 0,
              mprevLogTerm |-> 0,
              mentries |-> <<>>,
              mcommitIndex |-> 0,
              msuccess |-> FALSE,
              mmatchIndex |-> 0,
              msource |-> c,
              mdest |-> srv,
              mcmd |-> [type |-> "get", key |-> KeyAny, value |-> Nil, idx |-> creqIdx'[c]],
              mresponse |-> [idx |-> 0, key |-> KeyAny, value |-> Nil, ok |-> FALSE],
              mleaderHint |-> Nil
            ] }
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint >>

ClientRcv(c,m) ==
    /\ c \in Client
    /\ m \in Net
    /\ m.mdest = c
    /\ m.mtype \in {"cpp","cgp"}
    /\ leaderHint' = [leaderHint EXCEPT ![c] = IF m.mleaderHint \in Server THEN m.mleaderHint ELSE leaderHint[c]]
    /\ Net' = Net \ {m}
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, creqIdx >>

Drop(m) ==
    /\ m \in Net
    /\ Net' = Net \ {m}
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, leaderHint, creqIdx >>

Receive ==
    \E i \in Server, m \in Net :
        RcvRVQ(i,m) \/ RcvRVP(i,m) \/ RcvAPQ(i,m) \/ RcvAPP(i,m) \/ HandleClientAtServer(i,m)
    \/ \E c \in Client, m2 \in Net : ClientRcv(c,m2)

StartElectionAny == \E i \in Server : StartElection(i)
LeaderTimeoutAny == \E i \in Server : LeaderTimeoutAction(i)
SendRVAny == \E i \in Server, j \in Server : SendRequestVote(i,j)
SendAEAny == \E i \in Server, j \in Server : SendAppendEntries(i,j)
BecomeLeaderAny == \E i \in Server : BecomeLeader(i)
AdvanceCommitAny == \E i \in Server : AdvanceCommitIndex(i)
ApplyCommittedAny == \E i \in Server : ApplyOneCommitted(i)
ClientSendAny == \E c \in Client : ClientSendPut(c) \/ ClientSendGet(c)
DropAny == \E m \in Net : Drop(m)

Next ==
    LeaderTimeoutAny
    \/ StartElectionAny
    \/ SendRVAny
    \/ SendAEAny
    \/ Receive
    \/ BecomeLeaderAny
    \/ AdvanceCommitAny
    \/ ApplyCommittedAny
    \/ ClientSendAny
    \/ DropAny

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Receive)
    /\ WF_vars(BecomeLeaderAny)
    /\ WF_vars(ApplyCommittedAny)
    /\ WF_vars(SendAEAny)

====