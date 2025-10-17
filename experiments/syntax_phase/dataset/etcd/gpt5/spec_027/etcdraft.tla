---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
  NODES,
  None,
  ELECTION_TIMEOUT,
  HEARTBEAT_TIMEOUT

ASSUME None \notin NODES
ASSUME ELECTION_TIMEOUT \in Nat \ {0}
ASSUME HEARTBEAT_TIMEOUT \in Nat \ {0}

StateType == {"StateFollower","StateCandidate","StateLeader","StatePreCandidate"}
MsgType ==
  {"MsgHup","MsgPreVote","MsgPreVoteResp","MsgVote","MsgVoteResp",
   "MsgApp","MsgAppResp","MsgHeartbeat","MsgHeartbeatResp","MsgProp"}

Entry == [term: Nat]

Message ==
  [ type: MsgType,
    from: NODES \cup {None},
    to: NODES \cup {None},
    term: Nat,
    prevIndex: Nat,
    prevTerm: Nat,
    entries: Seq(Entry),
    commit: Nat,
    reject: BOOLEAN,
    lastIndex: Nat,
    lastTerm: Nat
  ]

VARIABLES
  term,              \* [n \in NODES -> Nat]
  vote,              \* [n \in NODES -> NODES \cup {None}]
  state,             \* [n \in NODES -> StateType]
  log,               \* [n \in NODES -> Seq(Entry)]
  commit,            \* [n \in NODES -> Nat]
  lead,              \* [n \in NODES -> NODES \cup {None}]
  electionElapsed,   \* [n \in NODES -> Nat]
  rTimeout,          \* [n \in NODES -> Nat]
  msgs,              \* SET of Message records
  prevoteTerm,       \* [n \in NODES -> Nat]
  prevotesYes,       \* [n \in NODES -> SUBSET NODES]
  votesYes,          \* [n \in NODES -> SUBSET NODES]
  votesNo,           \* [n \in NODES -> SUBSET NODES]
  match,             \* [leader \in NODES -> [peer \in NODES -> Nat]]
  next               \* [leader \in NODES -> [peer \in NODES -> Nat]]

LenLog(n) == Len(log[n])
LastTermOf(n) == IF LenLog(n) = 0 THEN 0 ELSE log[n][LenLog(n)].term
TermAt(l, i) == IF i = 0 THEN 0 ELSE IF i <= Len(l) THEN l[i].term ELSE 0
Prefix(l, i) == IF i = 0 THEN << >> ELSE IF i >= Len(l) THEN l ELSE SubSeq(l, 1, i)
FromIndex(l, i) == IF i > Len(l) THEN << >> ELSE SubSeq(l, i, Len(l))
MapTerm(s, t) == [ i \in 1..Len(s) |-> [term |-> t] ]
Majority(S) == Cardinality(S) > Cardinality(NODES) / 2
Max(S) == CHOOSE m \in S : \A x \in S : x <= m
MinNat(a, b) == IF a <= b THEN a ELSE b

HupMsg(n) ==
  [ type |-> "MsgHup",
    from |-> n,
    to |-> n,
    term |-> term[n],
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> commit[n],
    reject |-> FALSE,
    lastIndex |-> LenLog(n),
    lastTerm |-> LastTermOf(n)
  ]

PreVoteMsg(n, q) ==
  [ type |-> "MsgPreVote",
    from |-> n,
    to |-> q,
    term |-> term[n] + 1,
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> commit[n],
    reject |-> FALSE,
    lastIndex |-> LenLog(n),
    lastTerm |-> LastTermOf(n)
  ]

PreVoteRespMsg(q, n, t, grant) ==
  [ type |-> "MsgPreVoteResp",
    from |-> q,
    to |-> n,
    term |-> t,
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> 0,
    reject |-> ~grant,
    lastIndex |-> 0,
    lastTerm |-> 0
  ]

VoteMsg(n, q) ==
  [ type |-> "MsgVote",
    from |-> n,
    to |-> q,
    term |-> term[n],
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> 0,
    reject |-> FALSE,
    lastIndex |-> LenLog(n),
    lastTerm |-> LastTermOf(n)
  ]

VoteRespMsg(q, n, t, grant) ==
  [ type |-> "MsgVoteResp",
    from |-> q,
    to |-> n,
    term |-> t,
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> 0,
    reject |-> ~grant,
    lastIndex |-> 0,
    lastTerm |-> 0
  ]

HeartbeatMsg(n, q) ==
  [ type |-> "MsgHeartbeat",
    from |-> n,
    to |-> q,
    term |-> term[n],
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> commit[n],
    reject |-> FALSE,
    lastIndex |-> 0,
    lastTerm |-> 0
  ]

HeartbeatRespMsg(q, n, t) ==
  [ type |-> "MsgHeartbeatResp",
    from |-> q,
    to |-> n,
    term |-> t,
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> 0,
    reject |-> FALSE,
    lastIndex |-> 0,
    lastTerm |-> 0
  ]

AppMsg(n, q) ==
  LET pi == next[n][q] - 1 IN
  [ type |-> "MsgApp",
    from |-> n,
    to |-> q,
    term |-> term[n],
    prevIndex |-> pi,
    prevTerm |-> TermAt(log[n], pi),
    entries |-> FromIndex(log[n], next[n][q]),
    commit |-> commit[n],
    reject |-> FALSE,
    lastIndex |-> 0,
    lastTerm |-> 0
  ]

AppRespMsg(q, n, t, ok, idx) ==
  [ type |-> "MsgAppResp",
    from |-> q,
    to |-> n,
    term |-> t,
    prevIndex |-> 0,
    prevTerm |-> 0,
    entries |-> << >>,
    commit |-> 0,
    reject |-> ~ok,
    lastIndex |-> 0,
    lastTerm |-> 0
  ] @@ [index |-> idx]

UpToDate(cTerm, cIdx, l) ==
  \/ cTerm > (IF Len(l)=0 THEN 0 ELSE l[Len(l)].term)
  \/ /\ cTerm = (IF Len(l)=0 THEN 0 ELSE l[Len(l)].term)
     /\ cIdx >= Len(l)

CanGrantVote(q, mfrom, mterm) ==
  \/ vote[q] = None
  \/ vote[q] = mfrom

Commitable(p, i) ==
  /\ i <= LenLog(p)
  /\ log[p][i].term = term[p]
  /\ Cardinality({ r \in NODES : IF r = p THEN LenLog(p) >= i ELSE match[p][r] >= i }) > Cardinality(NODES) / 2

Init ==
  /\ term = [n \in NODES |-> 0]
  /\ vote = [n \in NODES |-> None]
  /\ state = [n \in NODES |-> "StateFollower"]
  /\ log = [n \in NODES |-> << >>]
  /\ commit = [n \in NODES |-> 0]
  /\ lead = [n \in NODES |-> None]
  /\ electionElapsed = [n \in NODES |-> 0]
  /\ rTimeout \in [NODES -> ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT - 1)]
  /\ msgs = {}
  /\ prevoteTerm = [n \in NODES |-> 0]
  /\ prevotesYes = [n \in NODES |-> {}]
  /\ votesYes = [n \in NODES |-> {}]
  /\ votesNo = [n \in NODES |-> {}]
  /\ match = [n \in NODES |-> [r \in NODES |-> 0]]
  /\ next = [n \in NODES |-> [r \in NODES |-> 1]]

Tick(n) ==
  /\ n \in NODES
  /\ electionElapsed' = [electionElapsed EXCEPT ![n] = @ + 1]
  /\ UNCHANGED << term, vote, state, log, commit, lead, rTimeout, msgs, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

EnqueueHup(n) ==
  /\ n \in NODES
  /\ electionElapsed[n] >= rTimeout[n]
  /\ state[n] # "StateLeader"
  /\ msgs' = msgs \cup { HupMsg(n) }
  /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << term, vote, state, log, commit, lead, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverHup(m) ==
  /\ m \in msgs
  /\ m.type = "MsgHup"
  /\ LET n == m.to IN
     /\ IF state[n] = "StateLeader" THEN
          /\ msgs' = msgs \ {m}
          /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>
        ELSE
          /\ state' = [state EXCEPT ![n] = "StatePreCandidate"]
          /\ prevoteTerm' = [prevoteTerm EXCEPT ![n] = term[n] + 1]
          /\ prevotesYes' = [prevotesYes EXCEPT ![n] = {n}]
          /\ msgs' = (msgs \ {m}) \cup { PreVoteMsg(n, q) : q \in NODES \ {n} }
          /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
          /\ UNCHANGED << term, vote, log, commit, lead, rTimeout, votesYes, votesNo, match, next >>

DeliverPreVote(m) ==
  /\ m \in msgs
  /\ m.type = "MsgPreVote"
  /\ LET q == m.to IN
     /\ LET grant == UpToDate(m.lastTerm, m.lastIndex, log[q]) IN
        /\ msgs' = (msgs \ {m}) \cup { PreVoteRespMsg(q, m.from, m.term, grant) }
        /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverPreVoteResp(m) ==
  /\ m \in msgs
  /\ m.type = "MsgPreVoteResp"
  /\ LET p == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ IF /\ state[p] = "StatePreCandidate"
              /\ prevoteTerm[p] = m.term
           THEN
             /\ LET yesSet == IF m.reject THEN prevotesYes[p] ELSE prevotesYes[p] \cup {m.from} IN
                /\ IF Majority(yesSet) THEN
                     /\ state' = [state EXCEPT ![p] = "StateCandidate"]
                     /\ term' = [term EXCEPT ![p] = @ + 1]
                     /\ vote' = [vote EXCEPT ![p] = p]
                     /\ votesYes' = [votesYes EXCEPT ![p] = {p}]
                     /\ votesNo' = [votesNo EXCEPT ![p] = {}]
                     /\ prevoteTerm' = [prevoteTerm EXCEPT ![p] = 0]
                     /\ prevotesYes' = [prevotesYes EXCEPT ![p] = {}]
                     /\ msgs' = msgs1 \cup { VoteMsg(p, q) : q \in NODES \ {p} }
                     /\ electionElapsed' = [electionElapsed EXCEPT ![p] = 0]
                     /\ UNCHANGED << log, commit, lead, rTimeout, match, next >>
                   ELSE
                     /\ prevotesYes' = [prevotesYes EXCEPT ![p] = yesSet]
                     /\ msgs' = msgs1
                     /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, votesYes, votesNo, match, next >>
           ELSE
             /\ msgs' = msgs1
             /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverVote(m) ==
  /\ m \in msgs
  /\ m.type = "MsgVote"
  /\ LET q == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ LET termQ == IF m.term > term[q] THEN m.term ELSE term[q] IN
           /\ term' = [term EXCEPT ![q] = termQ]
           /\ state' = [state EXCEPT ![q] = "StateFollower"]
           /\ lead' = [lead EXCEPT ![q] = None]
           /\ LET can == /\ m.term = term'[q]
                         /\ CanGrantVote(q, m.from, m.term)
                         /\ UpToDate(m.lastTerm, m.lastIndex, log[q]) IN
              /\ IF can THEN
                   /\ vote' = [vote EXCEPT ![q] = m.from]
                   /\ msgs' = msgs1 \cup { VoteRespMsg(q, m.from, term'[q], TRUE) }
                   /\ electionElapsed' = [electionElapsed EXCEPT ![q] = 0]
                   /\ UNCHANGED << log, commit, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>
                 ELSE
                   /\ vote' = [vote EXCEPT ![q] = IF m.term = term'[q] /\ vote[q] = None THEN None ELSE vote[q]]
                   /\ msgs' = msgs1 \cup { VoteRespMsg(q, m.from, term'[q], FALSE) }
                   /\ UNCHANGED << log, commit, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverVoteResp(m) ==
  /\ m \in msgs
  /\ m.type = "MsgVoteResp"
  /\ LET p == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ IF m.term > term[p] THEN
             /\ term' = [term EXCEPT ![p] = m.term]
             /\ state' = [state EXCEPT ![p] = "StateFollower"]
             /\ vote' = [vote EXCEPT ![p] = None]
             /\ lead' = [lead EXCEPT ![p] = None]
             /\ msgs' = msgs1
             /\ UNCHANGED << log, commit, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>
           ELSE IF /\ state[p] = "StateCandidate" /\ m.term = term[p] THEN
             /\ LET vY == IF m.reject THEN votesYes[p] ELSE votesYes[p] \cup {m.from} IN
                /\ LET vN == IF m.reject THEN votesNo[p] \cup {m.from} ELSE votesNo[p] IN
                   /\ IF Majority(vY) THEN
                        /\ state' = [state EXCEPT ![p] = "StateLeader"]
                        /\ lead' = [lead EXCEPT ![p] = p]
                        /\ votesYes' = [votesYes EXCEPT ![p] = {}]
                        /\ votesNo' = [votesNo EXCEPT ![p] = {}]
                        /\ match' = [match EXCEPT ![p] = [r \in NODES |-> IF r = p THEN LenLog(p) ELSE 0]]
                        /\ next' = [next EXCEPT ![p] = [r \in NODES |-> LenLog(p) + 1]]
                        /\ log' = [log EXCEPT ![p] = Append(log[p], [term |-> term[p]])]
                        /\ commit' = commit
                        /\ term' = term
                        /\ vote' = vote
                        /\ msgs' = msgs1 \cup { AppMsg(p, q) : q \in NODES \ {p} }
                        /\ UNCHANGED << electionElapsed, rTimeout, prevoteTerm, prevotesYes >>
                      ELSE IF Majority(vN) THEN
                        /\ state' = [state EXCEPT ![p] = "StateFollower"]
                        /\ votesYes' = [votesYes EXCEPT ![p] = {}]
                        /\ votesNo' = [votesNo EXCEPT ![p] = {}]
                        /\ msgs' = msgs1
                        /\ term' = term
                        /\ vote' = vote
                        /\ lead' = [lead EXCEPT ![p] = None]
                        /\ UNCHANGED << log, commit, electionElapsed, rTimeout, prevoteTerm, prevotesYes, match, next >>
                      ELSE
                        /\ votesYes' = [votesYes EXCEPT ![p] = vY]
                        /\ votesNo' = [votesNo EXCEPT ![p] = vN]
                        /\ msgs' = msgs1
                        /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, match, next >>
           ELSE
             /\ msgs' = msgs1
             /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverHeartbeat(m) ==
  /\ m \in msgs
  /\ m.type = "MsgHeartbeat"
  /\ LET f == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ IF m.term > term[f] THEN
             /\ term' = [term EXCEPT ![f] = m.term]
             /\ state' = [state EXCEPT ![f] = "StateFollower"]
             /\ vote' = [vote EXCEPT ![f] = None]
             /\ lead' = [lead EXCEPT ![f] = m.from]
           ELSE
             /\ term' = term
             /\ state' = state
             /\ vote' = vote
             /\ lead' = [lead EXCEPT ![f] = m.from]
        /\ commit' = [commit EXCEPT ![f] = MinNat(m.commit, LenLog(f))]
        /\ electionElapsed' = [electionElapsed EXCEPT ![f] = 0]
        /\ msgs' = msgs1 \cup { HeartbeatRespMsg(f, m.from, term'[f]) }
        /\ UNCHANGED << log, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverHeartbeatResp(m) ==
  /\ m \in msgs
  /\ m.type = "MsgHeartbeatResp"
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverApp(m) ==
  /\ m \in msgs
  /\ m.type = "MsgApp"
  /\ LET f == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ LET term1 == IF m.term > term[f] THEN m.term ELSE term[f] IN
           LET state1 == IF m.term > term[f] THEN "StateFollower" ELSE state[f] IN
           LET vote1 == IF m.term > term[f] THEN None ELSE vote[f] IN
             /\ lead' = [lead EXCEPT ![f] = m.from]
             /\ electionElapsed' = [electionElapsed EXCEPT ![f] = 0]
             /\ IF /\ m.prevIndex <= LenLog(f)
                   /\ TermAt(log[f], m.prevIndex) = m.prevTerm
                THEN
                  /\ log' = [log EXCEPT ![f] = Prefix(log[f], m.prevIndex) \o m.entries]
                  /\ commit' = [commit EXCEPT ![f] = MinNat(m.commit, LenLog(f) + Len(m.entries))]
                  /\ msgs' = msgs1 \cup { AppRespMsg(f, m.from, term1, TRUE, m.prevIndex + Len(m.entries)) }
                ELSE
                  /\ log' = log
                  /\ commit' = commit
                  /\ msgs' = msgs1 \cup { AppRespMsg(f, m.from, term1, FALSE, m.prevIndex) }
             /\ term' = [term EXCEPT ![f] = term1]
             /\ state' = [state EXCEPT ![f] = state1]
             /\ vote' = [vote EXCEPT ![f] = vote1]
             /\ UNCHANGED << rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverAppResp(m) ==
  /\ m \in msgs
  /\ m.type = "MsgAppResp"
  /\ LET p == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ IF m.term > term[p] THEN
             /\ term' = [term EXCEPT ![p] = m.term]
             /\ state' = [state EXCEPT ![p] = "StateFollower"]
             /\ vote' = [vote EXCEPT ![p] = None]
             /\ lead' = [lead EXCEPT ![p] = None]
             /\ msgs' = msgs1
             /\ UNCHANGED << log, commit, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>
           ELSE
             /\ IF ~m.reject THEN
                  /\ match' = [match EXCEPT ![p] = [match[p] EXCEPT ![m.from] = m.index]]
                  /\ next' = [next EXCEPT ![p] = [next[p] EXCEPT ![m.from] = m.index + 1]]
                  /\ LET cset ==
                       { i \in 1..LenLog(p) :
                           /\ i > commit[p]
                           /\ Commitable(p, i)
                       } IN
                     /\ commit' = [commit EXCEPT ![p] = IF cset = {} THEN commit[p] ELSE Max(cset)]
                  /\ msgs' = msgs1 \cup (IF next'[p][m.from] <= LenLog(p) THEN { AppMsg(p, m.from) } ELSE {})
                  /\ UNCHANGED << term, vote, state, log, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo >>
                ELSE
                  /\ next' = [next EXCEPT ![p] = [next[p] EXCEPT ![m.from] = IF next[p][m.from] = 1 THEN 1 ELSE next[p][m.from] - 1]]
                  /\ msgs' = msgs1 \cup { AppMsg(p, m.from) }
                  /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match >>

LeaderSendHeartbeat(n) ==
  /\ n \in NODES
  /\ state[n] = "StateLeader"
  /\ msgs' = msgs \cup { HeartbeatMsg(n, q) : q \in NODES \ {n} }
  /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

EnqueueProp(n) ==
  /\ n \in NODES
  /\ msgs' = msgs \cup {
      [ type |-> "MsgProp",
        from |-> None,
        to |-> n,
        term |-> 0,
        prevIndex |-> 0,
        prevTerm |-> 0,
        entries |-> << [term |-> 0] >>,
        commit |-> 0,
        reject |-> FALSE,
        lastIndex |-> 0,
        lastTerm |-> 0
      ]
    }
  /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DeliverProp(m) ==
  /\ m \in msgs
  /\ m.type = "MsgProp"
  /\ LET n == m.to IN
     /\ LET msgs1 == msgs \ {m} IN
        /\ IF state[n] = "StateLeader" THEN
             /\ LET newLog == log[n] \o MapTerm(m.entries, term[n]) IN
                /\ log' = [log EXCEPT ![n] = newLog]
                /\ match' = [match EXCEPT ![n] = [r \in NODES |-> IF r = n THEN Len(newLog) ELSE match[n][r]]]
                /\ next' = [next EXCEPT ![n] = [r \in NODES |-> IF r = n THEN Len(newLog) + 1 ELSE next[n][r]]]
                /\ msgs' = msgs1 \cup { AppMsg(n, q) : q \in NODES \ {n} }
                /\ UNCHANGED << term, vote, state, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo >>
           ELSE
             /\ msgs' = msgs1
             /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

DropMessage ==
  /\ msgs # {}
  /\ \E m \in msgs:
       /\ msgs' = msgs \ {m}
       /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, rTimeout, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

ResetElectionTimeout(n) ==
  /\ n \in NODES
  /\ rTimeout' \in [NODES -> ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT - 1)]
  /\ UNCHANGED << term, vote, state, log, commit, lead, electionElapsed, msgs, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

Deliver ==
  \E m \in msgs:
    \/ DeliverHup(m)
    \/ DeliverPreVote(m)
    \/ DeliverPreVoteResp(m)
    \/ DeliverVote(m)
    \/ DeliverVoteResp(m)
    \/ DeliverHeartbeat(m)
    \/ DeliverHeartbeatResp(m)
    \/ DeliverApp(m)
    \/ DeliverAppResp(m)
    \/ DeliverProp(m)

Next ==
  \/ \E n \in NODES: Tick(n)
  \/ \E n \in NODES: EnqueueHup(n)
  \/ Deliver
  \/ \E n \in NODES: LeaderSendHeartbeat(n)
  \/ EnqueueProp(CHOOSE n \in NODES: TRUE)
  \/ DropMessage
  \/ \E n \in NODES: ResetElectionTimeout(n)

Spec ==
  Init /\ [][Next]_<< term, vote, state, log, commit, lead, electionElapsed, rTimeout, msgs, prevoteTerm, prevotesYes, votesYes, votesNo, match, next >>

====