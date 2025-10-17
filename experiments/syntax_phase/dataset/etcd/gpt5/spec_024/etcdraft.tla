---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  NODES,
  None,
  ELECTION_TIMEOUT,
  CMD

States == {"StateFollower", "StateCandidate", "StateLeader", "StatePreCandidate"}
MsgTypes == {"MsgHup","MsgPreVote","MsgPreVoteResp","MsgVote","MsgVoteResp","MsgApp","MsgAppResp","MsgProp"}

VARIABLES
  state,
  term,
  vote,
  log,
  commitIndex,
  leaderKnown,
  elapsed,
  nextIdx,
  matchIdx,
  net,
  prevotes,
  votes

Message(m) ==
  /\ m \in [
      type: MsgTypes,
      from: NODES,
      to: NODES,
      term: Nat,
      index: Nat,
      logTerm: Nat,
      entries: Seq([term: Nat, cmd: UNION {CMD, {"noop"}}]),
      commit: Nat,
      reject: BOOLEAN
     ]

NetType == SUBSET { m \in [
      type: MsgTypes,
      from: NODES,
      to: NODES,
      term: Nat,
      index: Nat,
      logTerm: Nat,
      entries: Seq([term: Nat, cmd: UNION {CMD, {"noop"}}]),
      commit: Nat,
      reject: BOOLEAN
     ] : TRUE }

TypeInv ==
  /\ state \in [NODES -> States]
  /\ term \in [NODES -> Nat]
  /\ vote \in [NODES -> (NODES \cup {None})]
  /\ log \in [NODES -> Seq([term: Nat, cmd: UNION {CMD, {"noop"}}])]
  /\ commitIndex \in [NODES -> Nat]
  /\ leaderKnown \in [NODES -> (NODES \cup {None})]
  /\ elapsed \in [NODES -> Nat]
  /\ nextIdx \in [NODES -> [NODES -> Nat]]
  /\ matchIdx \in [NODES -> [NODES -> Nat]]
  /\ net \in NetType
  /\ prevotes \in [NODES -> SUBSET NODES]
  /\ votes \in [NODES -> SUBSET NODES]

ToOthers(n) == NODES \ {n}

LenLog(n) == Len(log[n])

LastLogTerm(n) == IF LenLog(n) = 0 THEN 0 ELSE log[n][LenLog(n)].term

UpTo(s, k) ==
  IF k = 0 THEN <<>>
  ELSE IF k >= Len(s) THEN s
  ELSE SubSeq(s, 1, k)

FromIdx(s, k) ==
  IF k > Len(s) THEN <<>>
  ELSE SubSeq(s, k, Len(s))

SuffixAfter(s, k) ==
  IF k >= Len(s) THEN <<>>
  ELSE SubSeq(s, k+1, Len(s))

Majority(S) == Cardinality(S) > Cardinality(NODES) \div 2

UpToDate(lastIdx, lastTerm, i) ==
  \/ lastTerm > LastLogTerm(i)
  \/ /\ lastTerm = LastLogTerm(i)
     /\ lastIdx >= LenLog(i)

PrevOK(i, m) ==
  \/ m.index = 0
  \/ /\ m.index <= LenLog(i)
     /\ (IF m.index = 0 THEN TRUE ELSE log[i][m.index].term = m.logTerm)

NewLogOnAppend(i, m) ==
  LET base == UpTo(log[i], m.index) IN
    IF Len(m.entries) = 0 THEN log[i]
    ELSE
      CHOOSE L \in Seq([term: Nat, cmd: UNION {CMD, {"noop"}}]) :
        /\ SubSeq(L, 1, m.index) = base
        /\ SubSeq(L, m.index+1, m.index + Len(m.entries)) = m.entries
        /\ \E sfx \in {<<>>, SuffixAfter(log[i], m.index + Len(m.entries))} :
             L = base \o m.entries \o sfx

AllMatchAtOrAbove(l, k) ==
  { i \in NODES :
      IF i = l THEN LenLog(l) >= k ELSE matchIdx[l][i] >= k }

NewLeaderCommit(l) ==
  LET cand == { k \in 0..LenLog(l) :
                  /\ (k = 0) \/ (k > 0 /\ log[l][k].term = term[l])
                  /\ Majority(AllMatchAtOrAbove(l, k)) }
  IN IF cand = {} THEN commitIndex[l] ELSE Max(cand)

Init ==
  /\ state = [n \in NODES |-> "StateFollower"]
  /\ term = [n \in NODES |-> 0]
  /\ vote = [n \in NODES |-> None]
  /\ log = [n \in NODES |-> <<>>]
  /\ commitIndex = [n \in NODES |-> 0]
  /\ leaderKnown = [n \in NODES |-> None]
  /\ elapsed = [n \in NODES |-> 0]
  /\ nextIdx = [l \in NODES |-> [i \in NODES |-> 1]]
  /\ matchIdx = [l \in NODES |-> [i \in NODES |-> 0]]
  /\ net = {}
  /\ prevotes = [n \in NODES |-> {}]
  /\ votes = [n \in NODES |-> {}]
  /\ TypeInv

HupSend ==
  \E n \in NODES :
    /\ elapsed[n] >= ELECTION_TIMEOUT
    /\ LET m == [
          type |-> "MsgHup",
          from |-> n,
          to |-> n,
          term |-> term[n],
          index |-> 0,
          logTerm |-> 0,
          entries |-> <<>>,
          commit |-> commitIndex[n],
          reject |-> FALSE
       ]
       IN /\ net' = net \cup {m}
          /\ elapsed' = [elapsed EXCEPT ![n] = 0]
          /\ UNCHANGED << state, term, vote, log, commitIndex, leaderKnown, nextIdx, matchIdx, prevotes, votes >>

DeliverHup ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgHup"
    /\ LET n == m.to IN
       /\ state[n] # "StateLeader"
       /\ net' = net \ {m}
       /\ state' = [state EXCEPT ![n] = "StatePreCandidate"]
       /\ prevotes' = [prevotes EXCEPT ![n] = {n}]
       /\ votes' = votes
       /\ term' = term
       /\ vote' = vote
       /\ log' = log
       /\ commitIndex' = commitIndex
       /\ leaderKnown' = leaderKnown
       /\ elapsed' = elapsed
       /\ \E reqs \in SUBSET ({ [ type |-> "MsgPreVote",
                                  from |-> n,
                                  to |-> i,
                                  term |-> term[n] + 1,
                                  index |-> LenLog(n),
                                  logTerm |-> LastLogTerm(n),
                                  entries |-> <<>>,
                                  commit |-> commitIndex[n],
                                  reject |-> FALSE ] : i \in ToOthers(n) }) :
            net' = (net \ {m}) \cup reqs
       /\ nextIdx' = nextIdx
       /\ matchIdx' = matchIdx

DeliverPreVote ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgPreVote"
    /\ LET i == m.to IN
       /\ net' = net \ {m} \cup {
           [ type |-> "MsgPreVoteResp",
             from |-> i,
             to |-> m.from,
             term |-> m.term,
             index |-> 0,
             logTerm |-> 0,
             entries |-> <<>>,
             commit |-> commitIndex[i],
             reject |-> ~(UpToDate(m.index, m.logTerm, i))
           ] }
       /\ UNCHANGED << state, term, vote, log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx, prevotes, votes >>

DeliverPreVoteResp ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgPreVoteResp"
    /\ LET n == m.to IN
       /\ state[n] = "StatePreCandidate"
       /\ net' = net \ {m}
       /\ IF ~m.reject THEN
            /\ prevotes' = [prevotes EXCEPT ![n] = prevotes[n] \cup {m.from}]
            /\ IF Majority(prevotes'[n]) THEN
                 /\ state' = [state EXCEPT ![n] = "StateCandidate"]
                 /\ term' = [term EXCEPT ![n] = term[n] + 1]
                 /\ vote' = [vote EXCEPT ![n] = n]
                 /\ votes' = [votes EXCEPT ![n] = {n}]
                 /\ \E reqs \in SUBSET ({ [ type |-> "MsgVote",
                                            from |-> n,
                                            to |-> i,
                                            term |-> term'[n],
                                            index |-> LenLog(n),
                                            logTerm |-> LastLogTerm(n),
                                            entries |-> <<>>,
                                            commit |-> commitIndex[n],
                                            reject |-> FALSE ] : i \in ToOthers(n) }) :
                      net' = (net \ {m}) \cup reqs
                 /\ UNCHANGED << log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx >>
               ELSE
                 /\ state' = state
                 /\ term' = term
                 /\ vote' = vote
                 /\ votes' = votes
                 /\ UNCHANGED << log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx >>
          ELSE
            /\ prevotes' = prevotes
            /\ UNCHANGED << state, term, vote, votes, log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx >>

DeliverVote ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgVote"
    /\ LET i == m.to IN
       /\ net' = net \ {m} \cup {
           [ type |-> "MsgVoteResp",
             from |-> i,
             to |-> m.from,
             term |-> IF m.term >= term[i] THEN m.term ELSE term[i],
             index |-> 0,
             logTerm |-> 0,
             entries |-> <<>>,
             commit |-> commitIndex[i],
             reject |-> IF m.term < term[i] THEN TRUE
                        ELSE
                          LET tNew == m.term IN
                          LET canVote ==
                                /\ (vote[i] = None \/ vote[i] = m.from)
                                /\ UpToDate(m.index, m.logTerm, i)
                          IN
                            IF tNew > term[i] THEN
                              ~canVote
                            ELSE
                              ~canVote
           ] }
       /\ IF m.term > term[i] THEN
            /\ term' = [term EXCEPT ![i] = m.term]
            /\ state' = [state EXCEPT ![i] = "StateFollower"]
            /\ vote' = [vote EXCEPT ![i] = None]
            /\ leaderKnown' = [leaderKnown EXCEPT ![i] = None]
          ELSE
            /\ term' = term
            /\ state' = state
            /\ vote' = vote
            /\ leaderKnown' = leaderKnown
       /\ IF m.term >= term[i]
             /\ (vote[i] = None \/ vote[i] = m.from)
             /\ UpToDate(m.index, m.logTerm, i)
          THEN vote' = [vote' EXCEPT ![i] = m.from] ELSE vote' = vote'
       /\ UNCHANGED << log, commitIndex, elapsed, nextIdx, matchIdx, prevotes, votes >>

DeliverVoteResp ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgVoteResp"
    /\ LET n == m.to IN
       /\ net' = net \ {m}
       /\ IF state[n] = "StateCandidate" /\ m.term = term[n] /\ ~m.reject THEN
            /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m.from}]
            /\ IF Majority(votes'[n]) THEN
                 /\ state' = [state EXCEPT ![n] = "StateLeader"]
                 /\ leaderKnown' = [leaderKnown EXCEPT ![n] = n]
                 /\ log' = [log EXCEPT ![n] = log[n] \o << [term |-> term[n], cmd |-> "noop"] >>]
                 /\ matchIdx' = [matchIdx EXCEPT ![n] = [matchIdx[n] EXCEPT ![n] = LenLog'(n)]]
                 /\ nextIdx' = [nextIdx EXCEPT ![n] = [i \in NODES |-> LenLog'(n) + 1]]
                 /\ commitIndex' = [commitIndex EXCEPT ![n] = commitIndex[n]]
                 /\ term' = term
                 /\ vote' = vote
                 /\ prevotes' = prevotes
                 /\ elapsed' = elapsed
                 /\ \E reqs \in SUBSET ({ [ type |-> "MsgApp",
                                            from |-> n,
                                            to |-> i,
                                            term |-> term[n],
                                            index |-> LenLog'(n) - 1,
                                            logTerm |-> IF LenLog'(n) = 1 THEN 0 ELSE log'[n][LenLog'(n)-1].term,
                                            entries |-> SubSeq(log'[n], LenLog(n)+1, LenLog'(n)),
                                            commit |-> commitIndex'[n],
                                            reject |-> FALSE ] : i \in ToOthers(n) }) :
                      net' = (net \ {m}) \cup reqs
               ELSE
                 /\ state' = state
                 /\ leaderKnown' = leaderKnown
                 /\ log' = log
                 /\ matchIdx' = matchIdx
                 /\ nextIdx' = nextIdx
                 /\ commitIndex' = commitIndex
                 /\ term' = term
                 /\ vote' = vote
                 /\ prevotes' = prevotes
                 /\ elapsed' = elapsed
          ELSE
            /\ votes' = votes
            /\ UNCHANGED << state, leaderKnown, log, matchIdx, nextIdx, commitIndex, term, vote, prevotes, elapsed >>
  \* helper for LenLog' used above
  /\ LET _ignore == 0 IN TRUE

LenLog'(n) == Len(log'[n])

ClientPropose ==
  \E l \in NODES, c \in CMD :
    /\ state[l] = "StateLeader"
    /\ LET m == [
         type |-> "MsgProp",
         from |-> l,
         to |-> l,
         term |-> term[l],
         index |-> 0,
         logTerm |-> 0,
         entries |-> << [term |-> 0, cmd |-> c] >>,
         commit |-> commitIndex[l],
         reject |-> FALSE
       ]
       IN /\ net' = net \cup {m}
          /\ UNCHANGED << state, term, vote, log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx, prevotes, votes >>

DeliverProp ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgProp"
    /\ LET l == m.to IN
       /\ state[l] = "StateLeader"
       /\ net' = net \ {m} \cup { [ type |-> "MsgApp",
                                    from |-> l,
                                    to |-> i,
                                    term |-> term[l],
                                    index |-> nextIdx[l][i] - 1,
                                    logTerm |-> IF nextIdx[l][i] = 1 THEN 0 ELSE log[l][nextIdx[l][i]-1].term,
                                    entries |-> SubSeq([log EXCEPT ![l] = log[l] \o << [term |-> term[l], cmd |-> m.entries[1].cmd] >>][l], nextIdx[l][i], Len([log EXCEPT ![l] = log[l] \o << [term |-> term[l], cmd |-> m.entries[1].cmd] >>][l])),
                                    commit |-> commitIndex[l],
                                    reject |-> FALSE ] : i \in ToOthers(l) }
       /\ log' = [log EXCEPT ![l] = log[l] \o << [term |-> term[l], cmd |-> m.entries[1].cmd] >>]
       /\ matchIdx' = [matchIdx EXCEPT ![l] = [matchIdx[l] EXCEPT ![l] = LenLog'(l)]]
       /\ nextIdx' = nextIdx
       /\ state' = state
       /\ term' = term
       /\ vote' = vote
       /\ commitIndex' = commitIndex
       /\ leaderKnown' = leaderKnown
       /\ elapsed' = elapsed
       /\ prevotes' = prevotes
       /\ votes' = votes
  /\ LET _ignore == 0 IN TRUE

LeaderSendApp ==
  \E l \in NODES, i \in ToOthers(l) :
    /\ state[l] = "StateLeader"
    /\ LET msg == [
         type |-> "MsgApp",
         from |-> l,
         to |-> i,
         term |-> term[l],
         index |-> nextIdx[l][i] - 1,
         logTerm |-> IF nextIdx[l][i] = 1 THEN 0 ELSE log[l][nextIdx[l][i]-1].term,
         entries |-> SubSeq(log[l], nextIdx[l][i], LenLog(l)),
         commit |-> commitIndex[l],
         reject |-> FALSE
       ]
       IN /\ net' = net \cup {msg}
          /\ UNCHANGED << state, term, vote, log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx, prevotes, votes >>

DeliverApp ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgApp"
    /\ LET i == m.to IN
       /\ net' =
          IF PrevOK(i, m) THEN
            (net \ {m}) \cup {
              [ type |-> "MsgAppResp",
                from |-> i,
                to |-> m.from,
                term |-> m.term,
                index |-> m.index + Len(m.entries),
                logTerm |-> 0,
                entries |-> <<>>,
                commit |-> commitIndex[i],
                reject |-> FALSE ] }
          ELSE
            (net \ {m}) \cup {
              [ type |-> "MsgAppResp",
                from |-> i,
                to |-> m.from,
                term |-> m.term,
                index |-> m.index,
                logTerm |-> 0,
                entries |-> <<>>,
                commit |-> commitIndex[i],
                reject |-> TRUE ] }
       /\ IF m.term > term[i] THEN
            /\ term' = [term EXCEPT ![i] = m.term]
            /\ state' = [state EXCEPT ![i] = "StateFollower"]
            /\ vote' = [vote EXCEPT ![i] = None]
            /\ leaderKnown' = [leaderKnown EXCEPT ![i] = m.from]
          ELSE
            /\ term' = term
            /\ state' = [state EXCEPT ![i] = "StateFollower"]
            /\ vote' = vote
            /\ leaderKnown' = [leaderKnown EXCEPT ![i] = m.from]
       /\ elapsed' = [elapsed EXCEPT ![i] = 0]
       /\ IF PrevOK(i, m) THEN
            /\ log' = [log EXCEPT ![i] = NewLogOnAppend(i, m)]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = Min(m.commit, Len(log'[i]))]
          ELSE
            /\ log' = log
            /\ commitIndex' = commitIndex
       /\ UNCHANGED << nextIdx, matchIdx, prevotes, votes >>

DeliverAppResp ==
  \E m \in net :
    /\ Message(m)
    /\ m.type = "MsgAppResp"
    /\ LET l == m.to IN
       /\ state[l] = "StateLeader"
       /\ net' = net \ {m}
       /\ IF m.term > term[l] THEN
            /\ term' = [term EXCEPT ![l] = m.term]
            /\ state' = [state EXCEPT ![l] = "StateFollower"]
            /\ vote' = [vote EXCEPT ![l] = None]
            /\ leaderKnown' = [leaderKnown EXCEPT ![l] = None]
            /\ UNCHANGED << log, commitIndex, elapsed, nextIdx, matchIdx, prevotes, votes >>
          ELSE
            /\ term' = term
            /\ vote' = vote
            /\ leaderKnown' = leaderKnown
            /\ IF m.reject THEN
                 /\ nextIdx' = [nextIdx EXCEPT ![l] = [nextIdx[l] EXCEPT ![m.from] = Max(1, nextIdx[l][m.from] - 1)]]
                 /\ matchIdx' = matchIdx
               ELSE
                 /\ matchIdx' = [matchIdx EXCEPT ![l] = [matchIdx[l] EXCEPT ![m.from] = m.index]]
                 /\ nextIdx' = [nextIdx EXCEPT ![l] = [nextIdx[l] EXCEPT ![m.from] = m.index + 1]]
            /\ commitIndex' = [commitIndex EXCEPT ![l] = Max(commitIndex[l], NewLeaderCommit(l))]
            /\ state' = state
            /\ log' = log
            /\ elapsed' = elapsed
            /\ prevotes' = prevotes
            /\ votes' = votes

Tick ==
  \E n \in NODES :
    /\ elapsed' = [elapsed EXCEPT ![n] = elapsed[n] + 1]
    /\ UNCHANGED << state, term, vote, log, commitIndex, leaderKnown, nextIdx, matchIdx, net, prevotes, votes >>

Drop ==
  \E m \in net :
    /\ net' = net \ {m}
    /\ UNCHANGED << state, term, vote, log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx, prevotes, votes >>

Next ==
  HupSend
  \/ DeliverHup
  \/ DeliverPreVote
  \/ DeliverPreVoteResp
  \/ DeliverVote
  \/ DeliverVoteResp
  \/ ClientPropose
  \/ DeliverProp
  \/ LeaderSendApp
  \/ DeliverApp
  \/ DeliverAppResp
  \/ Tick
  \/ Drop

Spec ==
  Init /\ [][Next]_<< state, term, vote, log, commitIndex, leaderKnown, elapsed, nextIdx, matchIdx, net, prevotes, votes >>

====