---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  NODES,
  None,
  ELECTION_TIMEOUT,
  HEARTBEAT_TIMEOUT,
  DATA

StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
StatePreCandidate == "StatePreCandidate"
States == {StateFollower, StateCandidate, StateLeader, StatePreCandidate}

MsgHup == "MsgHup"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgProp == "MsgProp"
MsgType == {MsgHup, MsgPreVote, MsgPreVoteResp, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgProp}

Entry == [term: Nat, data: DATA]

Message ==
  [ type: MsgType,
    from: NODES,
    to: NODES,
    term: Nat,
    lastIndex: Nat,
    lastTerm: Nat,
    prevIndex: Nat,
    prevTerm: Nat,
    entries: Seq(Entry),
    commit: Nat,
    index: Nat,
    reject: BOOLEAN,
    hint: Nat
  ]

VARIABLES
  state,
  term,
  vote,
  lead,
  logs,
  commit,
  nextIndex,
  matchIndex,
  preVotesGranted,
  votesGranted,
  elapse,
  randTimeout,
  msgs

TypeOK ==
  /\ state \in [NODES -> States]
  /\ term \in [NODES -> Nat]
  /\ vote \in [NODES -> (NODES \cup {None})]
  /\ lead \in [NODES -> (NODES \cup {None})]
  /\ logs \in [NODES -> Seq(Entry)]
  /\ commit \in [NODES -> Nat]
  /\ nextIndex \in [NODES -> [NODES -> Nat]]
  /\ matchIndex \in [NODES -> [NODES -> Nat]]
  /\ preVotesGranted \in [NODES -> SUBSET NODES]
  /\ votesGranted \in [NODES -> SUBSET NODES]
  /\ elapse \in [NODES -> Nat]
  /\ randTimeout \in [NODES -> (ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT - 1))]
  /\ msgs \in SUBSET Message

Init ==
  /\ state = [n \in NODES |-> StateFollower]
  /\ term = [n \in NODES |-> 0]
  /\ vote = [n \in NODES |-> None]
  /\ lead = [n \in NODES |-> None]
  /\ logs = [n \in NODES |-> << >>]
  /\ commit = [n \in NODES |-> 0]
  /\ nextIndex = [n \in NODES |-> [p \in NODES |-> 1]]
  /\ matchIndex = [n \in NODES |-> [p \in NODES |-> 0]]
  /\ preVotesGranted = [n \in NODES |-> {}]
  /\ votesGranted = [n \in NODES |-> {}]
  /\ elapse = [n \in NODES |-> 0]
  /\ randTimeout \in [NODES -> (ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT - 1))]
  /\ msgs = {}
  /\ TypeOK

Len(s) == Cardinality(Domain(s)) \* 0 + Length(s)

LastIndex(n) == Len(logs[n])
TermAt(n, i) == IF i = 0 THEN 0 ELSE IF i <= Len(logs[n]) THEN logs[n][i].term ELSE 0
LastTerm(n) == TermAt(n, LastIndex(n))

IsUpToDate(cLT, cLI, myLT, myLI) == (cLT > myLT) \/ (cLT = myLT /\ cLI >= myLI)

Quorum(S) == 2 * Cardinality(S) > Cardinality(NODES)

Min(S) == CHOOSE m \in S: \A x \in S: m <= x
Max(S) == CHOOSE m \in S: \A x \in S: m >= x

Tick(n) ==
  /\ n \in NODES
  /\ elapse' = [elapse EXCEPT ![n] = elapse[n] + 1]
  /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, randTimeout, msgs >>

TimeoutHup(n) ==
  /\ n \in NODES
  /\ state[n] # StateLeader
  /\ elapse[n] >= randTimeout[n]
  /\ LET m == [ type |-> MsgHup, from |-> n, to |-> n, term |-> 0,
                 lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                 entries |-> << >>, commit |-> 0, index |-> 0, reject |-> FALSE, hint |-> 0 ]
     IN msgs' = msgs \cup { m }
  /\ elapse' = [elapse EXCEPT ![n] = 0]
  /\ randTimeout' = [randTimeout EXCEPT ![n] \in (ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT - 1))]
  /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted >>

DeliverHup(m) ==
  /\ m \in msgs
  /\ m.type = MsgHup
  /\ LET n == m.from IN
     /\ msgs' =
          (msgs \ {m})
          \cup { [ type |-> MsgPreVote, from |-> n, to |-> p, term |-> term[n] + 1,
                   lastIndex |-> LastIndex(n), lastTerm |-> LastTerm(n),
                   prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                   commit |-> 0, index |-> 0, reject |-> FALSE, hint |-> 0 ]
               : p \in NODES }
     /\ state' = [state EXCEPT ![n] = StatePreCandidate]
     /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {n}]
     /\ lead' = [lead EXCEPT ![n] = None]
     /\ UNCHANGED << term, vote, logs, commit, nextIndex, matchIndex, votesGranted, elapse, randTimeout >>

DeliverPreVote(m) ==
  /\ m \in msgs
  /\ m.type = MsgPreVote
  /\ LET v == m.to IN
     /\ msgs' =
          (msgs \ {m})
          \cup { [ type |-> MsgPreVoteResp, from |-> v, to |-> m.from, term |-> m.term,
                   lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                   entries |-> << >>, commit |-> 0, index |-> 0,
                   reject |-> ~(IsUpToDate(m.lastTerm, m.lastIndex, LastTerm(v), LastIndex(v))),
                   hint |-> 0 ] }
     /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

DeliverPreVoteResp(m) ==
  /\ m \in msgs
  /\ m.type = MsgPreVoteResp
  /\ LET n == m.to IN
     /\ msgs' =
          (msgs \ {m})
          \cup IF state[n] = StatePreCandidate /\ m.term = term[n] + 1 /\ ~m.reject
                THEN { [ type |-> MsgVote, from |-> n, to |-> p, term |-> term[n] + 1,
                         lastIndex |-> LastIndex(n), lastTerm |-> LastTerm(n),
                         prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                         commit |-> 0, index |-> 0, reject |-> FALSE, hint |-> 0 ] : p \in NODES \ {n} }
                ELSE {}
     /\ IF state[n] = StatePreCandidate /\ m.term = term[n] + 1 /\ ~m.reject
        THEN
          /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = preVotesGranted[n] \cup {m.from}]
          /\ IF Quorum(preVotesGranted'[n])
             THEN
               /\ state' = [state EXCEPT ![n] = StateCandidate]
               /\ term' = [term EXCEPT ![n] = term[n] + 1]
               /\ vote' = [vote EXCEPT ![n] = n]
               /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
               /\ elapse' = [elapse EXCEPT ![n] = 0]
               /\ randTimeout' = [randTimeout EXCEPT ![n] \in (ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT - 1))]
               /\ UNCHANGED << lead, logs, commit, nextIndex, matchIndex >>
             ELSE
               /\ UNCHANGED << state, term, vote, votesGranted, elapse, randTimeout, lead, logs, commit, nextIndex, matchIndex >>
        ELSE
          /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

DeliverVote(m) ==
  /\ m \in msgs
  /\ m.type = MsgVote
  /\ LET v == m.to IN
     /\ msgs' =
          (msgs \ {m})
          \cup { [ type |-> MsgVoteResp, from |-> v, to |-> m.from,
                   term |-> IF m.term > term[v] THEN m.term ELSE term[v],
                   lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                   entries |-> << >>, commit |-> 0, index |-> 0,
                   reject |-> ~( ( (vote[v] = None) \/ (vote[v] = m.from) ) /\ (IF m.term > term[v] THEN TRUE ELSE m.term = term[v]) /\ IsUpToDate(m.lastTerm, m.lastIndex, LastTerm(v), LastIndex(v)) ),
                   hint |-> 0 ] }
     /\ IF m.term > term[v]
        THEN
          /\ term1 == [term EXCEPT ![v] = m.term]
          /\ state1 == [state EXCEPT ![v] = StateFollower]
          /\ vote1 == [vote EXCEPT ![v] = None]
          /\ lead1 == [lead EXCEPT ![v] = None]
          /\ term' = term1
          /\ state' = state1
          /\ vote' = vote1
          /\ lead' = lead1
        ELSE
          /\ UNCHANGED << state, term, vote, lead >>
     /\ canVote == (vote'[v] = None) \/ (vote'[v] = m.from)
     /\ upToDate == IsUpToDate(m.lastTerm, m.lastIndex, LastTerm(v), LastIndex(v))
     /\ granted == canVote /\ (m.term = term'[v]) /\ upToDate
     /\ vote'' == [vote' EXCEPT ![v] = IF granted THEN m.from ELSE vote'[v]]
     /\ elapse' = [elapse EXCEPT ![v] = IF granted THEN 0 ELSE elapse[v]]
     /\ vote' = vote''
     /\ UNCHANGED << logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, randTimeout >>

DeliverVoteResp(m) ==
  /\ m \in msgs
  /\ m.type = MsgVoteResp
  /\ LET n == m.to IN
     /\ msgs' =
          (msgs \ {m})
          \cup IF state[n] = StateCandidate /\ m.term = term[n] /\ ~m.reject
                THEN {} ELSE {}
     /\ IF m.term > term[n]
        THEN
          /\ term' = [term EXCEPT ![n] = m.term]
          /\ state' = [state EXCEPT ![n] = StateFollower]
          /\ vote' = [vote EXCEPT ![n] = None]
          /\ lead' = [lead EXCEPT ![n] = None]
          /\ preVotesGranted' = preVotesGranted
          /\ votesGranted' = votesGranted
          /\ UNCHANGED << logs, commit, nextIndex, matchIndex, elapse, randTimeout >>
        ELSE
          /\ IF (m.term = term[n]) /\ state[n] = StateCandidate
             THEN
               /\ votesGranted' = [votesGranted EXCEPT ![n] = IF m.reject THEN votesGranted[n] ELSE votesGranted[n] \cup {m.from}]
               /\ IF Quorum(votesGranted'[n])
                  THEN
                    /\ state' = [state EXCEPT ![n] = StateLeader]
                    /\ lead' = [lead EXCEPT ![n] = n]
                    /\ nextIndex' =
                        [nextIndex EXCEPT
                          ![n] = [p \in NODES |-> IF p = n THEN Len(logs[n]) + 1 ELSE Len(logs[n]) + 1]]
                    /\ matchIndex' =
                        [matchIndex EXCEPT
                          ![n] = [p \in NODES |-> IF p = n THEN Len(logs[n]) ELSE 0]]
                    /\ logs' = [logs EXCEPT ![n] = Append(logs[n], [term |-> term[n], data |-> CHOOSE d \in DATA: TRUE])]
                    /\ matchIndex'' = [matchIndex' EXCEPT ![n][n] = Len(logs'[n])]
                    /\ nextIndex'' = [nextIndex' EXCEPT ![n] = [p \in NODES |-> IF p = n THEN Len(logs'[n]) + 1 ELSE nextIndex'[n][p]]]
                    /\ nextIndex' = nextIndex''
                    /\ matchIndex' = matchIndex''
                    /\ votesGranted' = votesGranted'
                    /\ term' = term
                    /\ vote' = vote
                    /\ preVotesGranted' = preVotesGranted
                    /\ elapse' = [elapse EXCEPT ![n] = 0]
                    /\ randTimeout' = [randTimeout EXCEPT ![n] \in (ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT - 1))]
                    /\ commit' = commit
                    /\ msgs' = msgs'
                      \cup { [ type |-> MsgApp, from |-> n, to |-> p, term |-> term[n],
                               lastIndex |-> 0, lastTerm |-> 0,
                               prevIndex |-> nextIndex'[n][p] - 1, prevTerm |-> TermAt(n, nextIndex'[n][p] - 1),
                               entries |-> SubSeq(logs'[n], nextIndex'[n][p], Len(logs'[n])),
                               commit |-> commit[n], index |-> 0, reject |-> FALSE, hint |-> 0 ]
                           : p \in NODES \ {n} }
                  ELSE
                    /\ UNCHANGED << state, lead, nextIndex, matchIndex, logs, term, vote, preVotesGranted, commit, elapse, randTimeout >>
             ELSE
               /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

DeliverHeartbeat(m) ==
  /\ m \in msgs
  /\ m.type = MsgHeartbeat
  /\ LET v == m.to IN
     /\ msgs' = (msgs \ {m}) \cup { [ type |-> MsgHeartbeatResp, from |-> v, to |-> m.from, term |-> IF m.term > term[v] THEN m.term ELSE term[v],
                                       lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                                       entries |-> << >>, commit |-> 0, index |-> 0, reject |-> FALSE, hint |-> 0 ] }
     /\ IF m.term > term[v]
        THEN
          /\ term' = [term EXCEPT ![v] = m.term]
          /\ state' = [state EXCEPT ![v] = StateFollower]
          /\ vote' = [vote EXCEPT ![v] = None]
          /\ lead' = [lead EXCEPT ![v] = m.from]
        ELSE
          /\ IF (m.term = term[v]) /\ state[v] # StateLeader
             THEN
               /\ state' = [state EXCEPT ![v] = StateFollower]
               /\ lead' = [lead EXCEPT ![v] = m.from]
               /\ UNCHANGED << term, vote >>
             ELSE
               /\ UNCHANGED << state, term, vote, lead >>
     /\ elapse' = [elapse EXCEPT ![v] = 0]
     /\ commit' = [commit EXCEPT ![v] = IF m.commit <= Len(logs[v]) THEN m.commit ELSE Len(logs[v])]
     /\ UNCHANGED << logs, nextIndex, matchIndex, preVotesGranted, votesGranted, randTimeout >>

DeliverHeartbeatResp(m) ==
  /\ m \in msgs
  /\ m.type = MsgHeartbeatResp
  /\ LET l == m.to IN
     /\ msgs' = msgs \ {m}
     /\ IF m.term > term[l]
        THEN
          /\ term' = [term EXCEPT ![l] = m.term]
          /\ state' = [state EXCEPT ![l] = StateFollower]
          /\ vote' = [vote EXCEPT ![l] = None]
          /\ lead' = [lead EXCEPT ![l] = None]
        ELSE
          /\ UNCHANGED << state, term, vote, lead >>
     /\ UNCHANGED << logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

DeliverApp(m) ==
  /\ m \in msgs
  /\ m.type = MsgApp
  /\ LET v == m.to IN
     /\ msgs' =
          (msgs \ {m})
          \cup IF (m.prevIndex = 0) \/ (m.prevIndex <= Len(logs[v]) /\ TermAt(v, m.prevIndex) = m.prevTerm)
                THEN { [ type |-> MsgAppResp, from |-> v, to |-> m.from, term |-> IF m.term > term[v] THEN m.term ELSE term[v],
                         lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                         entries |-> << >>, commit |-> 0, index |-> 0 + 0 + Len( IF (m.prevIndex = 0) \/ (m.prevIndex <= Len(logs[v]) /\ TermAt(v, m.prevIndex) = m.prevTerm)
                                                                                   THEN (LET li == Len(logs[v]) IN
                                                                                         LET ne == m.entries IN
                                                                                         LET overlapLen == IF m.prevIndex + Len(ne) <= li THEN Len(ne) ELSE li - m.prevIndex IN
                                                                                         LET Conflicts == { k \in (IF overlapLen = 0 THEN {} ELSE 1..overlapLen) : logs[v][m.prevIndex + k].term # ne[k].term } IN
                                                                                         LET truncIdx == IF Conflicts = {} THEN m.prevIndex + overlapLen ELSE m.prevIndex + Min(Conflicts) - 1 IN
                                                                                         LET baseLog == IF truncIdx = 0 THEN << >> ELSE SubSeq(logs[v], 1, truncIdx) IN
                                                                                         LET toAppendStart == IF (IF overlapLen = 0 THEN TRUE ELSE Conflicts = {}) THEN overlapLen + 1 ELSE Min(Conflicts) IN
                                                                                         LET toAppend == IF toAppendStart > Len(ne) THEN << >> ELSE SubSeq(ne, toAppendStart, Len(ne)) IN
                                                                                         baseLog \o toAppend) ELSE logs[v] ),
                         reject |-> FALSE, hint |-> 0 ] }
                ELSE { [ type |-> MsgAppResp, from |-> v, to |-> m.from, term |-> IF m.term > term[v] THEN m.term ELSE term[v],
                         lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                         entries |-> << >>, commit |-> 0, index |-> Len(logs[v]), reject |-> TRUE, hint |-> Len(logs[v]) ] }
     /\ IF m.term > term[v]
        THEN
          /\ term' = [term EXCEPT ![v] = m.term]
          /\ state' = [state EXCEPT ![v] = StateFollower]
          /\ vote' = [vote EXCEPT ![v] = None]
          /\ lead' = [lead EXCEPT ![v] = m.from]
        ELSE
          /\ IF (m.term = term[v]) /\ state[v] # StateLeader
             THEN
               /\ state' = [state EXCEPT ![v] = StateFollower]
               /\ lead' = [lead EXCEPT ![v] = m.from]
               /\ UNCHANGED << term, vote >>
             ELSE
               /\ UNCHANGED << state, term, vote, lead >>
     /\ elapse' = [elapse EXCEPT ![v] = 0]
     /\ IF (m.prevIndex = 0) \/ (m.prevIndex <= Len(logs[v]) /\ TermAt(v, m.prevIndex) = m.prevTerm)
        THEN
          /\ LET li == Len(logs[v]) IN
             LET ne == m.entries IN
             LET overlapLen == IF m.prevIndex + Len(ne) <= li THEN Len(ne) ELSE li - m.prevIndex IN
             LET Conflicts == { k \in (IF overlapLen = 0 THEN {} ELSE 1..overlapLen) : logs[v][m.prevIndex + k].term # ne[k].term } IN
             LET truncIdx == IF Conflicts = {} THEN m.prevIndex + overlapLen ELSE m.prevIndex + Min(Conflicts) - 1 IN
             LET baseLog == IF truncIdx = 0 THEN << >> ELSE SubSeq(logs[v], 1, truncIdx) IN
             LET toAppendStart == IF (IF overlapLen = 0 THEN TRUE ELSE Conflicts = {}) THEN overlapLen + 1 ELSE Min(Conflicts) IN
             LET toAppend == IF toAppendStart > Len(ne) THEN << >> ELSE SubSeq(ne, toAppendStart, Len(ne)) IN
             /\ logs' = [logs EXCEPT ![v] = baseLog \o toAppend]
             /\ commit' = [commit EXCEPT ![v] = IF m.commit <= Len(logs'[v]) THEN m.commit ELSE Len(logs'[v])]
        ELSE
          /\ UNCHANGED << logs, commit >>
     /\ UNCHANGED << nextIndex, matchIndex, preVotesGranted, votesGranted, randTimeout >>

DeliverAppResp(m) ==
  /\ m \in msgs
  /\ m.type = MsgAppResp
  /\ LET l == m.to IN
     /\ msgs' = msgs \ {m}
     /\ IF m.term > term[l]
        THEN
          /\ term' = [term EXCEPT ![l] = m.term]
          /\ state' = [state EXCEPT ![l] = StateFollower]
          /\ vote' = [vote EXCEPT ![l] = None]
          /\ lead' = [lead EXCEPT ![l] = None]
          /\ UNCHANGED << logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>
        ELSE
          /\ IF (m.term = term[l]) /\ state[l] = StateLeader
             THEN
               /\ IF m.reject
                  THEN
                    /\ nextIndex' = [nextIndex EXCEPT ![l][m.from] = IF nextIndex[l][m.from] > 1 THEN Max({1, Min({ nextIndex[l][m.from] - 1, m.index + 1 })}) ELSE 1]
                    /\ UNCHANGED << matchIndex, logs, commit, preVotesGranted, votesGranted, elapse, randTimeout, state, term, vote, lead >>
                  ELSE
                    /\ matchIndex' = [matchIndex EXCEPT ![l][m.from] = Max({ matchIndex[l][m.from], m.index })]
                    /\ nextIndex' = [nextIndex EXCEPT ![l][m.from] = matchIndex'[l][m.from] + 1]
                    /\ LET Cands == { i \in (IF Len(logs[l]) = 0 THEN {} ELSE 1..Len(logs[l])) :
                                        i > commit[l]
                                        /\ logs[l][i].term = term[l]
                                        /\ Quorum({ p \in NODES : (p = l /\ Len(logs[l]) >= i) \/ (p # l /\ matchIndex'[l][p] >= i) })
                                      }
                       IN commit' = [commit EXCEPT ![l] = IF Cands = {} THEN commit[l] ELSE Max(Cands)]
                    /\ UNCHANGED << logs, preVotesGranted, votesGranted, elapse, randTimeout, state, term, vote, lead >>
             ELSE
               /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

LeaderSendHeartbeat(l, p) ==
  /\ l \in NODES /\ p \in NODES /\ l # p
  /\ state[l] = StateLeader
  /\ msgs' = msgs \cup { [ type |-> MsgHeartbeat, from |-> l, to |-> p, term |-> term[l],
                           lastIndex |-> 0, lastTerm |-> 0, prevIndex |-> 0, prevTerm |-> 0,
                           entries |-> << >>, commit |-> commit[l], index |-> 0, reject |-> FALSE, hint |-> 0 ] }
  /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

LeaderSendAppend(l, p) ==
  /\ l \in NODES /\ p \in NODES /\ l # p
  /\ state[l] = StateLeader
  /\ msgs' =
       msgs \cup { [ type |-> MsgApp, from |-> l, to |-> p, term |-> term[l],
                     lastIndex |-> 0, lastTerm |-> 0,
                     prevIndex |-> nextIndex[l][p] - 1, prevTerm |-> TermAt(l, nextIndex[l][p] - 1),
                     entries |-> SubSeq(logs[l], nextIndex[l][p], Len(logs[l])),
                     commit |-> commit[l], index |-> 0, reject |-> FALSE, hint |-> 0 ] }
  /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

ClientSendProp(c) ==
  /\ c \in NODES
  /\ \E l \in NODES: state[l] = StateLeader
  /\ LET l == CHOOSE x \in NODES: state[x] = StateLeader IN
     /\ msgs' = msgs \cup { [ type |-> MsgProp, from |-> c, to |-> l, term |-> 0,
                              lastIndex |-> 0, lastTerm |-> 0,
                              prevIndex |-> 0, prevTerm |-> 0,
                              entries |-> << [term |-> 0, data |-> CHOOSE d \in DATA: TRUE] >>,
                              commit |-> 0, index |-> 0, reject |-> FALSE, hint |-> 0 ] }
  /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

DeliverProp(m) ==
  /\ m \in msgs
  /\ m.type = MsgProp
  /\ LET l == m.to IN
     /\ msgs' =
          (msgs \ {m})
          \cup IF state[l] = StateLeader
                THEN { [ type |-> MsgApp, from |-> l, to |-> p, term |-> term[l],
                         lastIndex |-> 0, lastTerm |-> 0,
                         prevIndex |-> nextIndex[l][p] - 1, prevTerm |-> TermAt(l, nextIndex[l][p] - 1),
                         entries |-> SubSeq([logs EXCEPT ![l] = Append(logs[l], [term |-> term[l], data |-> m.entries[1].data])][l], nextIndex[l][p], Len([logs EXCEPT ![l] = Append(logs[l], [term |-> term[l], data |-> m.entries[1].data])][l])),
                         commit |-> commit[l], index |-> 0, reject |-> FALSE, hint |-> 0 ] : p \in NODES \ {l} }
                ELSE {}
     /\ IF state[l] = StateLeader
        THEN
          /\ logs' = [logs EXCEPT ![l] = Append(logs[l], [term |-> term[l], data |-> m.entries[1].data])]
          /\ matchIndex' = [matchIndex EXCEPT ![l][l] = Len(logs'[l])]
          /\ nextIndex' = nextIndex
          /\ UNCHANGED << state, term, vote, lead, commit, preVotesGranted, votesGranted, elapse, randTimeout >>
        ELSE
          /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

Drop(m) ==
  /\ m \in msgs
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout >>

Deliver(m) ==
  DeliverHup(m)
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
  \/ \E n \in NODES: TimeoutHup(n)
  \/ \E m \in msgs: Deliver(m)
  \/ \E l, p \in NODES: LeaderSendHeartbeat(l, p)
  \/ \E l, p \in NODES: LeaderSendAppend(l, p)
  \/ \E c \in NODES: ClientSendProp(c)
  \/ \E m \in msgs: Drop(m)

vars == << state, term, vote, lead, logs, commit, nextIndex, matchIndex, preVotesGranted, votesGranted, elapse, randTimeout, msgs >>

Spec == Init /\ [][Next]_vars
====