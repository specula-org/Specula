---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  NODES,
  CMD,
  ELECTION_TIMEOUT,
  HEARTBEAT_TIMEOUT

None == 0

StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
StatePreCandidate == "StatePreCandidate"
StateType == {StateFollower, StateCandidate, StateLeader, StatePreCandidate}

MsgHup == "MsgHup"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgHeartbeat == "MsgHeartbeat"
MsgProp == "MsgProp"
MsgType == {MsgHup, MsgPreVote, MsgPreVoteResp, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgProp}

Entry == [term: Nat, data: CMD]

Message ==
  [ type: MsgType,
    from: NODES,
    to: NODES,
    term: Nat,
    prevIndex: Nat,
    prevTerm: Nat,
    entries: Seq(Entry),
    leaderCommit: Nat,
    granted: BOOLEAN,
    index: Nat,
    reject: BOOLEAN,
    candIndex: Nat,
    candTerm: Nat
  ]

VARIABLES
  state,
  term,
  votedFor,
  log,
  commit,
  electionElapsed,
  heartbeatElapsed,
  leader,
  msgs,
  matchIndex,
  electionPhase,
  electionVotes

Vars == << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, msgs, matchIndex, electionPhase, electionVotes >>

TermAt(l, i) == IF i = 0 THEN 0 ELSE IF i <= Len(l) THEN l[i].term ELSE 0
LastIndexOf(n) == Len(log[n])
LastTermOf(n) == TermAt(log[n], LastIndexOf(n))
UpToDate(ci, ct, l) == ct > TermAt(l, Len(l)) \/ (ct = TermAt(l, Len(l)) /\ ci >= Len(l))
Majority(S) == Cardinality(S) > Cardinality(NODES) / 2

PrevOK(n, pi, pt) == TermAt(log[n], pi) = pt

SetMatch(l, f, v) ==
  [matchIndex EXCEPT ![l][f] = v]

CommitCandidate(l, i) ==
  /\ i \in 0..LastIndexOf(l)
  /\ TermAt(log[l], i) = term[l]
  /\ Majority({ n \in NODES: matchIndex[l][n] >= i })

MaxCommit(l) ==
  CHOOSE i \in { j \in 0..LastIndexOf(l) : CommitCandidate(l, j) }:
    \A k \in { j \in 0..LastIndexOf(l) : CommitCandidate(l, j) }: i >= k
  \* If the set is empty, CHOOSE yields an arbitrary value; guard usage with conditional.
HasCommitCandidate(l) == \E j \in 0..LastIndexOf(l): CommitCandidate(l, j)

Init ==
  /\ state = [n \in NODES |-> StateFollower]
  /\ term = [n \in NODES |-> 0]
  /\ votedFor = [n \in NODES |-> None]
  /\ log = [n \in NODES |-> <<>>]
  /\ commit = [n \in NODES |-> 0]
  /\ electionElapsed = [n \in NODES |-> 0]
  /\ heartbeatElapsed = [n \in NODES |-> 0]
  /\ leader = None
  /\ msgs = {}
  /\ matchIndex = [l \in NODES |-> [n \in NODES |-> 0]]
  /\ electionPhase = [n \in NODES |-> "none"]
  /\ electionVotes = [n \in NODES |-> {}]

Enqueue(ms) ==
  msgs' = msgs \cup ms

DequeueOne(m) ==
  /\ m \in msgs
  /\ msgs' = msgs \ { m }

BumpToFollowerIfHigherTerm(n, m) ==
  IF m.term > term[n] /\ ~(m.type \in {MsgPreVote, MsgPreVoteResp})
  THEN /\ term' = [term EXCEPT ![n] = m.term]
       /\ state' = [state EXCEPT ![n] = StateFollower]
       /\ votedFor' = [votedFor EXCEPT ![n] = None]
  ELSE /\ term' = term
       /\ state' = state
       /\ votedFor' = votedFor

TickElection ==
  \E n \in NODES:
    /\ UNCHANGED << state, term, votedFor, log, commit, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = @ + 1]
    /\ IF state[n] # StateLeader /\ electionElapsed'[n] >= ELECTION_TIMEOUT
       THEN /\ electionElapsed' = [electionElapsed' EXCEPT ![n] = 0]
            /\ Enqueue({ [type |-> MsgHup,
                          from |-> n,
                          to |-> n,
                          term |-> term[n],
                          prevIndex |-> 0,
                          prevTerm |-> 0,
                          entries |-> <<>>,
                          leaderCommit |-> 0,
                          granted |-> FALSE,
                          index |-> 0,
                          reject |-> FALSE,
                          candIndex |-> 0,
                          candTerm |-> 0] })
       ELSE /\ UNCHANGED msgs

TickHeartbeat ==
  \E n \in NODES:
    /\ state[n] = StateLeader
    /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, leader, matchIndex, electionPhase, electionVotes >>
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = @ + 1]
    /\ IF heartbeatElapsed'[n] >= HEARTBEAT_TIMEOUT
       THEN /\ heartbeatElapsed' = [heartbeatElapsed' EXCEPT ![n] = 0]
            /\ Enqueue({ [type |-> MsgHeartbeat,
                          from |-> n,
                          to |-> d,
                          term |-> term[n],
                          prevIndex |-> 0,
                          prevTerm |-> 0,
                          entries |-> <<>>,
                          leaderCommit |-> commit[n],
                          granted |-> FALSE,
                          index |-> 0,
                          reject |-> FALSE,
                          candIndex |-> 0,
                          candTerm |-> 0] : d \in NODES \ {n} })
       ELSE /\ UNCHANGED msgs

ClientSendProp ==
  \E n \in NODES:
    /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
    /\ Enqueue({ [type |-> MsgProp,
                  from |-> n,
                  to |-> n,
                  term |-> term[n],
                  prevIndex |-> 0,
                  prevTerm |-> 0,
                  entries |-> <<>>,
                  leaderCommit |-> 0,
                  granted |-> FALSE,
                  index |-> 0,
                  reject |-> FALSE,
                  candIndex |-> 0,
                  candTerm |-> 0] })

DeliverProp ==
  \E m \in msgs:
    /\ m.type = MsgProp
    /\ DequeueOne(m)
    /\ IF state[m.to] = StateLeader
       THEN LET l == m.to IN
            /\ log' = [log EXCEPT ![l] = Append(@, [term |-> term[l], data |-> CHOOSE c \in CMD: TRUE])]
            /\ matchIndex' = [matchIndex EXCEPT ![l][l] = Len(log'[l])]
            /\ UNCHANGED << state, term, votedFor, commit, electionElapsed, heartbeatElapsed, leader, electionPhase, electionVotes >>
            /\ Enqueue({ [type |-> MsgApp,
                          from |-> l,
                          to |-> f,
                          term |-> term[l],
                          prevIndex |-> matchIndex[l][f],
                          prevTerm |-> TermAt(log[l], matchIndex[l][f]),
                          entries |-> SubSeq(log'[l], matchIndex[l][f] + 1, Len(log'[l])),
                          leaderCommit |-> commit[l],
                          granted |-> FALSE,
                          index |-> 0,
                          reject |-> FALSE,
                          candIndex |-> 0,
                          candTerm |-> 0] : f \in NODES \ {l} })
       ELSE /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes, msgs >>

DeliverHup ==
  \E m \in msgs:
    /\ m.type = MsgHup
    /\ DequeueOne(m)
    /\ LET n == m.to IN
       /\ IF state[n] = StateLeader
          THEN /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes, msgs >>
          ELSE /\ state' = [state EXCEPT ![n] = StatePreCandidate]
               /\ electionPhase' = [electionPhase EXCEPT ![n] = "pre"]
               /\ electionVotes' = [electionVotes EXCEPT ![n] = {n}]
               /\ UNCHANGED << term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex >>
               /\ Enqueue({ [type |-> MsgPreVote,
                             from |-> n,
                             to |-> d,
                             term |-> term[n] + 1,
                             prevIndex |-> 0,
                             prevTerm |-> 0,
                             entries |-> <<>>,
                             leaderCommit |-> 0,
                             granted |-> FALSE,
                             index |-> 0,
                             reject |-> FALSE,
                             candIndex |-> LastIndexOf(n),
                             candTerm |-> LastTermOf(n)] : d \in NODES })

DeliverPreVote ==
  \E m \in msgs:
    /\ m.type = MsgPreVote
    /\ DequeueOne(m)
    /\ LET r == m.to IN
       /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
       /\ Enqueue({ [type |-> MsgPreVoteResp,
                     from |-> r,
                     to |-> m.from,
                     term |-> m.term,
                     prevIndex |-> 0,
                     prevTerm |-> 0,
                     entries |-> <<>>,
                     leaderCommit |-> 0,
                     granted |-> UpToDate(m.candIndex, m.candTerm, log[r]),
                     index |-> 0,
                     reject |-> FALSE,
                     candIndex |-> 0,
                     candTerm |-> 0] })

DeliverPreVoteResp ==
  \E m \in msgs:
    /\ m.type = MsgPreVoteResp
    /\ DequeueOne(m)
    /\ LET n == m.to IN
       /\ UNCHANGED << term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex >>
       /\ IF state[n] = StatePreCandidate /\ electionPhase[n] = "pre" /\ m.granted
          THEN /\ electionVotes' = [electionVotes EXCEPT ![n] = @ \cup {m.from}]
               /\ electionPhase' = electionPhase
               /\ IF Majority(electionVotes'[n])
                  THEN /\ state' = [state EXCEPT ![n] = StateCandidate]
                       /\ term' = [term EXCEPT ![n] = @ + 1]
                       /\ votedFor' = [votedFor EXCEPT ![n] = n]
                       /\ electionPhase' = [electionPhase' EXCEPT ![n] = "election"]
                       /\ electionVotes' = [electionVotes' EXCEPT ![n] = {n}]
                       /\ Enqueue({ [type |-> MsgVote,
                                     from |-> n,
                                     to |-> d,
                                     term |-> term'[n],
                                     prevIndex |-> 0,
                                     prevTerm |-> 0,
                                     entries |-> <<>>,
                                     leaderCommit |-> 0,
                                     granted |-> FALSE,
                                     index |-> 0,
                                     reject |-> FALSE,
                                     candIndex |-> LastIndexOf(n),
                                     candTerm |-> LastTermOf(n)] : d \in NODES })
                  ELSE /\ UNCHANGED << state, term, votedFor, msgs, electionPhase >>
          ELSE /\ UNCHANGED << state, term, votedFor, electionVotes, electionPhase, msgs >>

DeliverVote ==
  \E m \in msgs:
    /\ m.type = MsgVote
    /\ DequeueOne(m)
    /\ LET r == m.to IN
       /\ BumpToFollowerIfHigherTerm(r, m)
       /\ IF m.term < term'[r]
          THEN /\ UNCHANGED << state', votedFor', log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
               /\ Enqueue({ [type |-> MsgVoteResp,
                             from |-> r,
                             to |-> m.from,
                             term |-> term'[r],
                             prevIndex |-> 0,
                             prevTerm |-> 0,
                             entries |-> <<>>,
                             leaderCommit |-> 0,
                             granted |-> FALSE,
                             index |-> 0,
                             reject |-> FALSE,
                             candIndex |-> 0,
                             candTerm |-> 0] })
          ELSE
            LET canGrant ==
                  (votedFor'[r] = None \/ votedFor'[r] = m.from)
                  /\ UpToDate(m.candIndex, m.candTerm, log[r])
            IN
            /\ votedFor'' == [votedFor' EXCEPT ![r] = IF canGrant THEN m.from ELSE @]
            /\ state'' == state'
            /\ term'' == term'
            /\ UNCHANGED << log, commit, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
            /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
            /\ state = state''
            /\ term = term''
            /\ votedFor = votedFor''
            /\ Enqueue({ [type |-> MsgVoteResp,
                          from |-> r,
                          to |-> m.from,
                          term |-> term[r],
                          prevIndex |-> 0,
                          prevTerm |-> 0,
                          entries |-> <<>>,
                          leaderCommit |-> 0,
                          granted |-> canGrant,
                          index |-> 0,
                          reject |-> FALSE,
                          candIndex |-> 0,
                          candTerm |-> 0] })

DeliverVoteResp ==
  \E m \in msgs:
    /\ m.type = MsgVoteResp
    /\ DequeueOne(m)
    /\ LET n == m.to IN
       /\ IF state[n] = StateCandidate /\ m.term = term[n]
          THEN /\ UNCHANGED << term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase >>
               /\ electionVotes' = [electionVotes EXCEPT ![n] = @ \cup (IF m.granted THEN {m.from} ELSE {})]
               /\ IF Majority(electionVotes'[n])
                  THEN /\ state' = [state EXCEPT ![n] = StateLeader]
                       /\ leader' = n
                       /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
                       /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in NODES |-> IF p = n THEN LastIndexOf(n) ELSE 0]]
                       /\ Enqueue({ [type |-> MsgHeartbeat,
                                     from |-> n,
                                     to |-> d,
                                     term |-> term[n],
                                     prevIndex |-> 0,
                                     prevTerm |-> 0,
                                     entries |-> <<>>,
                                     leaderCommit |-> commit[n],
                                     granted |-> FALSE,
                                     index |-> 0,
                                     reject |-> FALSE,
                                     candIndex |-> 0,
                                     candTerm |-> 0] : d \in NODES \ {n} })
                  ELSE /\ UNCHANGED << state, leader, heartbeatElapsed, matchIndex, msgs >>
          ELSE /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, msgs, matchIndex, electionPhase, electionVotes >>

DeliverApp ==
  \E m \in msgs:
    /\ m.type = MsgApp
    /\ DequeueOne(m)
    /\ LET r == m.to IN
       /\ BumpToFollowerIfHigherTerm(r, m)
       /\ IF m.term < term'[r]
          THEN /\ UNCHANGED << state', votedFor', log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
               /\ Enqueue({ [type |-> MsgAppResp,
                             from |-> r,
                             to |-> m.from,
                             term |-> term'[r],
                             prevIndex |-> 0,
                             prevTerm |-> 0,
                             entries |-> <<>>,
                             leaderCommit |-> 0,
                             granted |-> FALSE,
                             index |-> LastIndexOf(r),
                             reject |-> TRUE,
                             candIndex |-> 0,
                             candTerm |-> 0] })
          ELSE
            IF PrevOK(r, m.prevIndex, m.prevTerm)
            THEN
              LET newLog == SubSeq(log[r], 1, m.prevIndex) \o m.entries IN
              /\ log' = [log EXCEPT ![r] = newLog]
              /\ commit' = [commit EXCEPT ![r] = Min(m.leaderCommit, Len(newLog))]
              /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
              /\ UNCHANGED << state', votedFor', heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
              /\ state = state'
              /\ votedFor = votedFor'
              /\ Enqueue({ [type |-> MsgAppResp,
                            from |-> r,
                            to |-> m.from,
                            term |-> term'[r],
                            prevIndex |-> 0,
                            prevTerm |-> 0,
                            entries |-> <<>>,
                            leaderCommit |-> 0,
                            granted |-> TRUE,
                            index |-> Len(newLog),
                            reject |-> FALSE,
                            candIndex |-> 0,
                            candTerm |-> 0] })
            ELSE
              /\ UNCHANGED << state', votedFor', log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
              /\ state = state'
              /\ votedFor = votedFor'
              /\ Enqueue({ [type |-> MsgAppResp,
                            from |-> r,
                            to |-> m.from,
                            term |-> term'[r],
                            prevIndex |-> 0,
                            prevTerm |-> 0,
                            entries |-> <<>>,
                            leaderCommit |-> 0,
                            granted |-> FALSE,
                            index |-> LastIndexOf(r),
                            reject |-> TRUE,
                            candIndex |-> 0,
                            candTerm |-> 0] })

DeliverAppResp ==
  \E m \in msgs:
    /\ m.type = MsgAppResp
    /\ DequeueOne(m)
    /\ LET l == m.to IN
       /\ IF state[l] = StateLeader
          THEN
            /\ IF m.term > term[l]
               THEN /\ state' = [state EXCEPT ![l] = StateFollower]
                    /\ term' = [term EXCEPT ![l] = m.term]
                    /\ votedFor' = [votedFor EXCEPT ![l] = None]
                    /\ leader' = None
                    /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, msgs, matchIndex, electionPhase, electionVotes >>
               ELSE
                 /\ UNCHANGED << state, term, votedFor, log, electionElapsed, heartbeatElapsed, leader, msgs, electionPhase, electionVotes >>
                 /\ IF m.reject = FALSE
                    THEN /\ matchIndex' = SetMatch(l, m.from, Max(matchIndex[l][m.from], m.index))
                         /\ commit' =
                              [commit EXCEPT ![l] =
                                IF HasCommitCandidate(l) THEN Max(commit[l], MaxCommit(l)) ELSE commit[l]]
                    ELSE /\ UNCHANGED << matchIndex, commit >>
          ELSE /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, msgs, matchIndex, electionPhase, electionVotes >>

DeliverHeartbeat ==
  \E m \in msgs:
    /\ m.type = MsgHeartbeat
    /\ DequeueOne(m)
    /\ LET r == m.to IN
       /\ BumpToFollowerIfHigherTerm(r, m)
       /\ IF m.term < term'[r]
          THEN /\ UNCHANGED << state', votedFor', log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes, msgs >>
          ELSE /\ commit' = [commit EXCEPT ![r] = Min(m.leaderCommit, Len(log[r]))]
               /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
               /\ UNCHANGED << state', votedFor', log, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes, msgs >>
               /\ state = state'
               /\ votedFor = votedFor'

DropMsg ==
  \E m \in msgs:
    /\ DequeueOne(m)
    /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

Next ==
  \/ TickElection
  \/ TickHeartbeat
  \/ ClientSendProp
  \/ DeliverProp
  \/ DeliverHup
  \/ DeliverPreVote
  \/ DeliverPreVoteResp
  \/ DeliverVote
  \/ DeliverVoteResp
  \/ DeliverApp
  \/ DeliverAppResp
  \/ DeliverHeartbeat
  \/ DropMsg

Spec ==
  Init /\ [][Next]_Vars

====