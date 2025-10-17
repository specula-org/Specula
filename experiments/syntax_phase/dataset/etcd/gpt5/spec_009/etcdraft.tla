---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

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
Majority(S) == 2 * Cardinality(S) > Cardinality(NODES)

PrevOK(n, pi, pt) == TermAt(log[n], pi) = pt

SetMatch(l, f, v) ==
  [matchIndex EXCEPT ![l][f] = v]

CommitCandidate(l, i) ==
  /\ i \in 0..LastIndexOf(l)
  /\ TermAt(log[l], i) = term[l]
  /\ Majority({ n \in NODES: matchIndex[l][n] >= i })

Max2(a, b) == IF a >= b THEN a ELSE b
Min2(a, b) == IF a <= b THEN a ELSE b

MaxCommit(l) ==
  LET S == { j \in 0..LastIndexOf(l) : CommitCandidate(l, j) } IN
    CHOOSE i \in S : \A k \in S : i >= k

HasCommitCandidate(l) == \E j \in 0..LastIndexOf(l) : CommitCandidate(l, j)

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

TickElection ==
  \E n \in NODES:
    LET ee1 == [electionElapsed EXCEPT ![n] = @ + 1] IN
    LET timeout == state[n] # StateLeader /\ ee1[n] >= ELECTION_TIMEOUT IN
    /\ electionElapsed' = IF timeout THEN [ee1 EXCEPT ![n] = 0] ELSE ee1
    /\ msgs' =
        IF timeout
        THEN msgs \cup {
              [ type |-> MsgHup,
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
                candTerm |-> 0 ]
            }
        ELSE msgs
    /\ UNCHANGED << state, term, votedFor, log, commit, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

TickHeartbeat ==
  \E n \in NODES:
    /\ state[n] = StateLeader
    LET hb1 == [heartbeatElapsed EXCEPT ![n] = @ + 1] IN
    LET timeout == hb1[n] >= HEARTBEAT_TIMEOUT IN
    /\ heartbeatElapsed' = IF timeout THEN [hb1 EXCEPT ![n] = 0] ELSE hb1
    /\ msgs' =
        IF timeout
        THEN msgs \cup {
              [ type |-> MsgHeartbeat,
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
                candTerm |-> 0 ] : d \in NODES \ {n}
            }
        ELSE msgs
    /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, leader, matchIndex, electionPhase, electionVotes >>

ClientSendProp ==
  \E n \in NODES:
    /\ msgs' = msgs \cup {
         [ type |-> MsgProp,
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
           candTerm |-> 0 ]
       }
    /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

DeliverProp ==
  \E m \in msgs:
    /\ m.type = MsgProp
    /\ state[m.to] = StateLeader
    /\ LET l == m.to IN
       /\ log' = [log EXCEPT ![l] = Append(@, [term |-> term[l], data |-> CHOOSE c \in CMD: TRUE])]
       /\ matchIndex' = [matchIndex EXCEPT ![l][l] = Len(log'[l])]
       /\ msgs' = (msgs \ {m}) \cup {
             [ type |-> MsgApp,
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
               candTerm |-> 0 ] : f \in NODES \ {l}
           }
       /\ UNCHANGED << state, term, votedFor, commit, electionElapsed, heartbeatElapsed, leader, electionPhase, electionVotes >>

DeliverHup ==
  \E m \in msgs:
    /\ m.type = MsgHup
    /\ state[m.to] # StateLeader
    /\ LET n == m.to IN
       /\ state' = [state EXCEPT ![n] = StatePreCandidate]
       /\ electionPhase' = [electionPhase EXCEPT ![n] = "pre"]
       /\ electionVotes' = [electionVotes EXCEPT ![n] = {n}]
       /\ msgs' = (msgs \ {m}) \cup {
             [ type |-> MsgPreVote,
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
               candTerm |-> LastTermOf(n) ] : d \in NODES
           }
       /\ UNCHANGED << term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex >>

DeliverPreVote ==
  \E m \in msgs:
    /\ m.type = MsgPreVote
    /\ LET r == m.to IN
       /\ msgs' = (msgs \ {m}) \cup {
             [ type |-> MsgPreVoteResp,
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
               candTerm |-> 0 ]
           }
       /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

DeliverPreVoteResp ==
  \E m \in msgs:
    /\ m.type = MsgPreVoteResp
    /\ LET n == m.to IN
       /\ IF state[n] = StatePreCandidate /\ electionPhase[n] = "pre" /\ m.granted
          THEN
            LET votes1 == electionVotes[n] \cup {m.from} IN
            IF Majority(votes1)
            THEN
              /\ state' = [state EXCEPT ![n] = StateCandidate]
              /\ term' = [term EXCEPT ![n] = @ + 1]
              /\ votedFor' = [votedFor EXCEPT ![n] = n]
              /\ electionPhase' = [electionPhase EXCEPT ![n] = "election"]
              /\ electionVotes' = [electionVotes EXCEPT ![n] = {n}]
              /\ msgs' = (msgs \ {m}) \cup {
                     [ type |-> MsgVote,
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
                       candTerm |-> LastTermOf(n) ] : d \in NODES
                 }
              /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex >>
            ELSE
              /\ electionVotes' = [electionVotes EXCEPT ![n] = votes1]
              /\ msgs' = msgs \ {m}
              /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase >>
          ELSE
            /\ msgs' = msgs \ {m}
            /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

DeliverVote ==
  \E m \in msgs:
    /\ m.type = MsgVote
    /\ LET r == m.to IN
       LET higher == (m.term > term[r]) /\ ~(m.type \in {MsgPreVote, MsgPreVoteResp}) IN
       LET term1 == IF higher THEN [term EXCEPT ![r] = m.term] ELSE term IN
       LET state1 == IF higher THEN [state EXCEPT ![r] = StateFollower] ELSE state IN
       LET voted1 == IF higher THEN [votedFor EXCEPT ![r] = None] ELSE votedFor IN
       /\ IF m.term < term1[r]
          THEN
            /\ term' = term1
            /\ state' = state1
            /\ votedFor' = voted1
            /\ msgs' = (msgs \ {m}) \cup {
                 [ type |-> MsgVoteResp,
                   from |-> r,
                   to |-> m.from,
                   term |-> term1[r],
                   prevIndex |-> 0,
                   prevTerm |-> 0,
                   entries |-> <<>>,
                   leaderCommit |-> 0,
                   granted |-> FALSE,
                   index |-> 0,
                   reject |-> FALSE,
                   candIndex |-> 0,
                   candTerm |-> 0 ]
               }
            /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
          ELSE
            LET canGrant ==
                  (voted1[r] = None \/ voted1[r] = m.from)
                  /\ UpToDate(m.candIndex, m.candTerm, log[r])
            IN
            /\ term' = term1
            /\ state' = state1
            /\ votedFor' = [voted1 EXCEPT ![r] = IF canGrant THEN m.from ELSE @]
            /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
            /\ msgs' = (msgs \ {m}) \cup {
                 [ type |-> MsgVoteResp,
                   from |-> r,
                   to |-> m.from,
                   term |-> term'[r],
                   prevIndex |-> 0,
                   prevTerm |-> 0,
                   entries |-> <<>>,
                   leaderCommit |-> 0,
                   granted |-> canGrant,
                   index |-> 0,
                   reject |-> FALSE,
                   candIndex |-> 0,
                   candTerm |-> 0 ]
               }
            /\ UNCHANGED << log, commit, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

DeliverVoteResp ==
  \E m \in msgs:
    /\ m.type = MsgVoteResp
    /\ LET n == m.to IN
       /\ state[n] = StateCandidate
       /\ m.term = term[n]
       LET votes1 == electionVotes[n] \cup (IF m.granted THEN {m.from} ELSE {}) IN
       /\ electionVotes' = [electionVotes EXCEPT ![n] = votes1]
       /\ IF Majority(votes1)
          THEN
            /\ state' = [state EXCEPT ![n] = StateLeader]
            /\ leader' = n
            /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
            /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in NODES |-> IF p = n THEN LastIndexOf(n) ELSE 0]]
            /\ msgs' = (msgs \ {m}) \cup {
                  [ type |-> MsgHeartbeat,
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
                    candTerm |-> 0 ] : d \in NODES \ {n}
               }
            /\ UNCHANGED << term, votedFor, log, commit, electionElapsed, electionPhase >>
          ELSE
            /\ msgs' = msgs \ {m}
            /\ UNCHANGED << state, leader, heartbeatElapsed, matchIndex, term, votedFor, log, commit, electionElapsed, electionPhase >>

DeliverApp ==
  \E m \in msgs:
    /\ m.type = MsgApp
    /\ LET r == m.to IN
       LET higher == (m.term > term[r]) /\ ~(m.type \in {MsgPreVote, MsgPreVoteResp}) IN
       LET term1 == IF higher THEN [term EXCEPT ![r] = m.term] ELSE term IN
       LET state1 == IF higher THEN [state EXCEPT ![r] = StateFollower] ELSE state IN
       LET voted1 == IF higher THEN [votedFor EXCEPT ![r] = None] ELSE votedFor IN
       /\ IF m.term < term1[r]
          THEN
            /\ term' = term1
            /\ state' = state1
            /\ votedFor' = voted1
            /\ msgs' = (msgs \ {m}) \cup {
                 [ type |-> MsgAppResp,
                   from |-> r,
                   to |-> m.from,
                   term |-> term1[r],
                   prevIndex |-> 0,
                   prevTerm |-> 0,
                   entries |-> <<>>,
                   leaderCommit |-> 0,
                   granted |-> FALSE,
                   index |-> LastIndexOf(r),
                   reject |-> TRUE,
                   candIndex |-> 0,
                   candTerm |-> 0 ]
               }
            /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
          ELSE
            IF PrevOK(r, m.prevIndex, m.prevTerm)
            THEN
              LET newLog == SubSeq(log[r], 1, m.prevIndex) \o m.entries IN
              /\ log' = [log EXCEPT ![r] = newLog]
              /\ commit' = [commit EXCEPT ![r] = Min2(m.leaderCommit, Len(newLog))]
              /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
              /\ term' = term1
              /\ state' = state1
              /\ votedFor' = voted1
              /\ msgs' = (msgs \ {m}) \cup {
                   [ type |-> MsgAppResp,
                     from |-> r,
                     to |-> m.from,
                     term |-> term1[r],
                     prevIndex |-> 0,
                     prevTerm |-> 0,
                     entries |-> <<>>,
                     leaderCommit |-> 0,
                     granted |-> TRUE,
                     index |-> Len(newLog),
                     reject |-> FALSE,
                     candIndex |-> 0,
                     candTerm |-> 0 ]
                 }
              /\ UNCHANGED << heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
            ELSE
              /\ term' = term1
              /\ state' = state1
              /\ votedFor' = voted1
              /\ msgs' = (msgs \ {m}) \cup {
                   [ type |-> MsgAppResp,
                     from |-> r,
                     to |-> m.from,
                     term |-> term1[r],
                     prevIndex |-> 0,
                     prevTerm |-> 0,
                     entries |-> <<>>,
                     leaderCommit |-> 0,
                     granted |-> FALSE,
                     index |-> LastIndexOf(r),
                     reject |-> TRUE,
                     candIndex |-> 0,
                     candTerm |-> 0 ]
                 }
              /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>

DeliverAppResp ==
  \E m \in msgs:
    /\ m.type = MsgAppResp
    /\ LET l == m.to IN
       /\ IF state[l] = StateLeader
          THEN
            IF m.term > term[l]
            THEN
              /\ state' = [state EXCEPT ![l] = StateFollower]
              /\ term' = [term EXCEPT ![l] = m.term]
              /\ votedFor' = [votedFor EXCEPT ![l] = None]
              /\ leader' = None
              /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, matchIndex, electionPhase, electionVotes >>
            ELSE
              /\ UNCHANGED << state, term, votedFor, log, electionElapsed, heartbeatElapsed, leader, electionPhase, electionVotes >>
              /\ IF m.reject = FALSE
                 THEN
                   /\ matchIndex' = SetMatch(l, m.from, Max2(matchIndex[l][m.from], m.index))
                   /\ commit' =
                        [commit EXCEPT ![l] =
                          IF HasCommitCandidate(l) THEN Max2(commit[l], MaxCommit(l)) ELSE commit[l]]
                 ELSE
                   /\ UNCHANGED commit
          ELSE
            /\ UNCHANGED << state, term, votedFor, log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
       /\ msgs' = msgs \ {m}

DeliverHeartbeat ==
  \E m \in msgs:
    /\ m.type = MsgHeartbeat
    /\ LET r == m.to IN
       LET higher == (m.term > term[r]) /\ ~(m.type \in {MsgPreVote, MsgPreVoteResp}) IN
       LET term1 == IF higher THEN [term EXCEPT ![r] = m.term] ELSE term IN
       LET state1 == IF higher THEN [state EXCEPT ![r] = StateFollower] ELSE state IN
       LET voted1 == IF higher THEN [votedFor EXCEPT ![r] = None] ELSE votedFor IN
       /\ IF m.term < term1[r]
          THEN
            /\ term' = term1
            /\ state' = state1
            /\ votedFor' = voted1
            /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
          ELSE
            /\ commit' = [commit EXCEPT ![r] = Min2(m.leaderCommit, Len(log[r]))]
            /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
            /\ term' = term1
            /\ state' = state1
            /\ votedFor' = voted1
            /\ UNCHANGED << log, heartbeatElapsed, leader, matchIndex, electionPhase, electionVotes >>
       /\ msgs' = msgs \ {m}

DropMsg ==
  \E m \in msgs:
    /\ msgs' = msgs \ {m}
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