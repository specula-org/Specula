---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
  Nodes,
  Data,
  NIL,
  ELECTION_TIMEOUT,
  HEARTBEAT_TIMEOUT

ASSUME NIL \notin Nodes

MsgType == {"Hup","PreVote","PreVoteResp","Vote","VoteResp","App","AppResp","Prop"}

Entry == [term: Nat, data: Data]

Message ==
  [ mtype: MsgType,
    from: Nodes,
    to: Nodes,
    term: Nat,
    index: Nat,
    logterm: Nat,
    entries: Seq(Entry),
    commit: Nat,
    success: BOOLEAN
  ]

Majority == Cardinality(Nodes) \div 2 + 1
Maj(S) == Cardinality(S) >= Majority

LastIndex(l) == Len(l)
LastTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
TermAt(l,i) == IF i = 0 THEN 0 ELSE IF i <= Len(l) THEN l[i].term ELSE 0

UpToDateBy(candTerm, candIdx, myLog) ==
  candTerm > LastTerm(myLog)
  \/ (candTerm = LastTerm(myLog) /\ candIdx >= LastIndex(myLog))

UpToDate(cand, me) ==
  UpToDateBy(LastTerm(log[cand]), LastIndex(log[cand]), log[me])

FirstConflict(l, pidx, ents) ==
  LET S == { i \in 1..Len(ents) :
               pidx + i <= Len(l) /\ l[pidx + i].term # ents[i].term }
  IN IF S = {} THEN 0 ELSE Min(S)

ApplyAppend(l, prevIdx, prevTerm, ents) ==
  IF prevIdx > Len(l) \/ TermAt(l, prevIdx) # prevTerm
  THEN [ok |-> FALSE, newlog |-> l, lastidx |-> Len(l)]
  ELSE
    LET j == FirstConflict(l, prevIdx, ents) IN
    IF Len(ents) = 0
    THEN [ok |-> TRUE, newlog |-> l, lastidx |-> Len(l)]
    ELSE
      IF j = 0
      THEN
        LET need == IF prevIdx + Len(ents) <= Len(l) THEN 0 ELSE (prevIdx + Len(ents) - Len(l))
            appended == IF need = 0 THEN << >> ELSE SubSeq(ents, Len(ents) - need + 1, Len(ents))
            nl == l \o appended
        IN [ok |-> TRUE, newlog |-> nl, lastidx |-> Len(nl)]
      ELSE
        LET nl == SubSeq(l, 1, prevIdx + j - 1) \o SubSeq(ents, j, Len(ents))
        IN [ok |-> TRUE, newlog |-> nl, lastidx |-> Len(nl)]

VARIABLES
  state,           \* [n \in Nodes |-> "Follower"|"Candidate"|"Leader"|"PreCandidate"]
  term,            \* [n \in Nodes |-> Nat]
  votedFor,        \* [n \in Nodes |-> Nodes \cup {NIL}]
  log,             \* [n \in Nodes |-> Seq(Entry)]
  commitIndex,     \* [n \in Nodes |-> Nat]
  electionElapsed, \* [n \in Nodes |-> Nat]
  heartbeatElapsed,\* [n \in Nodes |-> Nat]
  preVotesGranted, \* [n \in Nodes |-> SUBSET Nodes]
  votesGranted,    \* [n \in Nodes |-> SUBSET Nodes]
  electionKind,    \* [n \in Nodes |-> {"none","pre","election"}]
  nextIndex,       \* [ldr \in Nodes |-> [n \in Nodes |-> Nat]]
  matchIndex,      \* [ldr \in Nodes |-> [n \in Nodes |-> Nat]]
  Net              \* SUBSET Message

TypeOK ==
  /\ state \in [Nodes -> {"Follower","Candidate","Leader","PreCandidate"}]
  /\ term \in [Nodes -> Nat]
  /\ votedFor \in [Nodes -> Nodes \cup {NIL}]
  /\ log \in [Nodes -> Seq(Entry)]
  /\ commitIndex \in [Nodes -> Nat]
  /\ electionElapsed \in [Nodes -> Nat]
  /\ heartbeatElapsed \in [Nodes -> Nat]
  /\ preVotesGranted \in [Nodes -> SUBSET Nodes]
  /\ votesGranted \in [Nodes -> SUBSET Nodes]
  /\ electionKind \in [Nodes -> {"none","pre","election"}]
  /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
  /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
  /\ Net \subseteq Message

Init ==
  /\ state = [n \in Nodes |-> "Follower"]
  /\ term = [n \in Nodes |-> 0]
  /\ votedFor = [n \in Nodes |-> NIL]
  /\ log = [n \in Nodes |-> << >>]
  /\ commitIndex = [n \in Nodes |-> 0]
  /\ electionElapsed = [n \in Nodes |-> 0]
  /\ heartbeatElapsed = [n \in Nodes |-> 0]
  /\ preVotesGranted = [n \in Nodes |-> {}]
  /\ votesGranted = [n \in Nodes |-> {}]
  /\ electionKind = [n \in Nodes |-> "none"]
  /\ nextIndex = [ldr \in Nodes |-> [n \in Nodes |-> 1]]
  /\ matchIndex = [ldr \in Nodes |-> [n \in Nodes |-> 0]]
  /\ Net = {}

MsgHupAction ==
  \E n \in Nodes:
    /\ electionElapsed[n] >= ELECTION_TIMEOUT
    /\ state[n] # "Leader"
    /\ Net' = Net \cup {
         [ mtype |-> "Hup", from |-> n, to |-> n, term |-> term[n],
           index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commitIndex[n], success |-> FALSE ]
       }
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED << state, term, votedFor, log, commitIndex, heartbeatElapsed,
                    preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

TickAction ==
  \E n \in Nodes:
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
    /\ heartbeatElapsed' = heartbeatElapsed
    /\ UNCHANGED << state, term, votedFor, log, commitIndex,
                    preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex, Net >>

BeatAction ==
  \E l \in Nodes:
    /\ state[l] = "Leader"
    /\ heartbeatElapsed[l] >= HEARTBEAT_TIMEOUT
    /\ LET msgs ==
         { [ mtype |-> "App", from |-> l, to |-> p, term |-> term[l],
             index |-> nextIndex[l][p] - 1,
             logterm |-> TermAt(log[l], nextIndex[l][p] - 1),
             entries |-> << >>, commit |-> commitIndex[l], success |-> FALSE ]
           : p \in (Nodes \ {l}) }
       IN /\ Net' = Net \cup msgs
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![l] = 0]
    /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed,
                    preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

ProposeAction ==
  \E l \in Nodes, d \in Data:
    /\ state[l] = "Leader"
    /\ Net' = Net \cup {
         [ mtype |-> "Prop", from |-> l, to |-> l, term |-> term[l],
           index |-> 0, logterm |-> 0,
           entries |-> << [term |-> 0, data |-> d] >>,
           commit |-> commitIndex[l], success |-> FALSE ]
       }
    /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                    preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DropAction ==
  \E m \in Net:
    /\ Net' = Net \ {m}
    /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                    preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverHup ==
  \E m \in Net:
    /\ m.mtype = "Hup" /\ m.to = m.from
    /\ LET n == m.to IN
       /\ IF state[n] = "Leader"
          THEN /\ Net' = Net \ {m}
               /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                               preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>
          ELSE
             /\ state' = [state EXCEPT ![n] = "PreCandidate"]
             /\ electionKind' = [electionKind EXCEPT ![n] = "pre"]
             /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {n}]
             /\ votesGranted' = votesGranted
             /\ LET msgs ==
                  { [ mtype |-> "PreVote", from |-> n, to |-> p, term |-> term[n] + 1,
                      index |-> LastIndex(log[n]), logterm |-> LastTerm(log[n]),
                      entries |-> << >>, commit |-> commitIndex[n], success |-> FALSE ]
                    : p \in (Nodes \ {n}) }
                IN /\ Net' = (Net \ {m}) \cup msgs
             /\ UNCHANGED << term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                             nextIndex, matchIndex >>

DeliverPreVote ==
  \E m \in Net:
    /\ m.mtype = "PreVote"
    /\ LET n == m.to IN
       /\ Net' = (Net \ {m}) \cup {
            [ mtype |-> "PreVoteResp", from |-> n, to |-> m.from, term |-> m.term,
              index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commitIndex[n],
              success |-> UpToDateBy(m.logterm, m.index, log[n]) ]
          }
       /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                       preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverPreVoteResp ==
  \E m \in Net:
    /\ m.mtype = "PreVoteResp"
    /\ LET n == m.to IN
       /\ IF state[n] = "PreCandidate" /\ electionKind[n] = "pre"
          THEN
            LET granted == IF m.success THEN preVotesGranted[n] \cup {m.from} ELSE preVotesGranted[n] IN
            IF Maj(granted)
            THEN
              /\ state' = [state EXCEPT ![n] = "Candidate"]
              /\ term' = [term EXCEPT ![n] = term[n] + 1]
              /\ votedFor' = [votedFor EXCEPT ![n] = n]
              /\ electionKind' = [electionKind EXCEPT ![n] = "election"]
              /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {}]
              /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
              /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
              /\ LET msgs ==
                   { [ mtype |-> "Vote", from |-> n, to |-> p, term |-> term[n] + 1,
                       index |-> LastIndex(log[n]), logterm |-> LastTerm(log[n]),
                       entries |-> << >>, commit |-> commitIndex[n], success |-> FALSE ]
                     : p \in (Nodes \ {n}) }
                 IN /\ Net' = (Net \ {m}) \cup msgs
              /\ UNCHANGED << log, commitIndex, heartbeatElapsed, nextIndex, matchIndex >>
            ELSE
              /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = granted]
              /\ Net' = Net \ {m}
              /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                              votesGranted, electionKind, nextIndex, matchIndex >>
          ELSE
            /\ Net' = Net \ {m}
            /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                            preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverVote ==
  \E m \in Net:
    /\ m.mtype = "Vote"
    /\ LET n == m.to IN
       /\ LET newTerm == IF m.term > term[n] THEN m.term ELSE term[n] IN
          LET newState == IF m.term > term[n] THEN "Follower" ELSE state[n] IN
          LET newVoted == IF m.term > term[n] THEN NIL ELSE votedFor[n] IN
          LET can ==
            (newVoted = NIL \/ newVoted = m.from)
            /\ UpToDateBy(m.logterm, m.index, log[n])
          IN
          /\ term' = [term EXCEPT ![n] = newTerm]
          /\ state' = [state EXCEPT ![n] = newState]
          /\ votedFor' = [votedFor EXCEPT ![n] = IF can THEN m.from ELSE newVoted]
          /\ electionElapsed' = [electionElapsed EXCEPT ![n] = IF can THEN 0 ELSE electionElapsed[n]]
          /\ Net' = (Net \ {m}) \cup {
                [ mtype |-> "VoteResp", from |-> n, to |-> m.from, term |-> newTerm,
                  index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commitIndex[n],
                  success |-> can ]
              }
          /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverVoteResp ==
  \E m \in Net:
    /\ m.mtype = "VoteResp"
    /\ LET n == m.to IN
       /\ IF m.term > term[n]
          THEN
            /\ term' = [term EXCEPT ![n] = m.term]
            /\ state' = [state EXCEPT ![n] = "Follower"]
            /\ votedFor' = [votedFor EXCEPT ![n] = NIL]
            /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
            /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {}]
            /\ electionKind' = [electionKind EXCEPT ![n] = "none"]
            /\ Net' = Net \ {m}
            /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed, nextIndex, matchIndex >>
          ELSE IF state[n] = "Candidate" /\ m.term = term[n]
          THEN
            LET granted == IF m.success THEN votesGranted[n] \cup {m.from} ELSE votesGranted[n] IN
            IF Maj(granted)
            THEN
              /\ state' = [state EXCEPT ![n] = "Leader"]
              /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
              /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {}]
              /\ electionKind' = [electionKind EXCEPT ![n] = "none"]
              /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
              /\ LET newLogN == log[n] \o << [term |-> term[n], data |-> CHOOSE x \in Data : TRUE] >>
                     newMatchIndexN == [p \in Nodes |-> IF p = n THEN Len(newLogN) ELSE matchIndex[n][p]]
                     newNextIndexN == [p \in Nodes |-> Len(newLogN) + 1]
                     msgs ==
                       { [ mtype |-> "App", from |-> n, to |-> p, term |-> term[n],
                           index |-> newNextIndexN[p] - 1,
                           logterm |-> TermAt(newLogN, newNextIndexN[p] - 1),
                           entries |-> SubSeq(newLogN, newNextIndexN[p], Len(newLogN)),
                           commit |-> commitIndex[n], success |-> FALSE ]
                         : p \in (Nodes \ {n}) }
                 IN
                 /\ log' = [log EXCEPT ![n] = newLogN]
                 /\ matchIndex' = [matchIndex EXCEPT ![n] = newMatchIndexN]
                 /\ nextIndex' = [nextIndex EXCEPT ![n] = newNextIndexN]
                 /\ Net' = (Net \ {m}) \cup msgs
              /\ UNCHANGED << term, votedFor, commitIndex, electionElapsed >>
            ELSE
              /\ votesGranted' = [votesGranted EXCEPT ![n] = granted]
              /\ Net' = Net \ {m}
              /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                              preVotesGranted, electionKind, nextIndex, matchIndex >>
          ELSE
            /\ Net' = Net \ {m}
            /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                            preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverProp ==
  \E m \in Net:
    /\ m.mtype = "Prop"
    /\ LET n == m.to IN
       /\ IF state[n] = "Leader"
          THEN
            /\ LET newLogN == log[n] \o << [term |-> term[n], data |-> m.entries[1].data] >>
                   newMatchIndexN == [p \in Nodes |-> IF p = n THEN Len(newLogN) ELSE matchIndex[n][p]]
                   newNextIndexN == [p \in Nodes |-> IF p = n THEN Len(newLogN) + 1 ELSE nextIndex[n][p]]
                   msgs ==
                     { [ mtype |-> "App", from |-> n, to |-> p, term |-> term[n],
                         index |-> newNextIndexN[p] - 1,
                         logterm |-> TermAt(newLogN, newNextIndexN[p] - 1),
                         entries |-> SubSeq(newLogN, newNextIndexN[p], Len(newLogN)),
                         commit |-> commitIndex[n], success |-> FALSE ]
                       : p \in (Nodes \ {n}) }
               IN
               /\ log' = [log EXCEPT ![n] = newLogN]
               /\ matchIndex' = [matchIndex EXCEPT ![n] = newMatchIndexN]
               /\ nextIndex' = [nextIndex EXCEPT ![n] = newNextIndexN]
               /\ Net' = (Net \ {m}) \cup msgs
            /\ UNCHANGED << state, term, votedFor, commitIndex, electionElapsed, heartbeatElapsed,
                            preVotesGranted, votesGranted, electionKind >>
          ELSE
            /\ Net' = Net \ {m}
            /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                            preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverApp ==
  \E m \in Net:
    /\ m.mtype = "App"
    /\ LET n == m.to IN
       /\ LET newTerm == IF m.term > term[n] THEN m.term ELSE term[n] IN
          LET newState == IF m.term > term[n] THEN "Follower" ELSE state[n] IN
          LET result == ApplyAppend(log[n], m.index, m.logterm, m.entries) IN
          /\ term' = [term EXCEPT ![n] = newTerm]
          /\ state' = [state EXCEPT ![n] = newState]
          /\ votedFor' = [votedFor EXCEPT ![n] = IF m.term > term[n] THEN NIL ELSE votedFor[n]]
          /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
          /\ log' = [log EXCEPT ![n] = result.newlog]
          /\ commitIndex' = [commitIndex EXCEPT ![n] = Min({m.commit, Len(result.newlog)})]
          /\ Net' = (Net \ {m}) \cup {
                [ mtype |-> "AppResp", from |-> n, to |-> m.from, term |-> newTerm,
                  index |-> IF result.ok THEN result.lastidx ELSE m.index,
                  logterm |-> 0, entries |-> << >>, commit |-> commitIndex'[n],
                  success |-> result.ok ]
              }
          /\ UNCHANGED << heartbeatElapsed, preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>

DeliverAppResp ==
  \E m \in Net:
    /\ m.mtype = "AppResp"
    /\ LET n == m.to IN
       /\ IF state[n] # "Leader"
          THEN /\ Net' = Net \ {m}
               /\ UNCHANGED << state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                               preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>
          ELSE
            IF m.term > term[n]
            THEN
              /\ term' = [term EXCEPT ![n] = m.term]
              /\ state' = [state EXCEPT ![n] = "Follower"]
              /\ votedFor' = [votedFor EXCEPT ![n] = NIL]
              /\ Net' = Net \ {m}
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed,
                              preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex >>
            ELSE
              /\ nextIndex' =
                   [nextIndex EXCEPT
                      ![n] =
                        [p \in Nodes |-> IF p = m.from
                                         THEN IF m.success THEN m.index + 1
                                              ELSE IF nextIndex[n][m.from] > 1 THEN nextIndex[n][m.from] - 1 ELSE 1
                                         ELSE nextIndex[n][p]]]
              /\ matchIndex' =
                   [matchIndex EXCEPT
                      ![n] =
                        [p \in Nodes |-> IF p = m.from
                                         THEN IF m.success THEN m.index ELSE matchIndex[n][p]
                                         ELSE matchIndex[n][p]]]
              /\ LET canCommit(k) ==
                     /\ k <= Len(log[n])
                     /\ TermAt(log[n], k) = term[n]
                     /\ Cardinality({ p \in Nodes : (IF p = n THEN Len(log[n]) ELSE matchIndex'[n][p]) >= k }) >= Majority
                 IN
                 LET Ks == { k \in 0..Len(log[n]) : canCommit(k) } IN
                 LET commitNew == IF Ks = {} THEN 0 ELSE Max(Ks) IN
              /\ commitIndex' = [commitIndex EXCEPT ![n] = Max({commitIndex[n], commitNew})]
              /\ Net' = Net \ {m}
              /\ UNCHANGED << state, term, votedFor, log, electionElapsed, heartbeatElapsed,
                              preVotesGranted, votesGranted, electionKind >>

Next ==
  \/ MsgHupAction
  \/ TickAction
  \/ BeatAction
  \/ ProposeAction
  \/ DropAction
  \/ DeliverHup
  \/ DeliverPreVote
  \/ DeliverPreVoteResp
  \/ DeliverVote
  \/ DeliverVoteResp
  \/ DeliverProp
  \/ DeliverApp
  \/ DeliverAppResp

Spec ==
  Init /\ TypeOK /\ [][Next]_<< state, term, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                      preVotesGranted, votesGranted, electionKind, nextIndex, matchIndex, Net >>

====