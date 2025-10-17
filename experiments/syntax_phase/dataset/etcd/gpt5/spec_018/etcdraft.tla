---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NODES,
    NONE,
    ElectionTimeout,
    HeartbeatTimeout,
    CLIENT_VALUES

ASSUME NONE \notin NODES
ASSUME ElectionTimeout \in Nat \ {0}
ASSUME HeartbeatTimeout \in Nat \ {0}

MsgTypes ==
    {
      "MsgPreVote", "MsgPreVoteResp",
      "MsgVote", "MsgVoteResp",
      "MsgApp", "MsgAppResp",
      "MsgHeartbeat", "MsgHeartbeatResp"
    }

States == {"StateFollower", "StateCandidate", "StateLeader", "StatePreCandidate"}

NOOP == "NOOP"
DATA == CLIENT_VALUES \cup {NOOP}

Entry == [term: Nat, data: DATA]
Entries == Seq(Entry)

MESSAGE ==
    [ type: MsgTypes,
      from: NODES \cup {NONE},
      to: NODES,
      term: Nat,
      index: Nat,
      logterm: Nat,
      entries: Entries,
      commit: Nat,
      granted: BOOLEAN,
      success: BOOLEAN
    ]

VARIABLES
    Term,            \* [n ∈ NODES -> Nat]
    Vote,            \* [n ∈ NODES -> (NODES \cup {NONE})]
    State,           \* [n ∈ NODES -> States]
    Lead,            \* [n ∈ NODES -> (NODES \cup {NONE})]
    Log,             \* [n ∈ NODES -> Entries]
    CommitIndex,     \* [n ∈ NODES -> Nat]
    ElectionElapsed, \* [n ∈ NODES -> Nat]
    HeartbeatElapsed,\* [n ∈ NODES -> Nat]
    NextIndex,       \* [n ∈ NODES -> [NODES -> Nat]]
    MatchIndex,      \* [n ∈ NODES -> [NODES -> Nat]]
    PreVotesGranted, \* [n ∈ NODES -> SUBSET NODES]
    VotesGranted,    \* [n ∈ NODES -> SUBSET NODES]
    Msgs             \* SUBSET MESSAGE

vars == << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted, Msgs >>

Majority(S) == 2 * Cardinality(S) > Cardinality(NODES)

LastIndex(n) == Len(Log[n])
LastTerm(n) == IF Len(Log[n]) = 0 THEN 0 ELSE Log[n][Len(Log[n])].term
LogTermAt(n, i) == IF i = 0 THEN 0 ELSE Log[n][i].term

UpToDate(cLogTerm, cIndex, f) ==
    cLogTerm > LastTerm(f)
    \/ (cLogTerm = LastTerm(f) /\ cIndex >= LastIndex(f))

CanCommit(l, i, match) ==
    /\ i > CommitIndex[l]
    /\ i > 0
    /\ Log[l][i].term = Term[l]
    /\ Majority({ p \in NODES :
          IF p = l THEN LastIndex(l) >= i ELSE match[p] >= i })

NewCommit(l, match) ==
    LET idxs == { i \in 0..LastIndex(l) : CanCommit(l, i, match) } IN
      IF idxs = {} THEN CommitIndex[l] ELSE Max(idxs)

Init ==
    /\ Term = [n \in NODES |-> 0]
    /\ Vote = [n \in NODES |-> NONE]
    /\ State = [n \in NODES |-> "StateFollower"]
    /\ Lead = [n \in NODES |-> NONE]
    /\ Log = [n \in NODES |-> << >>]
    /\ CommitIndex = [n \in NODES |-> 0]
    /\ ElectionElapsed = [n \in NODES |-> 0]
    /\ HeartbeatElapsed = [n \in NODES |-> 0]
    /\ NextIndex = [l \in NODES |-> [p \in NODES |-> 1]]
    /\ MatchIndex = [l \in NODES |-> [p \in NODES |-> 0]]
    /\ PreVotesGranted = [n \in NODES |-> {}]
    /\ VotesGranted = [n \in NODES |-> {}]
    /\ Msgs = {}

BecomeFollower(n, newTerm, leader) ==
    /\ Term' = [Term EXCEPT ![n] = newTerm]
    /\ State' = [State EXCEPT ![n] = "StateFollower"]
    /\ Vote' = [Vote EXCEPT ![n] = NONE]
    /\ Lead' = [Lead EXCEPT ![n] = leader]
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
    /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![n] = 0]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ UNCHANGED << Log, CommitIndex, NextIndex, MatchIndex, Msgs >>

BecomePreCandidate(n) ==
    /\ State' = [State EXCEPT ![n] = "StatePreCandidate"]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {n}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ UNCHANGED << Term, Vote, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, Msgs >>

BecomeCandidate(n) ==
    /\ State' = [State EXCEPT ![n] = "StateCandidate"]
    /\ Term' = [Term EXCEPT ![n] = Term[n] + 1]
    /\ Vote' = [Vote EXCEPT ![n] = n]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {n}]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED << Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex, Msgs >>

BecomeLeader(n) ==
    LET li == LastIndex(n) IN
    /\ State' = [State EXCEPT ![n] = "StateLeader"]
    /\ Lead' = [Lead EXCEPT ![n] = n]
    /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![n] = 0]
    /\ Log' = [Log EXCEPT ![n] = Append(@, [term |-> Term[n], data |-> NOOP])]
    /\ NextIndex' = [NextIndex EXCEPT ![n] = [p \in NODES |-> li + 2]]
    /\ MatchIndex' = [MatchIndex EXCEPT ![n] = [p \in NODES |-> IF p = n THEN li + 1 ELSE 0]]
    /\ UNCHANGED << Term, Vote, CommitIndex, ElectionElapsed, PreVotesGranted, VotesGranted, Msgs >>

Tick(n) ==
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = ElectionElapsed[n] + 1]
    /\ HeartbeatElapsed' =
        [HeartbeatElapsed EXCEPT ![n] =
            IF State[n] = "StateLeader" THEN HeartbeatElapsed[n] + 1 ELSE HeartbeatElapsed[n]]
    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, NextIndex, MatchIndex, PreVotesGranted, VotesGranted, Msgs >>

StartPreVote(n) ==
    /\ State[n] # "StateLeader"
    /\ ElectionElapsed[n] >= ElectionTimeout
    /\ State' = [State EXCEPT ![n] = "StatePreCandidate"]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {n}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
    /\ Msgs' =
        Msgs \cup
        { [ type |-> "MsgPreVote", from |-> n, to |-> p, term |-> Term[n] + 1,
            index |-> LastIndex(n), logterm |-> LastTerm(n),
            entries |-> << >>, commit |-> 0, granted |-> FALSE, success |-> FALSE ] : p \in NODES }
    /\ UNCHANGED << Term, Vote, Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex >>

HeartbeatTimeoutFire(n) ==
    /\ State[n] = "StateLeader"
    /\ HeartbeatElapsed[n] >= HeartbeatTimeout
    /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![n] = 0]
    /\ Msgs' = Msgs \cup { [ type |-> "MsgHeartbeat",
                             from |-> n, to |-> p, term |-> Term[n],
                             index |-> 0, logterm |-> 0, entries |-> << >>,
                             commit |-> CommitIndex[n], granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {n} }
    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

Drop ==
    \E m \in Msgs :
        /\ Msgs' = Msgs \ {m}
        /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverPreVote ==
    \E m \in Msgs :
      /\ m.type = "MsgPreVote"
      /\ LET i == m.to IN
         /\ Msgs' = Msgs \ {m} \cup {
              [ type |-> "MsgPreVoteResp", from |-> i, to |-> m.from, term |-> m.term,
                index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
                granted |-> UpToDate(m.logterm, m.index, i), success |-> FALSE ] }
         /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverPreVoteResp ==
    \E m \in Msgs :
      /\ m.type = "MsgPreVoteResp"
      /\ LET c == m.to IN
         /\ IF State[c] = "StatePreCandidate" /\ m.granted THEN
              /\ PreVotesGranted1 == [PreVotesGranted EXCEPT ![c] = @ \cup {m.from}]
              /\ IF Majority(PreVotesGranted1[c]) THEN
                    /\ State' = [State EXCEPT ![c] = "StateCandidate"]
                    /\ Term' = [Term EXCEPT ![c] = Term[c] + 1]
                    /\ Vote' = [Vote EXCEPT ![c] = c]
                    /\ VotesGranted' = [VotesGranted EXCEPT ![c] = {c}]
                    /\ PreVotesGranted' = [PreVotesGranted1 EXCEPT ![c] = {}]
                    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![c] = 0]
                    /\ Msgs' =
                        (Msgs \ {m}) \cup
                        { [ type |-> "MsgVote", from |-> c, to |-> p, term |-> Term[c] + 1,
                            index |-> LastIndex(c), logterm |-> LastTerm(c),
                            entries |-> << >>, commit |-> 0, granted |-> FALSE, success |-> FALSE ] : p \in NODES }
                    /\ UNCHANGED << Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex >>
                 ELSE
                    /\ PreVotesGranted' = PreVotesGranted1
                    /\ Msgs' = Msgs \ {m}
                    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, VotesGranted >>
            ELSE
              /\ Msgs' = Msgs \ {m}
              /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverVote ==
    \E m \in Msgs :
      /\ m.type = "MsgVote"
      /\ LET i == m.to IN
         /\ IF m.term > Term[i] THEN
              /\ canVote == UpToDate(m.logterm, m.index, i)
              /\ Term' = [Term EXCEPT ![i] = m.term]
              /\ State' = [State EXCEPT ![i] = "StateFollower"]
              /\ Vote' = [Vote EXCEPT ![i] = IF canVote THEN m.from ELSE NONE]
              /\ Lead' = [Lead EXCEPT ![i] = NONE]
              /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = IF canVote THEN 0 ELSE ElectionElapsed[i]]
              /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![i] = 0]
              /\ Msgs' = (Msgs \ {m}) \cup {
                    [ type |-> "MsgVoteResp", from |-> i, to |-> m.from, term |-> m.term,
                      index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
                      granted |-> canVote, success |-> FALSE ] }
              /\ UNCHANGED << Log, CommitIndex, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE IF m.term = Term[i] THEN
              /\ canVote2 == (Vote[i] = NONE \/ Vote[i] = m.from) /\ UpToDate(m.logterm, m.index, i)
              /\ Vote' = [Vote EXCEPT ![i] = IF canVote2 THEN m.from ELSE Vote[i]]
              /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = IF canVote2 THEN 0 ELSE ElectionElapsed[i]]
              /\ Msgs' = (Msgs \ {m}) \cup {
                    [ type |-> "MsgVoteResp", from |-> i, to |-> m.from, term |-> Term[i],
                      index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
                      granted |-> canVote2, success |-> FALSE ] }
              /\ UNCHANGED << Term, State, Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE
              /\ Msgs' = Msgs \ {m}
              /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverVoteResp ==
    \E m \in Msgs :
      /\ m.type = "MsgVoteResp"
      /\ LET c == m.to IN
         /\ IF m.term > Term[c] THEN
              /\ Msgs' = Msgs \ {m}
              /\ BecomeFollower(c, m.term, NONE)
            ELSE IF State[c] = "StateCandidate" /\ m.term = Term[c] /\ m.granted THEN
              /\ VotesGranted1 == [VotesGranted EXCEPT ![c] = @ \cup {m.from}]
              /\ IF Majority(VotesGranted1[c]) THEN
                    /\ Msgs0 == Msgs \ {m}
                    /\ State1 == [State EXCEPT ![c] = "StateLeader"]
                    /\ Lead1 == [Lead EXCEPT ![c] = c]
                    /\ Log1 == [Log EXCEPT ![c] = Append(@, [term |-> Term[c], data |-> NOOP])]
                    /\ li == LastIndex(c)
                    /\ NextIndex1 == [NextIndex EXCEPT ![c] = [p \in NODES |-> li + 2]]
                    /\ MatchIndex1 == [MatchIndex EXCEPT ![c] = [p \in NODES |-> IF p = c THEN li + 1 ELSE 0]]
                    /\ Msgs' =
                        Msgs0 \cup
                        { [ type |-> "MsgApp",
                            from |-> c, to |-> p, term |-> Term[c],
                            index |-> NextIndex1[c][p] - 1,
                            logterm |-> LogTermAt(c, NextIndex1[c][p] - 1),
                            entries |-> SubSeq(Log1[c], NextIndex1[c][p], Len(Log1[c])),
                            commit |-> CommitIndex[c],
                            granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {c} }
                    /\ State' = State1
                    /\ Lead' = Lead1
                    /\ Log' = Log1
                    /\ NextIndex' = NextIndex1
                    /\ MatchIndex' = MatchIndex1
                    /\ UNCHANGED << Term, Vote, CommitIndex, ElectionElapsed, HeartbeatElapsed, PreVotesGranted, VotesGranted >>
                 ELSE
                    /\ VotesGranted' = VotesGranted1
                    /\ Msgs' = Msgs \ {m}
                    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted >>
            ELSE
              /\ Msgs' = Msgs \ {m}
              /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverApp ==
    \E m \in Msgs :
      /\ m.type = "MsgApp"
      /\ LET i == m.to IN
         /\ Msgs1 == Msgs \ {m} IN
         /\ IF m.term > Term[i] THEN
              /\ Term2 == [Term EXCEPT ![i] = m.term]
              /\ State2 == [State EXCEPT ![i] = "StateFollower"]
              /\ Vote2 == [Vote EXCEPT ![i] = NONE]
              /\ Lead2 == [Lead EXCEPT ![i] = m.from]
              /\ ElectionElapsed2 == [ElectionElapsed EXCEPT ![i] = 0]
              /\ HeartbeatElapsed2 == [HeartbeatElapsed EXCEPT ![i] = 0]
              /\ IF m.index = 0 \/ (m.index <= Len(Log[i]) /\ Log[i][m.index].term = m.logterm) THEN
                    /\ newLog == SubSeq(Log[i], 1, m.index) \o m.entries
                    /\ Log' = [Log EXCEPT ![i] = newLog]
                    /\ CommitIndex' = [CommitIndex EXCEPT ![i] = Min(m.commit, Len(newLog))]
                    /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgAppResp", from |-> i, to |-> m.from, term |-> Term2[i],
                          index |-> Len(newLog), logterm |-> 0, entries |-> << >>,
                          commit |-> CommitIndex'[i], granted |-> FALSE, success |-> TRUE ] }
                 ELSE
                    /\ Log' = Log
                    /\ CommitIndex' = CommitIndex
                    /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgAppResp", from |-> i, to |-> m.from, term |-> Term2[i],
                          index |-> Len(Log[i]), logterm |-> 0, entries |-> << >>,
                          commit |-> CommitIndex[i], granted |-> FALSE, success |-> FALSE ] }
              /\ Term' = Term2
              /\ State' = State2
              /\ Vote' = Vote2
              /\ Lead' = Lead2
              /\ ElectionElapsed' = ElectionElapsed2
              /\ HeartbeatElapsed' = HeartbeatElapsed2
              /\ UNCHANGED << NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE IF m.term = Term[i] THEN
              /\ State' = [State EXCEPT ![i] = "StateFollower"]
              /\ Lead' = [Lead EXCEPT ![i] = m.from]
              /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = 0]
              /\ IF m.index = 0 \/ (m.index <= Len(Log[i]) /\ Log[i][m.index].term = m.logterm) THEN
                    /\ newLog2 == SubSeq(Log[i], 1, m.index) \o m.entries
                    /\ Log' = [Log EXCEPT ![i] = newLog2]
                    /\ CommitIndex' = [CommitIndex EXCEPT ![i] = Min(m.commit, Len(newLog2))]
                    /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgAppResp", from |-> i, to |-> m.from, term |-> Term[i],
                          index |-> Len(newLog2), logterm |-> 0, entries |-> << >>,
                          commit |-> CommitIndex'[i], granted |-> FALSE, success |-> TRUE ] }
                 ELSE
                    /\ Log' = Log
                    /\ CommitIndex' = CommitIndex
                    /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgAppResp", from |-> i, to |-> m.from, term |-> Term[i],
                          index |-> Len(Log[i]), logterm |-> 0, entries |-> << >>,
                          commit |-> CommitIndex[i], granted |-> FALSE, success |-> FALSE ] }
              /\ UNCHANGED << Term, Vote, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE
              /\ Msgs' = Msgs1
              /\ UNCHANGED vars

DeliverAppResp ==
    \E m \in Msgs :
      /\ m.type = "MsgAppResp"
      /\ LET l == m.to IN
         /\ Msgs1 == Msgs \ {m} IN
         /\ IF State[l] = "StateLeader" /\ m.term = Term[l] THEN
              /\ IF m.success THEN
                    /\ MatchIndex' = [MatchIndex EXCEPT ![l] = [@ EXCEPT ![m.from] = m.index]]
                    /\ NextIndex' = [NextIndex EXCEPT ![l] = [@ EXCEPT ![m.from] = m.index + 1]]
                    /\ CommitIndex' = [CommitIndex EXCEPT ![l] = NewCommit(l, MatchIndex'[l])]
                    /\ Msgs' = Msgs1
                    /\ UNCHANGED << Term, Vote, State, Lead, Log, ElectionElapsed, HeartbeatElapsed, PreVotesGranted, VotesGranted >>
                 ELSE
                    /\ NextIndex' = [NextIndex EXCEPT ![l] = [@ EXCEPT ![m.from] = Max(1, NextIndex[l][m.from] - 1)]]
                    /\ MatchIndex' = MatchIndex
                    /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgApp",
                          from |-> l, to |-> m.from, term |-> Term[l],
                          index |-> NextIndex'[l][m.from] - 1,
                          logterm |-> LogTermAt(l, NextIndex'[l][m.from] - 1),
                          entries |-> SubSeq(Log[l], NextIndex'[l][m.from], LastIndex(l)),
                          commit |-> CommitIndex[l],
                          granted |-> FALSE, success |-> FALSE ] }
                    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, PreVotesGranted, VotesGranted >>
            ELSE
              /\ Msgs' = Msgs1
              /\ UNCHANGED vars

DeliverHeartbeat ==
    \E m \in Msgs :
      /\ m.type = "MsgHeartbeat"
      /\ LET i == m.to IN
         /\ Msgs1 == Msgs \ {m} IN
         /\ IF m.term > Term[i] THEN
              /\ Term' = [Term EXCEPT ![i] = m.term]
              /\ State' = [State EXCEPT ![i] = "StateFollower"]
              /\ Vote' = [Vote EXCEPT ![i] = NONE]
              /\ Lead' = [Lead EXCEPT ![i] = m.from]
              /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = 0]
              /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![i] = 0]
              /\ CommitIndex' = [CommitIndex EXCEPT ![i] = Min(m.commit, Len(Log[i]))]
              /\ Msgs' = Msgs1 \cup {
                  [ type |-> "MsgHeartbeatResp", from |-> i, to |-> m.from, term |-> Term'[i],
                    index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> CommitIndex'[i],
                    granted |-> FALSE, success |-> TRUE ] }
              /\ UNCHANGED << Log, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE IF m.term = Term[i] THEN
              /\ State' = [State EXCEPT ![i] = "StateFollower"]
              /\ Lead' = [Lead EXCEPT ![i] = m.from]
              /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = 0]
              /\ CommitIndex' = [CommitIndex EXCEPT ![i] = Min(m.commit, Len(Log[i]))]
              /\ Msgs' = Msgs1 \cup {
                  [ type |-> "MsgHeartbeatResp", from |-> i, to |-> m.from, term |-> Term[i],
                    index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> CommitIndex'[i],
                    granted |-> FALSE, success |-> TRUE ] }
              /\ UNCHANGED << Term, Vote, HeartbeatElapsed, Log, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE
              /\ Msgs' = Msgs1
              /\ UNCHANGED vars

DeliverHeartbeatResp ==
    \E m \in Msgs :
      /\ m.type = "MsgHeartbeatResp"
      /\ LET l == m.to IN
         /\ Msgs1 == Msgs \ {m} IN
         /\ IF State[l] = "StateLeader" /\ m.term = Term[l] THEN
              /\ Msgs' =
                  IF NextIndex[l][m.from] <= LastIndex(l) THEN
                      Msgs1 \cup {
                        [ type |-> "MsgApp",
                          from |-> l, to |-> m.from, term |-> Term[l],
                          index |-> NextIndex[l][m.from] - 1,
                          logterm |-> LogTermAt(l, NextIndex[l][m.from] - 1),
                          entries |-> SubSeq(Log[l], NextIndex[l][m.from], LastIndex(l)),
                          commit |-> CommitIndex[l],
                          granted |-> FALSE, success |-> FALSE ] }
                  ELSE Msgs1
              /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
            ELSE
              /\ Msgs' = Msgs1
              /\ UNCHANGED vars

StepDownOnHigherTerm ==
    \E m \in Msgs :
        /\ m.term > Term[m.to]
        /\ Msgs' = Msgs
        /\ BecomeFollower(m.to, m.term, IF m.type \in {"MsgApp", "MsgHeartbeat"} THEN m.from ELSE NONE)

Next ==
    \/ \E n \in NODES : Tick(n)
    \/ \E n \in NODES : StartPreVote(n)
    \/ \E n \in NODES : HeartbeatTimeoutFire(n)
    \/ Drop
    \/ DeliverPreVote
    \/ DeliverPreVoteResp
    \/ DeliverVote
    \/ DeliverVoteResp
    \/ DeliverApp
    \/ DeliverAppResp
    \/ DeliverHeartbeat
    \/ DeliverHeartbeatResp
    \/ StepDownOnHigherTerm

Spec == Init /\ [][Next]_vars

====