---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NODES,
    NONE,
    ElectionTimeout,
    HeartbeatTimeout,
    CLIENT_VALUES

ASSUME NONE \notin NODES
ASSUME ElectionTimeout \in Nat \ {0}
ASSUME HeartbeatTimeout \in Nat \ {0}

MsgTypes == {
    "MsgHup",
    "MsgPreVote", "MsgPreVoteResp",
    "MsgVote", "MsgVoteResp",
    "MsgApp", "MsgAppResp",
    "MsgHeartbeat", "MsgHeartbeatResp",
    "MsgProp"
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

SetAllNatTo(v) == [x \in NODES |-> v]

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

Send(msg) == Msgs' = Msgs \cup {msg}

Bcast(l, t) ==
    \A p \in NODES \ {l} :
        TRUE

AppendEntriesFor(l, p) ==
    LET ni == NextIndex[l][p] IN
    LET prevIdx == ni - 1 IN
    LET prevTerm == LogTermAt(l, prevIdx) IN
    LET ents == SubSeq(Log[l], ni, LastIndex(l)) IN
    Send([ type |-> "MsgApp",
           from |-> l, to |-> p, term |-> Term[l],
           index |-> prevIdx, logterm |-> prevTerm,
           entries |-> ents, commit |-> CommitIndex[l],
           granted |-> FALSE, success |-> FALSE ])

BroadcastApp(l) ==
    /\ \A p \in NODES \ {l} : TRUE
    /\ Msgs' = Msgs \cup { [ type |-> "MsgApp",
                             from |-> l, to |-> p, term |-> Term[l],
                             index |-> NextIndex[l][p] - 1,
                             logterm |-> LogTermAt(l, NextIndex[l][p] - 1),
                             entries |-> SubSeq(Log[l], NextIndex[l][p], LastIndex(l)),
                             commit |-> CommitIndex[l],
                             granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {l} }

BroadcastHeartbeat(l) ==
    /\ \A p \in NODES \ {l} : TRUE
    /\ Msgs' = Msgs \cup { [ type |-> "MsgHeartbeat",
                             from |-> l, to |-> p, term |-> Term[l],
                             index |-> 0, logterm |-> 0,
                             entries |-> << >>, commit |-> CommitIndex[l],
                             granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {l} }

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
    /\ UNCHANGED << Term, Vote, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex >>
    /\ Msgs' =
        Msgs \cup
        { [ type |-> "MsgPreVote", from |-> n, to |-> p, term |-> Term[n] + 1,
            index |-> LastIndex(n), logterm |-> LastTerm(n),
            entries |-> << >>, commit |-> 0, granted |-> FALSE, success |-> FALSE ] : p \in NODES }

BecomeCandidate(n) ==
    /\ State' = [State EXCEPT ![n] = "StateCandidate"]
    /\ Term' = [Term EXCEPT ![n] = Term[n] + 1]
    /\ Vote' = [Vote EXCEPT ![n] = n]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {n}]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED << Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex >>
    /\ Msgs' =
        Msgs \cup
        { [ type |-> "MsgVote", from |-> n, to |-> p, term |-> Term[n] + 1,
            index |-> LastIndex(n), logterm |-> LastTerm(n),
            entries |-> << >>, commit |-> 0, granted |-> FALSE, success |-> FALSE ] : p \in NODES }

BecomeLeader(n) ==
    LET li == LastIndex(n) IN
    /\ State' = [State EXCEPT ![n] = "StateLeader"]
    /\ Lead' = [Lead EXCEPT ![n] = n]
    /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![n] = 0]
    /\ Log' = [Log EXCEPT ![n] = Append(@, [term |-> Term[n], data |-> NOOP])]
    /\ NextIndex' = [NextIndex EXCEPT ![n] = [p \in NODES |-> li + 2]]
    /\ MatchIndex' = [MatchIndex EXCEPT ![n] = [p \in NODES |-> IF p = n THEN li + 1 ELSE 0]]
    /\ UNCHANGED << Term, Vote, CommitIndex, ElectionElapsed, PreVotesGranted, VotesGranted >>
    /\ Msgs' =
        Msgs \cup
        { [ type |-> "MsgApp",
            from |-> n, to |-> p, term |-> Term[n],
            index |-> (li + 1) - 1,
            logterm |-> LogTermAt(n, li + 1 - 1),
            entries |-> SubSeq(Log'[n], li + 1, LastIndex(n) + 1),
            commit |-> CommitIndex[n],
            granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {n} }

MaybeCommit(l) ==
    LET idxs == { i \in 0..LastIndex(l) :
                    /\ i > CommitIndex[l]
                    /\ Log[l][i].term = Term[l]
                    /\ Majority({ p \in NODES :
                          IF p = l THEN LastIndex(l) >= i ELSE MatchIndex[l][p] >= i }) } IN
    IF idxs = {} THEN
        /\ CommitIndex' = CommitIndex
    ELSE
        /\ CommitIndex' = [CommitIndex EXCEPT ![l] = Max(idxs)]
    /\ UNCHANGED << Term, Vote, State, Lead, Log, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted, Msgs >>

Tick(n) ==
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = ElectionElapsed[n] + 1]
    /\ HeartbeatElapsed' =
        [HeartbeatElapsed EXCEPT ![n] =
            IF State[n] = "StateLeader" THEN HeartbeatElapsed[n] + 1 ELSE HeartbeatElapsed[n]]
    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, NextIndex, MatchIndex, PreVotesGranted, VotesGranted, Msgs >>

ElectionTimeoutToHup(n) ==
    /\ State[n] # "StateLeader"
    /\ ElectionElapsed[n] >= ElectionTimeout
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
    /\ Msgs' = Msgs \cup {
        [ type |-> "MsgHup", from |-> n, to |-> n, term |-> Term[n],
          index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
          granted |-> FALSE, success |-> FALSE ]
    }
    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

HeartbeatTimeoutFire(n) ==
    /\ State[n] = "StateLeader"
    /\ HeartbeatElapsed[n] >= HeartbeatTimeout
    /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![n] = 0]
    /\ Msgs' = Msgs \cup { [ type |-> "MsgHeartbeat",
                             from |-> n, to |-> p, term |-> Term[n],
                             index |-> 0, logterm |-> 0, entries |-> << >>,
                             commit |-> CommitIndex[n], granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {n} }
    /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

ClientSendProp(l, v) ==
    /\ State[l] = "StateLeader"
    /\ v \in CLIENT_VALUES
    /\ Msgs' = Msgs \cup {
        [ type |-> "MsgProp", from |-> NONE, to |-> l, term |-> Term[l],
          index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
          granted |-> FALSE, success |-> FALSE ]
    }
    /\ UNCHANGED vars

Drop ==
    \E m \in Msgs :
        /\ Msgs' = Msgs \ {m}
        /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverHup ==
    \E m \in Msgs :
        /\ m.type = "MsgHup"
        /\ LET n == m.to IN
           /\ Msgs' = Msgs \ {m}
           /\ IF State[n] = "StateLeader" THEN
                /\ UNCHANGED vars
              ELSE
                /\ IF TRUE THEN
                      BecomePreCandidate(n)
                   ELSE
                      BecomeCandidate(n)

DeliverPreVote ==
    \E m \in Msgs :
        /\ m.type = "MsgPreVote"
        /\ LET i == m.to IN
           /\ Msgs1 == Msgs \ {m} IN
           /\ IF m.term > Term[i] THEN
                /\ UNCHANGED << Term, Vote, State, Lead >>
                /\ TRUE
              ELSE
                /\ TRUE
           /\ LET grant ==
                  UpToDate(m.logterm, m.index, i)
              IN
              /\ Msgs' = Msgs1 \cup {
                    [ type |-> "MsgPreVoteResp", from |-> i, to |-> m.from, term |-> m.term,
                      index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
                      granted |-> grant, success |-> FALSE ] }
           /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = ElectionElapsed[i]]
           /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverPreVoteResp ==
    \E m \in Msgs :
        /\ m.type = "MsgPreVoteResp"
        /\ LET c == m.to IN
           /\ Msgs' = Msgs \ {m}
           /\ IF State[c] = "StatePreCandidate" /\ m.granted THEN
                /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![c] = @ \cup {m.from}]
                /\ IF Majority(PreVotesGranted'[c]) THEN
                      BecomeCandidate(c)
                   ELSE
                      /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, VotesGranted >>
              ELSE
                /\ UNCHANGED vars

DeliverVote ==
    \E m \in Msgs :
        /\ m.type = "MsgVote"
        /\ LET i == m.to IN
           /\ Msgs1 == Msgs \ {m} IN
           /\ IF m.term > Term[i] THEN
                /\ Term1 == [Term EXCEPT ![i] = m.term]
                /\ State1 == [State EXCEPT ![i] = "StateFollower"]
                /\ Vote1 == [Vote EXCEPT ![i] = NONE]
                /\ Lead1 == [Lead EXCEPT ![i] = NONE]
                /\ ElectionElapsed1 == [ElectionElapsed EXCEPT ![i] = 0]
                /\ HeartbeatElapsed1 == [HeartbeatElapsed EXCEPT ![i] = 0]
                /\ LET canVote ==
                        (Vote1[i] = NONE \/ Vote1[i] = m.from)
                        /\ UpToDate(m.logterm, m.index, i)
                   IN
                   /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgVoteResp", from |-> i, to |-> m.from, term |-> Term1[i],
                          index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
                          granted |-> canVote, success |-> FALSE ] }
                   /\ Term' = Term1
                   /\ State' = State1
                   /\ Vote' = [Vote1 EXCEPT ![i] = IF canVote THEN m.from ELSE Vote1[i]]
                   /\ Lead' = Lead1
                   /\ ElectionElapsed' = ElectionElapsed1
                   /\ HeartbeatElapsed' = HeartbeatElapsed1
                   /\ UNCHANGED << Log, CommitIndex, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>
              ELSE
                /\ LET canVote ==
                        (Vote[i] = NONE \/ Vote[i] = m.from)
                        /\ m.term = Term[i]
                        /\ UpToDate(m.logterm, m.index, i)
                   IN
                   /\ Msgs' = Msgs1 \cup {
                        [ type |-> "MsgVoteResp", from |-> i, to |-> m.from, term |-> Term[i],
                          index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> 0,
                          granted |-> canVote, success |-> FALSE ] }
                   /\ Vote' = [Vote EXCEPT ![i] = IF canVote THEN m.from ELSE Vote[i]]
                   /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![i] = IF canVote THEN 0 ELSE ElectionElapsed[i]]
                   /\ UNCHANGED << Term, State, Lead, Log, CommitIndex, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

DeliverVoteResp ==
    \E m \in Msgs :
        /\ m.type = "MsgVoteResp"
        /\ LET c == m.to IN
           /\ Msgs' = Msgs \ {m}
           /\ IF m.term > Term[c] THEN
                /\ BecomeFollower(c, m.term, NONE)
              ELSE IF State[c] = "StateCandidate" /\ m.term = Term[c] /\ m.granted THEN
                /\ VotesGranted' = [VotesGranted EXCEPT ![c] = @ \cup {m.from}]
                /\ IF Majority(VotesGranted'[c]) THEN
                      BecomeLeader(c)
                   ELSE
                      /\ UNCHANGED << Term, Vote, State, Lead, Log, CommitIndex, ElectionElapsed, HeartbeatElapsed, NextIndex, MatchIndex, PreVotesGranted >>
              ELSE
                /\ UNCHANGED vars

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
                      /\ newLog == Append(SubSeq(Log[i], 1, m.index), m.entries)
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
                      /\ newLog2 == Append(SubSeq(Log[i], 1, m.index), m.entries)
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
                      /\ CommitIndex1 ==
                          [i \in NODES |-> CommitIndex[i]]
                      /\ UNCHANGED << Term, Vote, State, Lead, Log, ElectionElapsed, HeartbeatElapsed, PreVotesGranted, VotesGranted >>
                      /\ Msgs' = Msgs1
                      /\ CommitIndex' \in { CommitIndex1, [CommitIndex1 EXCEPT ![l] = Max({i \in 0..LastIndex(l) :
                              /\ i > CommitIndex1[l]
                              /\ Log[l][i].term = Term[l]
                              /\ Majority({ p \in NODES :
                                    IF p = l THEN LastIndex(l) >= i ELSE MatchIndex'[l][p] >= i })}) ] }
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

DeliverProp ==
    \E m \in Msgs :
        /\ m.type = "MsgProp"
        /\ LET l == m.to IN
           /\ State[l] = "StateLeader"
           /\ \E v \in CLIENT_VALUES : TRUE
           /\ Msgs1 == Msgs \ {m} IN
           /\ Log' = [Log EXCEPT ![l] = Append(@, [term |-> Term[l], data |-> v])]
           /\ MatchIndex' = [MatchIndex EXCEPT ![l] = [@ EXCEPT ![l] = LastIndex(l) + 1]]
           /\ NextIndex' = NextIndex
           /\ Msgs' =
                Msgs1 \cup {
                    [ type |-> "MsgApp",
                      from |-> l, to |-> p, term |-> Term[l],
                      index |-> NextIndex[l][p] - 1,
                      logterm |-> LogTermAt(l, NextIndex[l][p] - 1),
                      entries |-> SubSeq(Log'[l], NextIndex[l][p], LastIndex(l) + 1),
                      commit |-> CommitIndex[l],
                      granted |-> FALSE, success |-> FALSE ] : p \in NODES \ {l} }
           /\ UNCHANGED << Term, Vote, State, Lead, CommitIndex, ElectionElapsed, HeartbeatElapsed, PreVotesGranted, VotesGranted >>

StepDownOnHigherTerm ==
    \E m \in Msgs :
        /\ m.term > Term[m.to]
        /\ Msgs' = Msgs
        /\ BecomeFollower(m.to, m.term, IF m.type \in {"MsgApp", "MsgHeartbeat"} THEN m.from ELSE NONE)

Next ==
    \/ \E n \in NODES : Tick(n)
    \/ \E n \in NODES : ElectionTimeoutToHup(n)
    \/ \E n \in NODES : HeartbeatTimeoutFire(n)
    \/ ClientSendProp(CHOOSE l \in NODES : State[l] = "StateLeader", CHOOSE v \in CLIENT_VALUES : TRUE)
    \/ Drop
    \/ DeliverHup
    \/ DeliverPreVote
    \/ DeliverPreVoteResp
    \/ DeliverVote
    \/ DeliverVoteResp
    \/ DeliverApp
    \/ DeliverAppResp
    \/ DeliverHeartbeat
    \/ DeliverHeartbeatResp
    \/ DeliverProp
    \/ StepDownOnHigherTerm

Spec == Init /\ [][Next]_vars

====