---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NODES,
    ELECTION_TIMEOUT_MIN,
    ELECTION_TIMEOUT_MAX,
    HEARTBEAT_TIMEOUT

None == 0

StateFollower == "StateFollower"
StatePreCandidate == "StatePreCandidate"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
States == {StateFollower, StatePreCandidate, StateCandidate, StateLeader}

MsgHup == "MsgHup"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgProp == "MsgProp"
MsgTypes == {MsgHup, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgProp}

Entry == [term: Nat]
Message ==
    [ type: MsgTypes,
      from: NODES,
      to: NODES,
      term: Nat,
      index: Nat,
      logterm: Nat,
      entries: Seq(Entry),
      commit: Nat,
      reject: BOOLEAN ]

VARIABLES
    state,
    term,
    vote,
    log,
    commitIndex,
    electionTimer,
    electionTimeout,
    heartbeatTimer,
    preVotesYes,
    votesYes,
    NextIndex,
    MatchIndex,
    Msgs

Nodes == NODES

MIN2(a, b) == IF a <= b THEN a ELSE b
MAX2(a, b) == IF a >= b THEN a ELSE b
MaxSet(S) == CHOOSE x \in S: \A y \in S: x >= y

LastIndex(n) == Len(log[n])

TermAtLog(lg, i) ==
    IF i = 0 THEN 0
    ELSE IF i <= Len(lg) THEN lg[i].term ELSE 0

TermAt(n, i) == TermAtLog(log[n], i)

IsUpToDate(cTerm, cIndex, n) ==
    cTerm > TermAt(n, LastIndex(n)) \/
    (cTerm = TermAt(n, LastIndex(n)) /\ cIndex >= LastIndex(n))

Maj(S) == Cardinality(S) > Cardinality(Nodes) \div 2

AppendEntriesToLog(lg, prevIndex, ents) ==
    SubSeq(lg, 1, prevIndex) \o ents

Followers(n) == Nodes \ {n}

Init ==
    /\ state \in [Nodes -> States]
    /\ state = [n \in Nodes |-> StateFollower]
    /\ term \in [Nodes -> Nat]
    /\ term = [n \in Nodes |-> 0]
    /\ vote \in [Nodes -> (Nodes \cup {None})]
    /\ vote = [n \in Nodes |-> None]
    /\ log \in [Nodes -> Seq(Entry)]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex \in [Nodes -> Nat]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ electionTimer \in [Nodes -> Nat]
    /\ electionTimer = [n \in Nodes |-> 0]
    /\ electionTimeout \in [Nodes -> (ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX)]
    /\ heartbeatTimer \in [Nodes -> Nat]
    /\ heartbeatTimer = [n \in Nodes |-> 0]
    /\ preVotesYes \in [Nodes -> SUBSET Nodes]
    /\ preVotesYes = [n \in Nodes |-> {}]
    /\ votesYes \in [Nodes -> SUBSET Nodes]
    /\ votesYes = [n \in Nodes |-> {}]
    /\ NextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ NextIndex = [l \in Nodes |-> [p \in Nodes |-> 1]]
    /\ MatchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ MatchIndex = [l \in Nodes |-> [p \in Nodes |-> 0]]
    /\ Msgs \in SUBSET Message
    /\ Msgs = {}

TickElection ==
    \E n \in Nodes:
        /\ electionTimer' = [electionTimer EXCEPT ![n] = electionTimer[n] + 1]
        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex, Msgs >>

TimeoutToHup ==
    \E n \in Nodes:
        /\ state[n] # StateLeader
        /\ electionTimer[n] >= electionTimeout[n]
        /\ \E et \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX:
            /\ LET newHup ==
                    [ type |-> MsgHup,
                      from |-> n,
                      to |-> n,
                      term |-> 0,
                      index |-> 0,
                      logterm |-> 0,
                      entries |-> <<>>,
                      commit |-> commitIndex[n],
                      reject |-> FALSE ]
               IN
               /\ Msgs' = Msgs \cup {newHup}
               /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
               /\ electionTimeout' = [electionTimeout EXCEPT ![n] = et]
               /\ UNCHANGED << state, term, vote, log, commitIndex, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

TickHeartbeat ==
    \E l \in Nodes:
        /\ state[l] = StateLeader
        /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![l] = heartbeatTimer[l] + 1]
        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, preVotesYes, votesYes, NextIndex, MatchIndex, Msgs >>

LeaderHeartbeat ==
    \E l \in Nodes:
        /\ state[l] = StateLeader
        /\ heartbeatTimer[l] >= HEARTBEAT_TIMEOUT
        /\ LET outs ==
                { [ type |-> MsgApp,
                    from |-> l,
                    to |-> p,
                    term |-> term[l],
                    index |-> IF NextIndex[l][p] = 0 THEN 0 ELSE NextIndex[l][p] - 1,
                    logterm |-> TermAt(l, IF NextIndex[l][p] = 0 THEN 0 ELSE NextIndex[l][p] - 1),
                    entries |-> <<>>,
                    commit |-> commitIndex[l],
                    reject |-> FALSE ] : p \in Nodes \ {l} }
           IN
           /\ Msgs' = Msgs \cup outs
           /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![l] = 0]
           /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, preVotesYes, votesYes, NextIndex, MatchIndex >>

ClientPropose ==
    \E l \in Nodes:
        /\ state[l] = StateLeader
        /\ LET prop ==
                [ type |-> MsgProp,
                  from |-> l,
                  to |-> l,
                  term |-> term[l],
                  index |-> 0,
                  logterm |-> 0,
                  entries |-> <<>>,
                  commit |-> commitIndex[l],
                  reject |-> FALSE ]
           IN
           /\ Msgs' = Msgs \cup {prop}
           /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

Drop ==
    \E m \in Msgs:
        /\ Msgs' = Msgs \ {m}
        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

DeliverHup ==
    \E m \in Msgs:
      /\ m.type = MsgHup
      /\ LET r == m.to IN
         IF state[r] = StateLeader THEN
           /\ Msgs' = Msgs \ {m}
           /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>
         ELSE
           /\ state' = [state EXCEPT ![r] = StatePreCandidate]
           /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {r}]
           /\ votesYes' = [votesYes EXCEPT ![r] = {}]
           /\ \E et \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX:
                /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                /\ electionTimeout' = [electionTimeout EXCEPT ![r] = et]
                /\ LET outs ==
                        { [ type |-> MsgPreVote,
                            from |-> r,
                            to |-> p,
                            term |-> term[r] + 1,
                            index |-> LastIndex(r),
                            logterm |-> TermAt(r, LastIndex(r)),
                            entries |-> <<>>,
                            commit |-> commitIndex[r],
                            reject |-> FALSE ] : p \in Nodes \ {r} }
                   IN
                   /\ Msgs' = (Msgs \ {m}) \cup outs
                /\ UNCHANGED << term, vote, log, commitIndex, heartbeatTimer, NextIndex, MatchIndex >>

DeliverPreVote ==
    \E m \in Msgs:
      /\ m.type = MsgPreVote
      /\ LET r == m.to IN
         /\ Msgs' = (Msgs \ {m}) \cup {
              [ type |-> MsgPreVoteResp,
                from |-> r,
                to |-> m.from,
                term |-> m.term,
                index |-> 0,
                logterm |-> 0,
                entries |-> <<>>,
                commit |-> commitIndex[r],
                reject |-> ~IsUpToDate(m.logterm, m.index, r) ] }
         /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

DeliverPreVoteResp ==
    \E m \in Msgs:
      /\ m.type = MsgPreVoteResp
      /\ LET r == m.to IN
         IF state[r] = StatePreCandidate /\ ~m.reject THEN
           /\ preVotesYes' = [preVotesYes EXCEPT ![r] = preVotesYes[r] \cup {m.from}]
           /\ IF Maj(preVotesYes'[r]) THEN
                /\ state' = [state EXCEPT ![r] = StateCandidate]
                /\ term' = [term EXCEPT ![r] = term[r] + 1]
                /\ vote' = [vote EXCEPT ![r] = r]
                /\ votesYes' = [votesYes EXCEPT ![r] = {r}]
                /\ \E et \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX:
                    /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                    /\ electionTimeout' = [electionTimeout EXCEPT ![r] = et]
                    /\ LET outs ==
                            { [ type |-> MsgVote,
                                from |-> r,
                                to |-> p,
                                term |-> term'[r],
                                index |-> LastIndex(r),
                                logterm |-> TermAt(r, LastIndex(r)),
                                entries |-> <<>>,
                                commit |-> commitIndex[r],
                                reject |-> FALSE ] : p \in Nodes \ {r} }
                       IN
                       /\ Msgs' = (Msgs \ {m}) \cup outs
                    /\ UNCHANGED << log, commitIndex, heartbeatTimer, preVotesYes, NextIndex, MatchIndex >>
              ELSE
                /\ Msgs' = Msgs \ {m}
                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, votesYes, NextIndex, MatchIndex >>
         ELSE
           /\ Msgs' = Msgs \ {m}
           /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

DeliverVote ==
    \E m \in Msgs:
      /\ m.type = MsgVote
      /\ LET r == m.to IN
         LET tNew == IF m.term > term[r] THEN m.term ELSE term[r] IN
         /\ IF m.term > term[r] THEN
                /\ term' = [term EXCEPT ![r] = m.term]
                /\ state' = [state EXCEPT ![r] = StateFollower]
                /\ vote' = [vote EXCEPT ![r] = None]
                /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
                /\ votesYes' = [votesYes EXCEPT ![r] = {}]
            ELSE
                /\ UNCHANGED << term, state, vote, preVotesYes, votesYes >>
         /\ LET canVote ==
                (vote[r] = None \/ vote[r] = m.from) /\ IsUpToDate(m.logterm, m.index, r)
            IN
            /\ Msgs' = (Msgs \ {m}) \cup {
                [ type |-> MsgVoteResp,
                  from |-> r,
                  to |-> m.from,
                  term |-> tNew,
                  index |-> 0,
                  logterm |-> 0,
                  entries |-> <<>>,
                  commit |-> commitIndex[r],
                  reject |-> ~canVote ] }
            /\ IF canVote THEN
                  /\ vote' = [vote EXCEPT ![r] = m.from]
                  /\ \E et \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX:
                      /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                      /\ electionTimeout' = [electionTimeout EXCEPT ![r] = et]
               ELSE
                  /\ UNCHANGED << vote, electionTimer, electionTimeout >>
         /\ UNCHANGED << log, commitIndex, heartbeatTimer, NextIndex, MatchIndex >>

DeliverVoteResp ==
    \E m \in Msgs:
      /\ m.type = MsgVoteResp
      /\ LET r == m.to IN
         IF m.term > term[r] THEN
            /\ Msgs' = Msgs \ {m}
            /\ term' = [term EXCEPT ![r] = m.term]
            /\ state' = [state EXCEPT ![r] = StateFollower]
            /\ vote' = [vote EXCEPT ![r] = None]
            /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
            /\ votesYes' = [votesYes EXCEPT ![r] = {}]
            /\ UNCHANGED << log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex >>
         ELSE
            IF state[r] = StateCandidate /\ ~m.reject /\ m.term = term[r] THEN
                /\ votesYes' = [votesYes EXCEPT ![r] = votesYes[r] \cup {m.from}]
                /\ IF Maj(votesYes'[r]) THEN
                    /\ state' = [state EXCEPT ![r] = StateLeader]
                    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![r] = 0]
                    /\ \E et \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX:
                        /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                        /\ electionTimeout' = [electionTimeout EXCEPT ![r] = et]
                        /\ log' = [log EXCEPT ![r] = Append(log[r], [term |-> term[r]])]
                        /\ LET newLen == Len(log'[r]) IN
                           /\ NextIndex' = [NextIndex EXCEPT ![r] = [p \in Nodes |-> newLen + 1]]
                           /\ MatchIndex' = [MatchIndex EXCEPT ![r] = [p \in Nodes |-> IF p = r THEN newLen ELSE 0]]
                           /\ LET outs ==
                                    { [ type |-> MsgApp,
                                        from |-> r,
                                        to |-> p,
                                        term |-> term[r],
                                        index |-> newLen - 1,
                                        logterm |-> TermAtLog(log'[r], newLen - 1),
                                        entries |-> SubSeq(log'[r], LastIndex(r) + 1, newLen),
                                        commit |-> commitIndex[r],
                                        reject |-> FALSE ] : p \in Nodes \ {r} }
                              IN
                              /\ Msgs' = (Msgs \ {m}) \cup outs
                        /\ UNCHANGED << term, vote, preVotesYes, votesYes, commitIndex >>
                  ELSE
                    /\ Msgs' = Msgs \ {m}
                    /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex, preVotesYes >>
            ELSE
                /\ Msgs' = Msgs \ {m}
                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex, preVotesYes, votesYes >>

DeliverApp ==
    \E m \in Msgs:
      /\ m.type = MsgApp
      /\ LET r == m.to IN
         LET tNew == IF m.term > term[r] THEN m.term ELSE term[r] IN
         /\ IF m.term > term[r] THEN
                /\ term' = [term EXCEPT ![r] = m.term]
                /\ state' = [state EXCEPT ![r] = StateFollower]
                /\ vote' = [vote EXCEPT ![r] = None]
                /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
                /\ votesYes' = [votesYes EXCEPT ![r] = {}]
            ELSE
                /\ UNCHANGED << term, state, vote, preVotesYes, votesYes >>
         /\ \E et \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX:
            /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
            /\ electionTimeout' = [electionTimeout EXCEPT ![r] = et]
            /\ IF m.index = 0 \/ TermAt(r, m.index) = m.logterm THEN
                /\ log' = [log EXCEPT ![r] = AppendEntriesToLog(log[r], m.index, m.entries)]
                /\ commitIndex' = [commitIndex EXCEPT ![r] = MIN2(m.commit, Len(log'[r]))]
                /\ Msgs' = (Msgs \ {m}) \cup {
                        [ type |-> MsgAppResp,
                          from |-> r,
                          to |-> m.from,
                          term |-> tNew,
                          index |-> Len(log'[r]),
                          logterm |-> 0,
                          entries |-> <<>>,
                          commit |-> commitIndex'[r],
                          reject |-> FALSE ] }
              ELSE
                /\ Msgs' = (Msgs \ {m}) \cup {
                        [ type |-> MsgAppResp,
                          from |-> r,
                          to |-> m.from,
                          term |-> tNew,
                          index |-> LastIndex(r),
                          logterm |-> 0,
                          entries |-> <<>>,
                          commit |-> commitIndex[r],
                          reject |-> TRUE ] }
                /\ UNCHANGED << log, commitIndex >>
         /\ UNCHANGED << heartbeatTimer, NextIndex, MatchIndex >>

DeliverAppResp ==
    \E m \in Msgs:
      /\ m.type = MsgAppResp
      /\ LET r == m.to IN
         IF m.term > term[r] THEN
            /\ Msgs' = Msgs \ {m}
            /\ term' = [term EXCEPT ![r] = m.term]
            /\ state' = [state EXCEPT ![r] = StateFollower]
            /\ vote' = [vote EXCEPT ![r] = None]
            /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
            /\ votesYes' = [votesYes EXCEPT ![r] = {}]
            /\ UNCHANGED << log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex >>
         ELSE
            IF state[r] = StateLeader THEN
                IF m.reject THEN
                    /\ NextIndex' = [NextIndex EXCEPT ![r][m.from] = MAX2(1, NextIndex[r][m.from] - 1)]
                    /\ LET prevIdx == NextIndex'[r][m.from] - 1 IN
                       /\ Msgs' = (Msgs \ {m}) \cup {
                            [ type |-> MsgApp,
                              from |-> r,
                              to |-> m.from,
                              term |-> term[r],
                              index |-> prevIdx,
                              logterm |-> TermAt(r, prevIdx),
                              entries |-> SubSeq(log[r], NextIndex'[r][m.from], LastIndex(r)),
                              commit |-> commitIndex[r],
                              reject |-> FALSE ] }
                    /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, MatchIndex >>
                ELSE
                    /\ MatchIndex' = [MatchIndex EXCEPT ![r][m.from] = m.index]
                    /\ NextIndex' = [NextIndex EXCEPT ![r][m.from] = m.index + 1]
                    /\ LET acked(i) ==
                            { p \in Nodes :
                                IF p = r THEN Len(log[r]) >= i ELSE MatchIndex'[r][p] >= i }
                       IN
                       /\ commitIndex' =
                            [commitIndex EXCEPT
                                ![r] = IF \E i \in 0..LastIndex(r): Maj(acked(i))
                                       THEN MaxSet({ i \in 0..LastIndex(r) : Maj(acked(i)) })
                                       ELSE commitIndex[r]]
                    /\ LET outs ==
                            { [ type |-> MsgApp,
                                from |-> r,
                                to |-> p,
                                term |-> term[r],
                                index |-> NextIndex'[r][p] - 1,
                                logterm |-> TermAt(r, NextIndex'[r][p] - 1),
                                entries |-> SubSeq(log[r], NextIndex'[r][p], LastIndex(r)),
                                commit |-> commitIndex'[r],
                                reject |-> FALSE ]
                              : p \in Nodes \ {r} /\ NextIndex'[r][p] <= LastIndex(r) }
                       IN
                       /\ Msgs' = (Msgs \ {m}) \cup outs
                    /\ UNCHANGED << state, term, vote, log, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes >>
            ELSE
                /\ Msgs' = Msgs \ {m}
                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

DeliverProp ==
    \E m \in Msgs:
      /\ m.type = MsgProp
      /\ LET r == m.to IN
         IF state[r] = StateLeader THEN
            /\ log' = [log EXCEPT ![r] = Append(log[r], [term |-> term[r]])]
            /\ LET newLen == Len(log'[r]) IN
               /\ MatchIndex' = [MatchIndex EXCEPT ![r][r] = newLen]
               /\ NextIndex' = [NextIndex EXCEPT ![r] = [p \in Nodes |-> NextIndex[r][p]], ![r][r] = newLen + 1]
               /\ LET outs ==
                        { [ type |-> MsgApp,
                            from |-> r,
                            to |-> p,
                            term |-> term[r],
                            index |-> NextIndex'[r][p] - 1,
                            logterm |-> TermAtLog(log'[r], NextIndex'[r][p] - 1),
                            entries |-> SubSeq(log'[r], NextIndex'[r][p], newLen),
                            commit |-> commitIndex[r],
                            reject |-> FALSE ] : p \in Nodes \ {r} }
                  IN
                  /\ Msgs' = (Msgs \ {m}) \cup outs
            /\ UNCHANGED << state, term, vote, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes >>
         ELSE
            /\ Msgs' = Msgs \ {m}
            /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>

Deliver ==
    DeliverHup
    \/ DeliverPreVote
    \/ DeliverPreVoteResp
    \/ DeliverVote
    \/ DeliverVoteResp
    \/ DeliverApp
    \/ DeliverAppResp
    \/ DeliverProp

Next ==
    TickElection
    \/ TimeoutToHup
    \/ TickHeartbeat
    \/ LeaderHeartbeat
    \/ ClientPropose
    \/ Drop
    \/ Deliver

Vars == << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex, Msgs >>

Spec ==
    Init /\ [][Next]_Vars

====