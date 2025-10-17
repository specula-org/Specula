---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

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

LastIndex(n) == Len(log[n])

TermAtLog(lg, i) ==
    IF i = 0 THEN 0
    ELSE IF i <= Len(lg) THEN lg[i].term ELSE 0

TermAt(n, i) == TermAtLog(log[n], i)

IsUpToDate(cTerm, cIndex, n) ==
    cTerm > TermAt(n, LastIndex(n)) \/ (cTerm = TermAt(n, LastIndex(n)) /\ cIndex >= LastIndex(n))

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
    /\ electionTimeout \in [Nodes -> Nat]
    /\ \A n \in Nodes: electionTimeout[n] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX
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
    /\ Msgs \subseteq { m \in Message:
            m.type \in MsgTypes /\ m.from \in Nodes /\ m.to \in Nodes }

ResetElection(n, et, ett) ==
    /\ et' = [electionTimer EXCEPT ![n] = 0]
    /\ ett' = [electionTimeout EXCEPT ![n] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]

ResetHeartbeat(n, ht) ==
    ht' = [heartbeatTimer EXCEPT ![n] = 0]

BumpTermToFollower(n, t, s, v, pvy, vy) ==
    /\ t' = [term EXCEPT ![n] = term[n]]
    /\ s' = [state EXCEPT ![n] = StateFollower]
    /\ v' = [vote EXCEPT ![n] = None]
    /\ pvy' = [preVotesYes EXCEPT ![n] = {}]
    /\ vy' = [votesYes EXCEPT ![n] = {}]

TickElection ==
    \E n \in Nodes:
        /\ electionTimer' = [electionTimer EXCEPT ![n] = electionTimer[n] + 1]
        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex, Msgs >>

TimeoutToHup ==
    \E n \in Nodes:
        /\ state[n] # StateLeader
        /\ electionTimer[n] >= electionTimeout[n]
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
           /\ electionTimeout' = [electionTimeout EXCEPT ![n] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
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

Deliver ==
    \E m \in Msgs:
        LET r == m.to IN
        /\ CASE
            m.type = MsgHup ->
                /\ Msgs' = Msgs \ {m}
                /\ IF state[r] = StateLeader THEN
                        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>
                   ELSE
                        /\ state' = [state EXCEPT ![r] = StatePreCandidate]
                        /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {r}]
                        /\ votesYes' = [votesYes EXCEPT ![r] = {}]
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
                        /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                        /\ electionTimeout' = [electionTimeout EXCEPT ![r] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
                        /\ UNCHANGED << term, vote, log, commitIndex, heartbeatTimer, NextIndex, MatchIndex >>
            [] m.type = MsgPreVote ->
                /\ Msgs' = Msgs \ {m} \cup {
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
            [] m.type = MsgPreVoteResp ->
                /\ Msgs' = Msgs \ {m}
                /\ IF state[r] = StatePreCandidate /\ ~m.reject THEN
                        /\ preVotesYes' = [preVotesYes EXCEPT ![r] = preVotesYes[r] \cup {m.from}]
                        /\ IF Maj(preVotesYes'[r]) THEN
                                /\ state' = [state EXCEPT ![r] = StateCandidate]
                                /\ term' = [term EXCEPT ![r] = term[r] + 1]
                                /\ vote' = [vote EXCEPT ![r] = r]
                                /\ votesYes' = [votesYes EXCEPT ![r] = {r}]
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
                                /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                                /\ electionTimeout' = [electionTimeout EXCEPT ![r] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
                                /\ UNCHANGED << log, commitIndex, heartbeatTimer, preVotesYes, NextIndex, MatchIndex >>
                           ELSE
                                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, votesYes, NextIndex, MatchIndex >>
                   ELSE
                        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>
            [] m.type = MsgVote ->
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
                   /\ Msgs' = Msgs \ {m} \cup {
                        [ type |-> MsgVoteResp,
                          from |-> r,
                          to |-> m.from,
                          term |-> term'[r],
                          index |-> 0,
                          logterm |-> 0,
                          entries |-> <<>>,
                          commit |-> commitIndex[r],
                          reject |-> ~canVote ] }
                /\ IF canVote THEN
                        /\ vote' = [vote EXCEPT ![r] = m.from]
                        /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                        /\ electionTimeout' = [electionTimeout EXCEPT ![r] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
                   ELSE
                        /\ UNCHANGED << vote, electionTimer, electionTimeout >>
                /\ UNCHANGED << log, commitIndex, heartbeatTimer, NextIndex, MatchIndex >>
            [] m.type = MsgVoteResp ->
                /\ Msgs' = Msgs \ {m}
                /\ IF m.term > term[r] /\ m.type # MsgPreVoteResp THEN
                        /\ term' = [term EXCEPT ![r] = m.term]
                        /\ state' = [state EXCEPT ![r] = StateFollower]
                        /\ vote' = [vote EXCEPT ![r] = None]
                        /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
                        /\ votesYes' = [votesYes EXCEPT ![r] = {}]
                        /\ UNCHANGED << log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex >>
                   ELSE
                        /\ IF state[r] = StateCandidate /\ ~m.reject /\ m.term = term[r] THEN
                                /\ votesYes' = [votesYes EXCEPT ![r] = votesYes[r] \cup {m.from}]
                                /\ IF Maj(votesYes'[r]) THEN
                                        /\ state' = [state EXCEPT ![r] = StateLeader]
                                        /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![r] = 0]
                                        /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                                        /\ electionTimeout' = [electionTimeout EXCEPT ![r] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
                                        /\ log' = [log EXCEPT ![r] = Append(log[r], [term |-> term[r]])]
                                        /\ NextIndex' = [NextIndex EXCEPT ![r] = [p \in Nodes |-> LastIndex'(r) + 1]]
                                        /\ MatchIndex' = [MatchIndex EXCEPT
                                            ![r] = [p \in Nodes |-> 0],
                                            ![r][r] = LastIndex'(r)]
                                        /\ LET outs ==
                                                { [ type |-> MsgApp,
                                                    from |-> r,
                                                    to |-> p,
                                                    term |-> term[r],
                                                    index |-> (LastIndex'(r) - 1),
                                                    logterm |-> TermAt(r, LastIndex'(r) - 1),
                                                    entries |-> SubSeq(log'[r], LastIndex(r)+1, LastIndex'(r)),
                                                    commit |-> commitIndex[r],
                                                    reject |-> FALSE ] : p \in Nodes \ {r} }
                                           IN
                                           /\ Msgs' = (Msgs \ {m}) \cup outs
                                        /\ UNCHANGED << term, vote, preVotesYes, votesYes, commitIndex >>
                                   ELSE
                                        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex, preVotesYes, votesYes, Msgs >>
                           ELSE
                                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex, preVotesYes, votesYes, Msgs >>
            [] m.type = MsgApp ->
                /\ Msgs' = Msgs \ {m}
                /\ IF m.term > term[r] THEN
                        /\ term' = [term EXCEPT ![r] = m.term]
                        /\ state' = [state EXCEPT ![r] = StateFollower]
                        /\ vote' = [vote EXCEPT ![r] = None]
                        /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
                        /\ votesYes' = [votesYes EXCEPT ![r] = {}]
                   ELSE
                        /\ UNCHANGED << term, state, vote, preVotesYes, votesYes >>
                /\ electionTimer' = [electionTimer EXCEPT ![r] = 0]
                /\ electionTimeout' = [electionTimeout EXCEPT ![r] \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
                /\ IF m.index = 0 \/ TermAt(r, m.index) = m.logterm THEN
                        /\ log' = [log EXCEPT ![r] = AppendEntriesToLog(log[r], m.index, m.entries)]
                        /\ commitIndex' = [commitIndex EXCEPT ![r] = Min(m.commit, LastIndex'(r))]
                        /\ Msgs' = (Msgs \ {m}) \cup {
                                [ type |-> MsgAppResp,
                                  from |-> r,
                                  to |-> m.from,
                                  term |-> term'[r],
                                  index |-> LastIndex'(r),
                                  logterm |-> 0,
                                  entries |-> <<>>,
                                  commit |-> commitIndex'[r],
                                  reject |-> FALSE ] }
                   ELSE
                        /\ UNCHANGED << log, commitIndex >>
                        /\ Msgs' = (Msgs \ {m}) \cup {
                                [ type |-> MsgAppResp,
                                  from |-> r,
                                  to |-> m.from,
                                  term |-> term'[r],
                                  index |-> LastIndex(r),
                                  logterm |-> 0,
                                  entries |-> <<>>,
                                  commit |-> commitIndex[r],
                                  reject |-> TRUE ] }
                /\ UNCHANGED << heartbeatTimer, NextIndex, MatchIndex >>
            [] m.type = MsgAppResp ->
                /\ Msgs' = Msgs \ {m}
                /\ IF m.term > term[r] THEN
                        /\ term' = [term EXCEPT ![r] = m.term]
                        /\ state' = [state EXCEPT ![r] = StateFollower]
                        /\ vote' = [vote EXCEPT ![r] = None]
                        /\ preVotesYes' = [preVotesYes EXCEPT ![r] = {}]
                        /\ votesYes' = [votesYes EXCEPT ![r] = {}]
                        /\ UNCHANGED << log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, NextIndex, MatchIndex >>
                   ELSE
                        /\ IF state[r] = StateLeader THEN
                                /\ IF m.reject THEN
                                        /\ NextIndex' = [NextIndex EXCEPT ![r][m.from] = Max(1, NextIndex[r][m.from] - 1)]
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
                                                    IF p = r THEN LastIndex(r) >= i ELSE MatchIndex'[r][p] >= i }
                                           IN
                                           /\ commitIndex' =
                                                [commitIndex EXCEPT
                                                    ![r] = IF \E i \in 0..LastIndex(r): Maj(acked(i))
                                                           THEN Max({i \in 0..LastIndex(r): Maj(acked(i))})
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
                                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex, Msgs >>
            [] m.type = MsgProp ->
                /\ Msgs' = Msgs \ {m}
                /\ IF state[r] = StateLeader THEN
                        /\ log' = [log EXCEPT ![r] = Append(log[r], [term |-> term[r]])]
                        /\ MatchIndex' = [MatchIndex EXCEPT ![r][r] = LastIndex'(r)]
                        /\ NextIndex' = [NextIndex EXCEPT ![r] = [p \in Nodes |-> NextIndex[r][p]], ![r][r] = LastIndex'(r) + 1]
                        /\ LET outs ==
                                { [ type |-> MsgApp,
                                    from |-> r,
                                    to |-> p,
                                    term |-> term[r],
                                    index |-> NextIndex'[r][p] - 1,
                                    logterm |-> TermAt(r, NextIndex'[r][p] - 1),
                                    entries |-> SubSeq(log'[r], NextIndex'[r][p], LastIndex'(r)),
                                    commit |-> commitIndex[r],
                                    reject |-> FALSE ] : p \in Nodes \ {r} }
                           IN
                           /\ Msgs' = (Msgs \ {m}) \cup outs
                        /\ UNCHANGED << state, term, vote, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes >>
                   ELSE
                        /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>
          OTHER ->
                /\ Msgs' = Msgs \ {m}
                /\ UNCHANGED << state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex >>
        /\ TRUE

Next ==
    TickElection
    \/ TimeoutToHup
    \/ TickHeartbeat
    \/ LeaderHeartbeat
    \/ ClientPropose
    \/ Drop
    \/ Deliver

Spec ==
    Init /\ [][Next]_<< state, term, vote, log, commitIndex, electionTimer, electionTimeout, heartbeatTimer, preVotesYes, votesYes, NextIndex, MatchIndex, Msgs >>

====