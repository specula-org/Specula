---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NODES, ELECTION_TIMEOUT, HEARTBEAT_TIMEOUT

ASSUME NODES # {} /\ ELECTION_TIMEOUT \in Nat \ {0} /\ HEARTBEAT_TIMEOUT \in Nat \ {0}

Node == NODES
None == 0

StateFollower == "StateFollower"
StatePreCandidate == "StatePreCandidate"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"

MsgHup == "MsgHup"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgProp == "MsgProp"

MsgType == {MsgHup, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgProp}
StateType == {StateFollower, StatePreCandidate, StateCandidate, StateLeader}

Entry == [term: Nat, cmd: _]
EntrySeq == Seq(Entry)

Quorum == (Cardinality(NODES) \div 2) + 1

LastIndex(log) == Len(log)
TermAt(log, i) == IF i = 0 THEN 0 ELSE IF i <= Len(log) THEN log[i].term ELSE 0
LastTerm(log) == TermAt(log, LastIndex(log))
UpToDate(cLastTerm, cLastIndex, log) == cLastTerm > LastTerm(log) \/ (cLastTerm = LastTerm(log) /\ cLastIndex >= LastIndex(log))
CountGE(j, matchrow) == Cardinality({ i \in NODES : matchrow[i] >= j})

Message ==
  [ type: MsgType,
    from: Node,
    to: Node,
    term: Nat,
    prevIndex: Nat,
    prevTerm: Nat,
    entries: EntrySeq,
    commit: Nat,
    reject: BOOLEAN,
    index: Nat,
    lastIndex: Nat,
    lastTerm: Nat ]

VARIABLES
  state, \* [Node -> StateType]
  term, \* [Node -> Nat]
  vote, \* [Node -> (NODES \cup {None})]
  log, \* [Node -> EntrySeq]
  commitIndex, \* [Node -> Nat]
  electionElapsed, \* [Node -> Nat]
  heartbeatElapsed, \* [Node -> Nat]
  preVotesGranted, \* [Node -> SUBSET NODES]
  preVoteTerm, \* [Node -> Nat]
  votesGranted, \* [Node -> SUBSET NODES]
  match, \* [Node -> [Node -> Nat]]
  nextIndex, \* [Node -> [Node -> Nat]]
  Net \* SUBSET of messages

vars == << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex, Net >>

Init ==
  /\ state \in [NODES -> {StateFollower}]
  /\ term \in [NODES -> 0..]
  /\ \A n \in NODES: term[n] = 0
  /\ vote \in [NODES -> (NODES \cup {None})]
  /\ \A n \in NODES: vote[n] = None
  /\ log \in [NODES -> EntrySeq]
  /\ \A n \in NODES: log[n] = << >>
  /\ commitIndex \in [NODES -> Nat]
  /\ \A n \in NODES: commitIndex[n] = 0
  /\ electionElapsed \in [NODES -> Nat]
  /\ \A n \in NODES: electionElapsed[n] = 0
  /\ heartbeatElapsed \in [NODES -> Nat]
  /\ \A n \in NODES: heartbeatElapsed[n] = 0
  /\ preVotesGranted \in [NODES -> SUBSET NODES]
  /\ \A n \in NODES: preVotesGranted[n] = {}
  /\ preVoteTerm \in [NODES -> Nat]
  /\ \A n \in NODES: preVoteTerm[n] = 0
  /\ votesGranted \in [NODES -> SUBSET NODES]
  /\ \A n \in NODES: votesGranted[n] = {}
  /\ match \in [NODES -> [NODES -> Nat]]
  /\ \A l \in NODES: \A i \in NODES: match[l][i] = 0
  /\ nextIndex \in [NODES -> [NODES -> Nat]]
  /\ \A l \in NODES: \A i \in NODES: nextIndex[l][i] = 1
  /\ Net = {}

Tick(node) ==
  /\ node \in NODES
  /\ LET hInc == IF state[node] = StateLeader THEN 1 ELSE 0 IN
     /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![node] = heartbeatElapsed[node] + hInc]
     /\ electionElapsed' = [electionElapsed EXCEPT ![node] = electionElapsed[node] + 1]
     /\ LET makeHup == [ type |-> MsgHup, from |-> node, to |-> node, term |-> term[node],
                         prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                         commit |-> 0, reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
            needHup == electionElapsed'[node] >= ELECTION_TIMEOUT /\ state[node] # StateLeader
            hbMsgs == { [ type |-> MsgHeartbeat, from |-> node, to |-> j, term |-> term[node],
                          prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                          commit |-> commitIndex[node], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
                        : j \in NODES \ {node} }
            needHb == state[node] = StateLeader /\ heartbeatElapsed'[node] >= HEARTBEAT_TIMEOUT
        IN
        /\ Net' =
             (IF needHb /\ needHup THEN Net \cup hbMsgs \cup {makeHup}
              ELSE IF needHb THEN Net \cup hbMsgs
              ELSE IF needHup THEN Net \cup {makeHup}
              ELSE Net)
        /\ IF needHb THEN heartbeatElapsed'' = [heartbeatElapsed' EXCEPT ![node] = 0] ELSE heartbeatElapsed'' = heartbeatElapsed'
        /\ heartbeatElapsed' = heartbeatElapsed''
  /\ UNCHANGED << state, term, vote, log, commitIndex, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>

Drop ==
  /\ Net # {}
  /\ \E m \in Net:
       /\ Net' = Net \ {m}
       /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>

ClientPropose ==
  /\ \E n \in NODES:
     LET payload == CHOOSE v: TRUE IN
     LET msg ==
       [ type |-> MsgProp, from |-> n, to |-> n, term |-> term[n],
         prevIndex |-> 0, prevTerm |-> 0,
         entries |-> << [term |-> 0, cmd |-> payload] >>,
         commit |-> 0, reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
     IN
     /\ Net' = Net \cup {msg}
     /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>

Deliver ==
  /\ Net # {}
  /\ \E m \in Net:
    LET from == m.from IN
    LET to == m.to IN
    LET t == m.term IN
    /\ CASE m.type = MsgHup ->
         /\ Net' = Net \ {m} \cup { [ type |-> MsgPreVote, from |-> to, to |-> j, term |-> term[to] + 1,
                                      prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                                      commit |-> 0, reject |-> FALSE, index |-> 0,
                                      lastIndex |-> LastIndex(log[to]), lastTerm |-> LastTerm(log[to]) ]
                                    : j \in NODES }
         /\ state' = [state EXCEPT ![to] = StatePreCandidate]
         /\ preVoteTerm' = [preVoteTerm EXCEPT ![to] = term[to] + 1]
         /\ preVotesGranted' = [preVotesGranted EXCEPT ![to] = {to}]
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
         /\ UNCHANGED << term, vote, log, commitIndex, heartbeatElapsed, votesGranted, match, nextIndex >>
       [] m.type = MsgPreVote ->
         /\ Net' = Net \ {m} \cup {
              [ type |-> MsgPreVoteResp, from |-> to, to |-> from,
                term |-> t, prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                commit |-> 0, reject |-> ~(t >= term[to] /\ UpToDate(m.lastTerm, m.lastIndex, log[to])),
                index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
         /\ UNCHANGED vars
       [] m.type = MsgPreVoteResp ->
         /\ Net' = Net \ {m}
         /\ IF state[to] = StatePreCandidate /\ preVoteTerm[to] = t /\ ~m.reject THEN
              LET newGrants == preVotesGranted[to] \cup {from} IN
              /\ preVotesGranted' = [preVotesGranted EXCEPT ![to] = newGrants]
              /\ IF Cardinality(newGrants) >= Quorum THEN
                   /\ state' = [state EXCEPT ![to] = StateCandidate]
                   /\ term' = [term EXCEPT ![to] = preVoteTerm[to]]
                   /\ vote' = [vote EXCEPT ![to] = to]
                   /\ votesGranted' = [votesGranted EXCEPT ![to] = {to}]
                   /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
                   /\ Net' = Net' \cup { [ type |-> MsgVote, from |-> to, to |-> j, term |-> term'[to],
                                           prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                                           commit |-> 0, reject |-> FALSE, index |-> 0,
                                           lastIndex |-> LastIndex(log[to]), lastTerm |-> LastTerm(log[to]) ] : j \in NODES }
                   /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVoteTerm, match, nextIndex >>
                 ELSE
                   /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVoteTerm, votesGranted, match, nextIndex >>
            ELSE
              /\ UNCHANGED vars
       [] m.type = MsgVote ->
         /\ Net' = Net \ {m} \cup {
              [ type |-> MsgVoteResp, from |-> to, to |-> from,
                term |-> IF t > term[to] THEN t ELSE term[to],
                prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                commit |-> 0,
                reject |-> ~( LET newTerm == IF t > term[to] THEN t ELSE term[to] IN
                               /\ newTerm = t
                               /\ (vote[to] = None \/ vote[to] = from)
                               /\ UpToDate(m.lastTerm, m.lastIndex, log[to]) ),
                index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
         /\ IF t > term[to] THEN
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
              /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
            ELSE
              /\ UNCHANGED << term, state, vote, electionElapsed >>
         /\ IF t >= term[to] /\ (vote[to] = None \/ vote[to] = from) /\ UpToDate(m.lastTerm, m.lastIndex, log[to]) THEN
              /\ vote' = [vote EXCEPT ![to] = from]
              /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
            ELSE
              /\ UNCHANGED << vote, electionElapsed >>
         /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgVoteResp ->
         /\ Net' = Net \ {m}
         /\ IF t > term[to] THEN
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
              /\ votesGranted' = [votesGranted EXCEPT ![to] = {}]
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, match, nextIndex >>
            ELSE IF state[to] = StateCandidate /\ t = term[to] THEN
              /\ votesGranted' = [votesGranted EXCEPT ![to] = (IF m.reject THEN votesGranted[to] ELSE votesGranted[to] \cup {from})]
              /\ IF Cardinality(votesGranted'[to]) >= Quorum THEN
                   LET newLog == Append(log[to], [term |-> term[to], cmd |-> "noop"]) IN
                   /\ state' = [state EXCEPT ![to] = StateLeader]
                   /\ log' = [log EXCEPT ![to] = newLog]
                   /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![to] = 0]
                   /\ match' = [match EXCEPT ![to] = [match[to] EXCEPT ![to] = LastIndex(newLog)]]
                   /\ nextIndex' = [nextIndex EXCEPT ![to] = [i \in NODES |-> LastIndex(newLog) + 1]]
                   /\ Net' = Net' \cup {
                        [ type |-> MsgApp, from |-> to, to |-> j, term |-> term[to],
                          prevIndex |-> nextIndex'[to][j] - 1,
                          prevTerm |-> TermAt(newLog, nextIndex'[to][j] - 1),
                          entries |-> SubSeq(newLog, nextIndex'[to][j], Len(newLog)),
                          commit |-> commitIndex[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
                        : j \in NODES \ {to} }
                   /\ UNCHANGED << term, vote, commitIndex, electionElapsed, preVotesGranted, preVoteTerm, votesGranted >>
                 ELSE
                   /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, match, nextIndex >>
            ELSE
              /\ UNCHANGED vars
       [] m.type = MsgApp ->
         /\ Net' = Net \ {m} \cup {
              [ type |-> MsgAppResp, from |-> to, to |-> from, term |-> IF t > term[to] THEN t ELSE term[to],
                prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                commit |-> 0,
                reject |-> ~( t >= term[to] /\ m.prevIndex <= Len(log[to]) /\ TermAt(log[to], m.prevIndex) = m.prevTerm ),
                index |-> IF (t >= term[to] /\ m.prevIndex <= Len(log[to]) /\ TermAt(log[to], m.prevTerm) = m.prevTerm)
                          THEN (m.prevIndex + Len(m.entries))
                          ELSE LastIndex(log[to]),
                lastIndex |-> 0, lastTerm |-> 0 ] }
         /\ IF t > term[to] THEN
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
              /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
            ELSE
              /\ UNCHANGED << term, state, vote, electionElapsed >>
         /\ IF t >= term[to] /\ m.prevIndex <= Len(log[to]) /\ TermAt(log[to], m.prevIndex) = m.prevTerm THEN
              LET newLog == SubSeq(log[to], 1, m.prevIndex) \o m.entries IN
              /\ log' = [log EXCEPT ![to] = newLog]
              /\ commitIndex' = [commitIndex EXCEPT ![to] = Min(m.commit, Len(newLog))]
              /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
            ELSE
              /\ UNCHANGED << log, commitIndex, electionElapsed >>
         /\ UNCHANGED << heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgAppResp ->
         /\ Net' = Net \ {m}
         /\ IF t > term[to] THEN
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
            ELSE IF state[to] = StateLeader /\ t = term[to] THEN
              /\ IF ~m.reject THEN
                   /\ match' = [match EXCEPT ![to] = [match[to] EXCEPT ![m.from] = m.index]]
                   /\ nextIndex' = [nextIndex EXCEPT ![to] = [nextIndex[to] EXCEPT ![m.from] = m.index + 1]]
                   /\ LET newC ==
                         Max({ j \in 0..Len(log[to]) :
                                CountGE(j, match'[to]) >= Quorum /\ TermAt(log[to], j) = term[to] })
                      IN commitIndex' = [commitIndex EXCEPT ![to] = Max(commitIndex[to], newC)]
                   /\ Net' =
                        IF nextIndex'[to][m.from] <= Len(log[to]) THEN
                          Net' \cup {
                            [ type |-> MsgApp, from |-> to, to |-> m.from, term |-> term[to],
                              prevIndex |-> nextIndex'[to][m.from] - 1,
                              prevTerm |-> TermAt(log[to], nextIndex'[to][m.from] - 1),
                              entries |-> SubSeq(log[to], nextIndex'[to][m.from], Len(log[to])),
                              commit |-> commitIndex'[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
                        ELSE Net'
                 ELSE
                   /\ nextIndex' = [nextIndex EXCEPT ![to] = [nextIndex[to] EXCEPT ![m.from] = Max(1, nextIndex[to][m.from] - 1)]]
                   /\ Net' = Net' \cup {
                        [ type |-> MsgApp, from |-> to, to |-> m.from, term |-> term[to],
                          prevIndex |-> nextIndex'[to][m.from] - 1,
                          prevTerm |-> TermAt(log[to], nextIndex'[to][m.from] - 1),
                          entries |-> SubSeq(log[to], nextIndex'[to][m.from], Len(log[to])),
                          commit |-> commitIndex[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
              /\ UNCHANGED << state, term, vote, log, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted >>
            ELSE
              /\ UNCHANGED vars
       [] m.type = MsgHeartbeat ->
         /\ Net' = Net \ {m} \cup {
              [ type |-> MsgHeartbeatResp, from |-> to, to |-> from, term |-> IF t > term[to] THEN t ELSE term[to],
                prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>, commit |-> 0, reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
         /\ IF t > term[to] THEN
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
            ELSE
              /\ UNCHANGED << term, state, vote >>
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
         /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgHeartbeatResp ->
         /\ Net' = Net \ {m}
         /\ UNCHANGED vars
       [] m.type = MsgProp ->
         /\ Net' = Net \ {m}
         /\ IF state[to] = StateLeader THEN
              LET e == [term |-> term[to], cmd |-> m.entries[1].cmd] IN
              LET newLog == Append(log[to], e) IN
              /\ log' = [log EXCEPT ![to] = newLog]
              /\ match' = [match EXCEPT ![to] = [match[to] EXCEPT ![to] = LastIndex(newLog)]]
              /\ nextIndex' = [nextIndex EXCEPT ![to] = [i \in NODES |-> LastIndex(newLog) + 1]]
              /\ Net' = Net' \cup {
                    [ type |-> MsgApp, from |-> to, to |-> j, term |-> term[to],
                      prevIndex |-> nextIndex'[to][j] - 1,
                      prevTerm |-> TermAt(newLog, nextIndex'[to][j] - 1),
                      entries |-> SubSeq(newLog, nextIndex'[to][j], Len(newLog)),
                      commit |-> commitIndex[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
                    : j \in NODES \ {to} }
              /\ UNCHANGED << state, term, vote, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted >>
            ELSE
              /\ UNCHANGED vars
       OTHER ->
         /\ Net' = Net \ {m}
         /\ UNCHANGED vars

Next == Tick(CHOOSE n \in NODES: TRUE)
        \/ Drop
        \/ ClientPropose
        \/ Deliver

Spec == Init /\ [][Next]_vars

====