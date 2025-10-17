---- MODULE etcdraft ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS NODES, ELECTION_TIMEOUT, HEARTBEAT_TIMEOUT, CMDS

ASSUME NODES # {} /\ ELECTION_TIMEOUT \in Nat \ {0} /\ HEARTBEAT_TIMEOUT \in Nat \ {0} /\ CMDS # {}

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

Entry == [term: Nat, cmd: CMDS]
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
  state,           \* [Node -> StateType]
  term,            \* [Node -> Nat]
  vote,            \* [Node -> (NODES \cup {None})]
  log,             \* [Node -> EntrySeq]
  commitIndex,     \* [Node -> Nat]
  electionElapsed, \* [Node -> Nat]
  heartbeatElapsed,\* [Node -> Nat]
  preVotesGranted, \* [Node -> SUBSET NODES]
  preVoteTerm,     \* [Node -> Nat]
  votesGranted,    \* [Node -> SUBSET NODES]
  match,           \* [Node -> [Node -> Nat]]
  nextIndex,       \* [Node -> [Node -> Nat]]
  Net              \* set of messages

vars == << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex, Net >>

Init ==
  /\ state \in [NODES -> {StateFollower}]
  /\ term \in [NODES -> Nat]
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
  /\ LET hInc == IF state[node] = StateLeader THEN 1 ELSE 0
         hNext == heartbeatElapsed[node] + hInc
         eNext == electionElapsed[node] + 1
         needHb == state[node] = StateLeader /\ hNext >= HEARTBEAT_TIMEOUT
         needHup == eNext >= ELECTION_TIMEOUT /\ state[node] # StateLeader
         makeHup ==
           [ type |-> MsgHup, from |-> node, to |-> node, term |-> term[node],
             prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
             commit |-> 0, reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
         hbMsgs ==
           { [ type |-> MsgHeartbeat, from |-> node, to |-> j, term |-> term[node],
               prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
               commit |-> commitIndex[node], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
             : j \in NODES \ {node} }
         net1 == IF needHb THEN Net \cup hbMsgs ELSE Net
         net2 == IF needHup THEN net1 \cup {makeHup} ELSE net1
     IN
     /\ Net' = net2
     /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![node] = IF needHb THEN 0 ELSE hNext]
     /\ electionElapsed' = [electionElapsed EXCEPT ![node] = eNext]
  /\ UNCHANGED << state, term, vote, log, commitIndex, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>

Drop ==
  /\ Net # {}
  /\ \E m \in Net:
       /\ Net' = Net \ {m}
       /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>

ClientPropose ==
  /\ \E n \in NODES:
     LET payload == CHOOSE v \in CMDS: TRUE IN
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
    LET net0 == Net \ {m} IN
    /\ CASE m.type = MsgHup ->
         LET out ==
             { [ type |-> MsgPreVote, from |-> to, to |-> j, term |-> term[to] + 1,
                 prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                 commit |-> 0, reject |-> FALSE, index |-> 0,
                 lastIndex |-> LastIndex(log[to]), lastTerm |-> LastTerm(log[to]) ]
               : j \in NODES }
         IN
         /\ Net' = net0 \cup out
         /\ state' = [state EXCEPT ![to] = StatePreCandidate]
         /\ preVoteTerm' = [preVoteTerm EXCEPT ![to] = term[to] + 1]
         /\ preVotesGranted' = [preVotesGranted EXCEPT ![to] = {to}]
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
         /\ UNCHANGED << term, vote, log, commitIndex, heartbeatElapsed, votesGranted, match, nextIndex >>
       [] m.type = MsgPreVote ->
         LET can ==
               t >= term[to] /\ UpToDate(m.lastTerm, m.lastIndex, log[to])
             resp ==
               [ type |-> MsgPreVoteResp, from |-> to, to |-> from,
                 term |-> t, prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                 commit |-> 0, reject |-> ~can,
                 index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
         IN
         /\ Net' = net0 \cup {resp}
         /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgPreVoteResp ->
         LET condOK == state[to] = StatePreCandidate /\ preVoteTerm[to] = t /\ ~m.reject
             newGrants == preVotesGranted[to] \cup {from}
             reached == Cardinality(newGrants) >= Quorum
             out ==
               { [ type |-> MsgVote, from |-> to, to |-> j, term |-> preVoteTerm[to],
                   prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                   commit |-> 0, reject |-> FALSE, index |-> 0,
                   lastIndex |-> LastIndex(log[to]), lastTerm |-> LastTerm(log[to]) ]
                 : j \in NODES }
         IN
         /\ Net' = net0 \cup (IF condOK /\ reached THEN out ELSE {})
         /\ preVotesGranted' = [preVotesGranted EXCEPT ![to] = IF condOK THEN newGrants ELSE @]
         /\ state' = [state EXCEPT ![to] = IF condOK /\ reached THEN StateCandidate ELSE @]
         /\ term' = [term EXCEPT ![to] = IF condOK /\ reached THEN preVoteTerm[to] ELSE @]
         /\ vote' = [vote EXCEPT ![to] = IF condOK /\ reached THEN to ELSE @]
         /\ votesGranted' = [votesGranted EXCEPT ![to] = IF condOK /\ reached THEN {to} ELSE @]
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = IF condOK /\ reached THEN 0 ELSE @]
         /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVoteTerm, match, nextIndex >>
       [] m.type = MsgVote ->
         LET tNew == IF t > term[to] THEN t ELSE term[to]
             wasVote == IF t > term[to] THEN None ELSE vote[to]
             canGrant == (t = tNew) /\ (wasVote = None \/ wasVote = from)
                          /\ UpToDate(m.lastTerm, m.lastIndex, log[to])
             resp ==
               [ type |-> MsgVoteResp, from |-> to, to |-> from,
                 term |-> tNew, prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                 commit |-> 0, reject |-> ~canGrant,
                 index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
         IN
         /\ Net' = net0 \cup {resp}
         /\ term' = [term EXCEPT ![to] = tNew]
         /\ state' = [state EXCEPT ![to] = IF t > term[to] THEN StateFollower ELSE @]
         /\ vote' = [vote EXCEPT ![to] = IF canGrant THEN from ELSE wasVote]
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = IF (t > term[to]) \/ canGrant THEN 0 ELSE @]
         /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgVoteResp ->
         /\ Net' = net0
         /\ IF t > term[to] THEN
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
              /\ votesGranted' = [votesGranted EXCEPT ![to] = {}]
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, match, nextIndex >>
            ELSE IF state[to] = StateCandidate /\ t = term[to] THEN
              LET newVG == IF m.reject THEN votesGranted[to] ELSE votesGranted[to] \cup {from}
                  reach == Cardinality(newVG) >= Quorum
                  newLog == IF reach THEN Append(log[to], [term |-> term[to], cmd |-> CHOOSE v \in CMDS: TRUE]) ELSE log[to]
                  out ==
                    { [ type |-> MsgApp, from |-> to, to |-> j, term |-> term[to],
                        prevIndex |-> (IF reach THEN (Len(newLog)) ELSE Len(log[to])) + 1 - 1,
                        prevTerm |-> TermAt(newLog, (IF reach THEN (Len(newLog)) ELSE Len(log[to])) + 1 - 1),
                        entries |-> (IF reach THEN SubSeq(newLog, Len(newLog), Len(newLog)) ELSE << >>),
                        commit |-> commitIndex[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
                      : j \in NODES \ {to} }
              IN
              /\ votesGranted' = [votesGranted EXCEPT ![to] = newVG]
              /\ IF reach THEN
                   /\ state' = [state EXCEPT ![to] = StateLeader]
                   /\ log' = [log EXCEPT ![to] = newLog]
                   /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![to] = 0]
                   /\ match' = [match EXCEPT ![to] = [match[to] EXCEPT ![to] = LastIndex(newLog)]]
                   /\ nextIndex' = [nextIndex EXCEPT ![to] = [i \in NODES |-> LastIndex(newLog) + 1]]
                   /\ Net' = Net' \cup out
                   /\ UNCHANGED << term, vote, commitIndex, electionElapsed, preVotesGranted, preVoteTerm >>
                 ELSE
                   /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, match, nextIndex >>
            ELSE
              /\ UNCHANGED vars
       [] m.type = MsgApp ->
         LET ok == t >= term[to] /\ m.prevIndex <= Len(log[to]) /\ TermAt(log[to], m.prevIndex) = m.prevTerm
             tNew == IF t > term[to] THEN t ELSE term[to]
             idxResp == IF ok THEN (m.prevIndex + Len(m.entries)) ELSE LastIndex(log[to])
             resp ==
               [ type |-> MsgAppResp, from |-> to, to |-> from, term |-> tNew,
                 prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                 commit |-> 0, reject |-> ~ok, index |-> idxResp, lastIndex |-> 0, lastTerm |-> 0 ]
             newLog == IF ok THEN (SubSeq(log[to], 1, m.prevIndex) \o m.entries) ELSE log[to]
             newCommit == IF ok THEN Min(m.commit, Len(newLog)) ELSE commitIndex[to]
         IN
         /\ Net' = net0 \cup {resp}
         /\ term' = [term EXCEPT ![to] = tNew]
         /\ state' = [state EXCEPT ![to] = IF t > term[to] THEN StateFollower ELSE @]
         /\ vote' = [vote EXCEPT ![to] = IF t > term[to] THEN None ELSE @]
         /\ log' = [log EXCEPT ![to] = newLog]
         /\ commitIndex' = [commitIndex EXCEPT ![to] = newCommit]
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = IF (t > term[to]) \/ ok THEN 0 ELSE @]
         /\ UNCHANGED << heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgAppResp ->
         /\ IF t > term[to] THEN
              /\ Net' = net0
              /\ term' = [term EXCEPT ![to] = t]
              /\ state' = [state EXCEPT ![to] = StateFollower]
              /\ vote' = [vote EXCEPT ![to] = None]
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
            ELSE IF state[to] = StateLeader /\ t = term[to] THEN
              /\ IF ~m.reject THEN
                   LET match1 == [match EXCEPT ![to] = [match[to] EXCEPT ![m.from] = m.index]]
                       next1 == [nextIndex EXCEPT ![to] = [nextIndex[to] EXCEPT ![m.from] = m.index + 1]]
                       S == { j \in 0..Len(log[to]) : CountGE(j, match1[to]) >= Quorum /\ TermAt(log[to], j) = term[to] }
                       newC == Max({commitIndex[to]} \cup S)
                       needMore == next1[to][m.from] <= Len(log[to])
                       out ==
                         IF needMore THEN
                           { [ type |-> MsgApp, from |-> to, to |-> m.from, term |-> term[to],
                               prevIndex |-> next1[to][m.from] - 1,
                               prevTerm |-> TermAt(log[to], next1[to][m.from] - 1),
                               entries |-> SubSeq(log[to], next1[to][m.from], Len(log[to])),
                               commit |-> newC, reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
                         ELSE {}
                   IN
                   /\ Net' = net0 \cup out
                   /\ match' = match1
                   /\ nextIndex' = next1
                   /\ commitIndex' = [commitIndex EXCEPT ![to] = newC]
                   /\ UNCHANGED << state, term, vote, log, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted >>
                 ELSE
                   LET next1 == [nextIndex EXCEPT ![to] = [nextIndex[to] EXCEPT ![m.from] = Max(1, nextIndex[to][m.from] - 1)]]
                       out ==
                         { [ type |-> MsgApp, from |-> to, to |-> m.from, term |-> term[to],
                             prevIndex |-> next1[to][m.from] - 1,
                             prevTerm |-> TermAt(log[to], next1[to][m.from] - 1),
                             entries |-> SubSeq(log[to], next1[to][m.from], Len(log[to])),
                             commit |-> commitIndex[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ] }
                   IN
                   /\ Net' = net0 \cup out
                   /\ nextIndex' = next1
                   /\ UNCHANGED << state, term, vote, log, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match >>
            ELSE
              /\ Net' = net0
              /\ UNCHANGED vars
       [] m.type = MsgHeartbeat ->
         LET tNew == IF t > term[to] THEN t ELSE term[to]
             resp ==
               [ type |-> MsgHeartbeatResp, from |-> to, to |-> from, term |-> tNew,
                 prevIndex |-> 0, prevTerm |-> 0, entries |-> << >>,
                 commit |-> 0, reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
         IN
         /\ Net' = net0 \cup {resp}
         /\ term' = [term EXCEPT ![to] = tNew]
         /\ state' = [state EXCEPT ![to] = IF t > term[to] THEN StateFollower ELSE @]
         /\ vote' = [vote EXCEPT ![to] = IF t > term[to] THEN None ELSE @]
         /\ electionElapsed' = [electionElapsed EXCEPT ![to] = 0]
         /\ UNCHANGED << log, commitIndex, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted, match, nextIndex >>
       [] m.type = MsgHeartbeatResp ->
         /\ Net' = net0
         /\ UNCHANGED vars
       [] m.type = MsgProp ->
         /\ IF state[to] = StateLeader THEN
              LET e == [term |-> term[to], cmd |-> m.entries[1].cmd]
                  newLog == Append(log[to], e)
                  out ==
                    { [ type |-> MsgApp, from |-> to, to |-> j, term |-> term[to],
                        prevIndex |-> (LastIndex(newLog) + 1) - 1,
                        prevTerm |-> TermAt(newLog, (LastIndex(newLog) + 1) - 1),
                        entries |-> SubSeq(newLog, LastIndex(newLog), LastIndex(newLog)),
                        commit |-> commitIndex[to], reject |-> FALSE, index |-> 0, lastIndex |-> 0, lastTerm |-> 0 ]
                      : j \in NODES \ {to} }
              IN
              /\ Net' = net0 \cup out
              /\ log' = [log EXCEPT ![to] = newLog]
              /\ match' = [match EXCEPT ![to] = [match[to] EXCEPT ![to] = LastIndex(newLog)]]
              /\ nextIndex' = [nextIndex EXCEPT ![to] = [i \in NODES |-> LastIndex(newLog) + 1]]
              /\ UNCHANGED << state, term, vote, commitIndex, electionElapsed, heartbeatElapsed, preVotesGranted, preVoteTerm, votesGranted >>
            ELSE
              /\ Net' = net0
              /\ UNCHANGED vars
       OTHER ->
         /\ Net' = net0
         /\ UNCHANGED vars

Next == Tick(CHOOSE n \in NODES: TRUE)
        \/ Drop
        \/ ClientPropose
        \/ Deliver

Spec == Init /\ [][Next]_vars

====