---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  NODES,
  ELECTION_TIMEOUT,
  HEARTBEAT_INTERVAL

None == 0

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

MSG_TYPES == {
  MsgHup, MsgPreVote, MsgPreVoteResp, MsgVote, MsgVoteResp,
  MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgProp
}

StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
StatePreCandidate == "StatePreCandidate"
NODE_STATES == {StateFollower, StateCandidate, StateLeader, StatePreCandidate}

Entry == [term: Nat, data: Nat]

NodeOpt == NODES \cup {None}

Message ==
  [ type: MSG_TYPES,
    from: NodeOpt,
    to: NodeOpt,
    term: Nat,
    index: Nat,
    logterm: Nat,
    entries: Seq(Entry),
    commit: Nat,
    reject: BOOLEAN
  ]

VARIABLES
  term,              \* [n \in NODES -> Nat]
  vote,              \* [n \in NODES -> NodeOpt]
  state,             \* [n \in NODES -> NODE_STATES]
  lead,              \* [n \in NODES -> NodeOpt]
  log,               \* [n \in NODES -> Seq(Entry)]
  commit,            \* [n \in NODES -> Nat]
  electionElapsed,   \* [n \in NODES -> Nat]
  heartbeatElapsed,  \* [n \in NODES -> Nat]
  nextIndex,         \* [i \in NODES -> [j \in NODES -> Nat]]
  preVotes,          \* [n \in NODES -> SUBSET NODES]
  votes,             \* [n \in NODES -> SUBSET NODES]
  Net                \* SUBSET Message

Vars == << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes, Net >>

TermAt(L, k) ==
  IF k = 0 THEN 0 ELSE IF k <= Len(L) THEN L[k].term ELSE 0

LastIndex(n) == Len(log[n])
LastTerm(n) == TermAt(log[n], Len(log[n]))

Prefix(L, k) == IF k = 0 THEN << >> ELSE SubSeq(L, 1, k)
EntriesFrom(L, k) == IF k <= Len(L) THEN SubSeq(L, k, Len(L)) ELSE << >>

HasMajority(S) == 2 * Cardinality(S) > Cardinality(NODES)

UpToDateIdxTerm(cLogTerm, cLogIdx, r) ==
  LET myTerm == LastTerm(r)
      myIdx  == LastIndex(r)
  IN (cLogTerm > myTerm) \/ (cLogTerm = myTerm /\ cLogIdx >= myIdx)

Max(S) == CHOOSE k \in S : \A j \in S : j <= k

Init ==
  /\ term = [n \in NODES |-> 0]
  /\ vote = [n \in NODES |-> None]
  /\ state = [n \in NODES |-> StateFollower]
  /\ lead = [n \in NODES |-> None]
  /\ log = [n \in NODES |-> << >>]
  /\ commit = [n \in NODES |-> 0]
  /\ electionElapsed = [n \in NODES |-> 0]
  /\ heartbeatElapsed = [n \in NODES |-> 0]
  /\ nextIndex = [i \in NODES |-> [j \in NODES |-> 1]]
  /\ preVotes = [n \in NODES |-> {}]
  /\ votes = [n \in NODES |-> {}]
  /\ Net = {}

Tick(n) ==
  /\ n \in NODES
  /\ electionElapsed' = [electionElapsed EXCEPT ![n] = @ + 1]
  /\ heartbeatElapsed' =
       [heartbeatElapsed EXCEPT ![n] =
         @ + IF state[n] = StateLeader THEN 1 ELSE 0]
  /\ UNCHANGED << term, vote, state, lead, log, commit, nextIndex, preVotes, votes, Net >>

TimeoutHup(n) ==
  /\ n \in NODES
  /\ state[n] # StateLeader
  /\ electionElapsed[n] >= ELECTION_TIMEOUT
  /\ Net' = Net \cup {
        [type |-> MsgHup, from |-> n, to |-> n, term |-> term[n],
         index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[n], reject |-> FALSE]
      }
  /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << term, vote, state, lead, log, commit, heartbeatElapsed, nextIndex, preVotes, votes >>

Heartbeat(i) ==
  /\ i \in NODES
  /\ state[i] = StateLeader
  /\ heartbeatElapsed[i] >= HEARTBEAT_INTERVAL
  /\ LET msgs ==
        { [ type |-> MsgHeartbeat, from |-> i, to |-> j, term |-> term[i],
            index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[i], reject |-> FALSE ]
          : j \in NODES \ {i} }
     IN Net' = Net \cup msgs
  /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
  /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, nextIndex, preVotes, votes >>

ClientPropose(i, d) ==
  /\ i \in NODES
  /\ state[i] = StateLeader
  /\ d \in Nat
  /\ LET e == [term |-> term[i], data |-> d]
         newLog == Append(log[i], e)
         msgs ==
           { [ type |-> MsgApp, from |-> i, to |-> j, term |-> term[i],
               index |-> nextIndex[i][j] - 1,
               logterm |-> TermAt(newLog, nextIndex[i][j] - 1),
               entries |-> EntriesFrom(newLog, nextIndex[i][j]),
               commit |-> commit[i], reject |-> FALSE ]
             : j \in NODES \ {i} }
     IN /\ log' = [log EXCEPT ![i] = newLog]
        /\ Net' = Net \cup msgs
        /\ UNCHANGED << term, vote, state, lead, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>

Drop ==
  /\ Net # {}
  /\ \E m \in Net : TRUE
  /\ \E m \in Net :
        Net' = Net \ {m}
  /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>

Deliver ==
  /\ Net # {}
  /\ \E m \in Net :
      LET i == m.to IN
      CASE m.type = MsgHup ->
           /\ i \in NODES
           /\ state[i] # StateLeader
           /\ state' = [state EXCEPT ![i] = StatePreCandidate]
           /\ preVotes' = [preVotes EXCEPT ![i] = {i}]
           /\ votes' = votes
           /\ lead' = [lead EXCEPT ![i] = None]
           /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
           /\ heartbeatElapsed' = heartbeatElapsed
           /\ term' = term
           /\ vote' = vote
           /\ log' = log
           /\ commit' = commit
           /\ nextIndex' = nextIndex
           /\ Net' =
                (Net \ {m})
                \cup { [ type |-> MsgPreVote, from |-> i, to |-> j, term |-> term[i] + 1,
                         index |-> LastIndex(i), logterm |-> LastTerm(i),
                         entries |-> << >>, commit |-> commit[i], reject |-> FALSE ]
                       : j \in NODES \ {i} }
      [] m.type = MsgPreVote ->
           /\ i \in NODES
           /\ LET leaseOK == electionElapsed[i] >= ELECTION_TIMEOUT
                  up == UpToDateIdxTerm(m.logterm, m.index, i)
                  grant == leaseOK /\ up
                  resp ==
                    [ type |-> MsgPreVoteResp, from |-> i, to |-> m.from,
                      term |-> m.term, index |-> 0, logterm |-> 0,
                      entries |-> << >>, commit |-> commit[i], reject |-> ~grant ]
              IN Net' = (Net \ {m}) \cup {resp}
           /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
      [] m.type = MsgPreVoteResp ->
           /\ i \in NODES
           /\ state[i] = StatePreCandidate
           /\ m.term = term[i] + 1
           /\ IF ~m.reject THEN
                /\ preVotes' = [preVotes EXCEPT ![i] = @ \cup {m.from}]
                /\ IF HasMajority(preVotes'[i]) THEN
                     /\ state' = [state EXCEPT ![i] = StateCandidate]
                     /\ term' = [term EXCEPT ![i] = @ + 1]
                     /\ vote' = [vote EXCEPT ![i] = i]
                     /\ votes' = [votes EXCEPT ![i] = {i}]
                     /\ Net' =
                          (Net \ {m})
                          \cup { [ type |-> MsgVote, from |-> i, to |-> j, term |-> term'[i],
                                   index |-> LastIndex(i), logterm |-> LastTerm(i),
                                   entries |-> << >>, commit |-> commit[i], reject |-> FALSE ]
                               : j \in NODES \ {i} }
                     /\ UNCHANGED << lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex >>
                   ELSE
                     /\ Net' = (Net \ {m})
                     /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, votes >>
              ELSE
                /\ Net' = (Net \ {m})
                /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
      [] m.type = MsgVote ->
           /\ i \in NODES
           /\ IF m.term > term[i] THEN
                /\ term1 = [term EXCEPT ![i] = m.term]
                /\ state1 = [state EXCEPT ![i] = StateFollower]
                /\ vote1 = [vote EXCEPT ![i] = None]
                /\ lead1 = [lead EXCEPT ![i] = None]
              ELSE
                /\ term1 = term
                /\ state1 = state
                /\ vote1 = vote
                /\ lead1 = lead
           /\ LET canVote == (vote1[i] = None) \/ (vote1[i] = m.from)
                  up == UpToDateIdxTerm(m.logterm, m.index, i)
                  grant == canVote /\ up /\ (m.term >= term1[i])
                  resp ==
                    [ type |-> MsgVoteResp, from |-> i, to |-> m.from, term |-> MAX(m.term, term1[i]),
                      index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[i], reject |-> ~grant ]
              IN /\ Net' = (Net \ {m}) \cup {resp}
                 /\ term' = term1
                 /\ state' = state1
                 /\ vote' = [vote1 EXCEPT ![i] = IF grant THEN m.from ELSE vote1[i]]
                 /\ lead' = lead1
                 /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
      [] m.type = MsgVoteResp ->
           /\ i \in NODES
           /\ state[i] = StateCandidate
           /\ m.term = term[i]
           /\ IF ~m.reject THEN
                /\ votes' = [votes EXCEPT ![i] = @ \cup {m.from}]
                /\ IF HasMajority(votes'[i]) THEN
                     /\ state' = [state EXCEPT ![i] = StateLeader]
                     /\ lead' = [lead EXCEPT ![i] = i]
                     /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
                     /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in NODES |-> LastIndex(i) + 1]]
                     /\ log' = [log EXCEPT ![i] = Append(log[i], [term |-> term[i], data |-> 0])]
                     /\ Net' =
                          (Net \ {m})
                          \cup { [ type |-> MsgApp, from |-> i, to |-> j, term |-> term[i],
                                   index |-> nextIndex'[i][j] - 1,
                                   logterm |-> TermAt(log'[i], nextIndex'[i][j] - 1),
                                   entries |-> EntriesFrom(log'[i], nextIndex'[i][j]),
                                   commit |-> commit[i], reject |-> FALSE ]
                               : j \in NODES \ {i} }
                     /\ UNCHANGED << term, vote, commit, electionElapsed, preVotes >>
                   ELSE
                     /\ Net' = (Net \ {m})
                     /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
              ELSE
                /\ Net' = (Net \ {m})
                /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
      [] m.type = MsgApp ->
           /\ i \in NODES
           /\ IF m.term > term[i] THEN
                /\ term1 = [term EXCEPT ![i] = m.term]
                /\ state1 = [state EXCEPT ![i] = StateFollower]
                /\ vote1 = [vote EXCEPT ![i] = None]
              ELSE
                /\ term1 = term
                /\ state1 = state
                /\ vote1 = vote
           /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
           /\ lead' = [lead EXCEPT ![i] = m.from]
           /\ LET ok ==
                  (m.index <= Len(log[i])) /\ (TermAt(log[i], m.index) = m.logterm)
                  newLog ==
                    IF ok THEN
                      Prefix(log[i], m.index) \o m.entries
                    ELSE
                      log[i]
                  newCommit == IF ok THEN Min(m.commit, Len(newLog)) ELSE commit[i]
                  resp ==
                    [ type |-> MsgAppResp, from |-> i, to |-> m.from, term |-> term1[i],
                      index |-> IF ok THEN Len(newLog) ELSE m.index,
                      logterm |-> 0, entries |-> << >>, commit |-> newCommit, reject |-> ~ok ]
              IN /\ log' = [log EXCEPT ![i] = newLog]
                 /\ commit' = [commit EXCEPT ![i] = newCommit]
                 /\ Net' = (Net \ {m}) \cup {resp}
                 /\ term' = term1
                 /\ state' = state1
                 /\ vote' = vote1
                 /\ heartbeatElapsed' = heartbeatElapsed
                 /\ nextIndex' = nextIndex
                 /\ preVotes' = preVotes
                 /\ votes' = votes
      [] m.type = MsgAppResp ->
           /\ i \in NODES
           /\ state[i] = StateLeader
           /\ IF m.term > term[i] THEN
                /\ term' = [term EXCEPT ![i] = m.term]
                /\ state' = [state EXCEPT ![i] = StateFollower]
                /\ vote' = [vote EXCEPT ![i] = None]
                /\ lead' = [lead EXCEPT ![i] = None]
                /\ Net' = (Net \ {m})
                /\ UNCHANGED << log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
              ELSE
                /\ LET ni ==
                       IF m.reject THEN
                         [nextIndex EXCEPT ![i][m.from] = IF nextIndex[i][m.from] > 1 THEN nextIndex[i][m.from] - 1 ELSE 1]
                       ELSE
                         [nextIndex EXCEPT ![i][m.from] = Max(nextIndex[i][m.from], m.index + 1)]
                       ;
                       canSend ==
                         ni[i][m.from] <= Len(log[i])
                       ;
                       commitCand ==
                         { k \in Nat :
                             k >= commit[i] + 1 /\ k <= Len(log[i]) /\
                             log[i][k].term = term[i] /\
                             HasMajority({ n \in NODES : Len(log[n]) >= k }) }
                       ;
                       newCommit ==
                         IF commitCand = {} THEN commit[i] ELSE Max(commitCand)
                       ;
                       moreMsg ==
                         IF canSend THEN
                           { [ type |-> MsgApp, from |-> i, to |-> m.from, term |-> term[i],
                               index |-> ni[i][m.from] - 1,
                               logterm |-> TermAt(log[i], ni[i][m.from] - 1),
                               entries |-> EntriesFrom(log[i], ni[i][m.from]),
                               commit |-> newCommit, reject |-> FALSE ] }
                         ELSE {}
                  IN /\ nextIndex' = ni
                     /\ commit' = [commit EXCEPT ![i] = newCommit]
                     /\ Net' = (Net \ {m}) \cup moreMsg
                     /\ UNCHANGED << term, vote, state, lead, log, electionElapsed, heartbeatElapsed, preVotes, votes >>
      [] m.type = MsgHeartbeat ->
           /\ i \in NODES
           /\ IF m.term > term[i] THEN
                /\ term1 = [term EXCEPT ![i] = m.term]
                /\ state1 = [state EXCEPT ![i] = StateFollower]
                /\ vote1 = [vote EXCEPT ![i] = None]
              ELSE
                /\ term1 = term
                /\ state1 = state
                /\ vote1 = vote
           /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
           /\ lead' = [lead EXCEPT ![i] = m.from]
           /\ commit' = [commit EXCEPT ![i] = Min(m.commit, Len(log[i]))]
           /\ Net' = (Net \ {m}) \cup {
                 [ type |-> MsgHeartbeatResp, from |-> i, to |-> m.from, term |-> term1[i],
                   index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit'[i], reject |-> FALSE ]
               }
           /\ term' = term1
           /\ state' = state1
           /\ vote' = vote1
           /\ UNCHANGED << log, heartbeatElapsed, nextIndex, preVotes, votes >>
      [] m.type = MsgHeartbeatResp ->
           /\ i \in NODES
           /\ state[i] = StateLeader
           /\ LET canSend == nextIndex[i][m.from] <= Len(log[i])
                  msgset ==
                    IF canSend THEN
                      { [ type |-> MsgApp, from |-> i, to |-> m.from, term |-> term[i],
                          index |-> nextIndex[i][m.from] - 1,
                          logterm |-> TermAt(log[i], nextIndex[i][m.from] - 1),
                          entries |-> EntriesFrom(log[i], nextIndex[i][m.from]),
                          commit |-> commit[i], reject |-> FALSE ] }
                    ELSE {}
              IN /\ Net' = (Net \ {m}) \cup msgset
                 /\ UNCHANGED Vars
      [] m.type = MsgProp ->
           /\ i \in NODES
           /\ IF state[i] = StateLeader THEN
                /\ LET e == [term |-> term[i], data |-> IF Len(m.entries) = 0 THEN 0 ELSE m.entries[1].data]
                       newLog == Append(log[i], e)
                       msgs ==
                         { [ type |-> MsgApp, from |-> i, to |-> j, term |-> term[i],
                             index |-> nextIndex[i][j] - 1,
                             logterm |-> TermAt(newLog, nextIndex[i][j] - 1),
                             entries |-> EntriesFrom(newLog, nextIndex[i][j]),
                             commit |-> commit[i], reject |-> FALSE ]
                           : j \in NODES \ {i} }
                   IN /\ log' = [log EXCEPT ![i] = newLog]
                      /\ Net' = (Net \ {m}) \cup msgs
                      /\ UNCHANGED << term, vote, state, lead, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
              ELSE
                /\ IF lead[i] # None THEN
                     /\ Net' = (Net \ {m}) \cup {
                           [ type |-> MsgProp, from |-> m.from, to |-> lead[i], term |-> term[i],
                             index |-> 0, logterm |-> 0, entries |-> m.entries, commit |-> commit[i], reject |-> FALSE ]
                         }
                   ELSE
                     /\ Net' = (Net \ {m})
                /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, nextIndex, preVotes, votes >>
      OTHER ->
           /\ FALSE
  )

Next ==
  \/ \E n \in NODES : Tick(n)
  \/ \E n \in NODES : TimeoutHup(n)
  \/ \E i \in NODES : Heartbeat(i)
  \/ ClientPropose(CHOOSE i \in NODES : state[i] = StateLeader, CHOOSE d \in Nat : d \geq 0)
  \/ Deliver
  \/ Drop

Spec ==
  Init /\ [][Next]_Vars

====