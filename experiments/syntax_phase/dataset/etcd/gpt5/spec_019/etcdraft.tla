---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NODES,
    HeartbeatTimeout,
    ElectionTimeout

ASSUME HeartbeatTimeout \in Nat \ {0}
ASSUME ElectionTimeout \in Nat \ {0}
ASSUME NODES # {}

NONE == 0
NodeOrNone == NODES \cup {NONE}

StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
StatePreCandidate == "StatePreCandidate"
States == {StateFollower, StateCandidate, StateLeader, StatePreCandidate}

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
MsgTypes == {MsgHup, MsgPreVote, MsgPreVoteResp, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat, MsgHeartbeatResp, MsgProp}

Entry == [term: Nat]
Message == [ type: MsgTypes,
             from: NodeOrNone,
             to: NodeOrNone,
             term: Nat,
             index: Nat,
             logterm: Nat,
             entries: Seq(Entry),
             commit: Nat,
             reject: BOOLEAN ]

VARIABLES
    term,               \* [NODES -> Nat]
    vote,               \* [NODES -> NodeOrNone]
    state,              \* [NODES -> States]
    lead,               \* [NODES -> NodeOrNone]
    log,                \* [NODES -> Seq(Entry)]
    commit,             \* [NODES -> Nat]
    electionElapsed,    \* [NODES -> Nat]
    heartbeatElapsed,   \* [NODES -> Nat]
    prevotesGranted,    \* [NODES -> SUBSET NODES]
    votesGranted,       \* [NODES -> SUBSET NODES]
    matchIdx,           \* [NODES -> [NODES -> Nat]]
    net                 \* SUBSET Message

vars == << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx, net >>

\* Helpers

LastIndex(i) == Len(log[i])
TermAt(l, idx) == IF idx = 0 THEN 0 ELSE IF idx <= Len(l) THEN l[idx].term ELSE 0
LastTerm(i) == TermAt(log[i], LastIndex(i))

Majority(S) == Cardinality(S) > Cardinality(NODES) \div 2

UpToDate(candTerm, candIndex, i) ==
    candTerm > LastTerm(i) \/ (candTerm = LastTerm(i) /\ candIndex >= LastIndex(i))

EntryOf(t) == [term |-> t]

SubSeqOrEmpty(s, a, b) ==
    IF a > b THEN << >> ELSE SubSeq(s, a, b)

LogSuffix(l, fromIdx) ==
    SubSeqOrEmpty(l, fromIdx + 1, Len(l))

MatchAt(i,j) == IF j = i THEN Len(log[i]) ELSE matchIdx[i][j]

AckersAtLeast(i,k) == { j \in NODES : MatchAt(i,j) >= k }

ComputeCommit(i) ==
    LET S == { k \in 0..Len(log[i]) :
               Majority(AckersAtLeast(i,k)) /\ TermAt(log[i], k) = term[i] }
    IN IF S = {} THEN commit[i] ELSE Max(S)

\* Initialization

Init ==
    /\ term \in [NODES -> 0..0]
    /\ vote \in [NODES -> {NONE}]
    /\ state \in [NODES -> {StateFollower}]
    /\ lead \in [NODES -> {NONE}]
    /\ log \in [NODES -> {<< >>}]
    /\ commit \in [NODES -> 0..0]
    /\ electionElapsed \in [NODES -> 0..0]
    /\ heartbeatElapsed \in [NODES -> 0..0]
    /\ prevotesGranted \in [NODES -> {{}}]
    /\ votesGranted \in [NODES -> {{}}]
    /\ matchIdx \in [NODES -> [NODES -> 0..0]]
    /\ net = {}

\* Sending helpers

PreVoteMsgs(i) ==
    { [type |-> MsgPreVote,
       from |-> i,
       to |-> j,
       term |-> term[i] + 1,
       index |-> LastIndex(i),
       logterm |-> LastTerm(i),
       entries |-> << >>,
       commit |-> commit[i],
       reject |-> FALSE] : j \in NODES /\ j # i }

VoteMsgs(i, t) ==
    { [type |-> MsgVote,
       from |-> i,
       to |-> j,
       term |-> t,
       index |-> LastIndex(i),
       logterm |-> LastTerm(i),
       entries |-> << >>,
       commit |-> commit[i],
       reject |-> FALSE] : j \in NODES /\ j # i }

HeartbeatMsgs(i) ==
    { [type |-> MsgHeartbeat,
       from |-> i,
       to |-> j,
       term |-> term[i],
       index |-> 0,
       logterm |-> 0,
       entries |-> << >>,
       commit |-> commit[i],
       reject |-> FALSE] : j \in NODES /\ j # i }

AppendMsg(i,j,prevIdx) ==
    [ type |-> MsgApp,
      from |-> i,
      to |-> j,
      term |-> term[i],
      index |-> prevIdx,
      logterm |-> TermAt(log[i], prevIdx),
      entries |-> LogSuffix(log[i], prevIdx),
      commit |-> commit[i],
      reject |-> FALSE ]

BroadcastAppFromLeader(i) ==
    { AppendMsg(i,j, matchIdx[i][j]) : j \in NODES /\ j # i }

\* State transitions

BecomeFollower(i, newTerm, newLead) ==
    /\ term' = [term EXCEPT ![i] = newTerm]
    /\ state' = [state EXCEPT ![i] = StateFollower]
    /\ vote' = [vote EXCEPT ![i] = NONE]
    /\ lead' = [lead EXCEPT ![i] = newLead]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ heartbeatElapsed' = heartbeatElapsed
    /\ prevotesGranted' = [prevotesGranted EXCEPT ![i] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ UNCHANGED << log, commit, matchIdx, net >>

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = StatePreCandidate]
    /\ prevotesGranted' = [prevotesGranted EXCEPT ![i] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << term, vote, lead, log, commit, heartbeatElapsed, matchIdx, net >>

BecomeCandidate(i) ==
    /\ term' = [term EXCEPT ![i] = @ + 1]
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ vote' = [vote EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ prevotesGranted' = [prevotesGranted EXCEPT ![i] = {}]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << lead, log, commit, heartbeatElapsed, matchIdx, net >>

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ lead' = [lead EXCEPT ![i] = i]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
    /\ matchIdx' = [matchIdx EXCEPT ![i] = [j \in NODES |-> IF j = i THEN Len(log[i]) ELSE 0]]
    /\ log' = [log EXCEPT ![i] = Append(log[i], EntryOf(term[i]))]
    /\ UNCHANGED << term, vote, commit, electionElapsed, prevotesGranted, votesGranted, net >>

\* Message delivery

DeliverHup(m, i) ==
    /\ m \in net /\ m.type = MsgHup /\ m.to = i
    /\ state[i] # StateLeader
    /\ BecomePreCandidate(i)
    /\ net' = (net \ {m}) \cup PreVoteMsgs(i)

DeliverPreVote(m, j) ==
    /\ m \in net /\ m.type = MsgPreVote /\ m.to = j
    /\ LET grant == UpToDate(m.logterm, m.index, j) IN
       /\ net' = (net \ {m}) \cup {
            [type |-> MsgPreVoteResp, from |-> j, to |-> m.from, term |-> m.term,
             index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[j],
             reject |-> ~grant] }
       /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

DeliverPreVoteResp(m, i) ==
    /\ m \in net /\ m.type = MsgPreVoteResp /\ m.to = i
    /\ state[i] = StatePreCandidate
    /\ LET net1 == net \ {m} IN
       LET grantedSet == IF ~m.reject THEN prevotesGranted[i] \cup {m.from} ELSE prevotesGranted[i] IN
       LET condMajority == Majority(grantedSet) IN
       IF condMajority
       THEN
         /\ term' = [term EXCEPT ![i] = @ + 1]
         /\ state' = [state EXCEPT ![i] = StateCandidate]
         /\ vote' = [vote EXCEPT ![i] = i]
         /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
         /\ prevotesGranted' = [prevotesGranted EXCEPT ![i] = {}]
         /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
         /\ net' = net1 \cup VoteMsgs(i, term[i] + 1)
         /\ UNCHANGED << lead, log, commit, heartbeatElapsed, matchIdx >>
       ELSE
         /\ prevotesGranted' = [prevotesGranted EXCEPT ![i] = grantedSet]
         /\ net' = net1
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, votesGranted, matchIdx >>

DeliverVote(m, j) ==
    /\ m \in net /\ m.type = MsgVote /\ m.to = j
    /\ LET net1 == net \ {m} IN
       IF m.term < term[j] THEN
         /\ net' = net1 \cup {
             [type |-> MsgVoteResp, from |-> j, to |-> m.from, term |-> term[j],
              index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[j], reject |-> TRUE] }
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>
       ELSE
         /\ LET t2 == IF m.term > term[j] THEN m.term ELSE term[j] IN
            /\ term' = [term EXCEPT ![j] = t2]
            /\ state' = [state EXCEPT ![j] = StateFollower]
            /\ lead' = [lead EXCEPT ![j] = NONE]
            /\ electionElapsed' = [electionElapsed EXCEPT ![j] = 0]
            /\ LET canVote == (vote[j] = NONE) \/ (vote[j] = m.from) IN
               LET up == UpToDate(m.logterm, m.index, j) IN
               LET grant == canVote /\ up IN
               /\ vote' = [vote EXCEPT ![j] = IF grant THEN m.from ELSE vote[j]]
               /\ net' = net1 \cup {
                   [type |-> MsgVoteResp, from |-> j, to |-> m.from, term |-> m.term,
                    index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[j], reject |-> ~grant] }
               /\ UNCHANGED << log, commit, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

DeliverVoteResp(m, i) ==
    /\ m \in net /\ m.type = MsgVoteResp /\ m.to = i
    /\ state[i] = StateCandidate
    /\ LET net1 == net \ {m} IN
       LET grantedSet == IF ~m.reject THEN votesGranted[i] \cup {m.from} ELSE votesGranted[i] IN
       LET condMajority == Majority(grantedSet) IN
       IF condMajority
       THEN
         /\ state' = [state EXCEPT ![i] = StateLeader]
         /\ lead' = [lead EXCEPT ![i] = i]
         /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
         /\ prevotesGranted' = [prevotesGranted EXCEPT ![i] = {}]
         /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
         /\ matchIdx' = [matchIdx EXCEPT ![i] = [j \in NODES |-> IF j = i THEN Len(log[i]) ELSE 0]]
         /\ log' = [log EXCEPT ![i] = Append(log[i], EntryOf(term[i]))]
         /\ net' = net1 \cup BroadcastAppFromLeader(i)
         /\ UNCHANGED << term, vote, commit, electionElapsed >>
       ELSE
         /\ votesGranted' = [votesGranted EXCEPT ![i] = grantedSet]
         /\ net' = net1
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, matchIdx >>

DeliverApp(m, j) ==
    /\ m \in net /\ m.type = MsgApp /\ m.to = j
    /\ LET net1 == net \ {m} IN
       IF m.term < term[j] THEN
         /\ net' = net1 \cup {
              [type |-> MsgAppResp, from |-> j, to |-> m.from, term |-> term[j],
               index |-> LastIndex(j), logterm |-> LastTerm(j), entries |-> << >>, commit |-> commit[j], reject |-> TRUE] }
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>
       ELSE
         /\ LET t2 == IF m.term > term[j] THEN m.term ELSE term[j] IN
            /\ term' = [term EXCEPT ![j] = t2]
            /\ state' = [state EXCEPT ![j] = StateFollower]
            /\ lead' = [lead EXCEPT ![j] = m.from]
            /\ electionElapsed' = [electionElapsed EXCEPT ![j] = 0]
            /\ LET prevOK == (m.index <= Len(log[j])) /\ (TermAt(log[j], m.index) = m.logterm) IN
               IF prevOK THEN
                 /\ log' = [log EXCEPT ![j] = SubSeqOrEmpty(log[j], 1, m.index) \o m.entries]
                 /\ commit' = [commit EXCEPT ![j] = Min(m.commit, Len(log'[j]))]
                 /\ net' = net1 \cup {
                      [type |-> MsgAppResp, from |-> j, to |-> m.from, term |-> t2,
                       index |-> m.index + Len(m.entries), logterm |-> 0, entries |-> << >>, commit |-> commit'[j], reject |-> FALSE] }
                 /\ UNCHANGED << vote, state, lead, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx, term >>
               ELSE
                 /\ log' = log
                 /\ commit' = commit
                 /\ net' = net1 \cup {
                      [type |-> MsgAppResp, from |-> j, to |-> m.from, term |-> t2,
                       index |-> LastIndex(j), logterm |-> LastTerm(j), entries |-> << >>, commit |-> commit[j], reject |-> TRUE] }
                 /\ UNCHANGED << vote, state, lead, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx, term >>

DeliverAppResp(m, i) ==
    /\ m \in net /\ m.type = MsgAppResp /\ m.to = i
    /\ state[i] = StateLeader
    /\ LET net1 == net \ {m} IN
       IF m.reject THEN
         /\ net' = net1 \cup { AppendMsg(i, m.from, Min(m.index, Len(log[i]))) }
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>
       ELSE
         /\ matchIdx' = [matchIdx EXCEPT ![i][m.from] = Max(matchIdx[i][m.from], m.index)]
         /\ LET newCommit == ComputeCommit(i) IN
            /\ commit' = [commit EXCEPT ![i] = Max(commit[i], newCommit)]
            /\ net' = net1 \cup { AppendMsg(i, m.from, matchIdx'[i][m.from]) }
            /\ UNCHANGED << term, vote, state, lead, log, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted >>

DeliverHeartbeat(m, j) ==
    /\ m \in net /\ m.type = MsgHeartbeat /\ m.to = j
    /\ LET net1 == net \ {m} IN
       IF m.term < term[j] THEN
         /\ net' = net1
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>
       ELSE
         /\ LET t2 == IF m.term > term[j] THEN m.term ELSE term[j] IN
            /\ term' = [term EXCEPT ![j] = t2]
            /\ state' = [state EXCEPT ![j] = StateFollower]
            /\ lead' = [lead EXCEPT ![j] = m.from]
            /\ electionElapsed' = [electionElapsed EXCEPT ![j] = 0]
            /\ commit' = [commit EXCEPT ![j] = Min(m.commit, Len(log[j]))]
            /\ net' = net1 \cup {
                 [type |-> MsgHeartbeatResp, from |-> j, to |-> m.from, term |-> t2,
                  index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit'[j], reject |-> FALSE] }
            /\ UNCHANGED << vote, log, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

DeliverHeartbeatResp(m, i) ==
    /\ m \in net /\ m.type = MsgHeartbeatResp /\ m.to = i
    /\ net' = net \ {m}
    /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

DeliverProp(m, i) ==
    /\ m \in net /\ m.type = MsgProp /\ m.to = i
    /\ LET net1 == net \ {m} IN
       IF state[i] = StateLeader THEN
         /\ log' = [log EXCEPT ![i] = Append(log[i], EntryOf(term[i]))]
         /\ net' = net1 \cup BroadcastAppFromLeader(i)
         /\ UNCHANGED << term, vote, state, lead, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>
       ELSE
         /\ IF lead[i] # NONE THEN
               /\ net' = net1 \cup {
                    [type |-> MsgProp, from |-> m.from, to |-> lead[i], term |-> term[i],
                     index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[i], reject |-> FALSE] }
            ELSE
               /\ net' = net1
         /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

\* Network actions

Deliver ==
    \E m \in net:
      \/ \E i \in NODES: DeliverHup(m,i)
      \/ \E j \in NODES: DeliverPreVote(m,j)
      \/ \E i \in NODES: DeliverPreVoteResp(m,i)
      \/ \E j \in NODES: DeliverVote(m,j)
      \/ \E i \in NODES: DeliverVoteResp(m,i)
      \/ \E j \in NODES: DeliverApp(m,j)
      \/ \E i \in NODES: DeliverAppResp(m,i)
      \/ \E j \in NODES: DeliverHeartbeat(m,j)
      \/ \E i \in NODES: DeliverHeartbeatResp(m,i)
      \/ \E i \in NODES: DeliverProp(m,i)

Drop ==
    \E m \in net:
      /\ net' = net \ {m}
      /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

\* Time

TickElection(i) ==
    /\ i \in NODES /\ state[i] # StateLeader
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = @ + 1]
    /\ IF electionElapsed'[i] >= ElectionTimeout
          THEN /\ net' = net \cup { [type |-> MsgHup, from |-> i, to |-> i, term |-> term[i],
                                     index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[i], reject |-> FALSE] }
               /\ UNCHANGED << term, vote, state, lead, log, commit, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>
          ELSE /\ net' = net
               /\ UNCHANGED << term, vote, state, lead, log, commit, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

TickHeartbeat(i) ==
    /\ i \in NODES /\ state[i] = StateLeader
    /\ LET heartbeatElapsed1 == heartbeatElapsed[i] + 1 IN
       IF heartbeatElapsed1 >= HeartbeatTimeout
          THEN /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
               /\ net' = net \cup HeartbeatMsgs(i)
               /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, prevotesGranted, votesGranted, matchIdx >>
          ELSE /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = heartbeatElapsed1]
               /\ net' = net
               /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, prevotesGranted, votesGranted, matchIdx >>

Tick ==
    \/ \E i \in NODES: TickElection(i)
    \/ \E i \in NODES: TickHeartbeat(i)

\* Client proposals

ClientPropose ==
    \E i \in NODES:
      /\ net' = net \cup { [type |-> MsgProp, from |-> i, to |-> i, term |-> term[i],
                            index |-> 0, logterm |-> 0, entries |-> << >>, commit |-> commit[i], reject |-> FALSE] }
      /\ UNCHANGED << term, vote, state, lead, log, commit, electionElapsed, heartbeatElapsed, prevotesGranted, votesGranted, matchIdx >>

Next ==
    \/ Deliver
    \/ Drop
    \/ Tick
    \/ ClientPropose

Spec ==
    Init /\ [][Next]_vars

====