---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS
    NODES,
    ELECTION_TIMEOUT,
    HEARTBEAT_TIMEOUT

Nil == "Nil"

States == {"StateFollower","StatePreCandidate","StateCandidate","StateLeader"}

MsgType ==
    {"MsgHup","MsgPreVote","MsgPreVoteResp","MsgVote","MsgVoteResp",
     "MsgApp","MsgAppResp","MsgHeartbeat","MsgHeartbeatResp","MsgProp"}

Entry == [term: Nat]

Message == [type: MsgType,
            from: NODES,
            to: NODES,
            term: Nat,
            index: Nat,
            logterm: Nat,
            entries: Seq(Entry),
            commit: Nat,
            reject: BOOLEAN]

Q == Cardinality(NODES) \div 2 + 1

VARIABLES
    state,            \* [NODES -> States]
    term,             \* [NODES -> Nat]
    votedFor,         \* [NODES -> (NODES \cup {Nil})]
    leader,           \* [NODES -> (NODES \cup {Nil})]
    log,              \* [NODES -> Seq(Entry)]
    commitIndex,      \* [NODES -> Nat]
    electionElapsed,  \* [NODES -> Nat]
    heartbeatElapsed, \* [NODES -> Nat]
    prevotesGranted,  \* [NODES -> SUBSET NODES]
    votesGranted,     \* [NODES -> SUBSET NODES]
    matchIndex,       \* [NODES -> [NODES -> Nat]]
    msgs              \* SUBSET Message

Msg(t,f,toN,tr,idx,ltr,es,com,rej) ==
    [type |-> t, from |-> f, to |-> toN, term |-> tr, index |-> idx,
     logterm |-> ltr, entries |-> es, commit |-> com, reject |-> rej]

LastIndex(n) == Len(log[n])

LastTerm(n) == IF LastIndex(n) = 0 THEN 0 ELSE log[n][LastIndex(n)].term

TermAtNode(n, i) ==
    IF i = 0 THEN 0
    ELSE IF i <= LastIndex(n) THEN log[n][i].term ELSE 0

UpToDate(candTerm, candIdx, n) ==
    candTerm > LastTerm(n)
    \/ (candTerm = LastTerm(n) /\ candIdx >= LastIndex(n))

AppendAt(n, idx, es) ==
    IF idx = 0 THEN es ELSE SubSeq(log[n], 1, idx) \o es

SuffixFrom(n, k) ==
    IF k < LastIndex(n) THEN SubSeq(log[n], k+1, LastIndex(n)) ELSE <<>>

QuorumReached(S) == Cardinality(S) >= Q

MaxNat(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S: \A x \in S: m >= x

CommSet(n) ==
    { i \in 0..LastIndex(n) :
        (TermAtNode(n,i) = term[n])
        /\ (Cardinality({ p \in NODES: matchIndex[n][p] >= i }) >= Q)
    }

Init ==
    /\ state = [n \in NODES |-> "StateFollower"]
    /\ term = [n \in NODES |-> 0]
    /\ votedFor = [n \in NODES |-> Nil]
    /\ leader = [n \in NODES |-> Nil]
    /\ log = [n \in NODES |-> <<>>]
    /\ commitIndex = [n \in NODES |-> 0]
    /\ electionElapsed = [n \in NODES |-> 0]
    /\ heartbeatElapsed = [n \in NODES |-> 0]
    /\ prevotesGranted = [n \in NODES |-> {}]
    /\ votesGranted = [n \in NODES |-> {}]
    /\ matchIndex =
        [l \in NODES |-> [p \in NODES |-> 0]]
    /\ msgs = {}

TickElection(n) ==
    /\ n \in NODES
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
    /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex, heartbeatElapsed,
                   prevotesGranted, votesGranted, matchIndex, msgs >>

Hup(n) ==
    /\ n \in NODES
    /\ state[n] # "StateLeader"
    /\ electionElapsed[n] >= ELECTION_TIMEOUT
    /\ state' = [state EXCEPT ![n] = "StatePreCandidate"]
    /\ prevotesGranted' = [prevotesGranted EXCEPT ![n] = {n}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ leader' = [leader EXCEPT ![n] = Nil]
    /\ LET S ==
        { Msg("MsgPreVote", n, p, term[n] + 1, LastIndex(n), LastTerm(n), <<>>, commitIndex[n], FALSE)
          : p \in NODES \ {n} }
       IN msgs' = msgs \cup S
    /\ UNCHANGED << term, votedFor, log, commitIndex, heartbeatElapsed, matchIndex >>

DeliverPreVote ==
    \E m \in msgs:
      /\ m.type = "MsgPreVote"
      /\ LET i == m.to IN
         /\ LET up == UpToDate(m.logterm, m.index, i) IN
            /\ msgs' =
                (msgs \ {m})
                \cup {
                    Msg("MsgPreVoteResp", i, m.from, m.term, 0, 0, <<>>, 0, ~up)
                   }
            /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                           electionElapsed, heartbeatElapsed, prevotesGranted,
                           votesGranted, matchIndex >>

DeliverPreVoteResp ==
    \E m \in msgs:
      /\ m.type = "MsgPreVoteResp"
      /\ LET n == m.to IN
         /\ LET granted == ~m.reject IN
            /\ LET cond == (state[n] = "StatePreCandidate") /\ granted IN
               /\ LET prevNew == IF cond THEN prevotesGranted[n] \cup {m.from} ELSE prevotesGranted[n] IN
                  /\ IF cond /\ ~QuorumReached(prevNew) THEN
                       /\ prevotesGranted' = [prevotesGranted EXCEPT ![n] = prevNew]
                       /\ msgs' = msgs \ {m}
                       /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                                      electionElapsed, heartbeatElapsed, votesGranted, matchIndex >>
                     ELSE IF cond /\ QuorumReached(prevNew) THEN
                       /\ state' = [state EXCEPT ![n] = "StateCandidate"]
                       /\ term' = [term EXCEPT ![n] = term[n] + 1]
                       /\ votedFor' = [votedFor EXCEPT ![n] = n]
                       /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
                       /\ prevotesGranted' = [prevotesGranted EXCEPT ![n] = {}]
                       /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
                       /\ leader' = [leader EXCEPT ![n] = Nil]
                       /\ LET S ==
                            { Msg("MsgVote", n, p, term[n] + 1, LastIndex(n), LastTerm(n), <<>>, commitIndex[n], FALSE)
                              : p \in NODES \ {n} }
                          IN msgs' = (msgs \ {m}) \cup S
                       /\ UNCHANGED << log, commitIndex, heartbeatElapsed, matchIndex >>
                     ELSE
                       /\ msgs' = msgs \ {m}
                       /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                                      electionElapsed, heartbeatElapsed, prevotesGranted,
                                      votesGranted, matchIndex >>

DeliverVote ==
    \E m \in msgs:
      /\ m.type = "MsgVote"
      /\ LET i == m.to IN
         /\ LET
              tNew == IF m.term > term[i] THEN m.term ELSE term[i]
              vfReset == IF m.term > term[i] THEN Nil ELSE votedFor[i]
              canVote == (m.term = tNew) /\ (vfReset = Nil \/ vfReset = m.from)
              up == UpToDate(m.logterm, m.index, i)
              grant == canVote /\ up
              vfNew == IF grant THEN m.from ELSE vfReset
              resp == Msg("MsgVoteResp", i, m.from, tNew, 0, 0, <<>>, 0, ~grant)
            IN
            /\ msgs' = (msgs \ {m}) \cup {resp}
            /\ term' = [term EXCEPT ![i] = tNew]
            /\ state' = [state EXCEPT ![i] = "StateFollower"]
            /\ leader' = [leader EXCEPT ![i] = Nil]
            /\ votedFor' = [votedFor EXCEPT ![i] = vfNew]
            /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed,
                           prevotesGranted, votesGranted, matchIndex >>

DeliverVoteResp ==
    \E m \in msgs:
      /\ m.type = "MsgVoteResp"
      /\ LET n == m.to IN
         /\ msgs' = msgs \ {m}
         /\ IF m.term > term[n] THEN
              /\ term' = [term EXCEPT ![n] = m.term]
              /\ state' = [state EXCEPT ![n] = "StateFollower"]
              /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
              /\ leader' = [leader EXCEPT ![n] = Nil]
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed,
                             prevotesGranted, votesGranted, matchIndex >>
            ELSE
              /\ IF state[n] = "StateCandidate" /\ ~m.reject /\ (m.term = term[n]) THEN
                   /\ LET newVotes == votesGranted[n] \cup {m.from} IN
                      /\ votesGranted' =
                           [votesGranted EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN {} ELSE newVotes]
                      /\ state' =
                           [state EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN "StateLeader" ELSE state[n]]
                      /\ leader' =
                           [leader EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN n ELSE leader[n]]
                      /\ prevotesGranted' =
                           [prevotesGranted EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN {} ELSE prevotesGranted[n]]
                      /\ log' =
                           [log EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN log[n] \o << [term |-> term[n]] >>
                             ELSE log[n]]
                      /\ matchIndex' =
                           [matchIndex EXCEPT ![n][n] =
                             IF QuorumReached(newVotes) THEN LastIndex(n) + 1 ELSE matchIndex[n][n]]
                      /\ electionElapsed' =
                           [electionElapsed EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN 0 ELSE electionElapsed[n]]
                      /\ heartbeatElapsed' =
                           [heartbeatElapsed EXCEPT ![n] =
                             IF QuorumReached(newVotes) THEN 0 ELSE heartbeatElapsed[n]]
                      /\ UNCHANGED << term, votedFor, commitIndex >>
                 ELSE
                   /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                                  electionElapsed, heartbeatElapsed, prevotesGranted,
                                  votesGranted, matchIndex >>

LeaderSendAppend ==
    \E l \in NODES:
      /\ state[l] = "StateLeader"
      /\ \E p \in NODES \ {l}:
           /\ msgs' =
               msgs \cup {
                 Msg("MsgApp", l, p, term[l],
                     matchIndex[l][p],
                     TermAtNode(l, matchIndex[l][p]),
                     SuffixFrom(l, matchIndex[l][p]),
                     commitIndex[l], FALSE)
               }
           /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                          electionElapsed, heartbeatElapsed, prevotesGranted,
                          votesGranted, matchIndex >>

DeliverAppend ==
    \E m \in msgs:
      /\ m.type = "MsgApp"
      /\ LET i == m.to IN
         /\ LET
              tNew == IF m.term > term[i] THEN m.term ELSE term[i]
              stNew == "StateFollower"
              leadNew == m.from
              consistent == (TermAtNode(i, m.index) = m.logterm)
              newLog == AppendAt(i, m.index, m.entries)
              newLen == m.index + Len(m.entries)
              ciNew == IF consistent THEN
                         IF m.commit <= newLen THEN m.commit ELSE newLen
                       ELSE commitIndex[i]
              respOK == Msg("MsgAppResp", i, m.from, tNew, newLen, 0, <<>>, 0, FALSE)
              respRJ == Msg("MsgAppResp", i, m.from, tNew, m.index, 0, <<>>, 0, TRUE)
            IN
            /\ msgs' =
                (msgs \ {m}) \cup { IF consistent THEN respOK ELSE respRJ }
            /\ term' = [term EXCEPT ![i] = tNew]
            /\ state' = [state EXCEPT ![i] = stNew]
            /\ leader' = [leader EXCEPT ![i] = leadNew]
            /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
            /\ commitIndex' =
                 [commitIndex EXCEPT ![i] = ciNew]
            /\ IF consistent THEN
                 /\ log' = [log EXCEPT ![i] = newLog]
               ELSE
                 /\ UNCHANGED log
            /\ UNCHANGED << votedFor, heartbeatElapsed, prevotesGranted, votesGranted, matchIndex >>

DeliverAppendResp ==
    \E m \in msgs:
      /\ m.type = "MsgAppResp"
      /\ LET l == m.to IN
         /\ msgs' = msgs \ {m}
         /\ IF m.term > term[l] THEN
              /\ term' = [term EXCEPT ![l] = m.term]
              /\ state' = [state EXCEPT ![l] = "StateFollower"]
              /\ votedFor' = [votedFor EXCEPT ![l] = Nil]
              /\ leader' = [leader EXCEPT ![l] = Nil]
              /\ UNCHANGED << log, commitIndex, electionElapsed, heartbeatElapsed,
                             prevotesGranted, votesGranted, matchIndex >>
            ELSE
              /\ IF state[l] = "StateLeader" /\ ~m.reject THEN
                   /\ matchIndex' =
                        [matchIndex EXCEPT ![l][m.from] = m.index, ![l][l] = LastIndex(l)]
                   /\ LET
                        cset == CommSet(l)
                        newC == MaxNat(cset)
                        ciNew == IF newC > commitIndex[l] THEN newC ELSE commitIndex[l]
                      IN commitIndex' = [commitIndex EXCEPT ![l] = ciNew]
                   /\ UNCHANGED << state, term, votedFor, leader, log,
                                  electionElapsed, heartbeatElapsed, prevotesGranted,
                                  votesGranted >>
                 ELSE
                   /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                                  electionElapsed, heartbeatElapsed, prevotesGranted,
                                  votesGranted, matchIndex >>

LeaderHeartbeat ==
    \E l \in NODES:
      /\ state[l] = "StateLeader"
      /\ LET S ==
          { Msg("MsgHeartbeat", l, p, term[l], 0, 0, <<>>, commitIndex[l], FALSE)
            : p \in NODES \ {l} }
         IN msgs' = msgs \cup S
      /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                     electionElapsed, heartbeatElapsed, prevotesGranted,
                     votesGranted, matchIndex >>

DeliverHeartbeat ==
    \E m \in msgs:
      /\ m.type = "MsgHeartbeat"
      /\ LET i == m.to IN
         /\ LET
              tNew == IF m.term > term[i] THEN m.term ELSE term[i]
              stNew == "StateFollower"
              leadNew == m.from
              ciNew == IF m.commit <= LastIndex(i) THEN m.commit ELSE LastIndex(i)
            IN
            /\ msgs' = msgs \ {m}
            /\ term' = [term EXCEPT ![i] = tNew]
            /\ state' = [state EXCEPT ![i] = stNew]
            /\ leader' = [leader EXCEPT ![i] = leadNew]
            /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = ciNew]
            /\ UNCHANGED << votedFor, log, heartbeatElapsed, prevotesGranted,
                           votesGranted, matchIndex >>

ClientPropose ==
    \E l \in NODES:
      /\ state[l] = "StateLeader"
      /\ log' = [log EXCEPT ![l] = log[l] \o << [term |-> term[l]] >>]
      /\ matchIndex' = [matchIndex EXCEPT ![l][l] = LastIndex(l) + 1]
      /\ UNCHANGED << state, term, votedFor, leader, commitIndex,
                     electionElapsed, heartbeatElapsed, prevotesGranted,
                     votesGranted, msgs >>

DropMsg ==
    \E m \in msgs:
      /\ msgs' = msgs \ {m}
      /\ UNCHANGED << state, term, votedFor, leader, log, commitIndex,
                     electionElapsed, heartbeatElapsed, prevotesGranted,
                     votesGranted, matchIndex >>

Next ==
    \/ TickElection(CHOOSE n \in NODES: TRUE)
    \/ Hup(CHOOSE n \in NODES: TRUE)
    \/ DeliverPreVote
    \/ DeliverPreVoteResp
    \/ DeliverVote
    \/ DeliverVoteResp
    \/ LeaderSendAppend
    \/ DeliverAppend
    \/ DeliverAppendResp
    \/ LeaderHeartbeat
    \/ DeliverHeartbeat
    \/ ClientPropose
    \/ DropMsg

vars == << state, term, votedFor, leader, log, commitIndex,
           electionElapsed, heartbeatElapsed, prevotesGranted,
           votesGranted, matchIndex, msgs >>

Spec == Init /\ [][Next]_vars

====