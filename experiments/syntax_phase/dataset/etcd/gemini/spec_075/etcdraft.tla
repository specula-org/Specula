---- MODULE etcdraft ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Servers,
          Clients,
          K, V,
          Nil,
          ElectionTimeout,
          HeartbeatInterval

ASSUME TLCGet("deadlock") = FALSE

VARIABLES
    messages,
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    appliedIndex,
    leader,
    nextIndex,
    matchIndex,
    timers,
    readOnlyState,
    kvStore,
    clientReqs,
    clientResps,
    history

vars == << messages, state, currentTerm, votedFor, log, commitIndex, appliedIndex,
           leader, nextIndex, matchIndex, timers, readOnlyState, kvStore,
           clientReqs, clientResps, history >>

\* Message Types
MsgHup == "MsgHup"
MsgBeat == "MsgBeat"
MsgProp == "MsgProp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgSnap == "MsgSnap"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgReadIndex == "MsgReadIndex"
MsgReadIndexResp == "MsgReadIndexResp"

\* Server States
StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StatePreCandidate == "StatePreCandidate"
StateLeader == "StateLeader"

\* Log entry fields: term, command (e.g., [op:"PUT", key:"k1", val:"v1"])
\* Message fields: type, from, to, term, mlogTerm, mlogIndex, entries, commit, reject, ctx

TypeOK ==
    /\ messages \subseteq [type: STRING, from: Servers \cup Clients, to: Servers, term: Int,
                           mlogTerm: Int, mlogIndex: Int, entries: Seq(SUBSET log),
                           commit: Int, reject: BOOLEAN, ctx: SUBSET clientReqs]
    /\ state \in [Servers -> {StateFollower, StateCandidate, StatePreCandidate, StateLeader}]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ log \in [Servers -> Seq([term: Nat, cmd: K \times V \cup {"NoOp"}])]
    /\ commitIndex \in [Servers -> Nat]
    /\ appliedIndex \in [Servers -> Nat]
    /\ leader \in Servers \cup {Nil}
    /\ nextIndex \in [Servers -> [Servers -> Int]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ timers \in [Servers -> Int]
    /\ readOnlyState \in [Servers -> [Nat -> [acks: SUBSET Servers, req: SUBSET clientReqs]]]
    /\ kvStore \in [Servers -> [K -> V \cup {Nil}]]
    /\ clientReqs \subseteq [cid: Clients, op: {"PUT", "GET"}, key: K, val: V]
    /\ clientResps \in [Clients -> [id: Int, val: V \cup {Nil}]]
    /\ history \in Seq([type: {"invoke", "return"}, client: Clients, op: {"PUT", "GET"}, key: K, val: V])

\* Helper operators
Quorum == (Cardinality(Servers) \div 2) + 1
LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF LastLogIndex(s) = 0 THEN 0 ELSE log[s][LastLogIndex(s)].term
IsUpToDate(s1, s2) ==
    LET lli1 == LastLogIndex(s1)
        llt1 == LastLogTerm(s1)
        lli2 == LastLogIndex(s2)
        llt2 == LastLogTerm(s2)
    IN \/ llt1 > llt2
       \/ (llt1 = llt2 /\ lli1 >= lli2)

BecomeFollower(s, term, newLeader) ==
    /\ state' = [state EXCEPT ![s] = StateFollower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = newLeader
    /\ timers' = [timers EXCEPT ![s] = - (ElectionTimeout + TLC!RandomElement(1..ElectionTimeout))]

\* Actions
Tick ==
    /\ timers' = [s \in Servers |-> timers[s] + 1]
    /\ UNCHANGED << messages, state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                    leader, nextIndex, matchIndex, readOnlyState, kvStore,
                    clientReqs, clientResps, history >>

ClientRequest(c, op, k, v) ==
    LET req == [cid |-> c, op |-> op, key |-> k, val |-> v]
    IN /\ req \notin clientReqs
       /\ clientReqs' = clientReqs \cup {req}
       /\ history' = Append(history, [type |-> "invoke", client |-> c, op |-> op, key |-> k, val |-> v])
       /\ UNCHANGED << messages, state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                       leader, nextIndex, matchIndex, timers, readOnlyState, kvStore, clientResps >>

Timeout(s) ==
    /\ timers[s] > 0
    /\ \/ /\ state[s] \in {StateFollower, StatePreCandidate}
          /\ timers[s] >= ElectionTimeout
          /\ state' = [state EXCEPT ![s] = StatePreCandidate]
          /\ messages' = messages \cup
                {[ type    |-> MsgPreVote,
                   from    |-> s,
                   to      |-> p,
                   term    |-> currentTerm[s] + 1,
                   mlogIndex |-> LastLogIndex(s),
                   mlogTerm  |-> LastLogTerm(s)
                 ] : p \in Servers}
          /\ timers' = [timers EXCEPT ![s] = 0]
          /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                          nextIndex, matchIndex, readOnlyState, kvStore, clientReqs, clientResps, history >>

       \/ /\ state[s] = StateCandidate
          /\ timers[s] >= ElectionTimeout
          /\ state' = [state EXCEPT ![s] = StateCandidate]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
          /\ votedFor' = [votedFor EXCEPT ![s] = s]
          /\ messages' = messages \cup
                {[ type    |-> MsgVote,
                   from    |-> s,
                   to      |-> p,
                   term    |-> currentTerm[s] + 1,
                   mlogIndex |-> LastLogIndex(s),
                   mlogTerm  |-> LastLogTerm(s)
                 ] : p \in Servers}
          /\ timers' = [timers EXCEPT ![s] = 0]
          /\ UNCHANGED << log, commitIndex, appliedIndex, leader, nextIndex, matchIndex,
                          readOnlyState, kvStore, clientReqs, clientResps, history >>

LeaderHeartbeat(s) ==
    /\ state[s] = StateLeader
    /\ timers[s] >= HeartbeatInterval
    /\ messages' = messages \cup
        {[ type |-> MsgHeartbeat, from |-> s, to |-> p, term |-> currentTerm[s],
           commit |-> Min({commitIndex[s], matchIndex[s][p]})
         ] : p \in Servers \ {s}}
    /\ timers' = [timers EXCEPT ![s] = 0]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                    nextIndex, matchIndex, readOnlyState, kvStore, clientReqs, clientResps, history >>

HandleMessage(s, msg) ==
    /\ msg \in messages
    /\ msg.to = s
    /\ LET from == msg.from
    /\ IF msg.term > currentTerm[s]
       THEN /\ BecomeFollower(s, msg.term, IF msg.type \in {MsgApp, MsgHeartbeat} THEN from ELSE Nil)
            /\ messages' = messages \ {msg}
            /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex,
                            readOnlyState, kvStore, clientReqs, clientResps, history >>
       ELSE /\ messages' = messages \ {msg}
            /\ IF msg.term < currentTerm[s]
               THEN /\ IF msg.type \in {MsgApp, MsgHeartbeat}
                       THEN messages' = (messages \ {msg}) \cup
                                {[ type |-> MsgAppResp, from |-> s, to |-> from, term |-> currentTerm[s], reject |-> TRUE ]}
                       ELSE UNCHANGED messages
                    /\ UNCHANGED << vars >>
               ELSE CASE state[s] = StateFollower /\ msg.type = MsgApp ->
                        /\ LET prevLogIndex == msg.mlogIndex
                               prevLogTerm == msg.mlogTerm
                               leaderCommit == msg.commit
                        /\ IF \/ prevLogIndex > LastLogIndex(s)
                              \/ (prevLogIndex > 0 /\ log[s][prevLogIndex].term /= prevLogTerm)
                           THEN /\ messages' = (messages \ {msg}) \cup
                                    {[ type |-> MsgAppResp, from |-> s, to |-> from, term |-> currentTerm[s],
                                       reject |-> TRUE, mlogIndex |-> LastLogIndex(s) ]}
                                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>
                           ELSE /\ log' = [log EXCEPT ![s] = SubSeq(@, 1, prevLogIndex) \o msg.entries]
                                /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({@, Min({leaderCommit, LastLogIndex(s)})})]
                                /\ timers' = [timers EXCEPT ![s] = 0]
                                /\ leader' = from
                                /\ messages' = (messages \ {msg}) \cup
                                    {[ type |-> MsgAppResp, from |-> s, to |-> from, term |-> currentTerm[s],
                                       reject |-> FALSE, mlogIndex |-> LastLogIndex(s) ]}
                                /\ UNCHANGED << state, currentTerm, votedFor, appliedIndex, nextIndex, matchIndex,
                                                readOnlyState, kvStore, clientReqs, clientResps, history >>

                    [] state[s] = StateFollower /\ msg.type = MsgHeartbeat ->
                        /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({@, Min({msg.commit, LastLogIndex(s)})})]
                        /\ timers' = [timers EXCEPT ![s] = 0]
                        /\ leader' = from
                        /\ IF msg.ctx /= {}
                           THEN messages' = (messages \ {msg}) \cup
                                {[ type |-> MsgHeartbeatResp, from |-> s, to |-> from, term |-> currentTerm[s], ctx |-> msg.ctx ]}
                           ELSE UNCHANGED messages
                        /\ UNCHANGED << state, currentTerm, votedFor, log, appliedIndex, nextIndex, matchIndex,
                                        readOnlyState, kvStore, clientReqs, clientResps, history >>

                    [] state[s] \in {StateFollower, StateCandidate, StatePreCandidate} /\ msg.type = MsgVote ->
                        /\ LET grant == \/ votedFor[s] = Nil \/ votedFor[s] = from
                                      \/ IsUpToDate(from, s)
                        /\ IF grant
                           THEN /\ votedFor' = [votedFor EXCEPT ![s] = from]
                                /\ timers' = [timers EXCEPT ![s] = 0]
                                /\ messages' = (messages \ {msg}) \cup
                                    {[ type |-> MsgVoteResp, from |-> s, to |-> from, term |-> currentTerm[s], reject |-> FALSE ]}
                                /\ UNCHANGED << state, currentTerm, log, commitIndex, appliedIndex, leader,
                                                nextIndex, matchIndex, readOnlyState, kvStore, clientReqs, clientResps, history >>
                           ELSE /\ messages' = (messages \ {msg}) \cup
                                    {[ type |-> MsgVoteResp, from |-> s, to |-> from, term |-> currentTerm[s], reject |-> TRUE ]}
                                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                    [] state[s] \in {StateFollower, StateCandidate, StatePreCandidate} /\ msg.type = MsgPreVote ->
                        /\ LET grant == IsUpToDate(from, s)
                        /\ messages' = (messages \ {msg}) \cup
                            {[ type |-> MsgPreVoteResp, from |-> s, to |-> from, term |-> msg.term, reject |-> NOT grant ]}
                        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                        nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                    [] state[s] = StateCandidate /\ msg.type = MsgVoteResp ->
                        /\ IF NOT msg.reject
                           THEN LET votes == {p \in Servers: \E m \in messages: m.type=MsgVoteResp /\ m.to=s /\ m.from=p /\ NOT m.reject} \cup {s}
                                IN IF Cardinality(votes) >= Quorum
                                   THEN /\ state' = [state EXCEPT ![s] = StateLeader]
                                        /\ leader' = s
                                        /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
                                        /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
                                        /\ timers' = [timers EXCEPT ![s] = 0]
                                        /\ log' = [log EXCEPT ![s] = Append(@, [term |-> currentTerm[s], cmd |-> "NoOp"])]
                                        /\ messages' = (messages \ {msg}) \cup
                                            {[ type |-> MsgApp, from |-> s, to |-> p, term |-> currentTerm[s],
                                               mlogIndex |-> LastLogIndex(s), mlogTerm |-> LastLogTerm(s),
                                               entries |-> << [term |-> currentTerm[s], cmd |-> "NoOp"] >>,
                                               commit |-> commitIndex[s]
                                             ] : p \in Servers \ {s}}
                                        /\ UNCHANGED << currentTerm, votedFor, commitIndex, appliedIndex,
                                                        readOnlyState, kvStore, clientReqs, clientResps, history >>
                                   ELSE UNCHANGED << vars >>
                           ELSE UNCHANGED << vars >>

                    [] state[s] = StatePreCandidate /\ msg.type = MsgPreVoteResp ->
                        /\ IF NOT msg.reject
                           THEN LET votes == {p \in Servers: \E m \in messages: m.type=MsgPreVoteResp /\ m.to=s /\ m.from=p /\ NOT m.reject} \cup {s}
                                IN IF Cardinality(votes) >= Quorum
                                   THEN /\ state' = [state EXCEPT ![s] = StateCandidate]
                                        /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
                                        /\ votedFor' = [votedFor EXCEPT ![s] = s]
                                        /\ timers' = [timers EXCEPT ![s] = 0]
                                        /\ messages' = (messages \ {msg}) \cup
                                            {[ type    |-> MsgVote,
                                               from    |-> s,
                                               to      |-> p,
                                               term    |-> currentTerm[s] + 1,
                                               mlogIndex |-> LastLogIndex(s),
                                               mlogTerm  |-> LastLogTerm(s)
                                             ] : p \in Servers}
                                        /\ UNCHANGED << log, commitIndex, appliedIndex, leader, nextIndex, matchIndex,
                                                        readOnlyState, kvStore, clientReqs, clientResps, history >>
                                   ELSE UNCHANGED << vars >>
                           ELSE UNCHANGED << vars >>

                    [] state[s] = StateLeader /\ msg.type = MsgAppResp ->
                        /\ IF NOT msg.reject
                           THEN /\ matchIndex' = [matchIndex EXCEPT ![s][from] = Max({@, msg.mlogIndex})]
                                /\ nextIndex' = [nextIndex EXCEPT ![s][from] = Max({@, msg.mlogIndex + 1})]
                                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                timers, readOnlyState, kvStore, clientReqs, clientResps, history >>
                           ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][from] = @ - 1]
                                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                    [] state[s] = StateLeader /\ msg.type = MsgProp ->
                        /\ LET newEntry == [term |-> currentTerm[s], cmd |-> [op |-> msg.entries[1].op, key |-> msg.entries[1].key, val |-> msg.entries[1].val]]
                        /\ log' = [log EXCEPT ![s] = Append(@, newEntry)]
                        /\ matchIndex' = [matchIndex EXCEPT ![s][s] = LastLogIndex(s) + 1]
                        /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, appliedIndex, leader,
                                        nextIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                    [] state[s] = StateLeader /\ msg.type = MsgReadIndex ->
                        /\ LET ctx == msg.ctx[1].cid
                        /\ readOnlyState' = [readOnlyState EXCEPT ![s][ctx] = [acks |-> {s}, req |-> msg.ctx]]
                        /\ messages' = (messages \ {msg}) \cup
                            {[ type |-> MsgHeartbeat, from |-> s, to |-> p, term |-> currentTerm[s],
                               commit |-> commitIndex[s], ctx |-> msg.ctx
                             ] : p \in Servers \ {s}}
                        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                        nextIndex, matchIndex, timers, kvStore, clientReqs, clientResps, history >>

                    [] state[s] = StateLeader /\ msg.type = MsgHeartbeatResp ->
                        /\ LET ctx == msg.ctx[1].cid
                        /\ readOnlyState' = [readOnlyState EXCEPT ![s][ctx].acks = @ \cup {from}]
                        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                        nextIndex, matchIndex, timers, kvStore, clientReqs, clientResps, history >>

                    [] TRUE -> UNCHANGED << vars >>

LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = StateLeader
    /\ LET newCommitIndex ==
        Max({ i \in 1..LastLogIndex(s) :
                /\ i > commitIndex[s]
                /\ log[s][i].term = currentTerm[s]
                /\ Cardinality({p \in Servers : matchIndex[s][p] >= i}) >= Quorum })
    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED << messages, state, currentTerm, votedFor, log, appliedIndex, leader,
                    nextIndex, matchIndex, timers, readOnlyState, kvStore,
                    clientReqs, clientResps, history >>

LeaderSendAppend(s) ==
    /\ state[s] = StateLeader
    /\ \E p \in Servers \ {s}: nextIndex[s][p] <= LastLogIndex(s)
    /\ messages' = messages \cup
        {[ type |-> MsgApp, from |-> s, to |-> p, term |-> currentTerm[s],
           mlogIndex |-> nextIndex[s][p] - 1,
           mlogTerm |-> IF nextIndex[s][p] - 1 > 0 THEN log[s][nextIndex[s][p] - 1].term ELSE 0,
           entries |-> << log[s][nextIndex[s][p]] >>,
           commit |-> commitIndex[s]
         ] : p \in Servers \ {s}, nextIndex[s][p] <= LastLogIndex(s)}
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                    nextIndex, matchIndex, timers, readOnlyState, kvStore,
                    clientReqs, clientResps, history >>

LeaderRespondToReadIndex(s) ==
    /\ state[s] = StateLeader
    /\ \E ctx \in DOMAIN readOnlyState[s]:
        /\ Cardinality(readOnlyState[s][ctx].acks) >= Quorum
        /\ LET req == readOnlyState[s][ctx].req[1]
               client == req.cid
               key == req.key
               val == kvStore[s][key]
        /\ clientResps' = [clientResps EXCEPT ![client] = [id |-> req.cid, val |-> val]]
        /\ history' = Append(history, [type |-> "return", client |-> client, op |-> "GET", key |-> key, val |-> val])
        /\ readOnlyState' = [readOnlyState EXCEPT ![s] = [c \in DOMAIN @ |-> IF c=ctx THEN {} ELSE @[c]]]
        /\ UNCHANGED << messages, state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                        nextIndex, matchIndex, timers, kvStore, clientReqs >>

Apply(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i == appliedIndex[s] + 1
           entry == log[s][i]
           cmd == entry.cmd
    /\ IF cmd /= "NoOp"
       THEN LET op == cmd.op
                 k == cmd.key
                 v == cmd.val
            IN /\ kvStore' = [kvStore EXCEPT ![s][k] = IF op = "PUT" THEN v ELSE @[k]]
               /\ IF \E req \in clientReqs: req.op = op /\ req.key = k /\ req.val = v
                  THEN LET req == CHOOSE r \in clientReqs: r.op = op /\ r.key = k /\ r.val = v
                       IN /\ clientResps' = [clientResps EXCEPT ![req.cid] = [id |-> req.cid, val |-> v]]
                          /\ history' = Append(history, [type |-> "return", client |-> req.cid, op |-> op, key |-> k, val |-> v])
                          /\ clientReqs' = clientReqs \ {req}
                  ELSE UNCHANGED << clientResps, history, clientReqs >>
       ELSE UNCHANGED << kvStore, clientResps, history, clientReqs >>
    /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
    /\ UNCHANGED << messages, state, currentTerm, votedFor, log, commitIndex, leader,
                    nextIndex, matchIndex, timers, readOnlyState >>

DropMessage(msg) ==
    /\ msg \in messages
    /\ messages' = messages \ {msg}
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                    nextIndex, matchIndex, timers, readOnlyState, kvStore,
                    clientReqs, clientResps, history >>

Next ==
    \/ Tick
    \/ \E s \in Servers: Timeout(s)
    \/ \E s \in Servers: LeaderHeartbeat(s)
    \/ \E s \in Servers, msg \in messages: HandleMessage(s, msg)
    \/ \E s \in Servers: LeaderAdvanceCommitIndex(s)
    \/ \E s \in Servers: LeaderSendAppend(s)
    \/ \E s \in Servers: LeaderRespondToReadIndex(s)
    \/ \E s \in Servers: Apply(s)
    \/ \E c \in Clients, k \in K, v \in V: ClientRequest(c, "PUT", k, v)
    \/ \E c \in Clients, k \in K: ClientRequest(c, "GET", k, Nil)
    \/ \E msg \in messages: DropMessage(msg)

Init ==
    /\ messages = {}
    /\ state = [s \in Servers |-> StateFollower]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ leader = Nil
    /\ nextIndex = [l \in Servers |-> [f \in Servers |-> 1]]
    /\ matchIndex = [l \in Servers |-> [f \in Servers |-> 0]]
    /\ timers = [s \in Servers |-> - (ElectionTimeout + TLC!RandomElement(1..ElectionTimeout))]
    /\ readOnlyState = [l \in Servers |-> [ctx \in {} |-> {}]]
    /\ kvStore = [s \in Servers |-> [k \in K |-> Nil]]
    /\ clientReqs = {}
    /\ clientResps = [c \in Clients |-> [id |-> -1, val |-> Nil]]
    /\ history = << >>

Spec == Init /\ [][Next]_vars

\* Invariants
ElectionSafety ==
    \A t \in {currentTerm[s] : s \in Servers} :
        Cardinality({s \in Servers : state[s] = StateLeader /\ currentTerm[s] = t}) <= 1

LeaderAppendOnly ==
    \A s \in Servers :
        state[s] = StateLeader => \A i \in 1..Len(log[s]) : log'[s][i] = log[s][i]

LogMatching ==
    \A s1, s2 \in Servers :
        \A i \in 1..Min({Len(log[s1]), Len(log[s2])}) :
            log[s1][i].term = log[s2][i].term => log[s1][i] = log[s2][i]

LeaderCompleteness ==
    \A t \in Nat, i \in Nat :
        (\E s \in Servers : i <= commitIndex[s] /\ log[s][i].term = t) =>
            (\A t2 \in t+1..Max({currentTerm[s] : s \in Servers}) :
                \A s2 \in Servers :
                    (state[s2] = StateLeader /\ currentTerm[s2] = t2) => i <= LastLogIndex(s2) /\ log[s2][i].term = t)

StateMachinSafety ==
    \A s1, s2 \in Servers, i \in Nat :
        (i <= appliedIndex[s1] /\ i <= appliedIndex[s2]) => log[s1][i] = log[s2][i]

CommittedLogsArePrefixes ==
    \A s1, s2 \in Servers :
        LET l1 == SubSeq(log[s1], 1, commitIndex[s1])
            l2 == SubSeq(log[s2], 1, commitIndex[s2])
        IN \/ Len(l1) <= Len(l2) /\ SubSeq(l2, 1, Len(l1)) = l1
           \/ Len(l2) < Len(l1) /\ SubSeq(l1, 1, Len(l2)) = l2

====