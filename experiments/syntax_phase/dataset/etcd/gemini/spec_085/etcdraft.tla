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

ClientRequestRecord == [cid: Clients, op: {"PUT"}, key: K, val: V]
ClientReadRequestRecord == [cid: Clients, op: {"GET"}, key: K, val: V]
LogEntryCmd == [op: {"PUT"}, key: K, val: V]
LogEntry == [term: Nat, cmd: LogEntryCmd \cup {"NoOp"}, cid: Clients \cup {Nil}]
ReadOnlyStateRecord == [acks: SUBSET Servers, req: ClientReadRequestRecord \cup {Nil}, index: Nat]

TypeOK ==
    /\ messages \subseteq [type: STRING, from: Servers \cup Clients, to: Servers, term: Int,
                           mlogTerm: Int, mlogIndex: Int, entries: Seq(LogEntry),
                           commit: Int, reject: BOOLEAN, ctx: ClientReadRequestRecord \cup {Nil}]
    /\ state \in [Servers -> {StateFollower, StateCandidate, StatePreCandidate, StateLeader}]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ log \in [Servers -> Seq(LogEntry)]
    /\ commitIndex \in [Servers -> Nat]
    /\ appliedIndex \in [Servers -> Nat]
    /\ leader \in Servers \cup {Nil}
    /\ nextIndex \in [Servers -> [Servers -> Int]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ timers \in [Servers -> Int]
    /\ readOnlyState \in [Servers -> [Clients -> ReadOnlyStateRecord \cup {Nil}]]
    /\ kvStore \in [Servers -> [K -> V \cup {Nil}]]
    /\ clientReqs \subseteq ClientRequestRecord
    /\ clientResps \in [Clients -> [id: Clients \cup {Nil}, val: V \cup {Nil}]]
    /\ history \in Seq([type: {"invoke", "return"}, client: Clients, op: {"PUT", "GET"}, key: K, val: V \cup {Nil}])

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

ClientRequest(c, k, v) ==
    LET req == [cid |-> c, op |-> "PUT", key |-> k, val |-> v]
    IN /\ req \notin clientReqs
       /\ clientReqs' = clientReqs \cup {req}
       /\ history' = Append(history, [type |-> "invoke", client |-> c, op |-> "PUT", key |-> k, val |-> v])
       /\ UNCHANGED << messages, state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                       leader, nextIndex, matchIndex, timers, readOnlyState, kvStore, clientResps >>

ClientReadRequest(c, k) ==
    /\ leader /= Nil
    /\ \A s \in Servers : readOnlyState[s][c] = Nil
    /\ LET req == [cid |-> c, op |-> "GET", key |-> k, val |-> Nil]
    IN /\ messages' = messages \cup
            {[ type |-> MsgReadIndex,
               from |-> c,
               to |-> leader,
               term |-> 0,
               ctx |-> req,
               mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, commit |-> 0, reject |-> FALSE
             ]}
       /\ history' = Append(history, [type |-> "invoke", client |-> c, op |-> "GET", key |-> k, val |-> Nil])
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                       nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps >>

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
                   mlogTerm  |-> LastLogTerm(s),
                   entries |-> << >>, commit |-> 0, reject |-> FALSE, ctx |-> Nil
                 ] : p \in Servers}
          /\ timers' = [timers EXCEPT ![s] = 0]
          /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                          nextIndex, matchIndex, readOnlyState, kvStore, clientReqs, clientResps, history >>

       \/ /\ state[s] = StateCandidate
          /\ timers[s] >= ElectionTimeout
          /\ state' = [state EXCEPT ![s] = StateCandidate]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
          /\ votedFor' = [votedFor EXCEPT ![s] = s]
          /\ messages' = messages \cup
                {[ type    |-> MsgVote,
                   from    |-> s,
                   to      |-> p,
                   term    |-> currentTerm[s] + 1,
                   mlogIndex |-> LastLogIndex(s),
                   mlogTerm  |-> LastLogTerm(s),
                   entries |-> << >>, commit |-> 0, reject |-> FALSE, ctx |-> Nil
                 ] : p \in Servers}
          /\ timers' = [timers EXCEPT ![s] = 0]
          /\ UNCHANGED << log, commitIndex, appliedIndex, leader, nextIndex, matchIndex,
                          readOnlyState, kvStore, clientReqs, clientResps, history >>

LeaderHeartbeat(s) ==
    /\ state[s] = StateLeader
    /\ timers[s] >= HeartbeatInterval
    /\ messages' = messages \cup
        {[ type |-> MsgHeartbeat, from |-> s, to |-> p, term |-> currentTerm[s],
           commit |-> commitIndex[s],
           mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, reject |-> FALSE, ctx |-> Nil
         ] : p \in Servers \ {s}}
    /\ timers' = [timers EXCEPT ![s] = 0]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                    nextIndex, matchIndex, readOnlyState, kvStore, clientReqs, clientResps, history >>

HandleMessage(s, msg) ==
    /\ msg \in messages
    /\ msg.to = s
    /\ LET from == msg.from
    IN /\ IF msg.term > currentTerm[s]
          THEN /\ BecomeFollower(s, msg.term, IF msg.type \in {MsgApp, MsgHeartbeat} THEN from ELSE Nil)
               /\ messages' = messages \ {msg}
               /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex,
                               readOnlyState, kvStore, clientReqs, clientResps, history >>
          ELSE /\ IF msg.term < currentTerm[s]
                  THEN /\ IF msg.type \in {MsgApp, MsgHeartbeat, MsgVote, MsgPreVote}
                          THEN messages' = (messages \ {msg}) \cup
                                   {[ type |-> MsgAppResp, from |-> s, to |-> from, term |-> currentTerm[s], reject |-> TRUE,
                                      mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, commit |-> 0, ctx |-> Nil ]}
                          ELSE messages' = messages \ {msg}
                       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                       nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>
                  ELSE CASE state[s] = StateFollower /\ msg.type = MsgApp ->
                           LET prevLogIndex == msg.mlogIndex
                               prevLogTerm == msg.mlogTerm
                               leaderCommit == msg.commit
                               newLog == SubSeq(log[s], 1, prevLogIndex) \o msg.entries
                           IN IF \/ prevLogIndex > LastLogIndex(s)
                                 \/ (prevLogIndex > 0 /\ log[s][prevLogIndex].term /= prevLogTerm)
                              THEN /\ messages' = (messages \ {msg}) \cup
                                       {[ type |-> MsgAppResp, from |-> s, to |-> from, term |-> currentTerm[s],
                                          reject |-> TRUE, mlogIndex |-> LastLogIndex(s),
                                          mlogTerm |-> 0, entries |-> << >>, commit |-> 0, ctx |-> Nil ]}
                                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                   nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>
                              ELSE /\ log' = [log EXCEPT ![s] = newLog]
                                   /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({@, Min({leaderCommit, Len(newLog)})})]
                                   /\ timers' = [timers EXCEPT ![s] = 0]
                                   /\ leader' = from
                                   /\ messages' = (messages \ {msg}) \cup
                                       {[ type |-> MsgAppResp, from |-> s, to |-> from, term |-> currentTerm[s],
                                          reject |-> FALSE, mlogIndex |-> Len(newLog),
                                          mlogTerm |-> 0, entries |-> << >>, commit |-> 0, ctx |-> Nil ]}
                                   /\ UNCHANGED << state, currentTerm, votedFor, appliedIndex, nextIndex, matchIndex,
                                                   readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] = StateFollower /\ msg.type = MsgHeartbeat ->
                           /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({@, Min({msg.commit, LastLogIndex(s)})})]
                           /\ timers' = [timers EXCEPT ![s] = 0]
                           /\ leader' = from
                           /\ IF msg.ctx /= Nil
                              THEN messages' = (messages \ {msg}) \cup
                                   {[ type |-> MsgHeartbeatResp, from |-> s, to |-> from, term |-> currentTerm[s], ctx |-> msg.ctx,
                                      mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, commit |-> 0, reject |-> FALSE ]}
                              ELSE messages' = messages \ {msg}
                           /\ UNCHANGED << state, currentTerm, votedFor, log, appliedIndex, nextIndex, matchIndex,
                                           readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] \in {StateFollower, StateCandidate, StatePreCandidate} /\ msg.type = MsgVote ->
                           LET grant == (votedFor[s] = Nil \/ votedFor[s] = from) /\ IsUpToDate(from, s)
                           IN IF grant
                              THEN /\ votedFor' = [votedFor EXCEPT ![s] = from]
                                   /\ timers' = [timers EXCEPT ![s] = 0]
                                   /\ messages' = (messages \ {msg}) \cup
                                       {[ type |-> MsgVoteResp, from |-> s, to |-> from, term |-> currentTerm[s], reject |-> FALSE,
                                          mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, commit |-> 0, ctx |-> Nil ]}
                                   /\ UNCHANGED << state, currentTerm, log, commitIndex, appliedIndex, leader,
                                                   nextIndex, matchIndex, readOnlyState, kvStore, clientReqs, clientResps, history >>
                              ELSE /\ messages' = (messages \ {msg}) \cup
                                       {[ type |-> MsgVoteResp, from |-> s, to |-> from, term |-> currentTerm[s], reject |-> TRUE,
                                          mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, commit |-> 0, ctx |-> Nil ]}
                                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                   nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] \in {StateFollower, StateCandidate, StatePreCandidate} /\ msg.type = MsgPreVote ->
                           LET grant == IsUpToDate(from, s)
                           IN /\ messages' = (messages \ {msg}) \cup
                               {[ type |-> MsgPreVoteResp, from |-> s, to |-> from, term |-> msg.term, reject |-> NOT grant,
                                  mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, commit |-> 0, ctx |-> Nil ]}
                              /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                              nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] = StateCandidate /\ msg.type = MsgVoteResp ->
                           LET votes = {p.from | p \in (messages \ {msg}) : p.type=MsgVoteResp /\ p.to=s /\ p.term=currentTerm[s] /\ NOT p.reject} \cup {s}
                           IN IF msg.term = currentTerm[s] /\ NOT msg.reject /\ Cardinality(votes \cup {from}) >= Quorum
                              THEN /\ state' = [state EXCEPT ![s] = StateLeader]
                                   /\ leader' = s
                                   /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
                                   /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
                                   /\ timers' = [timers EXCEPT ![s] = 0]
                                   /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], cmd |-> "NoOp", cid |-> Nil])]
                                   /\ messages' = (messages \ {msg}) \cup
                                       {[ type |-> MsgApp, from |-> s, to |-> p, term |-> currentTerm[s],
                                          mlogIndex |-> LastLogIndex(s), mlogTerm |-> LastLogTerm(s),
                                          entries |-> << [term |-> currentTerm[s], cmd |-> "NoOp", cid |-> Nil] >>,
                                          commit |-> commitIndex[s], reject |-> FALSE, ctx |-> Nil
                                        ] : p \in Servers \ {s}}
                                   /\ UNCHANGED << currentTerm, votedFor, commitIndex, appliedIndex,
                                                   readOnlyState, kvStore, clientReqs, clientResps, history >>
                              ELSE /\ messages' = messages \ {msg}
                                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                   nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] = StatePreCandidate /\ msg.type = MsgPreVoteResp ->
                           LET votes = {p.from | p \in (messages \ {msg}) : p.type=MsgPreVoteResp /\ p.to=s /\ p.term=msg.term /\ NOT p.reject} \cup {s}
                           IN IF msg.term = currentTerm[s] + 1 /\ NOT msg.reject /\ Cardinality(votes \cup {from}) >= Quorum
                              THEN /\ state' = [state EXCEPT ![s] = StateCandidate]
                                   /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                                   /\ votedFor' = [votedFor EXCEPT ![s] = s]
                                   /\ timers' = [timers EXCEPT ![s] = 0]
                                   /\ messages' = (messages \ {msg}) \cup
                                       {[ type    |-> MsgVote,
                                          from    |-> s,
                                          to      |-> p,
                                          term    |-> currentTerm[s] + 1,
                                          mlogIndex |-> LastLogIndex(s),
                                          mlogTerm  |-> LastLogTerm(s),
                                          entries |-> << >>, commit |-> 0, reject |-> FALSE, ctx |-> Nil
                                        ] : p \in Servers}
                                   /\ UNCHANGED << log, commitIndex, appliedIndex, leader, nextIndex, matchIndex,
                                                   readOnlyState, kvStore, clientReqs, clientResps, history >>
                              ELSE /\ messages' = messages \ {msg}
                                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                   nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] = StateLeader /\ msg.type = MsgAppResp ->
                           /\ messages' = messages \ {msg}
                           /\ IF NOT msg.reject
                              THEN /\ matchIndex' = [matchIndex EXCEPT ![s][from] = Max({@, msg.mlogIndex})]
                                   /\ nextIndex' = [nextIndex EXCEPT ![s][from] = Max({@, msg.mlogIndex + 1})]
                                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                   timers, readOnlyState, kvStore, clientReqs, clientResps, history >>
                              ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][from] = Max({1, @ - 1})]
                                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                                   matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

                       [] state[s] = StateLeader /\ msg.type = MsgReadIndex ->
                           /\ LET cid == msg.ctx.cid
                           /\ readOnlyState' = [readOnlyState EXCEPT ![s][cid] = [acks |-> {s}, req |-> msg.ctx, index |-> commitIndex[s]]]
                           /\ messages' = (messages \ {msg}) \cup
                               {[ type |-> MsgHeartbeat, from |-> s, to |-> p, term |-> currentTerm[s],
                                  commit |-> commitIndex[s], ctx |-> msg.ctx,
                                  mlogTerm |-> 0, mlogIndex |-> 0, entries |-> << >>, reject |-> FALSE
                                ] : p \in Servers \ {s}}
                           /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                           nextIndex, matchIndex, timers, kvStore, clientReqs, clientResps, history >>

                       [] state[s] = StateLeader /\ msg.type = MsgHeartbeatResp ->
                           /\ messages' = messages \ {msg}
                           /\ IF msg.ctx /= Nil
                              THEN LET cid == msg.ctx.cid
                                   IN IF readOnlyState[s][cid] /= Nil
                                      THEN readOnlyState' = [readOnlyState EXCEPT ![s][cid].acks = @ \cup {from}]
                                      ELSE UNCHANGED readOnlyState
                              ELSE UNCHANGED readOnlyState
                           /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                           nextIndex, matchIndex, timers, kvStore, clientReqs, clientResps, history >>

                       [] OTHER ->
                           /\ messages' = messages \ {msg}
                           /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                                           nextIndex, matchIndex, timers, readOnlyState, kvStore, clientReqs, clientResps, history >>

LeaderPropose(s) ==
    /\ state[s] = StateLeader
    /\ \E req \in clientReqs:
        LET newEntry == [term |-> currentTerm[s], cmd |-> [op |-> req.op, key |-> req.key, val |-> req.val], cid |-> req.cid]
        IN /\ log' = [log EXCEPT ![s] = Append(@, newEntry)]
           /\ matchIndex' = [matchIndex EXCEPT ![s][s] = Len(log'[s])]
           /\ clientReqs' = clientReqs \ {req}
           /\ UNCHANGED << messages, state, currentTerm, votedFor, commitIndex, appliedIndex, leader,
                           nextIndex, timers, readOnlyState, kvStore, clientResps, history >>

LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = StateLeader
    /\ LET newCommitIndex ==
        Max({commitIndex[s]} \cup { i \in (commitIndex[s]+1)..LastLogIndex(s) :
                /\ log[s][i].term = currentTerm[s]
                /\ Cardinality({p \in Servers : matchIndex[s][p] >= i}) >= Quorum })
    /\ newCommitIndex > commitIndex[s]
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
           entries |-> SubSeq(log[s], nextIndex[s][p], LastLogIndex(s)),
           commit |-> commitIndex[s],
           reject |-> FALSE, ctx |-> Nil
         ] : p \in {q \in Servers \ {s} | nextIndex[s][q] <= LastLogIndex(s)}}
    /\ nextIndex' = [nextIndex EXCEPT ![s][p] = LastLogIndex(s) + 1
                                    FOR p \in {q \in Servers \ {s} | nextIndex[s][q] <= LastLogIndex(s)}]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                    matchIndex, timers, readOnlyState, kvStore,
                    clientReqs, clientResps, history >>

LeaderRespondToReadIndex(s) ==
    /\ state[s] = StateLeader
    /\ \E cid \in DOMAIN readOnlyState[s]:
        LET rs == readOnlyState[s][cid]
        IN /\ rs /= Nil
           /\ Cardinality(rs.acks) >= Quorum
           /\ appliedIndex[s] >= rs.index
           /\ LET req == rs.req
                  client == req.cid
                  key == req.key
                  val == kvStore[s][key]
           /\ clientResps' = [clientResps EXCEPT ![client] = [id |-> client, val |-> val]]
           /\ history' = Append(history, [type |-> "return", client |-> client, op |-> "GET", key |-> key, val |-> val])
           /\ readOnlyState' = [readOnlyState EXCEPT ![s][cid] = Nil]
           /\ UNCHANGED << messages, state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
                           nextIndex, matchIndex, timers, kvStore, clientReqs >>

Apply(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i == appliedIndex[s] + 1
           entry == log[s][i]
           cmd == entry.cmd
           cid == entry.cid
    /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
    /\ IF cmd /= "NoOp"
       THEN LET op == cmd.op
                 k == cmd.key
                 v == cmd.val
            IN /\ kvStore' = [kvStore EXCEPT ![s][k] = v]
               /\ IF cid /= Nil
                  THEN /\ clientResps' = [clientResps EXCEPT ![cid] = [id |-> cid, val |-> v]]
                       /\ history' = Append(history, [type |-> "return", client |-> cid, op |-> op, key |-> k, val |-> v])
                  ELSE UNCHANGED << clientResps, history >>
               /\ UNCHANGED clientReqs
       ELSE UNCHANGED << kvStore, clientResps, history, clientReqs >>
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
    \/ \E s \in Servers: LeaderPropose(s)
    \/ \E s \in Servers: LeaderAdvanceCommitIndex(s)
    \/ \E s \in Servers: LeaderSendAppend(s)
    \/ \E s \in Servers: LeaderRespondToReadIndex(s)
    \/ \E s \in Servers: Apply(s)
    \/ \E c \in Clients, k \in K, v \in V: ClientRequest(c, k, v)
    \/ \E c \in Clients, k \in K: ClientReadRequest(c, k)
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
    /\ readOnlyState = [l \in Servers |-> [c \in Clients |-> Nil]]
    /\ kvStore = [s \in Servers |-> [k \in K |-> Nil]]
    /\ clientReqs = {}
    /\ clientResps = [c \in Clients |-> [id |-> Nil, val |-> Nil]]
    /\ history = << >>

Spec == Init /\ [][Next]_vars

\* Invariants
ElectionSafety ==
    \A t \in {currentTerm[s] : s \in Servers} :
        Cardinality({s \in Servers : state[s] = StateLeader /\ currentTerm[s] = t}) <= 1

LeaderAppendOnly ==
    \A s \in Servers, i \in 1..Len(log[s]) :
        state[s] = StateLeader => log'[s][i] = log[s][i]

LogMatching ==
    \A s1, s2 \in Servers, i \in 1..Min({Len(log[s1]), Len(log[s2])}) :
        log[s1][i].term = log[s2][i].term => log[s1][i] = log[s2][i]

LeaderCompleteness ==
    \A t \in Nat, i \in Nat :
        (\E s \in Servers : i <= commitIndex[s] /\ log[s][i].term = t) =>
            (\A t2 \in (t+1)..Max({0} \cup {currentTerm[s] : s \in Servers}) :
                \A s2 \in Servers :
                    (state[s2] = StateLeader /\ currentTerm[s2] = t2) => i <= LastLogIndex(s2) /\ log[s2][i].term = t)

StateMachineSafety ==
    \A s1, s2 \in Servers, i \in 1..Min({appliedIndex[s1], appliedIndex[s2]}) :
        log[s1][i] = log[s2][i]

CommittedLogsArePrefixes ==
    \A s1, s2 \in Servers :
        LET l1 == SubSeq(log[s1], 1, commitIndex[s1])
            l2 == SubSeq(log[s2], 1, commitIndex[s2])
        IN \/ Len(l1) <= Len(l2) /\ SubSeq(l2, 1, Len(l1)) = l1
           \/ Len(l2) < Len(l1) /\ SubSeq(l1, 1, Len(l2)) = l2

====
