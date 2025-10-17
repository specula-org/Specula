---- MODULE etcdraft ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* @type: Set(Str);
    Server,
    \* @type: Set(Str);
    Value,
    \* @type: Str;
    NilValue,
    \* @type: Str;
    DefaultVote,
    \* @type: Bool;
    PreVoteEnabled,
    \* @type: Bool;
    CheckQuorumEnabled

ASSUME /\ Server # {}
       /\ NilValue \notin Value
       /\ DefaultVote \notin Server

VARIABLES
    \* @type: [Server -> Str];
    state,
    \* @type: [Server -> Int];
    currentTerm,
    \* @type: [Server -> Str];
    votedFor,
    \* @type: [Server -> Seq([term: Int, command: Value, type: Str, voters: Set(Str), learners: Set(Str)])];
    log,
    \* @type: [Server -> Int];
    commitIndex,
    \* @type: [Server -> Int];
    appliedIndex,
    \* @type: [Server -> [peer: Server -> Int]];
    nextIndex,
    \* @type: [Server -> [peer: Server -> Int]];
    matchIndex,
    \* @type: [Server -> Set(Server)];
    votesGranted,
    \* @type: Set([type: Str, to: Server, from: Server, term: Int, mindex: Int, mterm: Int, entries: Seq(Any), commit: Int, reject: Bool, context: Str]);
    messages,
    \* @type: [Server -> Str];
    timer,
    \* @type: [Server -> Set(Server)];
    voters,
    \* @type: [Server -> Set(Server)];
    learners,
    \* @type: [Server -> Str];
    leader,
    \* @type: [Server -> Str];
    leadTransferee,
    \* @type: [Server -> Int];
    pendingConfIndex,
    \* @type: [Server -> [ctx: Str -> Set(Server)]];
    readIndexAcks,
    \* @type: [Server -> [ctx: Str -> Value]];
    readIndexReq,
    \* @type: [Server -> [key: Str -> Value]];
    kvStore

vars == << state, currentTerm, votedFor, log, commitIndex, appliedIndex,
           nextIndex, matchIndex, votesGranted, messages, timer, voters, learners,
           leader, leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore >>

Quorum(s) == (Cardinality(s) \div 2) + 1

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) > 0 THEN l[Len(l)].term ELSE 0

IsUpToDate(entryTerm, entryIndex, log) ==
    LET lastTerm == LastLogTerm(log)
        lastIndex == LastLogIndex(log)
    IN \/ entryTerm > lastTerm
       \/ (entryTerm = lastTerm /\ entryIndex >= lastIndex)

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = DefaultVote]
    /\ leader' = [leader EXCEPT ![s] = DefaultVote]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = DefaultVote]
    /\ timer' = [timer EXCEPT ![s] = "active"]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, votesGranted,
                   messages, voters, learners, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leader' = [leader EXCEPT ![s] = DefaultVote]
    /\ timer' = [timer EXCEPT ![s] = "active"]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex,
                   messages, leadTransferee, voters, learners, pendingConfIndex,
                   readIndexAcks, readIndexReq, kvStore>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "precandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ leader' = [leader EXCEPT ![s] = DefaultVote]
    /\ timer' = [timer EXCEPT ![s] = "active"]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex,
                   matchIndex, messages, leadTransferee, voters, learners, pendingConfIndex,
                   readIndexAcks, readIndexReq, kvStore>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "leader"]
    /\ leader' = [leader EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0] WITH [s] = LastLogIndex(log[s])]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = DefaultVote]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = LastLogIndex(log[s])]
    /\ timer' = [timer EXCEPT ![s] = "active"]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex,
                   votesGranted, messages, voters, learners, readIndexAcks, readIndexReq, kvStore>>

TypeOK ==
    /\ state \in [Server -> {"follower", "candidate", "leader", "precandidate"}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {DefaultVote}]
    /\ \A s \in Server: log[s] \in Seq([term: Nat, command: Value, type: Str, voters: Set(Server), learners: Set(Server)])
    /\ commitIndex \in [Server -> Nat]
    /\ appliedIndex \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> Set(Server)]
    /\ messages \in SUBSET [type: Str, to: Server, from: Server, term: Int, mindex: Int, mterm: Int, entries: Seq(Any), commit: Int, reject: Bool, context: Str]
    /\ timer \in [Server -> {"active", "reset"}]
    /\ voters \in [Server -> Set(Server)]
    /\ learners \in [Server -> Set(Server)]
    /\ leader \in [Server -> Server \cup {DefaultVote}]
    /\ leadTransferee \in [Server -> Server \cup {DefaultVote}]
    /\ pendingConfIndex \in [Server -> Nat]
    /\ readIndexAcks \in [Server -> [Str -> Set(Server)]]
    /\ readIndexReq \in [Server -> [Str -> Value]]
    /\ kvStore \in [Server -> [Str -> Value]]

Init ==
    /\ state = [s \in Server |-> "follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> DefaultVote]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ appliedIndex = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ messages = {}
    /\ timer = [s \in Server |-> "active"]
    /\ voters = [s \in Server |-> Server]
    /\ learners = [s \in Server |-> {}]
    /\ leader = [s \in Server |-> DefaultVote]
    /\ leadTransferee = [s \in Server |-> DefaultVote]
    /\ pendingConfIndex = [s \in Server |-> 0]
    /\ readIndexAcks = [s \in Server |-> [ctx \in {} |-> {}]]
    /\ readIndexReq = [s \in Server |-> [ctx \in {} |-> NilValue]]
    /\ kvStore = [s \in Server |-> [k \in {} |-> NilValue]]

Timeout(s) ==
    /\ timer[s] = "active"
    /\ \/ /\ state[s] \in {"follower", "candidate", "precandidate"}
          /\ s \notin learners[s]
          /\ IF PreVoteEnabled
             THEN /\ BecomePreCandidate(s)
                  /\ messages' = messages \cup
                      {[type |-> "RequestPreVote", to |-> p, from |-> s,
                        term |-> currentTerm[s] + 1,
                        mindex |-> LastLogIndex(log[s]), mterm |-> LastLogTerm(log[s]),
                        entries |-> <<>>, commit |-> 0, reject |-> FALSE, context |-> ""]
                        | p \in voters[s]}
             ELSE /\ BecomeCandidate(s)
                  /\ messages' = messages \cup
                      {[type |-> "RequestVote", to |-> p, from |-> s,
                        term |-> currentTerm[s] + 1,
                        mindex |-> LastLogIndex(log[s]), mterm |-> LastLogTerm(log[s]),
                        entries |-> <<>>, commit |-> 0, reject |-> FALSE, context |-> ""]
                        | p \in voters[s]}
       \/ /\ state[s] = "leader"
          /\ \/ /\ CheckQuorumEnabled
                /\ Cardinality({p \in voters[s] | matchIndex[s][p] >= commitIndex[s] \/ p = s}) < Quorum(voters[s])
                /\ BecomeFollower(s, currentTerm[s])
                /\ messages' = messages
             \/ /\ leadTransferee[s] # DefaultVote
                /\ leadTransferee' = [leadTransferee EXCEPT ![s] = DefaultVote]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                               nextIndex, matchIndex, votesGranted, messages, timer, voters,
                               learners, leader, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ messages' = messages \cup
                      {[type |-> "AppendEntries", to |-> p, from |-> s, term |-> currentTerm[s],
                        mindex |-> 0, mterm |-> 0, entries |-> <<>>,
                        commit |-> commitIndex[s], reject |-> FALSE, context |-> ""]
                        | p \in voters[s] \cup learners[s]}
                /\ timer' = [timer EXCEPT ![s] = "active"]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                               nextIndex, matchIndex, votesGranted, leadTransferee, voters,
                               learners, leader, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>

ClientRequest(s, cmd, type, newVoters, newLearners) ==
    /\ state[s] = "leader"
    /\ leadTransferee[s] = DefaultVote
    /\ LET newEntry == [term |-> currentTerm[s], command |-> cmd, type |-> type, voters |-> newVoters, learners |-> newLearners]
          newLog == log[s] \o <<newEntry>>
       IN /\ \/ type # "ConfChange"
             \/ appliedIndex[s] >= pendingConfIndex[s]
          /\ log' = [log EXCEPT ![s] = newLog]
          /\ pendingConfIndex' = IF type = "ConfChange"
                                 THEN [pendingConfIndex EXCEPT ![s] = LastLogIndex(newLog)]
                                 ELSE pendingConfIndex
          /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex,
                         nextIndex, matchIndex, votesGranted, messages, timer, voters,
                         learners, leader, leadTransferee, readIndexAcks, readIndexReq, kvStore>>

Receive(m) ==
    LET i == m.to
        j == m.from
    IN
    /\ m \in messages
    /\ \/ /\ m.term > currentTerm[i]
          /\ \/ m.type \in {"AppendEntries", "RequestVote"}
             /\ BecomeFollower(i, m.term)
             /\ messages' = messages \ {m}
          /\ \/ m.type \in {"RequestPreVote", "AppendEntriesResponse", "RequestVoteResponse", "RequestPreVoteResponse"}
             /\ UNCHANGED vars
    /\ \/ /\ m.term = currentTerm[i]
          /\ \/ /\ m.type = "RequestVote"
                /\ state[i] \in {"follower", "candidate"}
                /\ (votedFor[i] = DefaultVote \/ votedFor[i] = j)
                /\ IsUpToDate(m.mterm, m.mindex, log[i])
                /\ votedFor' = [votedFor EXCEPT ![i] = j]
                /\ messages' = messages \ {m} \cup
                    {[type |-> "RequestVoteResponse", to |-> j, from |-> i, term |-> currentTerm[i],
                      mindex |-> 0, mterm |-> 0, entries |-> <<>>, commit |-> 0,
                      reject |-> FALSE, context |-> ""]}
                /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex, nextIndex,
                               matchIndex, votesGranted, timer, voters, learners, leader,
                               leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "RequestPreVote"
                /\ state[i] \in {"follower", "candidate", "precandidate"}
                /\ IsUpToDate(m.mterm, m.mindex, log[i])
                /\ messages' = messages \ {m} \cup
                    {[type |-> "RequestPreVoteResponse", to |-> j, from |-> i, term |-> m.term,
                      mindex |-> 0, mterm |-> 0, entries |-> <<>>, commit |-> 0,
                      reject |-> FALSE, context |-> ""]}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                               nextIndex, matchIndex, votesGranted, timer, voters, learners,
                               leader, leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "RequestVoteResponse"
                /\ state[i] = "candidate"
                /\ \lnot m.reject
                /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                /\ IF Cardinality(votesGranted'[i]) >= Quorum(voters[i])
                   THEN BecomeLeader(i) /\ messages' = messages \ {m}
                   ELSE messages' = messages \ {m}
                        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                       nextIndex, matchIndex, timer, voters, learners, leader,
                                       leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "RequestPreVoteResponse"
                /\ state[i] = "precandidate"
                /\ \lnot m.reject
                /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                /\ IF Cardinality(votesGranted'[i]) >= Quorum(voters[i])
                   THEN BecomeCandidate(i) /\
                        messages' = (messages \ {m}) \cup
                            {[type |-> "RequestVote", to |-> p, from |-> i,
                              term |-> currentTerm[i] + 1,
                              mindex |-> LastLogIndex(log[i]), mterm |-> LastLogTerm(log[i]),
                              entries |-> <<>>, commit |-> 0, reject |-> FALSE, context |-> ""]
                              | p \in voters[i]}
                   ELSE messages' = messages \ {m}
                        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                       nextIndex, matchIndex, timer, voters, learners, leader,
                                       leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "AppendEntries"
                /\ state[i] \in {"follower", "candidate", "precandidate"}
                /\ state' = [state EXCEPT ![i] = "follower"]
                /\ leader' = [leader EXCEPT ![i] = j]
                /\ timer' = [timer EXCEPT ![i] = "active"]
                /\ LET prevIndex == m.mindex
                      prevTerm == m.mterm
                   IN IF \/ prevIndex = 0
                         \/ (prevIndex <= Len(log[i]) /\ log[i][prevIndex].term = prevTerm)
                      THEN /\ LET newEntries == m.entries
                                newLog == SubSeq(log[i], 1, prevIndex) \o newEntries
                             IN log' = [log EXCEPT ![i] = newLog]
                          /\ commitIndex' = [commitIndex EXCEPT ![i] = min(m.commit, LastLogIndex(log'[i]))]
                          /\ messages' = messages \ {m} \cup
                                {[type |-> "AppendEntriesResponse", to |-> j, from |-> i, term |-> currentTerm[i],
                                  mindex |-> LastLogIndex(log'[i]), mterm |-> 0, entries |-> <<>>,
                                  commit |-> 0, reject |-> FALSE, context |-> ""]}
                          /\ UNCHANGED <<currentTerm, votedFor, appliedIndex, nextIndex,
                                         matchIndex, votesGranted, voters, learners, leadTransferee,
                                         pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
                      ELSE /\ messages' = messages \ {m} \cup
                                {[type |-> "AppendEntriesResponse", to |-> j, from |-> i, term |-> currentTerm[i],
                                  mindex |-> m.mindex, mterm |-> 0, entries |-> <<>>,
                                  commit |-> 0, reject |-> TRUE, context |-> ""]}
                           /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex,
                                          nextIndex, matchIndex, votesGranted, voters, learners,
                                          leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "AppendEntriesResponse"
                /\ state[i] = "leader"
                /\ \/ /\ \lnot m.reject
                      /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = m.mindex + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![j] = m.mindex]]
                      /\ LET newCommitIndex ==
                               LET s == {k \in {n \in DOMAIN log[i] | log[i][n].term = currentTerm[i]} |
                                             Cardinality({p \in voters[i] | matchIndex[i][p] >= k}) >= Quorum(voters[i])}
                               IN IF s = {} THEN commitIndex[i] ELSE Max(s)
                         IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                      /\ IF leadTransferee[i] = j /\ m.mindex = LastLogIndex(log[i])
                         THEN messages' = messages \ {m} \cup
                                {[type |-> "TimeoutNow", to |-> j, from |-> i, term |-> currentTerm[i],
                                  mindex |-> 0, mterm |-> 0, entries |-> <<>>, commit |-> 0,
                                  reject |-> FALSE, context |-> ""]}
                         ELSE messages' = messages \ {m}
                   \/ /\ m.reject
                      /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = nextIndex[i][j] - 1]]
                      /\ messages' = messages \ {m}
                      /\ UNCHANGED <<matchIndex, commitIndex>>
                /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex, votesGranted,
                               timer, voters, learners, leader, leadTransferee, pendingConfIndex,
                               readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "TimeoutNow"
                /\ state[i] = "follower"
                /\ BecomeCandidate(i)
                /\ messages' = (messages \ {m}) \cup
                    {[type |-> "RequestVote", to |-> p, from |-> i,
                      term |-> currentTerm[i] + 1,
                      mindex |-> LastLogIndex(log[i]), mterm |-> LastLogTerm(log[i]),
                      entries |-> <<>>, commit |-> 0, reject |-> FALSE, context |-> "transfer"]}
             \/ /\ m.type = "ReadIndex"
                /\ state[i] = "leader"
                /\ LET ctx == m.context
                   IN /\ readIndexReq' = [readIndexReq EXCEPT ![i] = [readIndexReq[i] EXCEPT ![ctx] = m.entries[1]]]
                      /\ readIndexAcks' = [readIndexAcks EXCEPT ![i] = [readIndexAcks[i] EXCEPT ![ctx] = {i}]]
                      /\ messages' = messages \ {m} \cup
                           {[type |-> "Heartbeat", to |-> p, from |-> i, term |-> currentTerm[i],
                             mindex |-> 0, mterm |-> 0, entries |-> <<>>, commit |-> commitIndex[i],
                             reject |-> FALSE, context |-> ctx]
                             | p \in voters[i] \ {i}}
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                     nextIndex, matchIndex, votesGranted, timer, voters, learners,
                                     leader, leadTransferee, pendingConfIndex, kvStore>>
             \/ /\ m.type = "Heartbeat"
                /\ state[i] \in {"follower", "candidate", "precandidate"}
                /\ state' = [state EXCEPT ![i] = "follower"]
                /\ leader' = [leader EXCEPT ![i] = j]
                /\ timer' = [timer EXCEPT ![i] = "active"]
                /\ messages' = messages \ {m} \cup
                     {[type |-> "HeartbeatResponse", to |-> j, from |-> i, term |-> currentTerm[i],
                       mindex |-> 0, mterm |-> 0, entries |-> <<>>, commit |-> 0,
                       reject |-> FALSE, context |-> m.context]}
                /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex,
                               matchIndex, votesGranted, voters, learners, leadTransferee,
                               pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>
             \/ /\ m.type = "HeartbeatResponse"
                /\ state[i] = "leader"
                /\ LET ctx == m.context
                   IN IF ctx # ""
                      THEN /\ readIndexAcks' = [readIndexAcks EXCEPT ![i] = [readIndexAcks[i] EXCEPT ![ctx] = readIndexAcks[i][ctx] \cup {j}]]
                           /\ IF Cardinality(readIndexAcks'[i][ctx]) >= Quorum(voters[i])
                              THEN messages' = messages \ {m} \cup
                                   {[type |-> "ReadIndexResponse", to |-> readIndexReq[i][ctx].from, from |-> i, term |-> currentTerm[i],
                                     mindex |-> commitIndex[i], mterm |-> 0, entries |-> <<readIndexReq[i][ctx]>>, commit |-> 0,
                                     reject |-> FALSE, context |-> ""]}
                              ELSE messages' = messages \ {m}
                           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                          nextIndex, matchIndex, votesGranted, timer, voters, learners,
                                          leader, leadTransferee, pendingConfIndex, readIndexReq, kvStore>>
                      ELSE messages' = messages \ {m}
                           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                          nextIndex, matchIndex, votesGranted, timer, voters, learners,
                                          leader, leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>

Apply(s) ==
    /\ appliedIndex[s] < commitIndex[s]
    /\ LET applyIdx == appliedIndex[s] + 1
          entry == log[s][applyIdx]
       IN /\ appliedIndex' = [appliedIndex EXCEPT ![s] = applyIdx]
          /\ IF entry.type = "ConfChange"
             THEN /\ voters' = [voters EXCEPT ![s] = entry.voters]
                  /\ learners' = [learners EXCEPT ![s] = entry.learners]
                  /\ UNCHANGED <<kvStore>>
             ELSE /\ kvStore' = [kvStore EXCEPT ![s] = [kvStore[s] EXCEPT ![entry.command.key] = entry.command.val]]
                  /\ UNCHANGED <<voters, learners>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex,
                   matchIndex, votesGranted, messages, timer, leader, leadTransferee,
                   pendingConfIndex, readIndexAcks, readIndexReq>>

TransferLeadership(s, target) ==
    /\ state[s] = "leader"
    /\ target \in voters[s]
    /\ target # s
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = target]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, messages, timer, voters,
                   learners, leader, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>

Send(m) ==
    /\ messages' = messages \cup {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, timer, voters, learners,
                   leader, leadTransferee, pendingConfIndex, readIndexAcks, readIndexReq, kvStore>>

Next ==
    \/ \E s \in Server: Timeout(s)
    \/ \E s \in Server, cmd \in Value, type \in {"Normal", "ConfChange"}, newVoters, newLearners \in SUBSET Server:
        ClientRequest(s, cmd, type, newVoters, newLearners)
    \/ \E m \in messages: Receive(m)
    \/ \E s \in Server: Apply(s)
    \/ \E s, t \in Server: TransferLeadership(s, t)
    \/ \E m \in {[type: Str, to: Server, from: Server, term: Int, mindex: Int, mterm: Int, entries: Seq(Any), commit: Int, reject: Bool, context: Str]}: Send(m)

Spec == Init /\ [][Next]_vars

AtMostOneLeaderPerTerm ==
    \A t \in {currentTerm[s] | s \in Server}:
        Cardinality({s \in Server | state[s] = "leader" /\ currentTerm[s] = t}) <= 1

LeaderCompleteness ==
    \A i, j \in Server:
        \A t \in {currentTerm[s] | s \in Server}:
            IF state[i] = "leader" /\ currentTerm[i] = t /\
               state[j] = "leader" /\ currentTerm[j] > t
            THEN \A idx \in 1..commitIndex[i]:
                    \E entry \in DOMAIN log[j]: log[j][entry] = log[i][idx]

LogMatching ==
    \A i, j \in Server:
        \A idx \in DOMAIN log[i] \cap DOMAIN log[j]:
            IF log[i][idx].term = log[j][idx].term
            THEN \A k \in 1..idx: log[i][k] = log[j][k]

State_Machine_Safety ==
    \A i, j \in Server:
        \A idx \in DOMAIN log[i] \cap DOMAIN log[j]:
            IF appliedIndex[i] >= idx /\ appliedIndex[j] >= idx
            THEN log[i][idx].command = log[j][idx].command

====