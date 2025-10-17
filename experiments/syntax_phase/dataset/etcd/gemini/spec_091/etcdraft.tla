---- MODULE etcdraft ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Server,          \* The set of server IDs, e.g., {"s1", "s2", "s3"}
    Value,           \* The set of client-provided values for the KV store
    Key,             \* The set of keys for the KV store
    Nil              \* A special value, distinct from all others

ASSUME Server \cap Value = {}
ASSUME Server \cap Key = {}
ASSUME Nil \notin Server \cup Value \cup Key

\* Message types, corresponding to pb.MessageType
MsgType ==
    { "MsgProp", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp",
      "MsgPreVote", "MsgPreVoteResp", "MsgHeartbeat", "MsgHeartbeatResp",
      "MsgSnap", "MsgTimeoutNow", "MsgReadIndex" }

\* Server states, corresponding to StateType
ServerState == { "Follower", "Candidate", "PreCandidate", "Leader" }

\* Log entry types
EntryType == { "Normal", "ConfChange" }

LogEntry == [term: Nat, val: Value \cup {Nil}, key: Key \cup {Nil}, type: EntryType]

\* Configuration constants from raft.go Config
CONSTANT
    ElectionTimeout,  \* Abstract time units for election timeout
    HeartbeatTimeout, \* Abstract time units for heartbeat timeout
    PreVoteEnabled    \* Boolean to enable/disable PreVote

VARIABLES
    servers,          \* A record mapping each server to its state
    network,          \* A set of messages in transit
    kvStore,          \* The distributed key-value store state
    clientWrites,     \* A sequence of pending client write requests {key, val}
    clientReads,      \* A sequence of pending client read requests {key, context}
    clientResponses   \* A sequence of responses to clients

vars == << servers, network, kvStore, clientWrites, clientReads, clientResponses >>

QuorumSize == (Cardinality(Server) \div 2) + 1

\* Helper functions
LastIndex(log) == Len(log)
LastTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term
Max(S) == CHOOSE x \in S: \A y \in S: y <= x

\* A candidate's log is up-to-date if its last entry has a higher term,
\* or the same term and a longer log. Corresponds to raftLog.isUpToDate.
IsUpToDate(candTerm, candIndex, voterLog) ==
    LET voterLastTerm == LastTerm(voterLog)
        voterLastIndex == LastIndex(voterLog)
    IN (candTerm > voterLastTerm) \/
       (candTerm = voterLastTerm /\ candIndex >= voterLastIndex)

TypeOK ==
    /\ servers \in [Server ->
        [ state         : ServerState,
          term          : Nat,
          votedFor      : Server \cup {Nil},
          log           : Seq(LogEntry),
          commitIndex   : Nat,
          appliedIndex  : Nat,
          leader        : Server \cup {Nil},
          electionTimer : 0..ElectionTimeout,
          \* Leader-specific state
          nextIndex     : [Server -> Nat],
          matchIndex    : [Server -> Nat],
          \* Candidate-specific state
          votesGranted  : SUBSET Server,
          \* ReadOnly state
          readOnly      : [ reqs : Seq([ctx: Nat, index: Nat, key: Key]),
                            acks : [Nat -> SUBSET Server],
                            readyToRead : SUBSET Nat ]
        ]]
    /\ network \subseteq
        [ type          : MsgType,
          from          : Server,
          to            : Server,
          term          : Nat,
          \* MsgApp / MsgAppResp
          index         : Nat,
          prevLogIndex  : Nat,
          prevLogTerm   : Nat,
          entries       : Seq(LogEntry),
          leaderCommit  : Nat,
          reject        : BOOLEAN,
          rejectHint    : Nat,
          \* MsgVote / MsgVoteResp
          logTerm       : Nat,
          logIndex      : Nat,
          \* MsgHeartbeatResp / MsgReadIndex
          context       : Nat \cup {Nil}
        ]
    /\ kvStore \in [Key -> Value]
    /\ clientWrites \in Seq([key: Key, val: Value])
    /\ clientReads \in Seq([key: Key, context: Nat])
    /\ clientResponses \in Seq([context: Nat, val: Value \cup {Nil}, success: BOOLEAN])

Init ==
    /\ servers = [ s \in Server |->
        [ state         |-> "Follower",
          term          |-> 0,
          votedFor      |-> Nil,
          log           |-> << >>,
          commitIndex   |-> 0,
          appliedIndex  |-> 0,
          leader        |-> Nil,
          electionTimer |-> 0,
          nextIndex     |-> [t \in Server |-> 1],
          matchIndex    |-> [t \in Server |-> 0],
          votesGranted  |-> {},
          readOnly      |-> [ reqs |-> << >>, acks |-> [ c \in {} |-> {} ], readyToRead |-> {} ]
        ] ]
    /\ network = {}
    /\ kvStore = [k \in Key |-> Nil]
    /\ clientWrites = << >>
    /\ clientReads = << >>
    /\ clientResponses = << >>

\* ----------------------------------------------------------------------------
\* Client Actions
\* ----------------------------------------------------------------------------
ClientWriteRequest(key, val) ==
    /\ clientWrites' = Append(clientWrites, [key |-> key, val |-> val])
    /\ UNCHANGED << servers, network, kvStore, clientReads, clientResponses >>

ClientReadRequest(key, context) ==
    /\ clientReads' = Append(clientReads, [key |-> key, context |-> context])
    /\ UNCHANGED << servers, network, kvStore, clientWrites, clientResponses >>

\* ----------------------------------------------------------------------------
\* Internal and Timer-Driven Actions
\* ----------------------------------------------------------------------------
Tick(s) ==
    /\ servers[s].electionTimer < ElectionTimeout
    /\ servers' = [servers EXCEPT ![s].electionTimer = @ + 1]
    /\ UNCHANGED << network, kvStore, clientWrites, clientReads, clientResponses >>

Timeout(s) ==
    LET self == servers[s]
    IN /\ self.state \in {"Follower", "Candidate", "PreCandidate"}
       /\ self.electionTimer = ElectionTimeout
       /\ ( \/ (PreVoteEnabled /\ self.state # "PreCandidate") /\
                LET newTerm == self.term + 1
                IN /\ servers' = [servers EXCEPT ![s] = [self EXCEPT
                        !state         = "PreCandidate",
                        !term          = newTerm,
                        !votedFor      = Nil,
                        !electionTimer = 0,
                        !votesGranted  = {s},
                        !leader        = Nil
                      ]]
                   /\ network' = network \cup
                        { [ type         |-> "MsgPreVote",
                            from         |-> s,
                            to           |-> peer,
                            term         |-> newTerm,
                            logIndex     |-> LastIndex(self.log),
                            logTerm      |-> LastTerm(self.log),
                            index        |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
                            leaderCommit |-> 0, reject |-> FALSE, rejectHint |-> 0,
                            context      |-> Nil
                          ] : peer \in Server \ {s} }
          \/ (((PreVoteEnabled /\ self.state = "PreCandidate") \/ ~PreVoteEnabled)) /\
                LET newTerm == self.term + 1
                IN /\ servers' = [servers EXCEPT ![s] = [self EXCEPT
                        !state         = "Candidate",
                        !term          = newTerm,
                        !votedFor      = s,
                        !electionTimer = 0,
                        !votesGranted  = {s},
                        !leader        = Nil
                      ]]
                   /\ network' = network \cup
                        { [ type         |-> "MsgVote",
                            from         |-> s,
                            to           |-> peer,
                            term         |-> newTerm,
                            logIndex     |-> LastIndex(self.log),
                            logTerm      |-> LastTerm(self.log),
                            index        |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
                            leaderCommit |-> 0, reject |-> FALSE, rejectHint |-> 0,
                            context      |-> Nil
                          ] : peer \in Server \ {s} }
          )
    /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

LeaderHeartbeat(s) ==
    /\ servers[s].state = "Leader"
    /\ network' = network \cup
        { [ type         |-> "MsgHeartbeat",
            from         |-> s,
            to           |-> p,
            term         |-> servers[s].term,
            leaderCommit |-> servers[s].commitIndex,
            context      |-> Nil,
            index        |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
            logIndex     |-> 0, logTerm     |-> 0, reject |-> FALSE, rejectHint |-> 0
          ] : p \in Server \ {s} }
    /\ UNCHANGED << servers, kvStore, clientWrites, clientReads, clientResponses >>

\* ----------------------------------------------------------------------------
\* Message Handling Actions
\* ----------------------------------------------------------------------------
Receive(msg) ==
    LET from == msg.from
        to == msg.to
        s == servers[to]
    IN
    \* If message has a higher term, recipient becomes a follower.
    \* PreVote messages are an exception and do not cause a term change.
    IF msg.type # "MsgPreVote" /\ msg.term > s.term THEN
        LET newS == [ s EXCEPT
                        !term = msg.term,
                        !state = "Follower",
                        !votedFor = Nil,
                        !leader = Nil ]
        IN HandleMessage(msg, newS)
    \* If message has a lower term, it's rejected/ignored.
    ELSE IF msg.term < s.term THEN
        LET respType = CASE msg.type = "MsgApp"       -> "MsgAppResp"
                         [] msg.type = "MsgHeartbeat" -> "MsgHeartbeatResp"
                         [] msg.type = "MsgVote"      -> "MsgVoteResp"
                         [] msg.type = "MsgPreVote"   -> "MsgPreVoteResp"
                         [] OTHER -> "Nil"
        IN IF respType # "Nil" THEN
            /\ network' = (network \ {msg}) \cup
                {[ type |-> respType, from |-> to, to |-> from, term |-> s.term,
                   reject |-> TRUE,
                   index |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
                   leaderCommit |-> 0, rejectHint |-> 0, logIndex |-> 0,
                   logTerm |-> 0, context |-> Nil ]}
            /\ UNCHANGED << servers, kvStore, clientWrites, clientReads, clientResponses >>
        ELSE
            /\ network' = network \ {msg}
            /\ UNCHANGED << servers, kvStore, clientWrites, clientReads, clientResponses >>
    \* If terms are equal, handle the message based on state.
    ELSE HandleMessage(msg, s)

HandleMessage(msg, s) ==
    CASE msg.type = "MsgVote" -> HandleVoteRequest(msg, s)
       [] msg.type = "MsgPreVote" -> HandleVoteRequest(msg, s)
       [] msg.type = "MsgVoteResp" -> HandleVoteResponse(msg, s)
       [] msg.type = "MsgPreVoteResp" -> HandleVoteResponse(msg, s)
       [] msg.type = "MsgApp" -> HandleAppendEntries(msg, s)
       [] msg.type = "MsgHeartbeat" -> HandleHeartbeat(msg, s)
       [] msg.type = "MsgAppResp" -> HandleAppendEntriesResponse(msg, s)
       [] msg.type = "MsgHeartbeatResp" -> HandleHeartbeatResponse(msg, s)
       [] msg.type = "MsgProp" -> HandleProposal(msg, s)
       [] msg.type = "MsgReadIndex" -> HandleReadIndex(msg, s)
       [] OTHER -> /\ network' = network \ {msg}
                   /\ UNCHANGED << servers, kvStore, clientWrites, clientReads, clientResponses >>

HandleVoteRequest(msg, s) ==
    LET to == msg.to
        from == msg.from
        voteGranted == /\ s.state \in {"Follower", "Candidate", "PreCandidate"}
                       /\ (s.votedFor = Nil \/ s.votedFor = from)
                       /\ IsUpToDate(msg.logTerm, msg.logIndex, s.log)
        newS == IF voteGranted THEN [s EXCEPT !votedFor = from] ELSE s
        respType == IF msg.type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp"
    IN
    /\ network' = (network \ {msg}) \cup
        {[ type |-> respType, from |-> to, to |-> from, term |-> s.term,
           reject |-> ~voteGranted,
           index |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
           leaderCommit |-> 0, rejectHint |-> 0, logIndex |-> 0,
           logTerm |-> 0, context |-> Nil ]}
    /\ servers' = [servers EXCEPT ![to] = newS]
    /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

HandleVoteResponse(msg, s) ==
    LET to == msg.to
    IN
    /\ IF s.state \in {"Candidate", "PreCandidate"} /\ msg.term = s.term THEN
        IF ~msg.reject THEN
            LET newVotes = s.votesGranted \cup {msg.from}
            IN
            IF Cardinality(newVotes) >= QuorumSize THEN
                IF s.state = "PreCandidate" THEN \* Won pre-vote, start real election
                    /\ servers' = [servers EXCEPT ![to] = [s EXCEPT
                            !state         = "Candidate",
                            !votedFor      = to,
                            !electionTimer = 0,
                            !votesGranted  = {to}
                          ]]
                       /\ network' = (network \ {msg}) \cup
                            { [ type         |-> "MsgVote",
                                from         |-> to,
                                to           |-> peer,
                                term         |-> s.term,
                                logIndex     |-> LastIndex(s.log),
                                logTerm      |-> LastTerm(s.log),
                                index        |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
                                leaderCommit |-> 0, reject |-> FALSE, rejectHint |-> 0,
                                context      |-> Nil
                              ] : peer \in Server \ {to} }
                ELSE \* Won election, become leader
                    LET lastIdx = LastIndex(s.log)
                        newLastIdx = lastIdx + 1
                    IN /\ servers' = [servers EXCEPT ![to] = [s EXCEPT
                            !state         = "Leader",
                            !leader        = to,
                            !nextIndex     = [p \in Server |-> newLastIdx],
                            !matchIndex    = [p \in Server |-> IF p = to THEN newLastIdx ELSE 0],
                            !log           = Append(@.log, [term |-> s.term, val |-> Nil, key |-> Nil, type |-> "Normal"])
                          ]]
                       /\ network' = network \ {msg}
            ELSE
                /\ servers' = [servers EXCEPT ![to].votesGranted = newVotes]
                /\ network' = network \ {msg}
        ELSE
            /\ UNCHANGED servers
            /\ network' = network \ {msg}
    ELSE
        /\ UNCHANGED servers
        /\ network' = network \ {msg}
    /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

HandleAppendEntries(msg, s) ==
    LET to == msg.to
        prevIdx = msg.prevLogIndex
        prevTerm = msg.prevLogTerm
        logOK = /\ prevIdx = 0
                \/ /\ prevIdx > 0
                   /\ prevIdx <= Len(s.log)
                   /\ s.log[prevIdx].term = prevTerm
        newS = [s EXCEPT !electionTimer = 0, !leader = msg.from]
    IN
    IF logOK THEN
        LET newLog = SubSeq(s.log, 1, prevIdx) \o msg.entries
            newCommitIndex = max(s.commitIndex, min(msg.leaderCommit, LastIndex(newLog)))
        IN /\ servers' = [servers EXCEPT ![to] = [newS EXCEPT !log = newLog, !commitIndex = newCommitIndex]]
           /\ network' = (network \ {msg}) \cup
                {[ type |-> "MsgAppResp", from |-> to, to |-> msg.from, term |-> s.term,
                   reject |-> FALSE, index |-> LastIndex(newLog),
                   prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
                   leaderCommit |-> 0, rejectHint |-> 0, logTerm |-> 0, context |-> Nil ]}
    ELSE
        /\ servers' = [servers EXCEPT ![to] = newS]
        /\ network' = (network \ {msg}) \cup
            {[ type |-> "MsgAppResp", from |-> to, to |-> msg.from, term |-> s.term,
               reject |-> TRUE, rejectHint |-> LastIndex(s.log),
               index |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
               leaderCommit |-> 0, logTerm |-> 0, context |-> Nil ]}
    /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

HandleHeartbeat(msg, s) ==
    LET to == msg.to
    IN /\ servers' = [servers EXCEPT ![to] =
            [ s EXCEPT !electionTimer = 0,
                       !leader = msg.from,
                       !commitIndex = max(@.commitIndex, min(msg.leaderCommit, LastIndex(s.log)))
            ]]
       /\ network' = (network \ {msg}) \cup
            {[ type |-> "MsgHeartbeatResp", from |-> to, to |-> msg.from, term |-> s.term,
               context |-> msg.context,
               reject |-> FALSE, index |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
               leaderCommit |-> 0, rejectHint |-> 0, logTerm |-> 0 ]}
       /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

HandleAppendEntriesResponse(msg, s) ==
    LET to == msg.to
        from == msg.from
    IN
    /\ IF s.state = "Leader" /\ msg.term = s.term THEN
        IF msg.reject THEN
            /\ servers' = [servers EXCEPT ![to].nextIndex[from] = max(1, s.nextIndex[from] - 1)]
        ELSE
            LET newNext = msg.index + 1
                newMatch = msg.index
                newNextIndex = [s.nextIndex EXCEPT ![from] = newNext]
                newMatchIndex = [s.matchIndex EXCEPT ![from] = newMatch]
                newCommitIndex =
                    LET CanCommit(n) =
                            /\ n > s.commitIndex
                            /\ n <= LastIndex(s.log)
                            /\ s.log[n].term = s.term
                            /\ Cardinality({p \in Server | newMatchIndex[p] >= n}) >= QuorumSize
                        Committable = {n \in s.commitIndex+1..LastIndex(s.log) : CanCommit(n)}
                    IN IF Committable = {}
                       THEN s.commitIndex
                       ELSE Max(Committable)
            IN /\ servers' = [servers EXCEPT ![to] = [s EXCEPT !nextIndex = newNextIndex,
                                                              !matchIndex = newMatchIndex,
                                                              !commitIndex = newCommitIndex]]
    ELSE
        /\ UNCHANGED servers
    /\ network' = network \ {msg}
    /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

HandleHeartbeatResponse(msg, s) ==
    LET to == msg.to
        from == msg.from
    IN
    /\ IF s.state = "Leader" /\ msg.term = s.term /\ msg.context # Nil THEN
        LET ctx = msg.context
            newAcks = s.readOnly.acks[ctx] \cup {from}
            newS = [s EXCEPT !readOnly.acks[ctx] = newAcks]
        IN IF Cardinality(newAcks) >= QuorumSize THEN
            /\ servers' = [servers EXCEPT ![to] = [newS EXCEPT !readOnly.readyToRead = @.readOnly.readyToRead \cup {ctx}]]
        ELSE
            /\ servers' = [servers EXCEPT ![to] = newS]
    ELSE
        /\ UNCHANGED servers
    /\ network' = network \ {msg}
    /\ UNCHANGED << kvStore, clientWrites, clientReads, clientResponses >>

HandleProposal(msg, s) ==
    IF s.state = "Leader" THEN
        LET req = Head(clientWrites)
            lastIdx = LastIndex(s.log)
            newEntry = [term |-> s.term, val |-> req.val, key |-> req.key, type |-> "Normal"]
        IN /\ servers' = [servers EXCEPT ![s].log = Append(@.log, newEntry)]
           /\ clientWrites' = Tail(clientWrites)
           /\ UNCHANGED << network, kvStore, clientReads, clientResponses >>
    ELSE
        /\ UNCHANGED << servers, network, kvStore, clientWrites, clientReads, clientResponses >>

HandleReadIndex(msg, s) ==
    IF s.state = "Leader" THEN
        LET req = Head(clientReads)
            ctx = req.context
            readState = [ctx |-> ctx, index |-> s.commitIndex, key |-> req.key]
            newReqs = Append(s.readOnly.reqs, readState)
            newAcks = [s.readOnly.acks EXCEPT ![ctx] = {s}]
            newReadOnly = [s.readOnly EXCEPT !reqs = newReqs, !acks = newAcks]
        IN /\ servers' = [servers EXCEPT ![s].readOnly = newReadOnly]
           /\ network' = network \cup
                { [ type         |-> "MsgHeartbeat",
                    from         |-> s,
                    to           |-> p,
                    term         |-> s.term,
                    leaderCommit |-> s.commitIndex,
                    context      |-> ctx,
                    index |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> << >>,
                    logIndex |-> 0, logTerm |-> 0, reject |-> FALSE, rejectHint |-> 0
                  ] : p \in Server \ {s} }
           /\ clientReads' = Tail(clientReads)
           /\ UNCHANGED << kvStore, clientWrites, clientResponses >>
    ELSE
        /\ UNCHANGED << servers, network, kvStore, clientWrites, clientReads, clientResponses >>

\* ----------------------------------------------------------------------------
\* State Machine Application
\* ----------------------------------------------------------------------------
Apply(s) ==
    LET self = servers[s]
    IN /\ self.commitIndex > self.appliedIndex
       /\ LET i = self.appliedIndex + 1
              entry = self.log[i]
          IN /\ kvStore' = IF entry.key # Nil THEN [kvStore EXCEPT ![entry.key] = entry.val] ELSE kvStore
             /\ servers' = [servers EXCEPT ![s].appliedIndex = i]
    /\ UNCHANGED << network, clientWrites, clientReads, clientResponses >>

RespondToClientRead(s) ==
    LET self = servers[s]
    IN /\ self.state = "Leader"
       /\ \E ctx \in self.readOnly.readyToRead:
            LET req = CHOOSE r \in self.readOnly.reqs: r.ctx = ctx
            IN req.index <= self.appliedIndex
       /\ LET ctx = CHOOSE c \in self.readOnly.readyToRead:
                      LET req = CHOOSE r \in self.readOnly.reqs: r.ctx = c
                      IN req.index <= self.appliedIndex
              req = CHOOSE r \in self.readOnly.reqs: r.ctx = ctx
              val = kvStore[req.key]
              newReqs = SelectSeq(self.readOnly.reqs, LAMBDA r: r.ctx # ctx)
          IN /\ clientResponses' = Append(clientResponses, [context |-> ctx, val |-> val, success |-> TRUE])
             /\ servers' = [servers EXCEPT ![s].readOnly.readyToRead = @.readOnly.readyToRead \ {ctx},
                                        ![s].readOnly.reqs = newReqs
                           ]
             /\ UNCHANGED << network, kvStore, clientWrites, clientReads >>

\* ----------------------------------------------------------------------------
\* Next State Relation
\* ----------------------------------------------------------------------------
Next ==
    \/ \E s \in Server: Tick(s)
    \/ \E s \in Server: Timeout(s)
    \/ \E s \in Server: LeaderHeartbeat(s)
    \/ \E s \in Server: Apply(s)
    \/ \E s \in Server: RespondToClientRead(s)
    \/ \E msg \in network: Receive(msg)
    \/ \E k \in Key, v \in Value: ClientWriteRequest(k, v)
    \/ \E k \in Key, c \in 1..MAXINT: ClientReadRequest(k, c)
    \/ \E s \in Server:
        /\ servers[s].state = "Leader"
        /\ Len(clientWrites) > 0
        /\ HandleProposal([type |-> "MsgProp", to |-> s], servers[s])
    \/ \E s \in Server:
        /\ servers[s].state = "Leader"
        /\ Len(clientReads) > 0
        /\ HandleReadIndex([type |-> "MsgReadIndex", to |-> s], servers[s])

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------------
\* Liveness and Safety Properties
\* ----------------------------------------------------------------------------
LeaderCompleteness ==
    \A s1, s2 \in Server:
        LET s1_log = servers[s1].log
        IN \A i \in 1..Len(s1_log):
            LET entry = s1_log[i]
            IN (servers[s1].commitIndex >= i) =>
                \A t \in DOMAIN servers:
                    (servers[t].term > entry.term /\ servers[t].state = "Leader") =>
                        (i <= Len(servers[t].log) /\ servers[t].log[i] = entry)

StateMachineSafety ==
    \A s1, s2 \in Server:
        \A i \in Nat:
            (i > 0 /\ i <= servers[s1].appliedIndex /\ i <= servers[s2].appliedIndex) =>
                (servers[s1].log[i] = servers[s2].log[i])

LogMatchingProperty ==
    \A s1, s2 \in Server:
        LET log1 = servers[s1].log
            log2 = servers[s2].log
        IN \A i \in 1..min(Len(log1), Len(log2)):
            (log1[i].term = log2[i].term) => (log1[i] = log2[i])

LeaderElectionSafety ==
    \A t \in Nat:
        Cardinality({s \in Server | servers[s].term = t /\ servers[s].state = "Leader"}) <= 1

THEOREM Spec => [](TypeOK)
THEOREM Spec => [](LeaderElectionSafety)
THEOREM Spec => [](LogMatchingProperty)
THEOREM Spec => [](StateMachineSafety)

====
