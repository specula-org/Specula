---- MODULE etcdraft ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    \* The set of server IDs.
    Servers,
    \* The set of possible client commands.
    Command,
    \* A special value representing null/none.
    Nil,
    \* Base timeout values in abstract ticks.
    HeartbeatTimeout,
    ElectionTimeout,
    \* Whether to enable the Pre-Vote optimization.
    PreVoteEnabled

ASSUME /\ TypeOK
       /\ HeartbeatTimeout > 0
       /\ ElectionTimeout > HeartbeatTimeout

\* -----------------------------------------------------------------------------
\* Model values for states and message types, based on raft.go.

ServerStates == {"Follower", "Candidate", "PreCandidate", "Leader"}
MessageTypes == {
    "MsgHup", "MsgBeat", "MsgProp", "MsgApp", "MsgAppResp", "MsgVote",
    "MsgVoteResp", "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp",
    "MsgPreVote", "MsgPreVoteResp", "MsgTimeoutNow", "MsgTransferLeader"
}

\* -----------------------------------------------------------------------------
\* State variables of the system.

vars == <<
    \* Per-server state variables, mapping closely to the `raft` struct in Go.
    state,          \* The server's current state (Follower, Candidate, etc.)
    currentTerm,    \* The server's current term number.
    votedFor,       \* The candidate ID this server voted for in the current term.
    log,            \* The server's log, a sequence of entries.
    commitIndex,    \* The index of the highest log entry known to be committed.
    appliedIndex,   \* The index of the highest log entry applied to the state machine.
    lead,           \* The server's belief of who the current leader is.
    leadTransferee, \* The target of a leadership transfer.

    \* Timer-related variables.
    electionElapsed,
    heartbeatElapsed,
    randomizedElectionTimeout,

    \* Leader-specific state for tracking followers.
    nextIndex,
    matchIndex,

    \* Candidate-specific state for tracking votes.
    votesGranted,
    preVotesGranted,

    \* The network is modeled as a set of in-flight messages.
    messages
>>

\* -----------------------------------------------------------------------------
\* Helper operators.

Quorum == (Cardinality(Servers) \div 2) + 1

LastLogIndex(lg) == Len(lg)
LastLogTerm(lg) == lg[Len(lg)].term

\* The log up-to-dateness check from Raft section 5.4.1.
IsUpToDate(candidateLogTerm, candidateLogIndex, voterLog) ==
    LET voterLastTerm == LastLogTerm(voterLog)
    IN (candidateLogTerm > voterLastTerm) \/
       ((candidateLogTerm = voterLastTerm) /\
        (candidateLogIndex >= LastLogIndex(voterLog)))

\* -----------------------------------------------------------------------------
\* Initial state of the system.

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << {term |-> 0, cmd |-> Nil} >>] \* Log starts with a sentinel at index 1.
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ lead = [s \in Servers |-> Nil]
    /\ leadTransferee = [s \in Servers |-> Nil]
    /\ electionElapsed = [s \in Servers |-> 0]
    /\ heartbeatElapsed = [s \in Servers |-> 0]
    /\ \E f \in [Servers -> {t \in INT: t >= ElectionTimeout /\ t < 2 * ElectionTimeout}]:
        randomizedElectionTimeout = f
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ preVotesGranted = [s \in Servers |-> {}]
    /\ messages = {}

\* -----------------------------------------------------------------------------
\* State transitions (Actions).

\* A server's internal timer ticks.
Tick(i) ==
    /\ state[i] = "Leader"
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = heartbeatElapsed[i] + 1]
        /\ electionElapsed' = [electionElapsed EXCEPT ![i] = electionElapsed[i] + 1]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                       lead, leadTransferee, randomizedElectionTimeout, nextIndex,
                       matchIndex, votesGranted, preVotesGranted, messages>>
    \/ state[i] \in {"Follower", "Candidate", "PreCandidate"}
        /\ electionElapsed' = [electionElapsed EXCEPT ![i] = electionElapsed[i] + 1]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                       lead, leadTransferee, heartbeatElapsed, randomizedElectionTimeout,
                       nextIndex, matchIndex, votesGranted, preVotesGranted, messages>>

\* A follower or candidate times out and starts an election (MsgHup).
ElectionTimeout(i) ==
    /\ state[i] \in {"Follower", "Candidate", "PreCandidate"}
    /\ electionElapsed[i] >= randomizedElectionTimeout[i]
    /\ IF PreVoteEnabled
       THEN \* Start a pre-vote campaign.
            /\ state' = [state EXCEPT ![i] = "PreCandidate"]
            /\ lead' = [lead EXCEPT ![i] = Nil]
            /\ preVotesGranted' = [preVotesGranted EXCEPT ![i] = {i}]
            /\ messages' = messages \cup
                { [ type |-> "MsgPreVote", from |-> i, to |-> j,
                    term |-> currentTerm[i] + 1,
                    logTerm |-> LastLogTerm(log[i]),
                    index |-> LastLogIndex(log[i]) ]
                  : j \in Servers }
            /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex,
                           nextIndex, matchIndex, leadTransferee, votesGranted>>
       ELSE \* Start a normal election.
            /\ state' = [state EXCEPT ![i] = "Candidate"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
            /\ votedFor' = [votedFor EXCEPT ![i] = i]
            /\ lead' = [lead EXCEPT ![i] = Nil]
            /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
            /\ messages' = messages \cup
                { [ type |-> "MsgVote", from |-> i, to |-> j,
                    term |-> currentTerm[i] + 1,
                    logTerm |-> LastLogTerm(log[i]),
                    index |-> LastLogIndex(log[i]) ]
                  : j \in Servers }
            /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex,
                           leadTransferee, preVotesGranted>>
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ \E r \in {t \in INT: t >= ElectionTimeout /\ t < 2 * ElectionTimeout}:
        randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![i] = r]
    /\ UNCHANGED <<heartbeatElapsed>>

\* A leader's heartbeat timer expires, causing it to send heartbeats (MsgBeat).
HeartbeatTimeout(i) ==
    /\ state[i] = "Leader"
    /\ heartbeatElapsed[i] >= HeartbeatTimeout
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
    /\ messages' = messages \cup
        { [ type |-> "MsgHeartbeat", from |-> i, to |-> j,
            term |-> currentTerm[i],
            commit |-> Min({commitIndex[i], matchIndex[i][j]}) ]
          : j \in Servers \ {i} }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   lead, leadTransferee, electionElapsed, randomizedElectionTimeout,
                   nextIndex, matchIndex, votesGranted, preVotesGranted>>

\* A client sends a proposal to a leader.
ClientRequest(i, cmd) ==
    /\ state[i] = "Leader"
    /\ leadTransferee[i] = Nil
    /\ LET newEntry == {term |-> currentTerm[i], cmd |-> cmd}
    /\ log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ matchIndex' = [matchIndex EXCEPT ![i][i] = LastLogIndex(log'[i])]
    /\ messages' = messages \cup
        { [ type |-> "MsgApp", from |-> i, to |-> j,
            term |-> currentTerm[i],
            prevLogIndex |-> LastLogIndex(log[i]),
            prevLogTerm |-> LastLogTerm(log[i]),
            entries |-> <<newEntry>>,
            leaderCommit |-> commitIndex[i] ]
          : j \in Servers \ {i} }
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex, lead,
                   leadTransferee, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, nextIndex, votesGranted, preVotesGranted>>

\* A server receives a message. This is the main dispatcher.
HandleMessage(msg) ==
    LET i == msg.to
        j == msg.from
        new_messages == messages \ {msg}
    IN
    \* Rule for messages with a higher term.
    IF msg.term > currentTerm[i]
    THEN /\ LET newLead == IF msg.type \in {"MsgApp", "MsgHeartbeat", "MsgSnap"} THEN j ELSE Nil
         /\ state' = [state EXCEPT ![i] = "Follower"]
         /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.term]
         /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
         /\ lead' = [lead EXCEPT ![i] = newLead]
         /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
         /\ \E r \in {t \in INT: t >= ElectionTimeout /\ t < 2 * ElectionTimeout}:
             randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![i] = r]
         /\ leadTransferee' = [leadTransferee EXCEPT ![i] = Nil]
         \* Re-queue the message to be processed in the new, lower term state.
         /\ messages' = new_messages \cup {msg}
         /\ UNCHANGED <<log, commitIndex, appliedIndex, heartbeatElapsed,
                        nextIndex, matchIndex, votesGranted, preVotesGranted>>
    \* Rule for messages with a lower term (stale messages are dropped).
    ELSE IF msg.term < currentTerm[i]
    THEN /\ messages' = new_messages
         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                        lead, leadTransferee, electionElapsed, heartbeatElapsed,
                        randomizedElectionTimeout, nextIndex, matchIndex,
                        votesGranted, preVotesGranted>>
    \* Rule for messages with the same term.
    ELSE CASE msg.type = "MsgApp" /\ state[i] \in {"Follower", "Candidate", "PreCandidate"} ->
            LET prevLogIndex == msg.prevLogIndex
                prevLogTerm == msg.prevLogTerm
                logOK == /\ prevLogIndex < LastLogIndex(log[i]) + 1
                         /\ log[i][prevLogIndex].term = prevLogTerm
            IN IF \neg logOK
               THEN /\ messages' = new_messages \cup
                        {[ type |-> "MsgAppResp", from |-> i, to |-> j,
                           term |-> currentTerm[i], reject |-> TRUE,
                           index |-> commitIndex[i] ]}
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                   appliedIndex, lead, leadTransferee, electionElapsed,
                                   heartbeatElapsed, randomizedElectionTimeout,
                                   nextIndex, matchIndex, votesGranted, preVotesGranted>>
               ELSE /\ LET newLog == SubSeq(log[i], 1, prevLogIndex) \o msg.entries
                    /\ log' = [log EXCEPT ![i] = newLog]
                    /\ IF msg.leaderCommit > commitIndex[i]
                       THEN commitIndex' = [commitIndex EXCEPT ![i] = Min({msg.leaderCommit, LastLogIndex(newLog)})]
                       ELSE UNCHANGED commitIndex
                    /\ messages' = new_messages \cup
                        {[ type |-> "MsgAppResp", from |-> i, to |-> j,
                           term |-> currentTerm[i], reject |-> FALSE,
                           index |-> LastLogIndex(newLog) ]}
                    /\ state' = [state EXCEPT ![i] = "Follower"]
                    /\ lead' = [lead EXCEPT ![i] = j]
                    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
                    /\ UNCHANGED <<currentTerm, votedFor, appliedIndex, leadTransferee,
                                   heartbeatElapsed, randomizedElectionTimeout,
                                   nextIndex, matchIndex, votesGranted, preVotesGranted>>
         [] msg.type = "MsgAppResp" /\ state[i] = "Leader" ->
            IF msg.reject
            THEN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({1, nextIndex[i][j] - 1})]
                 /\ UNCHANGED matchIndex
            ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][j] = msg.index + 1]
                 /\ matchIndex' = [matchIndex EXCEPT ![i][j] = msg.index]
            /\ messages' = new_messages
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                           lead, leadTransferee, electionElapsed, heartbeatElapsed,
                           randomizedElectionTimeout, votesGranted, preVotesGranted>>
         [] msg.type = "MsgVote" ->
            LET grant == (votedFor[i] = Nil \/ votedFor[i] = j) /\
                         IsUpToDate(msg.logTerm, msg.index, log[i])
            IN IF grant
               THEN /\ votedFor' = [votedFor EXCEPT ![i] = j]
                    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
                    /\ messages' = new_messages \cup
                        {[ type |-> "MsgVoteResp", from |-> i, to |-> j,
                           term |-> currentTerm[i], reject |-> FALSE ]}
                    /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex,
                                   lead, leadTransferee, heartbeatElapsed,
                                   randomizedElectionTimeout, nextIndex, matchIndex,
                                   votesGranted, preVotesGranted>>
               ELSE /\ messages' = new_messages \cup
                        {[ type |-> "MsgVoteResp", from |-> i, to |-> j,
                           term |-> currentTerm[i], reject |-> TRUE ]}
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                   appliedIndex, lead, leadTransferee, electionElapsed,
                                   heartbeatElapsed, randomizedElectionTimeout,
                                   nextIndex, matchIndex, votesGranted, preVotesGranted>>
         [] msg.type = "MsgVoteResp" /\ state[i] = "Candidate" ->
            LET newVotes == IF \neg msg.reject
                            THEN votesGranted[i] \cup {j}
                            ELSE votesGranted[i]
            IN IF Cardinality(newVotes) >= Quorum
               THEN /\ state' = [state EXCEPT ![i] = "Leader"]
                    /\ lead' = [lead EXCEPT ![i] = i]
                    /\ nextIndex' = [nextIndex EXCEPT ![i] = [s \in Servers |-> LastLogIndex(log[i]) + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![i] = [s \in Servers |-> 0] WITH [i] |-> LastLogIndex(log[i])]
                    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
                    /\ LET noOpEntry == {term |-> currentTerm[i], cmd |-> "NoOp"}
                    /\ log' = [log EXCEPT ![i] = Append(log[i], noOpEntry)]
                    /\ messages' = new_messages \cup
                        { [ type |-> "MsgApp", from |-> i, to |-> s,
                            term |-> currentTerm[i],
                            prevLogIndex |-> LastLogIndex(log[i]),
                            prevLogTerm |-> LastLogTerm(log[i]),
                            entries |-> <<noOpEntry>>,
                            leaderCommit |-> commitIndex[i] ]
                          : s \in Servers \ {i} }
                    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, appliedIndex,
                                   leadTransferee, electionElapsed,
                                   randomizedElectionTimeout, votesGranted, preVotesGranted>>
               ELSE /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                    /\ messages' = new_messages
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                   appliedIndex, lead, leadTransferee, electionElapsed,
                                   heartbeatElapsed, randomizedElectionTimeout,
                                   nextIndex, matchIndex, preVotesGranted>>
         [] msg.type = "MsgPreVote" ->
            LET grant == IsUpToDate(msg.logTerm, msg.index, log[i])
            IN /\ messages' = new_messages \cup
                    {[ type |-> "MsgPreVoteResp", from |-> i, to |-> j,
                       term |-> msg.term, reject |-> \neg grant ]}
               /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                              appliedIndex, lead, leadTransferee, electionElapsed,
                              heartbeatElapsed, randomizedElectionTimeout,
                              nextIndex, matchIndex, votesGranted, preVotesGranted>>
         [] msg.type = "MsgPreVoteResp" /\ state[i] = "PreCandidate" ->
            LET newVotes == IF \neg msg.reject
                            THEN preVotesGranted[i] \cup {j}
                            ELSE preVotesGranted[i]
            IN IF Cardinality(newVotes) >= Quorum
               THEN \* Won pre-vote, now start a real election.
                    /\ state' = [state EXCEPT ![i] = "Candidate"]
                    /\ currentTerm' = [currentTerm EXCEPT ![i] = msg.term]
                    /\ votedFor' = [votedFor EXCEPT ![i] = i]
                    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
                    /\ messages' = new_messages \cup
                        { [ type |-> "MsgVote", from |-> i, to |-> s,
                            term |-> msg.term,
                            logTerm |-> LastLogTerm(log[i]),
                            index |-> LastLogIndex(log[i]) ]
                          : s \in Servers }
                    /\ UNCHANGED <<log, commitIndex, appliedIndex, lead, leadTransferee,
                                   electionElapsed, heartbeatElapsed,
                                   randomizedElectionTimeout, nextIndex, matchIndex,
                                   preVotesGranted>>
               ELSE /\ preVotesGranted' = [preVotesGranted EXCEPT ![i] = newVotes]
                    /\ messages' = new_messages
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                   appliedIndex, lead, leadTransferee, electionElapsed,
                                   heartbeatElapsed, randomizedElectionTimeout,
                                   nextIndex, matchIndex, votesGranted>>
         [] msg.type = "MsgHeartbeat" /\ state[i] \in {"Follower", "Candidate", "PreCandidate"} ->
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ lead' = [lead EXCEPT ![i] = j]
            /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
            /\ IF msg.commit > commitIndex[i]
               THEN commitIndex' = [commitIndex EXCEPT ![i] = Min({msg.commit, LastLogIndex(log[i])})]
               ELSE UNCHANGED commitIndex
            /\ messages' = new_messages \cup
                {[ type |-> "MsgHeartbeatResp", from |-> i, to |-> j,
                   term |-> currentTerm[i] ]}
            /\ UNCHANGED <<currentTerm, votedFor, log, appliedIndex, leadTransferee,
                           heartbeatElapsed, randomizedElectionTimeout,
                           nextIndex, matchIndex, votesGranted, preVotesGranted>>
         [] msg.type = "MsgHeartbeatResp" /\ state[i] = "Leader" ->
            /\ messages' = new_messages
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                           lead, leadTransferee, electionElapsed, heartbeatElapsed,
                           randomizedElectionTimeout, nextIndex, matchIndex,
                           votesGranted, preVotesGranted>>
         [] OTHER ->
            /\ messages' = new_messages
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                           lead, leadTransferee, electionElapsed, heartbeatElapsed,
                           randomizedElectionTimeout, nextIndex, matchIndex,
                           votesGranted, preVotesGranted>>

\* A leader advances its commit index if a quorum of followers has replicated an entry.
LeaderAdvanceCommit(i) ==
    /\ state[i] = "Leader"
    /\ LET possibleCommits ==
            { n \in (commitIndex[i] + 1)..LastLogIndex(log[i]) :
                /\ log[i][n].term = currentTerm[i]
                /\ Cardinality({s \in Servers : matchIndex[i][s] >= n}) >= Quorum }
    /\ possibleCommits /= {}
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max(possibleCommits)]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex, lead,
                   leadTransferee, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, nextIndex, matchIndex,
                   votesGranted, preVotesGranted, messages>>

\* A server applies a committed entry to its state machine.
Apply(i) ==
    /\ appliedIndex[i] < commitIndex[i]
    /\ appliedIndex' = [appliedIndex EXCEPT ![i] = appliedIndex[i] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead,
                   leadTransferee, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, nextIndex, matchIndex,
                   votesGranted, preVotesGranted, messages>>

\* -----------------------------------------------------------------------------
\* The next-state relation.

Next ==
    \/ \E i \in Servers:
        \/ Tick(i)
        \/ ElectionTimeout(i)
        \/ HeartbeatTimeout(i)
        \/ \E cmd \in Command: ClientRequest(i, cmd)
        \/ LeaderAdvanceCommit(i)
        \/ Apply(i)
    \/ \E msg \in messages: HandleMessage(msg)

\* -----------------------------------------------------------------------------
\* Invariants and properties.

TypeOK ==
    /\ state \in [Servers -> ServerStates]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ \A s \in Servers: log[s] \in Seq({r \in [term: Nat, cmd: Command \cup {Nil}] : TRUE})
    /\ commitIndex \in [Servers -> Nat]
    /\ appliedIndex \in [Servers -> Nat]
    /\ lead \in [Servers -> Servers \cup {Nil}]
    /\ leadTransferee \in [Servers -> Servers \cup {Nil}]
    /\ electionElapsed \in [Servers -> Nat]
    /\ heartbeatElapsed \in [Servers -> Nat]
    /\ randomizedElectionTimeout \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ preVotesGranted \in [Servers -> SUBSET Servers]
    /\ messages \subseteq [
        type: MessageTypes, from: Servers, to: Servers, term: Nat,
        logTerm: Nat, index: Nat, entries: Seq(DOMAIN log[1]),
        commit: Nat, leaderCommit: Nat, prevLogIndex: Nat, prevLogTerm: Nat,
        reject: BOOLEAN
    ]

\* At most one leader can exist in any given term.
ElectionSafety ==
    \A t \in {currentTerm[s] : s \in Servers}:
        Cardinality({s \in Servers: state[s] = "Leader" /\ currentTerm[s] = t}) <= 1

\* A leader's log is never overwritten or deleted.
LeaderLogsOnlyAppend ==
    \A i \in Servers:
        state[i] = "Leader" => log[i] = PREV log[i] \/ Len(log[i]) > Len(PREV log[i])

\* If two logs contain an entry with the same index and term, the logs are identical up to that index.
LogMatching ==
    \A i, j \in Servers:
        \A idx \in 1..Min({Len(log[i]), Len(log[j])}):
            log[i][idx].term = log[j][idx].term => log[i][idx] = log[j][idx]

\* Committed entries are persistent and present in all future leader logs.
LeaderCompleteness ==
    \A i \in Servers, idx \in 1..commitIndex[i]:
        \A j \in Servers, t \in (currentTerm[i] + 1)..Max({currentTerm[s] : s \in Servers}):
            (state[j] = "Leader" /\ currentTerm[j] = t) =>
                /\ Len(log[j]) >= idx
                /\ log[j][idx] = log[i][idx]

\* If a server has applied an entry, no other server can apply a different entry at that index.
StateSafety ==
    \A i, j \in Servers:
        \A idx \in 1..Min({appliedIndex[i], appliedIndex[j]}):
            log[i][idx] = log[j][idx]

\* All servers must maintain these basic invariants.
ServerInvariants ==
    \A i \in Servers:
        /\ appliedIndex[i] <= commitIndex[i]
        /\ commitIndex[i] <= LastLogIndex(log[i])
        /\ (state[i] = "Leader" => lead[i] = i)

=============================================================================
