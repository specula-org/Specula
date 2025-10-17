---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Set(Str);
    Commands,
    \* @type: Int;
    ElectionTimeout,
    \* @type: Int;
    HeartbeatTimeout

ASSUME /\ Servers /= {}
       /\ HeartbeatTimeout > 0
       /\ ElectionTimeout > HeartbeatTimeout
       /\ Card(Servers) % 2 = 1

NilServer == "NilServer"
NilTerm == 0
NilIndex == 0

Quorum == (Card(Servers) \div 2) + 1

VARIABLES
    \* @type: [key: Str, val: Int];
    currentTerm,
    \* @type: [key: Str, val: Str];
    votedFor,
    \* @type: [key: Str, val: Seq([term: Int, command: Str])];
    log,
    \* @type: [key: Str, val: Int];
    commitIndex,
    \* @type: [key: Str, val: Str];
    state,
    \* @type: [key: Str, val: Str];
    leader,
    \* @type: [key: Str, val: Int];
    electionTimer,
    \* @type: [key: Str, val: Int];
    heartbeatTimer,
    \* @type: [key: Str, val: Set(Str)];
    votesGranted,
    \* @type: [key: Str, val: [key: Str, val: Int]];
    nextIndex,
    \* @type: [key: Str, val: [key: Str, val: Int]];
    matchIndex,
    \* @type: Bag([type: Str, from: Str, to: Str, mterm: Int, prevLogIndex: Int, prevLogTerm: Int, entries: Seq([term: Int, command: Str]), leaderCommit: Int, lastLogIndex: Int, lastLogTerm: Int, voteGranted: Bool]);
    messages

vars == <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, heartbeatTimer, votesGranted, nextIndex, matchIndex, messages>>

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN NilTerm ELSE l[Len(l)].term

IsUpToDate(myLog, candLogIndex, candLogTerm) ==
    LET myLastLogTerm == LastLogTerm(myLog)
        myLastLogIndex == LastLogIndex(myLog)
    IN \/ candLogTerm > myLastLogTerm
       \/ /\ candLogTerm = myLastLogTerm
          /\ candLogIndex >= myLastLogIndex

BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = NilServer]
    /\ leader' = [leader EXCEPT ![i] = NilServer]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = ElectionTimeout]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]

\* Actions

Tick(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[i] > 0
    /\ electionTimer' = [electionTimer EXCEPT ![i] = electionTimer[i] - 1]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, heartbeatTimer, votesGranted, nextIndex, matchIndex, messages>>

LeaderTick(i) ==
    /\ state[i] = "Leader"
    /\ heartbeatTimer[i] > 0
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = heartbeatTimer[i] - 1]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, votesGranted, nextIndex, matchIndex, messages>>

ElectionTimeout(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[i] = 0
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ leader' = [leader EXCEPT ![i] = NilServer]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = ElectionTimeout]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ messages' = messages \+ [
            type |-> "MsgPreVote",
            from |-> i,
            to |-> j,
            mterm |-> currentTerm[i] + 1,
            lastLogIndex |-> LastLogIndex(log[i]),
            lastLogTerm |-> LastLogTerm(log[i])
        ] @@ (j \in Servers \ {i})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, heartbeatTimer>>

HeartbeatTimeout(i) ==
    /\ state[i] = "Leader"
    /\ heartbeatTimer[i] = 0
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = HeartbeatTimeout]
    /\ messages' = messages \+ [
            type |-> "MsgApp",
            from |-> i,
            to |-> j,
            mterm |-> currentTerm[i],
            prevLogIndex |-> nextIndex[i][j] - 1,
            prevLogTerm |-> IF nextIndex[i][j] - 1 > 0 THEN log[i][nextIndex[i][j] - 1].term ELSE NilTerm,
            entries |-> << >>,
            leaderCommit |-> commitIndex[i]
        ] @@ (j \in Servers \ {i})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, votesGranted, nextIndex, matchIndex>>

ClientRequest(cmd) ==
    /\ \E i \in Servers: state[i] = "Leader"
    /\ LET leaderNode == CHOOSE l \in Servers: state[l] = "Leader"
       IN /\ log' = [log EXCEPT ![leaderNode] = Append(log[leaderNode], [term |-> currentTerm[leaderNode], command |-> cmd])]
          /\ messages' = messages \+ [
                type |-> "MsgApp",
                from |-> leaderNode,
                to |-> j,
                mterm |-> currentTerm[leaderNode],
                prevLogIndex |-> LastLogIndex(log[leaderNode]),
                prevLogTerm |-> LastLogTerm(log[leaderNode]),
                entries |-> <<[term |-> currentTerm[leaderNode], command |-> cmd]>>,
                leaderCommit |-> commitIndex[leaderNode]
             ] @@ (j \in Servers \ {leaderNode})
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, state, leader, electionTimer, heartbeatTimer, votesGranted, nextIndex, matchIndex>>

HandleMessage(m) ==
    LET i == m.to
    IN
    \* Message with a higher term: revert to follower
    IF m.mterm > currentTerm[i] THEN
        /\ BecomeFollower(i, m.mterm)
        /\ UNCHANGED <<log, commitIndex, heartbeatTimer, nextIndex, matchIndex, messages>>
    ELSE
        CASE m.type = "MsgPreVote" ->
            IF m.mterm < currentTerm[i] THEN
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<vars>>
            ELSE
                /\ LET voteOK == /\ votedFor[i] \in {NilServer, m.from}
                                 /\ IsUpToDate(log[i], m.lastLogIndex, m.lastLogTerm)
                   IN messages' = (messages \- {m}) \+ {[
                        type |-> "MsgPreVoteResp",
                        from |-> i,
                        to |-> m.from,
                        mterm |-> currentTerm[i],
                        voteGranted |-> voteOK
                    ]}
                /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, heartbeatTimer, votesGranted, nextIndex, matchIndex>>

        [] m.type = "MsgPreVoteResp" ->
            IF m.mterm = currentTerm[i] /\ state[i] = "PreCandidate" THEN
                /\ LET newVotes == IF m.voteGranted THEN votesGranted[i] \cup {m.from} ELSE votesGranted[i]
                   IN /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                      /\ IF Card(newVotes) >= Quorum THEN
                            \* Won pre-vote, start real election
                            /\ state' = [state EXCEPT ![i] = "Candidate"]
                            /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
                            /\ votedFor' = [votedFor EXCEPT ![i] = i]
                            /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
                            /\ electionTimer' = [electionTimer EXCEPT ![i] = ElectionTimeout]
                            /\ messages' = (messages \- {m}) \+ [
                                    type |-> "MsgVote",
                                    from |-> i,
                                    to |-> j,
                                    mterm |-> currentTerm[i] + 1,
                                    lastLogIndex |-> LastLogIndex(log[i]),
                                    lastLogTerm |-> LastLogTerm(log[i])
                                ] @@ (j \in Servers \ {i})
                            /\ UNCHANGED <<log, commitIndex, leader, heartbeatTimer, nextIndex, matchIndex>>
                         ELSE
                            /\ messages' = messages \- {m}
                            /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
            ELSE
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<vars>>

        [] m.type = "MsgVote" ->
            IF m.mterm < currentTerm[i] THEN
                /\ messages' = (messages \- {m}) \+ {[
                        type |-> "MsgVoteResp",
                        from |-> i,
                        to |-> m.from,
                        mterm |-> currentTerm[i],
                        voteGranted |-> FALSE
                    ]}
                /\ UNCHANGED <<vars>>
            ELSE
                /\ LET voteOK == /\ votedFor[i] \in {NilServer, m.from}
                                 /\ IsUpToDate(log[i], m.lastLogIndex, m.lastLogTerm)
                   IN /\ IF voteOK THEN
                            /\ votedFor' = [votedFor EXCEPT ![i] = m.from]
                            /\ electionTimer' = [electionTimer EXCEPT ![i] = ElectionTimeout]
                         ELSE
                            /\ UNCHANGED <<votedFor, electionTimer>>
                      /\ messages' = (messages \- {m}) \+ {[
                            type |-> "MsgVoteResp",
                            from |-> i,
                            to |-> m.from,
                            mterm |-> currentTerm[i],
                            voteGranted |-> voteOK
                         ]}
                /\ UNCHANGED <<currentTerm, log, commitIndex, state, leader, heartbeatTimer, votesGranted, nextIndex, matchIndex>>

        [] m.type = "MsgVoteResp" ->
            IF m.mterm = currentTerm[i] /\ state[i] = "Candidate" THEN
                /\ LET newVotes == IF m.voteGranted THEN votesGranted[i] \cup {m.from} ELSE votesGranted[i]
                   IN /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                      /\ IF Card(newVotes) >= Quorum THEN
                            \* Won election, become leader
                            /\ state' = [state EXCEPT ![i] = "Leader"]
                            /\ leader' = [leader EXCEPT ![i] = i]
                            /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> LastLogIndex(log[i]) + 1]]
                            /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> NilIndex]]
                            /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![i] = HeartbeatTimeout]
                            /\ messages' = (messages \- {m}) \+ [
                                    type |-> "MsgApp",
                                    from |-> i,
                                    to |-> j,
                                    mterm |-> currentTerm[i],
                                    prevLogIndex |-> LastLogIndex(log[i]),
                                    prevLogTerm |-> LastLogTerm(log[i]),
                                    entries |-> << >>,
                                    leaderCommit |-> commitIndex[i]
                                ] @@ (j \in Servers \ {i})
                            /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionTimer>>
                         ELSE
                            /\ messages' = messages \- {m}
                            /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, heartbeatTimer, nextIndex, matchIndex>>
            ELSE
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<vars>>

        [] m.type = "MsgApp" ->
            IF m.mterm < currentTerm[i] THEN
                /\ messages' = (messages \- {m}) \+ {[
                        type |-> "MsgAppResp",
                        from |-> i,
                        to |-> m.from,
                        mterm |-> currentTerm[i],
                        success |-> FALSE,
                        matchIndex |-> NilIndex
                    ]}
                /\ UNCHANGED <<vars>>
            ELSE
                /\ electionTimer' = [electionTimer EXCEPT ![i] = ElectionTimeout]
                /\ leader' = [leader EXCEPT ![i] = m.from]
                /\ LET logOK == /\ m.prevLogIndex <= LastLogIndex(log[i])
                                /\ IF m.prevLogIndex > 0 THEN log[i][m.prevLogIndex].term = m.prevLogTerm ELSE TRUE
                   IN IF logOK THEN
                        /\ LET newLog == SubSeq(log[i], 1, m.prevLogIndex) \o m.entries
                           IN /\ log' = [log EXCEPT ![i] = newLog]
                              /\ IF m.leaderCommit > commitIndex[i] THEN
                                    /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.leaderCommit, LastLogIndex(newLog)})]
                                 ELSE
                                    /\ UNCHANGED commitIndex
                        /\ messages' = (messages \- {m}) \+ {[
                                type |-> "MsgAppResp",
                                from |-> i,
                                to |-> m.from,
                                mterm |-> currentTerm[i],
                                success |-> TRUE,
                                matchIndex |-> LastLogIndex(newLog)
                            ]}
                        /\ UNCHANGED <<currentTerm, votedFor, state, heartbeatTimer, votesGranted, nextIndex, matchIndex>>
                      ELSE
                        /\ messages' = (messages \- {m}) \+ {[
                                type |-> "MsgAppResp",
                                from |-> i,
                                to |-> m.from,
                                mterm |-> currentTerm[i],
                                success |-> FALSE,
                                matchIndex |-> NilIndex
                            ]}
                        /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, heartbeatTimer, votesGranted, nextIndex, matchIndex>>

        [] m.type = "MsgAppResp" ->
            IF m.mterm = currentTerm[i] /\ state[i] = "Leader" THEN
                /\ IF m.success THEN
                    /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.from] = m.matchIndex + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![m.from] = m.matchIndex]]
                    /\ LET newCommitIndex ==
                            CHOOSE N \in (commitIndex[i]+1)..LastLogIndex(log[i])+1 :
                                /\ N > commitIndex[i]
                                /\ log[i][N-1].term = currentTerm[i]
                                /\ Card({j \in Servers |-> matchIndex[i][j] >= N-1} \cup {i}) >= Quorum
                       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                   ELSE
                    /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.from] = Max({1, nextIndex[i][m.from] - 1})]]
                    /\ UNCHANGED <<matchIndex, commitIndex>>
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<currentTerm, votedFor, log, state, leader, electionTimer, heartbeatTimer, votesGranted>>
            ELSE
                /\ messages' = messages \- {m}
                /\ UNCHANGED <<vars>>

DropMessage(m) ==
    /\ messages' = messages \- {m}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leader, electionTimer, heartbeatTimer, votesGranted, nextIndex, matchIndex>>

Init ==
    /\ currentTerm = [i \in Servers |-> NilTerm]
    /\ votedFor = [i \in Servers |-> NilServer]
    /\ log = [i \in Servers |-> << >>]
    /\ commitIndex = [i \in Servers |-> NilIndex]
    /\ state = [i \in Servers |-> "Follower"]
    /\ leader = [i \in Servers |-> NilServer]
    /\ electionTimer = [i \in Servers |-> ElectionTimeout]
    /\ heartbeatTimer = [i \in Servers |-> HeartbeatTimeout]
    /\ votesGranted = [i \in Servers |-> {}]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ messages = [type |-> ""]

Next ==
    \/ \E i \in Servers: Tick(i)
    \/ \E i \in Servers: LeaderTick(i)
    \/ \E i \in Servers: ElectionTimeout(i)
    \/ \E i \in Servers: HeartbeatTimeout(i)
    \/ \E cmd \in Commands: ClientRequest(cmd)
    \/ \E m \in BagToSet(messages): HandleMessage(m)
    \/ \E m \in BagToSet(messages): DropMessage(m)

====