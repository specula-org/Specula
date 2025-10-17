---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Nodes,
    ClientValues,
    Nil,
    electionTimeout,
    heartbeatTimeout

ASSUME
    /\ electionTimeout > heartbeatTimeout
    /\ heartbeatTimeout > 0
    /\ IsFiniteSet(Nodes)
    /\ Cardinality(Nodes) % 2 = 1
    /\ Nil \notin Nodes

\* Message types
MsgHup == "MsgHup"
MsgProp == "MsgProp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"

MessageTypes == { MsgHup, MsgProp, MsgApp, MsgAppResp, MsgPreVote, MsgPreVoteResp, MsgVote, MsgVoteResp }

\* Node states
Follower == "Follower"
PreCandidate == "PreCandidate"
Candidate == "Candidate"
Leader == "Leader"

NodeStates == { Follower, PreCandidate, Candidate, Leader }

vars == <<
    state, currentTerm, votedFor, log, commitIndex,
    electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
    nextIndex, matchIndex,
    messages
>>

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    electionElapsed,
    heartbeatElapsed,
    randomizedElectionTimeout,
    nextIndex,
    matchIndex,
    messages

\* Helper operators
Quorum == (Cardinality(Nodes) \div 2) + 1

LastLogIndex(lg) == Len(lg)

LastLogTerm(lg) == IF Len(lg) > 0 THEN lg[Len(lg)].term ELSE 0

isUpToDate(idx1, term1, idx2, term2) ==
    \/ term1 > term2
    \/ (term1 = term2 /\ idx1 >= idx2)

Bagify(S) == [x \in S |-> 1]

\* Initial state
Init ==
    /\ state = [n \in Nodes |-> Follower]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> Nil]
    /\ log = [n \in Nodes |-> << >>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ electionElapsed = [n \in Nodes |-> 0]
    /\ heartbeatElapsed = [n \in Nodes |-> 0]
    /\ randomizedElectionTimeout = [n \in Nodes |-> electionTimeout]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ messages = EmptyBag

\* Actions

\* A node's timer ticks.
Tick(i) ==
    /\ \/ /\ state[i] \in {Follower, PreCandidate, Candidate}
          /\ electionElapsed' = [electionElapsed EXCEPT ![i] = @ + 1]
          /\ heartbeatElapsed' = heartbeatElapsed
       \/ /\ state[i] = Leader
          /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = @ + 1]
          /\ electionElapsed' = electionElapsed
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![i] = CHOOSE t \in (electionTimeout .. 2*electionTimeout-1) : TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, messages>>

\* A follower or candidate times out and starts an election.
Timeout(i) ==
    /\ state[i] \in {Follower, PreCandidate, Candidate}
    /\ electionElapsed[i] >= randomizedElectionTimeout[i]
    /\ messages' = messages (+) {[ type |-> MsgHup, to |-> i ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

\* A leader's heartbeat timer expires, so it sends heartbeats.
LeaderHeartbeat(i) ==
    /\ state[i] = Leader
    /\ heartbeatElapsed[i] >= heartbeatTimeout
    /\ LET
        AppendEntries(j) ==
            LET prevIdx == nextIndex[i][j] - 1
                prevTerm == IF prevIdx > 0 THEN log[i][prevIdx].term ELSE 0
            IN [ type |-> MsgApp, from |-> i, to |-> j, term |-> currentTerm[i],
                 prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                 entries |-> << >>, leaderCommit |-> commitIndex[i] ]
    IN
        messages' = messages (+) Bagify({AppendEntries(j) : j \in Nodes \ {i}})
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

\* A client sends a proposal to a node.
ClientRequest(val, i) ==
    /\ val \in ClientValues
    /\ i \in Nodes
    /\ messages' = messages (+) {[ type |-> MsgProp, to |-> i, val |-> val ]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

\* Common logic for a node to step down when it sees a higher term.
BecomeFollower(i, term, current_vars) ==
    /\ state' = [current_vars.state EXCEPT ![i] = Follower]
    /\ currentTerm' = [current_vars.currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [current_vars.votedFor EXCEPT ![i] = Nil]
    /\ electionElapsed' = [current_vars.electionElapsed EXCEPT ![i] = 0]
    /\ heartbeatElapsed' = current_vars.heartbeatElapsed
    /\ randomizedElectionTimeout' = current_vars.randomizedElectionTimeout
    /\ log' = current_vars.log
    /\ commitIndex' = current_vars.commitIndex
    /\ nextIndex' = current_vars.nextIndex
    /\ matchIndex' = current_vars.matchIndex

HandleMessage(i, m, current_vars) ==
    LET sc_state == current_vars.state
        sc_currentTerm == current_vars.currentTerm
        sc_votedFor == current_vars.votedFor
        sc_log == current_vars.log
        sc_commitIndex == current_vars.commitIndex
        sc_electionElapsed == current_vars.electionElapsed
        sc_heartbeatElapsed == current_vars.heartbeatElapsed
        sc_randomizedElectionTimeout == current_vars.randomizedElectionTimeout
        sc_nextIndex == current_vars.nextIndex
        sc_matchIndex == current_vars.matchIndex
    IN
    CASE m.type = MsgHup ->
        /\ sc_state[i] \in {Follower, PreCandidate, Candidate}
        /\ state' = [sc_state EXCEPT ![i] = PreCandidate]
        /\ currentTerm' = sc_currentTerm
        /\ votedFor' = sc_votedFor
        /\ LET
            nextTerm == sc_currentTerm[i] + 1
            lastIdx == LastLogIndex(sc_log[i])
            lastTerm == LastLogTerm(sc_log[i])
            PreVoteRequest(j) == [ type |-> MsgPreVote, from |-> i, to |-> j, term |-> nextTerm,
                                   lastLogIndex |-> lastIdx, lastLogTerm |-> lastTerm ]
        IN
            messages' = messages (-) {m} (+) Bagify({PreVoteRequest(j) : j \in Nodes \ {i}})
                         (+) {[ type |-> MsgPreVoteResp, from |-> i, to |-> i, term |-> nextTerm, voteGranted |-> TRUE ]}
        /\ electionElapsed' = [sc_electionElapsed EXCEPT ![i] = 0]
        /\ UNCHANGED <<log, commitIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

    [] m.type = MsgProp ->
        IF sc_state[i] = Leader THEN
            /\ LET newEntry == [term |-> sc_currentTerm[i], val |-> m.val]
                   newLog == Append(sc_log[i], newEntry)
                   lastIdx == Len(newLog)
            IN
                /\ log' = [sc_log EXCEPT ![i] = newLog]
                /\ matchIndex' = [sc_matchIndex EXCEPT ![i] = [ @ EXCEPT ![i] = lastIdx ]]
                /\ nextIndex' = [sc_nextIndex EXCEPT ![i] = [ @ EXCEPT ![i] = lastIdx + 1 ]]
                /\ LET
                    AppendEntries(j) ==
                        LET prevIdx == sc_nextIndex[i][j] - 1
                            prevTerm == IF prevIdx > 0 THEN sc_log[i][prevIdx].term ELSE 0
                            entriesToSend == SubSeq(newLog, sc_nextIndex[i][j], Len(newLog))
                        IN [ type |-> MsgApp, from |-> i, to |-> j, term |-> sc_currentTerm[i],
                             prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                             entries |-> entriesToSend, leaderCommit |-> sc_commitIndex[i] ]
                IN
                    messages' = messages (-) {m} (+) Bagify({AppendEntries(j) : j \in Nodes \ {i}})
            /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout>>
        ELSE
            /\ messages' = messages (-) {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

    [] m.type \in {MsgPreVote, MsgVote} ->
        /\ m.term >= sc_currentTerm[i]
        /\ LET
            voted == sc_votedFor[i]
            canVote == \/ m.type = MsgPreVote
                       \/ (voted = Nil \/ voted = m.from)
            logOK == isUpToDate(m.lastLogIndex, m.lastLogTerm, LastLogIndex(sc_log[i]), LastLogTerm(sc_log[i]))
            grant == canVote /\ logOK
            respType == IF m.type = MsgPreVote THEN MsgPreVoteResp ELSE MsgVoteResp
        IN
            /\ messages' = messages (-) {m} (+) {[ type |-> respType, from |-> i, to |-> m.from, term |-> sc_currentTerm[i], voteGranted |-> grant ]}
            /\ IF grant /\ m.type = MsgVote THEN
                /\ votedFor' = [sc_votedFor EXCEPT ![i] = m.from]
                /\ electionElapsed' = [sc_electionElapsed EXCEPT ![i] = 0]
            ELSE
                /\ UNCHANGED <<votedFor, electionElapsed>>
        /\ UNCHANGED <<state, currentTerm, log, commitIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

    [] m.type \in {MsgPreVoteResp, MsgVoteResp} ->
        /\ m.term = sc_currentTerm[i]
        /\ LET
            isPreVoteResp == m.type = MsgPreVoteResp
            isVoteResp == m.type = MsgVoteResp
            isMyState == \/ (isPreVoteResp /\ sc_state[i] = PreCandidate)
                        \/ (isVoteResp /\ sc_state[i] = Candidate)
        IN
        IF isMyState THEN
            /\ LET
                Responses == { msg \in DOMAIN messages :
                                  /\ msg.to = i
                                  /\ msg.type = m.type
                                  /\ msg.term = sc_currentTerm[i] }
                grants == Cardinality({ res.from : res \in Responses | res.voteGranted })
            IN
            IF grants >= Quorum THEN
                IF isPreVoteResp THEN
                    /\ state' = [sc_state EXCEPT ![i] = Candidate]
                    /\ currentTerm' = [sc_currentTerm EXCEPT ![i] = @ + 1]
                    /\ votedFor' = [sc_votedFor EXCEPT ![i] = i]
                    /\ electionElapsed' = [sc_electionElapsed EXCEPT ![i] = 0]
                    /\ LET
                        newTerm == sc_currentTerm[i] + 1
                        lastIdx == LastLogIndex(sc_log[i])
                        lastTerm == LastLogTerm(sc_log[i])
                        VoteRequest(j) == [ type |-> MsgVote, from |-> i, to |-> j, term |-> newTerm,
                                            lastLogIndex |-> lastIdx, lastLogTerm |-> lastTerm ]
                    IN
                        messages' = messages (-) {m} (+) Bagify({VoteRequest(j) : j \in Nodes \ {i}})
                                     (+) {[ type |-> MsgVoteResp, from |-> i, to |-> i, term |-> newTerm, voteGranted |-> TRUE ]}
                    /\ UNCHANGED <<log, commitIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>
                ELSE
                    /\ state' = [sc_state EXCEPT ![i] = Leader]
                    /\ LET lastIdx == LastLogIndex(sc_log[i])
                    IN
                        /\ nextIndex' = [sc_nextIndex EXCEPT ![i] = [j \in Nodes |-> lastIdx + 1]]
                        /\ matchIndex' = [sc_matchIndex EXCEPT ![i] = [j \in Nodes |-> 0]]
                    /\ heartbeatElapsed' = [sc_heartbeatElapsed EXCEPT ![i] = 0]
                    /\ LET
                        AppendEntries(j) ==
                            [ type |-> MsgApp, from |-> i, to |-> j, term |-> sc_currentTerm[i],
                              prevLogIndex |-> LastLogIndex(sc_log[i]), prevLogTerm |-> LastLogTerm(sc_log[i]),
                              entries |-> << >>, leaderCommit |-> sc_commitIndex[i] ]
                    IN
                        messages' = messages (-) {m} (+) Bagify({AppendEntries(j) : j \in Nodes \ {i}})
                    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionElapsed, randomizedElectionTimeout>>
            ELSE
                /\ messages' = messages (-) {m}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>
        ELSE
            /\ messages' = messages (-) {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

    [] m.type = MsgApp ->
        /\ m.term = sc_currentTerm[i]
        /\ sc_state[i] \in {Follower, PreCandidate, Candidate}
        /\ state' = [sc_state EXCEPT ![i] = Follower]
        /\ electionElapsed' = [sc_electionElapsed EXCEPT ![i] = 0]
        /\ LET
            prevIdx == m.prevLogIndex
            prevTerm == m.prevLogTerm
            logOK == \/ prevIdx = 0
                     \/ (prevIdx <= Len(sc_log[i]) /\ sc_log[i][prevIdx].term = prevTerm)
        IN
            IF logOK THEN
                /\ LET
                    FindConflict(idx) ==
                        IF idx > Len(m.entries) THEN idx
                        ELSE IF \/ prevIdx + idx > Len(sc_log[i])
                                \/ m.entries[idx].term /= sc_log[i][prevIdx + idx].term
                             THEN idx
                             ELSE FindConflict(idx + 1)
                    conflictIdx == FindConflict(1)
                    newEntries == SubSeq(m.entries, conflictIdx, Len(m.entries))
                    prefix == SubSeq(sc_log[i], 1, prevIdx + conflictIdx - 1)
                    newLog == prefix \o newEntries
                    newCommit == m.leaderCommit
                    lastNewIdx == LastLogIndex(newLog)
                IN
                    /\ log' = [sc_log EXCEPT ![i] = newLog]
                    /\ commitIndex' = [sc_commitIndex EXCEPT ![i] = IF newCommit < lastNewIdx THEN newCommit ELSE lastNewIdx]
                /\ messages' = messages (-) {m} (+) {[ type |-> MsgAppResp, from |-> i, to |-> m.from, term |-> sc_currentTerm[i],
                                                       matchIndex |-> LastLogIndex(newLog), success |-> TRUE ]}
                /\ UNCHANGED <<currentTerm, votedFor, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>
            ELSE
                /\ messages' = messages (-) {m} (+) {[ type |-> MsgAppResp, from |-> i, to |-> m.from, term |-> sc_currentTerm[i],
                                                       matchIndex |-> 0, success |-> FALSE ]}
                /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

    [] m.type = MsgAppResp ->
        /\ m.term = sc_currentTerm[i]
        /\ sc_state[i] = Leader
        /\ LET j == m.from IN
            /\ messages' = messages (-) {m}
            /\ IF m.success THEN
                /\ LET newMatchIndexVal == m.matchIndex
                       newMatchIndex == [sc_matchIndex EXCEPT ![i] = [ @ EXCEPT ![j] = newMatchIndexVal ]]
                IN
                    /\ matchIndex' = newMatchIndex
                    /\ nextIndex' = [sc_nextIndex EXCEPT ![i] = [ @ EXCEPT ![j] = newMatchIndexVal + 1 ]]
                    /\ LET
                        match_on_leader_term == {idx \in {sc_commitIndex[i]+1..LastLogIndex(sc_log[i])} |
                            sc_log[i][idx].term = sc_currentTerm[i] /\
                            Cardinality({n \in Nodes | newMatchIndex[i][n] >= idx}) >= Quorum
                        }
                        newCommitIndex == IF match_on_leader_term = {} THEN sc_commitIndex[i] ELSE Max(match_on_leader_term)
                    IN
                        commitIndex' = [sc_commitIndex EXCEPT ![i] = newCommitIndex]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, electionElapsed, heartbeatElapsed, randomizedElectionTimeout>>
            ELSE
                /\ LET newNext == sc_nextIndex[i][j] - 1
                IN nextIndex' = [sc_nextIndex EXCEPT ![i] = [ @ EXCEPT ![j] = IF newNext < 1 THEN 1 ELSE newNext ]]
                /\ UNCHANGED <<state, currentTerm, votedFor, log, matchIndex, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout>>

    [] m.type \notin MessageTypes \/ m.term < sc_currentTerm[i] ->
        /\ messages' = messages (-) {m}
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex>>

\* A node i receives a message m.
Receive(m) ==
    LET i == m.to IN
    /\ i \in Nodes
    /\ IF m.term > currentTerm[i] THEN
        LET new_vars == [
                state |-> [state EXCEPT ![i] = Follower],
                currentTerm |-> [currentTerm EXCEPT ![i] = m.term],
                votedFor |-> [votedFor EXCEPT ![i] = Nil],
                log |-> log,
                commitIndex |-> commitIndex,
                electionElapsed |-> [electionElapsed EXCEPT ![i] = 0],
                heartbeatElapsed |-> heartbeatElapsed,
                randomizedElectionTimeout |-> randomizedElectionTimeout,
                nextIndex |-> nextIndex,
                matchIndex |-> matchIndex
            ]
        IN HandleMessage(i, m, new_vars)
    ELSE
        LET current_vars == [
                state |-> state,
                currentTerm |-> currentTerm,
                votedFor |-> votedFor,
                log |-> log,
                commitIndex |-> commitIndex,
                electionElapsed |-> electionElapsed,
                heartbeatElapsed |-> heartbeatElapsed,
                randomizedElectionTimeout |-> randomizedElectionTimeout,
                nextIndex |-> nextIndex,
                matchIndex |-> matchIndex
            ]
        IN HandleMessage(i, m, current_vars)

Next ==
    \/ \E i \in Nodes:
        \/ Tick(i)
        \/ Timeout(i)
        \/ LeaderHeartbeat(i)
    \/ \E val \in ClientValues, i \in Nodes: ClientRequest(val, i)
    \/ \E m \in DOMAIN messages: Receive(m)

Spec == Init /\ [][Next]_vars

====
