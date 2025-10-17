---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,
    Data,
    ElectionTimeout,
    HeartbeatTimeout,
    Nil

ASSUME TLCGet("deadlock") = FALSE

VARIABLES
    messages,
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    electionTimer,
    heartbeatTimer,
    matchIndex,
    nextIndex,
    votesGranted

vars == << messages, state, currentTerm, votedFor, log, commitIndex, leader,
           electionTimer, heartbeatTimer, matchIndex, nextIndex, votesGranted >>

(* Message Types *)
MsgHup == "MsgHup"
MsgBeat == "MsgBeat"
MsgProp == "MsgProp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"

(* Node States *)
Follower == "Follower"
Candidate == "Candidate"
PreCandidate == "PreCandidate"
Leader == "Leader"

Quorum == (Cardinality(Servers) \div 2) + 1

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF l = << >> THEN 0 ELSE (Tail(l)).term

isUpToDate(candidateIndex, candidateTerm, myIndex, myTerm) ==
    \/ candidateTerm > myTerm
    \/ (candidateTerm = myTerm /\ candidateIndex >= myIndex)

TypeOk ==
    /\ state \in [Servers -> {Follower, Candidate, PreCandidate, Leader}]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ leader \in Servers \cup {Nil}
    /\ \A s \in Servers: \A e \in DOMAIN log[s]: log[s][e].term \in Nat
    /\ commitIndex \in [Servers -> Nat]
    /\ electionTimer \in [Servers -> Nat]
    /\ heartbeatTimer \in [Servers -> Nat]

Init ==
    /\ messages = EmptyBag
    /\ state = [s \in Servers |-> Follower]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ leader = Nil
    /\ electionTimer = [s \in Servers |-> 0]
    /\ heartbeatTimer = [s \in Servers |-> 0]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ votesGranted = [s \in Servers |-> {}]

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = Follower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = IF leader # Nil /\ currentTerm[leader] = term THEN leader ELSE Nil
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, heartbeatTimer, matchIndex, nextIndex, votesGranted, messages>>

StepDown(s, term) ==
    /\ state[s] # Follower
    /\ BecomeFollower(s, term)

ClientPropose(val) ==
    /\ \E s \in Servers:
        /\ state[s] = Leader
        /\ LET newEntry == [term |-> currentTerm[s], index |-> LastLogIndex(log[s]) + 1, data |-> val]
           IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
        /\ messages' = messages \cup Bagify({[type |-> MsgApp, from |-> s, to |-> p, term |-> currentTerm[s],
                                              prevLogIndex |-> LastLogIndex(log[s]),
                                              prevLogTerm |-> LastLogTerm(log[s]),
                                              entries |-> <<newEntry>>,
                                              leaderCommit |-> commitIndex[s]]
                                              : p \in Servers \ {s}})
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader, electionTimer, heartbeatTimer, matchIndex, nextIndex, votesGranted>>

Tick ==
    /\ \E s \in Servers:
        /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] + 1]
        /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = heartbeatTimer[s] + 1]
        /\ UNCHANGED <<messages, state, currentTerm, votedFor, log, commitIndex, leader, matchIndex, nextIndex, votesGranted>>

Timeout ==
    \/ \E s \in Servers:
        /\ state[s] \in {Follower, Candidate, PreCandidate}
        /\ electionTimer[s] >= ElectionTimeout
        /\ state' = [state EXCEPT ![s] = PreCandidate]
        /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
        /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
        /\ messages' = messages \cup Bagify({[type |-> MsgPreVote, from |-> s, to |-> p, term |-> currentTerm[s] + 1,
                                              lastLogIndex |-> LastLogIndex(log[s]),
                                              lastLogTerm |-> LastLogTerm(log[s])]
                                              : p \in Servers \ {s}})
        /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader, heartbeatTimer, matchIndex, nextIndex>>
    \/ \E s \in Servers:
        /\ state[s] = Leader
        /\ heartbeatTimer[s] >= HeartbeatTimeout
        /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
        /\ messages' = messages \cup Bagify({[type |-> MsgApp, from |-> s, to |-> p, term |-> currentTerm[s],
                                              prevLogIndex |-> LastLogIndex(log[s]),
                                              prevLogTerm |-> LastLogTerm(log[s]),
                                              entries |-> << >>,
                                              leaderCommit |-> commitIndex[s]]
                                              : p \in Servers \ {s}})
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, matchIndex, nextIndex, votesGranted>>

Receive(msg) ==
    LET s == msg.to IN
    /\ messages' = BagMinus(messages, {msg})
    /\ IF msg.term > currentTerm[s]
       THEN /\ StepDown(s, msg.term)
            /\ UNCHANGED <<messages>>
       ELSE /\ IF msg.term < currentTerm[s]
              THEN UNCHANGED vars
              ELSE CASE msg.type = MsgPreVote ->
                        LET myLastLogIndex == LastLogIndex(log[s])
                            myLastLogTerm == LastLogTerm(log[s])
                            voteGranted == isUpToDate(msg.lastLogIndex, msg.lastLogTerm, myLastLogIndex, myLastLogTerm)
                        IN /\ messages' = BagAdd(messages', [type |-> MsgPreVoteResp, from |-> s, to |-> msg.from, term |-> msg.term, reject |-> NOT voteGranted])
                           /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, heartbeatTimer, matchIndex, nextIndex, votesGranted>>
                   [] msg.type = MsgPreVoteResp /\ state[s] = PreCandidate ->
                        LET newVotes == IF msg.reject THEN votesGranted[s] ELSE votesGranted[s] \cup {msg.from}
                        IN IF Cardinality(newVotes \cup {s}) >= Quorum
                           THEN (* Start real election *)
                                /\ state' = [state EXCEPT ![s] = Candidate]
                                /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                                /\ votedFor' = [votedFor EXCEPT ![s] = s]
                                /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                                /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                                /\ messages' = messages' \cup Bagify({[type |-> MsgVote, from |-> s, to |-> p, term |-> currentTerm[s] + 1,
                                                                        lastLogIndex |-> LastLogIndex(log[s]),
                                                                        lastLogTerm |-> LastLogTerm(log[s])]
                                                                        : p \in Servers \ {s}})
                                /\ UNCHANGED <<log, commitIndex, leader, heartbeatTimer, matchIndex, nextIndex>>
                           ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, heartbeatTimer, matchIndex, nextIndex, messages>>
                   [] msg.type = MsgVote ->
                        LET myLastLogIndex == LastLogIndex(log[s])
                            myLastLogTerm == LastLogTerm(log[s])
                            grantVote == /\ votedFor[s] \in {Nil, msg.from}
                                         /\ isUpToDate(msg.lastLogIndex, msg.lastLogTerm, myLastLogIndex, myLastLogTerm)
                        IN /\ IF grantVote
                              THEN /\ votedFor' = [votedFor EXCEPT ![s] = msg.from]
                                   /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                              ELSE /\ UNCHANGED <<votedFor, electionTimer>>
                           /\ messages' = BagAdd(messages', [type |-> MsgVoteResp, from |-> s, to |-> msg.from, term |-> currentTerm[s], reject |-> NOT grantVote])
                           /\ UNCHANGED <<state, currentTerm, log, commitIndex, leader, heartbeatTimer, matchIndex, nextIndex, votesGranted>>
                   [] msg.type = MsgVoteResp /\ state[s] = Candidate ->
                        LET newVotes == IF msg.reject THEN votesGranted[s] ELSE votesGranted[s] \cup {msg.from}
                        IN IF Cardinality(newVotes) >= Quorum
                           THEN (* Become Leader *)
                                /\ state' = [state EXCEPT ![s] = Leader]
                                /\ leader' = s
                                /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(log[s]) + 1]]
                                /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
                                /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
                                /\ LET emptyEntry == [term |-> currentTerm[s], index |-> LastLogIndex(log[s]) + 1, data |-> "noop"]
                                   IN log' = [log EXCEPT ![s] = Append(log[s], emptyEntry)]
                                /\ messages' = messages' \cup Bagify({[type |-> MsgApp, from |-> s, to |-> p, term |-> currentTerm[s],
                                                                        prevLogIndex |-> LastLogIndex(log[s]),
                                                                        prevLogTerm |-> LastLogTerm(log[s]),
                                                                        entries |-> <<emptyEntry>>,
                                                                        leaderCommit |-> commitIndex[s]]
                                                                        : p \in Servers \ {s}})
                                /\ UNCHANGED <<currentTerm, votedFor, commitIndex, electionTimer, votesGranted>>
                           ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, heartbeatTimer, matchIndex, nextIndex, messages>>
                   [] msg.type = MsgApp /\ state[s] \in {Follower, Candidate, PreCandidate} ->
                        /\ state' = [state EXCEPT ![s] = Follower]
                        /\ leader' = msg.from
                        /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                        /\ LET logOk == /\ msg.prevLogIndex <= LastLogIndex(log[s])
                                        /\ (msg.prevLogIndex = 0 \/ log[s][msg.prevLogIndex].term = msg.prevLogTerm)
                        IN IF logOk
                           THEN /\ LET newLog == SubSeq(log[s], 1, msg.prevLogIndex) \o msg.entries
                                  IN log' = [log EXCEPT ![s] = newLog]
                               /\ commitIndex' = [commitIndex EXCEPT ![s] = min(msg.leaderCommit, LastLogIndex(newLog))]
                               /\ messages' = BagAdd(messages', [type |-> MsgAppResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
                                                                 reject |-> FALSE, index |-> LastLogIndex(newLog)])
                           ELSE /\ messages' = BagAdd(messages', [type |-> MsgAppResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
                                                                 reject |-> TRUE, index |-> commitIndex[s]])
                                /\ UNCHANGED <<log, commitIndex>>
                        /\ UNCHANGED <<currentTerm, votedFor, heartbeatTimer, matchIndex, nextIndex, votesGranted>>
                   [] msg.type = MsgAppResp /\ state[s] = Leader ->
                        LET p == msg.from IN
                        /\ IF msg.reject
                           THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![p] = nextIndex[s][p] - 1]]
                                /\ UNCHANGED <<matchIndex>>
                           ELSE /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![p] = msg.index]]
                                /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![p] = msg.index + 1]]
                        /\ LET newCommitIndex ==
                                LET CanCommit(idx) ==
                                    /\ idx > commitIndex[s]
                                    /\ log[s][idx].term = currentTerm[s]
                                    /\ Cardinality({q \in Servers |-> matchIndex'[s][q] >= idx} \cup {s}) >= Quorum
                                IN IF \E idx \in {commitIndex[s]+1..LastLogIndex(log[s])}: CanCommit(idx)
                                   THEN CHOOSE idx \in {commitIndex[s]+1..LastLogIndex(log[s])}: CanCommit(idx)
                                   ELSE commitIndex[s]
                           IN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                        /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, electionTimer, heartbeatTimer, votesGranted, messages>>
                   [] msg.type = MsgProp /\ state[s] # Leader ->
                        UNCHANGED vars
                   [] TRUE -> UNCHANGED vars

DropMessage(msg) ==
    /\ messages' = BagMinus(messages, {msg})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, electionTimer, heartbeatTimer, matchIndex, nextIndex, votesGranted>>

Next ==
    \/ \E val \in Data: ClientPropose(val)
    \/ Tick
    \/ Timeout
    \/ \E msg \in DOMAIN messages: Receive(msg)
    \/ \E msg \in DOMAIN messages: DropMessage(msg)

=============================================================================