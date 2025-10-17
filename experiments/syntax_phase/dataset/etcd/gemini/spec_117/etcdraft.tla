---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Server,      \* The set of servers, e.g., {"n1", "n2", "n3"}
    Command,     \* The set of possible client commands
    Nil,         \* A special value, distinct from Server IDs
    ElectionTimeoutMin,
    ElectionTimeoutMax,
    HeartbeatTimeout

ASSUME /\ Server \subseteq {"n1", "n2", "n3", "n4", "n5"}
       /\ Command = {"v1", "v2"}
       /\ ElectionTimeoutMin \in Nat
       /\ ElectionTimeoutMax \in Nat
       /\ HeartbeatTimeout \in Nat
       /\ ElectionTimeoutMin =< ElectionTimeoutMax
       /\ HeartbeatTimeout < ElectionTimeoutMin

\* System state variables
vars == << state, currentTerm, votedFor, log, commitIndex,
           leader, electionTimer, heartbeatTimer,
           nextIndex, matchIndex, network >>

\* Message types
MessageTypes == { "MsgProp", "MsgApp", "MsgAppResp", "MsgPreVote", "MsgPreVoteResp", "MsgVote", "MsgVoteResp" }
NodeStates == { "Follower", "PreCandidate", "Candidate", "Leader" }

TypeOK ==
    /\ state \in [Server -> NodeStates]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq([term: Nat, command: Command])]
    /\ commitIndex \in [Server -> Nat]
    /\ leader \in [Server -> Server \cup {Nil}]
    /\ electionTimer \in [Server -> 0..ElectionTimeoutMax]
    /\ heartbeatTimer \in [Server -> 0..HeartbeatTimeout]
    /\ nextIndex \in [Server -> [Server -> Nat \cup {0}]]
    /\ matchIndex \in [Server -> [Server -> Nat \cup {0}]]
    /\ IsBag(network)

\* Helper operators
Quorum == (Cardinality(Server) \div 2) + 1
LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
IsUpToDate(candidateLog, voterLog) ==
    LET candLastTerm == LastLogTerm(candidateLog)
        voterLastTerm == LastLogTerm(voterLog)
    IN \/ candLastTerm > voterLastTerm
       \/ /\ candLastTerm = voterLastTerm
          /\ LastLogIndex(candidateLog) >= LastLogIndex(voterLog)

\* Initial state of the system
Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ leader = [s \in Server |-> Nil]
    /\ electionTimer \in [Server -> ElectionTimeoutMin..ElectionTimeoutMax]
    /\ heartbeatTimer = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [p \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [p \in Server |-> 0]]
    /\ network = EmptyBag

\* Actions

\* A node's election timer ticks down.
Tick(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimer[s] > 0
    /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] - 1]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader,
                    heartbeatTimer, nextIndex, matchIndex, network >>

\* A follower or pre-candidate times out and starts a pre-election campaign.
TimeoutStartPreElection(s) ==
    /\ state[s] \in {"Follower", "PreCandidate"}
    /\ electionTimer[s] = 0
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![s] \in ElectionTimeoutMin..ElectionTimeoutMax]
    /\ LET nextTerm == currentTerm[s] + 1
           lastIdx == LastLogIndex(log[s])
           lastTerm == LastLogTerm(log[s])
           newMsgs == Bagify({[ type |-> "MsgPreVote", from |-> s, to |-> p, term |-> nextTerm,
                                lastLogIndex |-> lastIdx, lastLogTerm |-> lastTerm ] : p \in Server \ {s}})
    \IN network' = network (+) newMsgs
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, heartbeatTimer, nextIndex, matchIndex >>

\* A node steps down to become a follower when it sees a higher term.
StepDown(s, newTerm) ==
    /\ newTerm > currentTerm[s]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ electionTimer' = [electionTimer EXCEPT ![s] \in ElectionTimeoutMin..ElectionTimeoutMax]

\* A node receives a pre-vote request.
HandlePreVoteRequest(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgPreVote"
        /\ m.to = s
        /\ LET candLog == [lastLogIndex |-> m.lastLogIndex, lastLogTerm |-> m.lastLogTerm]
               voterLog == [lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s])]
               grant == /\ m.term > currentTerm[s]
                        /\ IsUpToDate([term |-> m.lastLogTerm, command |-> ""] \circ << >>, log[s])
               resp == [ type |-> "MsgPreVoteResp", from |-> s, to |-> m.from,
                         term |-> m.term, reject |-> ~grant ]
        \IN /\ network' = (network (-) Bagify({m})) (+) Bagify({resp})
            /\ UNCHANGED vars

\* A pre-candidate receives a pre-vote response.
HandlePreVoteResponse(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgPreVoteResp"
        /\ m.to = s
        /\ state[s] = "PreCandidate"
        /\ network' = network (-) Bagify({m})
        /\ IF m.term = currentTerm[s] + 1 /\ ~m.reject
           THEN LET votes == {p \in Server: \E resp \in BagToSet(network):
                                /\ resp.type = "MsgPreVoteResp"
                                /\ resp.from = p
                                /\ resp.to = s
                                /\ resp.term = m.term
                                /\ ~resp.reject} \cup {s}
                IN IF Cardinality(votes) >= Quorum
                   THEN /\ state' = [state EXCEPT ![s] = "Candidate"]
                        /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                        /\ votedFor' = [votedFor EXCEPT ![s] = s]
                        /\ leader' = [leader EXCEPT ![s] = Nil]
                        /\ electionTimer' = [electionTimer EXCEPT ![s] \in ElectionTimeoutMin..ElectionTimeoutMax]
                        /\ LET newTerm == currentTerm[s] + 1
                               lastIdx == LastLogIndex(log[s])
                               lastTerm == LastLogTerm(log[s])
                               newMsgs == Bagify({[ type |-> "MsgVote", from |-> s, to |-> p, term |-> newTerm,
                                                    lastLogIndex |-> lastIdx, lastLogTerm |-> lastTerm ] : p \in Server \ {s}})
                        \IN network' = (network (-) Bagify({m})) (+) newMsgs
                        /\ UNCHANGED << log, commitIndex, heartbeatTimer, nextIndex, matchIndex >>
                   ELSE UNCHANGED vars
           ELSE UNCHANGED vars

\* A node receives a vote request.
HandleVoteRequest(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgVote"
        /\ m.to = s
        /\ LET grant == /\ m.term = currentTerm[s]
                        /\ (votedFor[s] = Nil \/ votedFor[s] = m.from)
                        /\ IsUpToDate([term |-> m.lastLogTerm, command |-> ""] \circ << >>, log[s])
               resp == [ type |-> "MsgVoteResp", from |-> s, to |-> m.from,
                         term |-> currentTerm[s], reject |-> ~grant ]
        \IN /\ network' = (network (-) Bagify({m})) (+) Bagify({resp})
            /\ IF grant THEN votedFor' = [votedFor EXCEPT ![s] = m.from]
                       ELSE UNCHANGED votedFor
            /\ UNCHANGED << state, currentTerm, log, commitIndex, leader,
                            electionTimer, heartbeatTimer, nextIndex, matchIndex >>

\* A candidate receives a vote response.
HandleVoteResponse(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgVoteResp"
        /\ m.to = s
        /\ state[s] = "Candidate"
        /\ m.term = currentTerm[s]
        /\ network' = network (-) Bagify({m})
        /\ IF ~m.reject
           THEN LET votes == {p \in Server: \E resp \in BagToSet(network):
                                /\ resp.type = "MsgVoteResp"
                                /\ resp.from = p
                                /\ resp.to = s
                                /\ resp.term = m.term
                                /\ ~resp.reject} \cup {s}
                IN IF Cardinality(votes) >= Quorum
                   THEN /\ state' = [state EXCEPT ![s] = "Leader"]
                        /\ leader' = [leader EXCEPT ![s] = s]
                        /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(log[s]) + 1]]
                        /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
                        /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
                        /\ LET noOpEntry == [term |-> currentTerm[s], command |-> "NoOp"]
                        \IN log' = [log EXCEPT ![s] = Append(log[s], noOpEntry)]
                        /\ UNCHANGED << currentTerm, votedFor, commitIndex, electionTimer >>
                   ELSE UNCHANGED vars
           ELSE UNCHANGED vars

\* A leader's heartbeat timer expires, so it sends heartbeats (empty AppendEntries).
LeaderHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatTimer[s] = 0
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = HeartbeatTimeout]
    /\ LET newMsgs == Bagify({[ type |-> "MsgApp", from |-> s, to |-> p, term |-> currentTerm[s],
                                prevLogIndex |-> nextIndex[s][p] - 1,
                                prevLogTerm |-> IF nextIndex[s][p] > 1 THEN log[s][nextIndex[s][p] - 1].term ELSE 0,
                                entries |-> << >>,
                                leaderCommit |-> commitIndex[s] ] : p \in Server \ {s}})
    \IN network' = network (+) newMsgs
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader,
                    electionTimer, nextIndex, matchIndex >>

\* A client sends a proposal to a node.
ClientRequest(cmd) ==
    \E s \in Server:
        /\ LET msg == [ type |-> "MsgProp", command |-> cmd, from |-> "client", to |-> s ]
        \IN network' = network (+) Bagify({msg})
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader,
                        electionTimer, heartbeatTimer, nextIndex, matchIndex >>

\* A leader receives a proposal and appends it to its log.
HandleProposal(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgProp"
        /\ m.to = s
        /\ state[s] = "Leader"
        /\ LET newEntry == [term |-> currentTerm[s], command |-> m.command]
        \IN /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
            /\ network' = network (-) Bagify({m})
            /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, leader,
                            electionTimer, heartbeatTimer, nextIndex, matchIndex >>

\* A follower receives a proposal and forwards it to the leader.
HandleFollowerProposal(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgProp"
        /\ m.to = s
        /\ state[s] = "Follower"
        /\ leader[s] /= Nil
        /\ LET fwdMsg == [m EXCEPT !.to = leader[s]]
        \IN network' = (network (-) Bagify({m})) (+) Bagify({fwdMsg})
        /\ UNCHANGED vars

\* A leader sends AppendEntries to a follower.
LeaderSendAppendEntries(s, p) ==
    /\ state[s] = "Leader"
    /\ p /= s
    /\ LastLogIndex(log[s]) >= nextIndex[s][p]
    /\ LET prevIdx == nextIndex[s][p] - 1
           prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
           newEntries == SubSeq(log[s], nextIndex[s][p], LastLogIndex(log[s]))
           msg == [ type |-> "MsgApp", from |-> s, to |-> p, term |-> currentTerm[s],
                    prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                    entries |-> newEntries, leaderCommit |-> commitIndex[s] ]
    \IN network' = network (+) Bagify({msg})
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader,
                    electionTimer, heartbeatTimer, nextIndex, matchIndex >>

\* A node receives an AppendEntries request.
HandleAppendEntriesRequest(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgApp"
        /\ m.to = s
        /\ LET logOk == /\ m.prevLogIndex = 0
                       \/ /\ m.prevLogIndex <= LastLogIndex(log[s])
                          /\ log[s][m.prevLogIndex].term = m.prevLogTerm
        \IN IF m.term < currentTerm[s]
            THEN /\ LET resp == [ type |-> "MsgAppResp", from |-> s, to |-> m.from,
                                  term |-> currentTerm[s], reject |-> TRUE, index |-> 0 ]
                 \IN network' = (network (-) Bagify({m})) (+) Bagify({resp})
                 /\ UNCHANGED vars
            ELSE /\ network' = network (-) Bagify({m})
                 /\ state' = [state EXCEPT ![s] = "Follower"]
                 /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                 /\ leader' = [leader EXCEPT ![s] = m.from]
                 /\ electionTimer' = [electionTimer EXCEPT ![s] \in ElectionTimeoutMin..ElectionTimeoutMax]
                 /\ IF logOk
                    THEN /\ LET newLog == Append(Head(log[s], m.prevLogIndex), m.entries)
                         \IN log' = [log EXCEPT ![s] = newLog]
                         /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], min(m.leaderCommit, LastLogIndex(newLog)))]
                         /\ LET resp == [ type |-> "MsgAppResp", from |-> s, to |-> m.from,
                                          term |-> currentTerm[s], reject |-> FALSE,
                                          index |-> LastLogIndex(newLog) ]
                         \IN network' = network' (+) Bagify({resp})
                         /\ UNCHANGED << votedFor, heartbeatTimer, nextIndex, matchIndex >>
                    ELSE /\ LET resp == [ type |-> "MsgAppResp", from |-> s, to |-> m.from,
                                          term |-> currentTerm[s], reject |-> TRUE, index |-> 0 ]
                         \IN network' = network' (+) Bagify({resp})
                         /\ UNCHANGED << votedFor, log, commitIndex, heartbeatTimer, nextIndex, matchIndex >>

\* A leader receives an AppendEntries response.
HandleAppendEntriesResponse(s) ==
    \E m \in BagToSet(network):
        /\ m.type = "MsgAppResp"
        /\ m.to = s
        /\ state[s] = "Leader"
        /\ m.term = currentTerm[s]
        /\ network' = network (-) Bagify({m})
        /\ IF m.reject
           THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = max(1, nextIndex[s][m.from] - 1)]]
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader,
                                electionTimer, heartbeatTimer, matchIndex >>
           ELSE /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![m.from] = m.index]]
                /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.index + 1]]
                /\ LET newCommitIndex ==
                        LET maxIdx == LastLogIndex(log[s])
                            possibleIs == {i \in commitIndex[s]+1..maxIdx:
                                            /\ log[s][i].term = currentTerm[s]
                                            /\ Cardinality({p \in Server: matchIndex'[s][p] >= i}) >= Quorum}
                        IN IF possibleIs = {} THEN commitIndex[s] ELSE Max(possibleIs)
                \IN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                /\ UNCHANGED << state, currentTerm, votedFor, log, leader,
                                electionTimer, heartbeatTimer >>

\* A message is dropped from the network.
DropMessage ==
    \E m \in BagToSet(network):
        /\ network' = network (-) Bagify({m})
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader,
                        electionTimer, heartbeatTimer, nextIndex, matchIndex >>

\* Universal term check: any node receiving a message with a higher term becomes a follower.
UpdateTerm(s) ==
    \E m \in BagToSet(network):
        /\ m.to = s
        /\ m.term > currentTerm[s]
        /\ StepDown(s, m.term)
        /\ UNCHANGED << log, commitIndex, network, heartbeatTimer, nextIndex, matchIndex >>

Next ==
    \/ \E s \in Server:
        \/ Tick(s)
        \/ TimeoutStartPreElection(s)
        \/ HandlePreVoteRequest(s)
        \/ HandlePreVoteResponse(s)
        \/ HandleVoteRequest(s)
        \/ HandleVoteResponse(s)
        \/ LeaderHeartbeat(s)
        \/ HandleProposal(s)
        \/ HandleFollowerProposal(s)
        \/ \E p \in Server: LeaderSendAppendEntries(s, p)
        \/ HandleAppendEntriesRequest(s)
        \/ HandleAppendEntriesResponse(s)
        \/ UpdateTerm(s)
    \/ \E cmd \in Command: ClientRequest(cmd)
    \/ DropMessage

Spec == Init /\ [][Next]_vars

=============================================================================
