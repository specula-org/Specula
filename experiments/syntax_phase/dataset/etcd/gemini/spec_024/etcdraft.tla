---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, Commands, Nil

ASSUME IsFiniteSet(Servers) /\ IsFiniteSet(Commands)
       /\ Cardinality(Servers) % 2 = 1
       /\ Nil \notin Servers

Quorum == (Cardinality(Servers) \div 2) + 1

(* Timers are modeled abstractly by non-determinism *)
CONSTANTS ElectionTimeout, HeartbeatTimeout

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    leader,
    votesGranted,
    preVotesGranted,
    nextIndex,
    matchIndex,
    messages

vars == <<state, currentTerm, votedFor, log, commitIndex, leader,
          votesGranted, preVotesGranted, nextIndex, matchIndex, messages>>

ServerStates == {"Follower", "PreCandidate", "Candidate", "Leader"}
MessageTypes == {"MsgHup", "MsgPreVote", "MsgVote", "MsgApp", "MsgProp",
                 "MsgPreVoteResp", "MsgVoteResp", "MsgAppResp"}

LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

IsUpToDate(candidateLastLogIndex, candidateLastLogTerm, myLog) ==
    LET myLastLogTerm == LastLogTerm(myLog)
        myLastLogIndex == LastLogIndex(myLog)
    IN \/ candidateLastLogTerm > myLastLogTerm
       \/ /\ candidateLastLogTerm = myLastLogTerm
          /\ candidateLastLogIndex >= myLastLogIndex

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ leader = [s \in Servers |-> Nil]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ preVotesGranted = [s \in Servers |-> {}]
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ messages = EmptyBag

(***************************************************************************)
(* Actions that generate internal events or client requests                *)
(***************************************************************************)

Timeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ messages' = messages (+) BagOf({[type |-> "MsgHup", to |-> s]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

ClientRequest(cmd) ==
    /\ cmd \in Commands
    /\ \E l \in Servers: state[l] = "Leader"
    /\ LET l == CHOOSE l \in Servers: state[l] = "Leader"
    /\ messages' = messages (+) BagOf({[type |-> "MsgProp", command |-> cmd, to |-> l]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

(***************************************************************************)
(* Message Handlers                                                        *)
(***************************************************************************)

HandleHup(s, m) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {s}]
    /\ messages' = (messages (-) BagOf({m})) (+) BagOf(
        {[type |-> "MsgPreVote", term |-> currentTerm[s] + 1, from |-> s, to |-> p,
          lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s])]
         : p \in Servers \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, nextIndex, matchIndex>>

HandlePreVoteRequest(s, m) ==
    /\ LET grantVote == /\ m.term > currentTerm[s]
                        /\ IsUpToDate(m.lastLogIndex, m.lastLogTerm, log[s])
    /\ messages' = (messages (-) BagOf({m})) (+)
        BagOf({[type |-> "MsgPreVoteResp", term |-> m.term, from |-> s, to |-> m.from,
          voteGranted |-> grantVote]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandlePreVoteResponse(s, m) ==
    /\ IF m.term > currentTerm[s] + 1
       THEN /\ BecomeFollower(s, m.term)
            /\ messages' = messages (-) BagOf({m})
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
       ELSE /\ state[s] = "PreCandidate"
            /\ m.term = currentTerm[s] + 1
            /\ LET newPreVotes == IF m.voteGranted THEN preVotesGranted[s] \cup {m.from} ELSE preVotesGranted[s]
            /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = newPreVotes]
            /\ IF Cardinality(newPreVotes) >= Quorum
               THEN (* Start real election *)
                    /\ state' = [state EXCEPT ![s] = "Candidate"]
                    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                    /\ votedFor' = [votedFor EXCEPT ![s] = s]
                    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                    /\ messages' = (messages (-) BagOf({m})) (+) BagOf(
                        {[type |-> "MsgVote", term |-> currentTerm[s] + 1, from |-> s, to |-> p,
                          lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s])]
                         : p \in Servers \ {s}})
                    /\ UNCHANGED <<log, commitIndex, leader, nextIndex, matchIndex>>
               ELSE /\ messages' = messages (-) BagOf({m})
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                                   votesGranted, nextIndex, matchIndex>>

HandleVoteRequest(s, m) ==
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = (messages (-) BagOf({m})) (+)
                BagOf({[type |-> "MsgVoteResp", term |-> currentTerm[s], from |-> s, to |-> m.from,
                  voteGranted |-> FALSE]})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>
       ELSE /\ LET grantVote == /\ m.term >= currentTerm[s]
                               /\ (votedFor[s] = Nil \/ votedFor[s] = m.from)
                               /\ IsUpToDate(m.lastLogIndex, m.lastLogTerm, log[s])
            /\ votedFor' = [votedFor EXCEPT ![s] = IF grantVote THEN m.from ELSE votedFor[s]]
            /\ messages' = (messages (-) BagOf({m})) (+)
                BagOf({[type |-> "MsgVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                  voteGranted |-> grantVote]})
            /\ IF m.term > currentTerm[s]
               THEN /\ BecomeFollower(s, m.term)
                    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
               ELSE UNCHANGED <<state, currentTerm, leader, votesGranted, preVotesGranted>>
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

HandleVoteResponse(s, m) ==
    /\ IF m.term > currentTerm[s]
       THEN /\ BecomeFollower(s, m.term)
            /\ messages' = messages (-) BagOf({m})
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
       ELSE /\ state[s] = "Candidate"
            /\ m.term = currentTerm[s]
            /\ LET newVotes == IF m.voteGranted THEN votesGranted[s] \cup {m.from} ELSE votesGranted[s]
            /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
            /\ IF Cardinality(newVotes) >= Quorum
               THEN (* Become Leader *)
                    /\ LET newLog == Append(log[s], [term |-> currentTerm[s], command |-> "NoOp"])
                    /\ state' = [state EXCEPT ![s] = "Leader"]
                    /\ leader' = [leader EXCEPT ![s] = s]
                    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(newLog) + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> IF p=s THEN LastLogIndex(newLog) ELSE 0]]
                    /\ log' = [log EXCEPT ![s] = newLog]
                    /\ messages' = (messages (-) BagOf({m})) (+) BagOf(
                        {[type |-> "MsgApp", term |-> currentTerm[s], from |-> s, to |-> p,
                          prevLogIndex |-> LastLogIndex(log[s]),
                          prevLogTerm |-> LastLogTerm(log[s]),
                          entries |-> << [term |-> currentTerm[s], command |-> "NoOp"] >>,
                          leaderCommit |-> commitIndex[s]]
                         : p \in Servers \ {s}})
                    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, preVotesGranted>>
               ELSE /\ messages' = messages (-) BagOf({m})
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                                   preVotesGranted, nextIndex, matchIndex>>

HandleProp(s, m) ==
    /\ IF state[s] = "Leader"
       THEN /\ LET newEntry == [term |-> currentTerm[s], command |-> m.command]
                 newLog == Append(log[s], newEntry)
            /\ log' = [log EXCEPT ![s] = newLog]
            /\ matchIndex' = [matchIndex EXCEPT ![s][s] = LastLogIndex(newLog)]
            /\ messages' = messages (-) BagOf({m})
            /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex>>
       ELSE (* Not leader, drop proposal *)
            /\ messages' = messages (-) BagOf({m})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>

LeaderSendHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ messages' = messages (+) BagOf(
        {[type |-> "MsgApp", term |-> currentTerm[s], from |-> s, to |-> p,
          prevLogIndex |-> LastLogIndex(log[s]),
          prevLogTerm |-> LastLogTerm(log[s]),
          entries |-> << >>,
          leaderCommit |-> commitIndex[s]]
         : p \in Servers \ {s}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

LeaderReplicateLog(s, p) ==
    /\ state[s] = "Leader"
    /\ p \in Servers \ {s}
    /\ LET pNextIndex == nextIndex[s][p]
    /\ pNextIndex <= LastLogIndex(log[s])
    /\ LET prevIdx == pNextIndex - 1
           prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
           newEntries == SubSeq(log[s], pNextIndex, LastLogIndex(log[s]))
    /\ messages' = messages (+) BagOf(
        {[type |-> "MsgApp", term |-> currentTerm[s], from |-> s, to |-> p,
          prevLogIndex |-> prevIdx,
          prevLogTerm |-> prevTerm,
          entries |-> newEntries,
          leaderCommit |-> commitIndex[s]]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandleAppendEntriesRequest(s, m) ==
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = (messages (-) BagOf({m})) (+)
                BagOf({[type |-> "MsgAppResp", term |-> currentTerm[s], from |-> s, to |-> m.from,
                  success |-> FALSE, matchIndex |-> 0]})
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>
       ELSE /\ LET logOk == \/ m.prevLogIndex = 0
                           \/ /\ m.prevLogIndex <= LastLogIndex(log[s])
                              /\ log[s][m.prevLogIndex].term = m.prevLogTerm
            /\ IF logOk
               THEN /\ LET newLog ==
                           LET existingEntries == SubSeq(log[s], 1, m.prevLogIndex)
                           IN existingEntries \o m.entries
                    /\ log' = [log EXCEPT ![s] = newLog]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] =
                        IF commitIndex[s] > m.leaderCommit THEN commitIndex[s] ELSE m.leaderCommit]
                    /\ messages' = (messages (-) BagOf({m})) (+)
                         BagOf({[type |-> "MsgAppResp", term |-> m.term, from |-> s, to |-> m.from,
                           success |-> TRUE, matchIndex |-> LastLogIndex(newLog)]})
               ELSE /\ messages' = (messages (-) BagOf({m})) (+)
                         BagOf({[type |-> "MsgAppResp", term |-> m.term, from |-> s, to |-> m.from,
                           success |-> FALSE, matchIndex |-> 0]})
                    /\ UNCHANGED <<log, commitIndex>>
            /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ leader' = [leader EXCEPT ![s] = m.from]
            /\ UNCHANGED <<votedFor, votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandleAppendEntriesResponse(s, m) ==
    /\ state[s] = "Leader"
    /\ IF m.term > currentTerm[s]
       THEN /\ BecomeFollower(s, m.term)
            /\ messages' = messages (-) BagOf({m})
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
       ELSE /\ IF m.term = currentTerm[s]
               THEN /\ IF m.success
                       THEN /\ LET newNext == [nextIndex[s] EXCEPT ![m.from] = m.matchIndex + 1]
                               LET newMatch == [matchIndex[s] EXCEPT ![m.from] = m.matchIndex, ![s] = LastLogIndex(log[s])]
                            /\ nextIndex' = [nextIndex EXCEPT ![s] = newNext]
                            /\ matchIndex' = [matchIndex EXCEPT ![s] = newMatch]
                            /\ LET CommittableIndices ==
                                   { N \in (commitIndex[s] + 1)..LastLogIndex(log[s]) |
                                       /\ log[s][N].term = currentTerm[s]
                                       /\ Cardinality({p \in Servers | newMatch[p] >= N}) >= Quorum }
                               newCommitIndex ==
                                   IF CommittableIndices = {}
                                   THEN commitIndex[s]
                                   ELSE Max(CommittableIndices)
                            /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = nextIndex[s][m.from] - 1]
                            /\ UNCHANGED <<matchIndex, commitIndex>>
                    /\ messages' = messages (-) BagOf({m})
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, leader,
                                   votesGranted, preVotesGranted>>
               ELSE (* Stale response, ignore *)
                    /\ messages' = messages (-) BagOf({m})
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

MessageStep ==
    \E m \in BagToSet(messages):
        LET s == m.to IN
        \/ (m.type = "MsgHup"         /\ HandleHup(s, m))
        \/ (m.type = "MsgPreVote"     /\ HandlePreVoteRequest(s, m))
        \/ (m.type = "MsgPreVoteResp" /\ HandlePreVoteResponse(s, m))
        \/ (m.type = "MsgVote"        /\ HandleVoteRequest(s, m))
        \/ (m.type = "MsgVoteResp"    /\ HandleVoteResponse(s, m))
        \/ (m.type = "MsgProp"        /\ HandleProp(s, m))
        \/ (m.type = "MsgApp"         /\ HandleAppendEntriesRequest(s, m))
        \/ (m.type = "MsgAppResp"     /\ HandleAppendEntriesResponse(s, m))

Next ==
    \/ \E s \in Servers: Timeout(s)
    \/ \E cmd \in Commands: ClientRequest(cmd)
    \/ \E s \in Servers: LeaderSendHeartbeat(s)
    \/ \E s \in Servers, p \in Servers: LeaderReplicateLog(s, p)
    \/ MessageStep

Spec == Init /\ [][Next]_vars

====
