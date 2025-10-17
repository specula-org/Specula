---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, Commands, Nil

ASSUME /\ TypeOK == IsFiniteSet(Servers) /\ IsFiniteSet(Commands)
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

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]

HandleHigherTerm(s, m) ==
    IF m.term > currentTerm[s]
    THEN /\ BecomeFollower(s, m.term)
         /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages>>
    ELSE UNCHANGED vars

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
    /\ messages' = BagUnion(messages, {[type |-> "MsgHup", to |-> s]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

ClientRequest(cmd) ==
    /\ cmd \in Commands
    /\ \E l \in Servers: state[l] = "Leader"
    /\ messages' = BagUnion(messages, {[type |-> "MsgProp", command |-> cmd, to |-> CHOOSE l \in Servers: state[l] = "Leader"]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

(***************************************************************************)
(* Message Handlers                                                        *)
(***************************************************************************)

HandleHup(s) ==
    /\ \E m \in BagToSet(messages): /\ m.type = "MsgHup" /\ m.to = s
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {s}]
    /\ messages' = (messages \ {m}) (+) BagUnion({},
        {[type |-> "MsgPreVote", term |-> currentTerm[s] + 1, from |-> s, to |-> p,
          lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s])]
         : p \in Servers \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, nextIndex, matchIndex>>

HandlePreVoteRequest(s, m) ==
    /\ m.type = "MsgPreVote"
    /\ m.to = s
    /\ LET myLastLogIndex == LastLogIndex(log[s])
           myLastLogTerm == LastLogTerm(log[s])
           grantVote == /\ m.term > currentTerm[s]
                        /\ IsUpToDate(m.lastLogIndex, m.lastLogTerm, log[s])
    /\ messages' = (messages \ {m}) (+)
        {[type |-> "MsgPreVoteResp", term |-> m.term, from |-> s, to |-> m.from,
          voteGranted |-> grantVote]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandlePreVoteResponse(s, m) ==
    /\ m.type = "MsgPreVoteResp"
    /\ m.to = s
    /\ state[s] = "PreCandidate"
    /\ m.term = currentTerm[s] + 1
    /\ LET newPreVotes == IF m.voteGranted THEN preVotesGranted[s] \cup {m.from} ELSE preVotesGranted[s]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = newPreVotes]
    /\ IF Cardinality(newPreVotes) >= Quorum
       THEN (* Start real election *)
            /\ state' = [state EXCEPT ![s] = "Candidate"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
            /\ votedFor' = [votedFor EXCEPT ![s] = s]
            /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
            /\ messages' = (messages \ {m}) (+) BagUnion({},
                {[type |-> "MsgVote", term |-> currentTerm[s] + 1, from |-> s, to |-> p,
                  lastLogIndex |-> LastLogIndex(log[s]), lastLogTerm |-> LastLogTerm(log[s])]
                 : p \in Servers \ {s}})
            /\ UNCHANGED <<log, commitIndex, leader, nextIndex, matchIndex>>
       ELSE /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, nextIndex, matchIndex>>

HandleVoteRequest(s, m) ==
    /\ m.type = "MsgVote"
    /\ m.to = s
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = (messages \ {m}) (+)
                {[type |-> "MsgVoteResp", term |-> currentTerm[s], from |-> s, to |-> m.from,
                  voteGranted |-> FALSE]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>
       ELSE /\ LET grantVote == /\ (votedFor[s] = Nil \/ votedFor[s] = m.from)
                               /\ IsUpToDate(m.lastLogIndex, m.lastLogTerm, log[s])
            /\ votedFor' = [votedFor EXCEPT ![s] = IF grantVote THEN m.from ELSE votedFor[s]]
            /\ messages' = (messages \ {m}) (+)
                {[type |-> "MsgVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                  voteGranted |-> grantVote]}
            /\ IF m.term > currentTerm[s]
               THEN /\ state' = [state EXCEPT ![s] = "Follower"]
                    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                    /\ leader' = [leader EXCEPT ![s] = Nil]
               ELSE UNCHANGED <<state, currentTerm, leader>>
            /\ UNCHANGED <<log, commitIndex, votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandleVoteResponse(s, m) ==
    /\ m.type = "MsgVoteResp"
    /\ m.to = s
    /\ state[s] = "Candidate"
    /\ m.term = currentTerm[s]
    /\ LET newVotes == IF m.voteGranted THEN votesGranted[s] \cup {m.from} ELSE votesGranted[s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
    /\ IF Cardinality(newVotes) >= Quorum
       THEN (* Become Leader *)
            /\ state' = [state EXCEPT ![s] = "Leader"]
            /\ leader' = [leader EXCEPT ![p] = IF p=s THEN s ELSE leader[p] ]
            /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(log[s]) + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
            /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], command |-> "NoOp"])]
            /\ messages' = (messages \ {m}) (+) BagUnion({},
                {[type |-> "MsgApp", term |-> currentTerm[s], from |-> s, to |-> p,
                  prevLogIndex |-> LastLogIndex(log[s]),
                  prevLogTerm |-> LastLogTerm(log[s]),
                  entries |-> << [term |-> currentTerm[s], command |-> "NoOp"] >>,
                  leaderCommit |-> commitIndex[s]]
                 : p \in Servers \ {s}})
            /\ UNCHANGED <<currentTerm, votedFor, commitIndex, preVotesGranted>>
       ELSE /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           preVotesGranted, nextIndex, matchIndex>>

HandleProp(s, m) ==
    /\ m.type = "MsgProp"
    /\ m.to = s
    /\ IF state[s] = "Leader"
       THEN /\ LET newEntry == [term |-> currentTerm[s], command |-> m.command]
            /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>
       ELSE (* Follower drops proposal *)
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>

LeaderSendHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ messages' = BagUnion(messages,
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
    /\ pNextIndex <= LastLogIndex(log[s]) + 1
    /\ LET prevIdx == pNextIndex - 1
           prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
           newEntries == SubSeq(log[s], pNextIndex, LastLogIndex(log[s]))
    /\ messages' = BagUnion(messages,
        {[type |-> "MsgApp", term |-> currentTerm[s], from |-> s, to |-> p,
          prevLogIndex |-> prevIdx,
          prevLogTerm |-> prevTerm,
          entries |-> newEntries,
          leaderCommit |-> commitIndex[s]]})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                   votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandleAppendEntriesRequest(s, m) ==
    /\ m.type = "MsgApp"
    /\ m.to = s
    /\ IF m.term < currentTerm[s]
       THEN /\ messages' = (messages \ {m}) (+)
                {[type |-> "MsgAppResp", term |-> currentTerm[s], from |-> s, to |-> m.from,
                  success |-> FALSE, matchIndex |-> 0]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>
       ELSE /\ LET logOk == \/ m.prevLogIndex = 0
                           \/ /\ m.prevLogIndex <= LastLogIndex(log[s])
                              /\ log[s][m.prevLogIndex].term = m.prevLogTerm
            /\ IF logOk
               THEN /\ LET newLog ==
                           LET existingEntries == SubSeq(log[s], 1, m.prevLogIndex)
                           IN AppendSeq(existingEntries, m.entries)
                    /\ log' = [log EXCEPT ![s] = newLog]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], m.leaderCommit)]
                    /\ messages' = (messages \ {m}) (+)
                         {[type |-> "MsgAppResp", term |-> currentTerm[s], from |-> s, to |-> m.from,
                           success |-> TRUE, matchIndex |-> LastLogIndex(newLog)]}
               ELSE /\ messages' = (messages \ {m}) (+)
                         {[type |-> "MsgAppResp", term |-> currentTerm[s], from |-> s, to |-> m.from,
                           success |-> FALSE, matchIndex |-> 0]}
                    /\ UNCHANGED <<log, commitIndex>>
            /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ leader' = [leader EXCEPT ![s] = m.from]
            /\ UNCHANGED <<votedFor, votesGranted, preVotesGranted, nextIndex, matchIndex>>

HandleAppendEntriesResponse(s, m) ==
    /\ m.type = "MsgAppResp"
    /\ m.to = s
    /\ state[s] = "Leader"
    /\ IF m.term = currentTerm[s]
       THEN /\ IF m.success
               THEN /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.matchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.matchIndex]
                    /\ LET newCommitIndex ==
                           CHOOSE N \in commitIndex[s]..LastLogIndex(log[s]):
                               /\ N > commitIndex[s]
                               /\ log[s][N].term = currentTerm[s]
                               /\ Cardinality({p \in Servers | matchIndex'[s][p] >= N}) >= Quorum
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = nextIndex[s][m.from] - 1]
                    /\ UNCHANGED <<matchIndex, commitIndex>>
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, leader,
                           votesGranted, preVotesGranted>>
       ELSE /\ messages' = messages \ {m}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader,
                           votesGranted, preVotesGranted, nextIndex, matchIndex>>

(* A server that receives a message with a higher term becomes a follower *)
StepDown(s, m) ==
    /\ m.to = s
    /\ m.term > currentTerm[s]
    /\ BecomeFollower(s, m.term)
    /\ messages' = messages
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

Receive(m) ==
    \/ \E s \in Servers:
        /\ m.to = s
        /\ m.term > currentTerm[s]
        /\ StepDown(s, m)
    \/ \E s \in Servers:
        /\ m.to = s
        /\ m.term <= currentTerm[s]
        /\ \/ HandlePreVoteRequest(s, m)
           \/ HandlePreVoteResponse(s, m)
           \/ HandleVoteRequest(s, m)
           \/ HandleVoteResponse(s, m)
           \/ HandleProp(s, m)
           \/ HandleAppendEntriesRequest(s, m)
           \/ HandleAppendEntriesResponse(s, m)
           \/ HandleHup(s)

Next ==
    \/ \E s \in Servers: Timeout(s)
    \/ \E cmd \in Commands: ClientRequest(cmd)
    \/ \E s \in Servers: LeaderSendHeartbeat(s)
    \/ \E s, p \in Servers: LeaderReplicateLog(s, p)
    \/ \E m \in BagToSet(messages): Receive(m)

Spec == Init /\ [][Next]_vars

====