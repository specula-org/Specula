---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Server, Key, Value, Client, NULL

VARIABLES state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, sm, network

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, sm, network>>

QuorumSize == Cardinality(Server) \div 2 + 1

None == CHOOSE none : none \notin Server

StateFollower == "Follower"
StateCandidate == "Candidate"
StateLeader == "Leader"

LogEntry == [term : Nat, cmd : [op: {"Put","Get"}, key: Key, val: Value, client: Client, cid: Nat]]

Init ==
    /\ state = [s \in Server |-> StateFollower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> None]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votes = [s \in Server |-> {}]
    /\ sm = [s \in Server |-> [k \in Key |-> NULL]]
    /\ network = {}

BecomeCandidate(s) ==
    /\ state[s] \in {StateFollower, StateCandidate}
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = StateCandidate]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votes' = [votes EXCEPT ![s] = {s}]
    /\ LET newTerm == currentTerm[s] + 1
           lastLogIndex == IF Len(log[s]) > 0 THEN Len(log[s]) ELSE 0
           lastLogTerm == IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE 0
       IN network' = network \cup {[type |-> "RequestVote", from |-> s, to |-> t, term |-> newTerm, candidateId |-> s, lastLogIndex |-> lastLogIndex, lastLogTerm |-> lastLogTerm] : t \in Server \ {s}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, sm>>

ReceiveRequestVote(s, m) ==
    /\ m \in network
    /\ m.type = "RequestVote"
    /\ m.to = s
    /\ LET lastLogTermFollower == IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE 0
           lastLogIndexFollower == Len(log[s])
           grant == 
               (votedFor[s] = None \/ votedFor[s] = m.candidateId)
               /\ ( m.lastLogTerm > lastLogTermFollower
                    \/ ( m.lastLogTerm = lastLogTermFollower
                         /\ m.lastLogIndex >= lastLogIndexFollower )
                  )
           newTerm == IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s]
        IN
           /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
           /\ state' = [state EXCEPT ![s] = IF m.term > currentTerm[s] THEN StateFollower ELSE state[s]]
           /\ votedFor' = [votedFor EXCEPT ![s] = IF grant THEN m.candidateId ELSE votedFor[s]]
           /\ network' = (network \ {m}) \cup {[type |-> "RequestVoteResponse", from |-> s, to |-> m.from, term |-> newTerm, voteGranted |-> grant]}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votes, sm>>

ReceiveRequestVoteResponse(s, m) ==
    /\ m \in network
    /\ m.type = "RequestVoteResponse"
    /\ m.to = s
    /\ state[s] = StateCandidate
    /\ m.term = currentTerm[s]
    /\ LET newVotes == IF m.voteGranted THEN votes[s] \cup {m.from} ELSE votes[s]
        IN
           /\ votes' = [votes EXCEPT ![s] = newVotes]
           /\ \/ /\ Cardinality(newVotes) >= QuorumSize
                 /\ state' = [state EXCEPT ![s] = StateLeader]
                 /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
                 /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
                 /\ network' = (network \ {m}) \cup {[type |-> "AppendEntries", from |-> s, to |-> t, term |-> currentTerm[s], prevLogIndex |-> Len(log[s]), prevLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[s]] : t \in Server \ {s}}
              \/ /\ Cardinality(newVotes) < QuorumSize
                 /\ UNCHANGED <<state, nextIndex, matchIndex>>
                 /\ network' = network \ {m}
    /\ UNCHANGED <<log, commitIndex, lastApplied, currentTerm, votedFor, sm>>

ReceiveClientRequest(s, m) ==
    /\ m \in network
    /\ m.type = "ClientRequest"
    /\ m.to = s
    /\ state[s] = StateLeader
    /\ LET newLogEntry == [term |-> currentTerm[s], cmd |-> [op |-> m.op, key |-> m.key, val |-> m.val, client |-> m.client, cid |-> m.cid]]
        newLog == log[s] \o <<newLogEntry>>
    IN
        /\ log' = [log EXCEPT ![s] = newLog]
        /\ matchIndex' = [matchIndex EXCEPT ![s][s] = Len(newLog)]
        /\ network' = network \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, votes, sm>>

SendAppendEntries(leader, follower) ==
    /\ state[leader] = StateLeader
    /\ LET prevLogIndex == nextIndex[leader][follower] - 1
        prevLogTerm == IF prevLogIndex > 0 THEN log[leader][prevLogIndex].term ELSE 0
        entries == IF nextIndex[leader][follower] <= Len(log[leader]) THEN SubSeq(log[leader], nextIndex[leader][follower], Len(log[leader])) ELSE <<>>
    IN
        /\ network' = network \cup {[type |-> "AppendEntries", from |-> leader, to |-> follower, term |-> currentTerm[leader], prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm, entries |-> entries, leaderCommit |-> commitIndex[leader]]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, sm>>

ReceiveAppendEntries(s, m) ==
    /\ m \in network
    /\ m.type = "AppendEntries"
    /\ m.to = s
    /\ LET newTerm == IF m.term > currentTerm[s] THEN m.term ELSE currentTerm[s]
        prevLogOk == 
            \/ m.prevLogIndex = 0
            \/ (m.prevLogIndex <= Len(log[s]) /\ log[s][m.prevLogIndex].term = m.prevLogTerm)
        IN
           /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
           /\ state' = [state EXCEPT ![s] = IF m.term > currentTerm[s] THEN StateFollower ELSE state[s]]
           /\ \/ /\ prevLogOk
                 /\ LET newLog == SubSeq(log[s], 1, m.prevLogIndex) \o m.entries
                    newCommitIndex == Min({m.leaderCommit, Len(newLog)})
                 IN
                    /\ log' = [log EXCEPT ![s] = newLog]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                    /\ network' = (network \ {m}) \cup {[type |-> "AppendEntriesResponse", from |-> s, to |-> m.from, term |-> newTerm, success |-> TRUE, lastIndex |-> Len(newLog), conflictIndex |-> 0, conflictTerm |-> 0]}
              \/ /\ ~prevLogOk
                 /\ LET conflictIndex == 
                        IF m.prevLogIndex > Len(log[s]) THEN Len(log[s]) + 1
                        ELSE CHOOSE i \in 1..m.prevLogIndex : 
                            \A j \in i..m.prevLogIndex : log[s][j].term = log[s][m.prevLogIndex].term
                    conflictTerm == IF m.prevLogIndex <= Len(log[s]) THEN log[s][m.prevLogIndex].term ELSE 0
                 IN
                    /\ UNCHANGED <<log, commitIndex>>
                    /\ network' = (network \ {m}) \cup {[type |-> "AppendEntriesResponse", from |-> s, to |-> m.from, term |-> newTerm, success |-> FALSE, lastIndex |-> 0, conflictIndex |-> conflictIndex, conflictTerm |-> conflictTerm]}
           /\ UNCHANGED <<votedFor, lastApplied, nextIndex, matchIndex, votes, sm>>

ReceiveAppendEntriesResponse(s, m) ==
    /\ m \in network
    /\ m.type = "AppendEntriesResponse"
    /\ m.to = s
    /\ state[s] = StateLeader
    /\ m.term = currentTerm[s]
    /\ \/ /\ m.success
          /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.lastIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.lastIndex]
          /\ LET possibleCommit == 
                CHOOSE N \in {commitIndex[s] + 1..Len(log[s])} : 
                    log[s][N].term = currentTerm[s] 
                    /\ Cardinality({t \in Server : matchIndex[s][t] >= N}) >= QuorumSize
             IN
                commitIndex' = [commitIndex EXCEPT ![s] = IF possibleCommit = 0 THEN commitIndex[s] ELSE possibleCommit]
          /\ network' = network \ {m}
       \/ /\ ~m.success
          /\ LET newNextIndex == 
                IF m.conflictTerm = 0 THEN m.conflictIndex
                ELSE LET maxIndexWithTerm == CHOOSE i \in 0..Len(log[s]) : 
                          \A j \in 1..Len(log[s]) : (j <= i => log[s][j].term <= m.conflictTerm) /\ (j > i => log[s][j].term > m.conflictTerm)
                     IN IF maxIndexWithTerm = 0 THEN m.conflictIndex ELSE maxIndexWithTerm + 1
             IN
                /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = newNextIndex]
                /\ UNCHANGED <<matchIndex, commitIndex>>
                /\ network' = network \ {m}
    /\ UNCHANGED <<log, lastApplied, currentTerm, votedFor, votes, sm>>

ApplyCommitted(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ LET idx == lastApplied[s] + 1
          cmd == log[s][idx].cmd
          newSM == IF cmd.op = "Put" THEN [sm[s] EXCEPT ![cmd.key] = cmd.val] ELSE sm[s]
        IN
           /\ lastApplied' = [lastApplied EXCEPT ![s] = idx]
           /\ sm' = [sm EXCEPT ![s] = newSM]
           /\ \/ /\ state[s] = StateLeader
                 /\ \/ /\ cmd.op = "Get"
                       /\ network' = network \cup {[type |-> "ClientResponse", from |-> s, to |-> cmd.client, result |-> [type |-> "Value", val |-> newSM[cmd.key], cid |-> cmd.cid]]}
                    \/ /\ cmd.op = "Put"
                       /\ network' = network \cup {[type |-> "ClientResponse", from |-> s, to |-> cmd.client, result |-> [type |-> "OK", val |-> cmd.val, cid |-> cmd.cid]]}
              \/ /\ state[s] # StateLeader
                 /\ UNCHANGED network
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes>>

SendHeartbeat(leader) ==
    /\ state[leader] = StateLeader
    /\ network' = network \cup {[type |-> "AppendEntries", from |-> leader, to |-> t, term |-> currentTerm[leader], prevLogIndex |-> Len(log[leader]), prevLogTerm |-> IF Len(log[leader]) > 0 THEN log[leader][Len(log[leader])].term ELSE 0, entries |-> <<>>, leaderCommit |-> commitIndex[leader]] : t \in Server \ {leader}}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, sm>>

BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = StateFollower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = None]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votes, sm, network>>

TypeInvariant ==
    /\ state \in [Server -> {StateFollower, StateCandidate, StateLeader}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {None}]
    /\ log \in [Server -> Seq(LogEntry)]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votes \in [Server -> SUBSET Server]
    /\ sm \in [Server -> [Key -> Value \cup {NULL}]]
    /\ \A s \in Server : commitIndex[s] <= Len(log[s])
    /\ \A s \in Server : lastApplied[s] <= commitIndex[s]

ElectionSafety == \A s1, s2 \in Server : 
    (state[s1] = StateLeader /\ state[s2] = StateLeader) => currentTerm[s1] # currentTerm[s2]

Next ==
    \/ \E s \in Server : BecomeCandidate(s)
    \/ \E m \in network : \E s \in Server : 
        \/ ReceiveRequestVote(s, m)
        \/ ReceiveRequestVoteResponse(s, m)
        \/ ReceiveAppendEntries(s, m)
        \/ ReceiveAppendEntriesResponse(s, m)
        \/ ReceiveClientRequest(s, m)
    \/ \E leader \in Server, follower \in Server \ {leader} : SendAppendEntries(leader, follower)
    \/ \E s \in Server : ApplyCommitted(s)
    \/ \E leader \in Server : SendHeartbeat(leader)
    \/ \E s \in Server : BecomeFollower(s, currentTerm[s] + 1)

Spec == Init /\ [][Next]_vars /\ TypeInvariant

====