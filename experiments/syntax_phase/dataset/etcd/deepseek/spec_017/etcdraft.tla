```tla
---- MODULE etcdraft ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes,  \* Set of nodes in the cluster
          QuorumSize,  \* Majority quorum size (|Nodes|/2 + 1)
          Keys,    \* Set of possible keys
          Values,  \* Set of possible values
          None,    \* Special value for unset states
          NULL     \* Special value for unset values

Min(a,b) == IF a < b THEN a ELSE b

VARIABLES 
    state,        \* [node -> {"Follower", "Candidate", "Leader", "PreCandidate"}]
    currentTerm,  \* [node -> Nat] Current term number
    votedFor,     \* [node -> Node \cup {None}] Voted candidate in current term
    log,          \* [node -> Seq([term: Nat, op: Op])] Log entries
    commitIndex,  \* [node -> Nat] Highest committed log index
    lastApplied,  \* [node -> Nat] Highest applied log index
    nextIndex,    \* [node -> [Node -> Nat]] Leader's next send index per follower
    matchIndex,   \* [node -> [Node -> Nat]] Leader's highest replicated index per follower
    votes,        \* [node -> SUBSET Node] Granted votes in current election
    leaderId,     \* [node -> Node \cup {None}] Current leader
    kvStore,      \* [node -> [Keys -> Values \cup {NULL}]] Key-value state
    msgs,         \* Set of in-flight messages
    nextOp,       \* Next client operation to process (or NULL)
    electionTimer \* [node -> {"normal", "expired"}] Election timeout state

OpType == {"Put", "Delete", "Get"}
Op == [type: {"Put"}, key: Keys, value: Values] \cup [type: {"Delete","Get"}, key: Keys]

Message == [ 
    type: {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse"},
    from: Node,
    to: Node,
    term: Nat,
    \* RequestVote fields
    lastLogIndex: Nat,
    lastLogTerm: Nat,
    \* RequestVoteResponse fields
    voteGranted: BOOLEAN,
    \* AppendEntries fields
    prevLogIndex: Nat,
    prevLogTerm: Nat,
    entries: Seq([term: Nat, op: Op]),
    leaderCommit: Nat,
    \* AppendEntriesResponse fields
    success: BOOLEAN,
    matchIndex: Nat
]

\* Helper functions
IsLeader(n) == state[n] = "Leader"
LogTerm(log, idx) == IF idx > 0 AND idx <= Len(log) THEN log[idx].term ELSE 0
LastLogIndex(n) == Len(log[n])
LastLogTerm(n) == LogTerm(log[n], LastLogIndex(n))
LogUpToDate(candidateLastIndex, candidateLastTerm, n) ==
    candidateLastTerm > LastLogTerm(n) \/
    (candidateLastTerm = LastLogTerm(n) /\ candidateLastIndex >= LastLogIndex(n))
CanGrantVote(n, candidate, candTerm, candLastIndex, candLastTerm) ==
    (votedFor[n] = None \/ votedFor[n] = candidate) /\
    LogUpToDate(candLastIndex, candLastTerm, n)
MajorityGranted(grantedSet) == Cardinality(grantedSet) >= QuorumSize

\* Initial state
Init == 
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votes = [n \in Nodes |-> {}]
    /\ leaderId = [n \in Nodes |-> None]
    /\ kvStore = [n \in Nodes |-> [k \in Keys |-> NULL]]
    /\ msgs = {}
    /\ nextOp = NULL
    /\ electionTimer = [n \in Nodes |-> "normal"]

\* Timeout triggers election
Timeout(n) ==
    /\ electionTimer[n] = "expired"
    /\ electionTimer' = [electionTimer EXCEPT ![n] = "normal"]
    /\ \/ /\ state[n] = "Follower"
          /\ state' = [state EXCEPT ![n] = "PreCandidate"]
          /\ votes' = [votes EXCEPT ![n] = {}]
          /\ msgs' = msgs \cup 
                {[type |-> "RequestVote", from |-> n, to |-> m, term |-> currentTerm[n],
                  lastLogIndex |-> LastLogIndex(n), lastLogTerm |-> LastLogTerm(n),
                  voteGranted |-> FALSE, prevLogIndex |-> 0, prevLogTerm |-> 0, 
                  entries |-> <<>>, leaderCommit |-> 0, success |-> FALSE, matchIndex |-> 0] 
                  : m \in Nodes \ {n}}
       \/ /\ state[n] = "Candidate" \/ state[n] = "PreCandidate"
          /\ state' = [state EXCEPT ![n] = "Candidate"]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
          /\ votedFor' = [votedFor EXCEPT ![n] = n]
          /\ votes' = [votes EXCEPT ![n] = {n}]
          /\ msgs' = msgs \cup 
                {[type |-> "RequestVote", from |-> n, to |-> m, term |-> currentTerm[n] + 1,
                  lastLogIndex |-> LastLogIndex(n), lastLogTerm |-> LastLogTerm(n),
                  voteGranted |-> FALSE, prevLogIndex |-> 0, prevLogTerm |-> 0, 
                  entries |-> <<>>, leaderCommit |-> 0, success |-> FALSE, matchIndex |-> 0] 
                  : m \in Nodes \ {n}}

\* Handle incoming RequestVote message
HandleRequestVote(n, msg) ==
    LET votedFor_next == IF msg.term > currentTerm[n] THEN None ELSE votedFor[n]
        grant == (votedFor_next = None \/ votedFor_next = msg.from) /\
                 LogUpToDate(msg.lastLogIndex, msg.lastLogTerm, n)
    IN
    IF msg.term < currentTerm[n] THEN
        /\ msgs' = msgs \cup 
              {[type |-> "RequestVoteResponse", from |-> n, to |-> msg.from, term |-> currentTerm[n],
                voteGranted |-> FALSE, lastLogIndex |-> 0, lastLogTerm |-> 0, 
                prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, 
                leaderCommit |-> 0, success |-> FALSE, matchIndex |-> 0]}
        /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, electionTimer>>
    ELSE
        /\ \/ /\ msg.term > currentTerm[n]
              /\ state' = [state EXCEPT ![n] = "Follower"]
              /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
              /\ leaderId' = [leaderId EXCEPT ![n] = None]
           \/ UNCHANGED <<state, currentTerm, leaderId>>
        /\ votedFor' = [votedFor EXCEPT ![n] = IF grant THEN msg.from ELSE votedFor_next]
        /\ electionTimer' = [electionTimer EXCEPT ![n] = "normal"]
        /\ msgs' = msgs \cup 
              {[type |-> "RequestVoteResponse", from |-> n, to |-> msg.from, term |-> currentTerm'[n],
                voteGranted |-> grant, lastLogIndex |-> 0, lastLogTerm |-> 0, 
                prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, 
                leaderCommit |-> 0, success |-> FALSE, matchIndex |-> 0]}

\* Handle RequestVoteResponse
HandleRequestVoteResponse(n, msg) ==
    IF msg.term < currentTerm[n] THEN 
        UNCHANGED <<state, currentTerm, votes, leaderId, nextIndex, matchIndex>>
    ELSE
        /\ votes' = [votes EXCEPT ![n] = @ \cup {msg.from}]
        /\ IF msg.voteGranted THEN
              LET newVotes = votes[n] \cup {msg.from}
              IN
              /\ \/ /\ MajorityGranted(newVotes)
                    /\ state' = [state EXCEPT ![n] = "Leader"]
                    /\ leaderId' = [leaderId EXCEPT ![n] = n]
                    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> LastLogIndex(n) + 1]]
                    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
                    /\ msgs' = msgs \cup 
                          {[type |-> "AppendEntries", from |-> n, to |-> f, term |-> currentTerm[n],
                            prevLogIndex |-> LastLogIndex(n), prevLogTerm |-> LastLogTerm(n),
                            entries |-> <<>>, leaderCommit |-> commitIndex[n],
                            lastLogIndex |-> 0, lastLogTerm |-> 0, voteGranted |-> FALSE, 
                            success |-> FALSE, matchIndex |-> 0] : f \in Nodes \ {n}}
                 \/ UNCHANGED <<state, leaderId, nextIndex, matchIndex>>
           ELSE
              UNCHANGED <<state, leaderId, nextIndex, matchIndex>>
        /\ UNCHANGED <<currentTerm>>

\* Leader appends client operation to log
LeaderAppend(n, op) ==
    LET newEntry == [term |-> currentTerm[n], op |-> op]
        newLog == Append(log[n], newEntry)
    IN
    /\ nextOp' = NULL
    /\ log' = [log EXCEPT ![n] = newLog]
    /\ nextIndex' = [nextIndex EXCEPT ![n][n] = Len(newLog) + 1]
    /\ matchIndex' = [matchIndex EXCEPT ![n][n] = Len(newLog)]
    /\ msgs' = msgs \cup 
          {[type |-> "AppendEntries", from |-> n, to |-> f, term |-> currentTerm[n],
            prevLogIndex |-> nextIndex[n][f] - 1,
            prevLogTerm |-> LogTerm(log[n], nextIndex[n][f] - 1),
            entries |-> SubSeq(log[n], nextIndex[n][f], Len(log[n])),
            leaderCommit |-> commitIndex[n],
            lastLogIndex |-> 0, lastLogTerm |-> 0, voteGranted |-> FALSE, 
            success |-> FALSE, matchIndex |-> 0] : f \in Nodes \ {n}}

\* Handle AppendEntries (heartbeat when entries empty)
HandleAppendEntries(n, msg) ==
    IF msg.term < currentTerm[n] THEN
        /\ msgs' = msgs \cup 
              {[type |-> "AppendEntriesResponse", from |-> n, to |-> msg.from, 
                term |-> currentTerm[n], success |-> FALSE, matchIndex |-> LastLogIndex(n),
                lastLogIndex |-> 0, lastLogTerm |-> 0, voteGranted |-> FALSE, 
                prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, 
                leaderCommit |-> 0]}
        /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, electionTimer, log, commitIndex>>
    ELSE
        /\ electionTimer' = [electionTimer EXCEPT ![n] = "normal"]
        /\ \/ /\ msg.term > currentTerm[n]
              /\ state' = [state EXCEPT ![n] = "Follower"]
              /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
              /\ votedFor' = [votedFor EXCEPT ![n] = None]
              /\ leaderId' = [leaderId EXCEPT ![n] = msg.from]
           \/ UNCHANGED <<state, currentTerm, votedFor, leaderId>>
        /\ IF msg.prevLogIndex > 0 /\ 
              (msg.prevLogIndex > LastLogIndex(n) \/ 
               LogTerm(log[n], msg.prevLogIndex) # msg.prevLogTerm) 
           THEN
               /\ msgs' = msgs \cup 
                     {[type |-> "AppendEntriesResponse", from |-> n, to |-> msg.from, 
                       term |-> currentTerm'[n], success |-> FALSE, matchIndex |-> LastLogIndex(n),
                       lastLogIndex |-> 0, lastLogTerm |-> 0, voteGranted |-> FALSE, 
                       prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, 
                       leaderCommit |-> 0]}
               /\ UNCHANGED <<log, commitIndex>>
        ELSE
               LET newLog == 
                    IF msg.entries # <<>> THEN 
                        SubSeq(log[n], 1, msg.prevLogIndex) \o msg.entries 
                    ELSE 
                        log[n]
               IN
               /\ log' = [log EXCEPT ![n] = newLog]
               /\ commitIndex' = [commitIndex EXCEPT ![n] = 
                    IF msg.leaderCommit > commitIndex[n] THEN 
                        Min(msg.leaderCommit, Len(newLog)) 
                    ELSE 
                        commitIndex[n]]
               /\ msgs' = msgs \cup 
                     {[type |-> "AppendEntriesResponse", from |-> n, to |-> msg.from, 
                       term |-> currentTerm'[n], success |-> TRUE, matchIndex |-> Len(newLog),
                       lastLogIndex |-> 0, lastLogTerm |-> 0, voteGranted |-> FALSE, 
                       prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, 
                       leaderCommit |-> 0]}

\* Handle AppendEntriesResponse (leader only)
HandleAppendEntriesResponse(n, msg) ==
    IF msg.term > currentTerm[n] THEN
        /\ state' = [state EXCEPT ![n] = "Follower"]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
        /\ votedFor' = [votedFor EXCEPT ![n] = None]
        /\ leaderId' = [leaderId EXCEPT ![n] = None]
        /\ UNCHANGED <<nextIndex, matchIndex, commitIndex>>
    ELSE
        /\ IF msg.success THEN
               /\ nextIndex' = [nextIndex EXCEPT ![n][msg.from] = msg.matchIndex + 1]
               /\ matchIndex' = [matchIndex EXCEPT ![n][msg.from] = msg.matchIndex]
               /\ LET S == { i \in 1..Len(log[n]) : 
                            log[n][i].term = currentTerm[n] /\
                            Cardinality({m \in Nodes : matchIndex[n][m] >= i}) >= QuorumSize }
                  IN
                  LET newCommit == IF S # {} THEN Max(S) ELSE 0
                  IN
                  IF newCommit > commitIndex[n] THEN
                      commitIndex' = [commitIndex EXCEPT ![n] = newCommit]
                  ELSE
                      UNCHANGED commitIndex
           ELSE
               /\ nextIndex' = [nextIndex EXCEPT ![n][msg.from] = nextIndex[n][msg.from] - 1]
               /\ UNCHANGED matchIndex
        /\ UNCHANGED <<state, currentTerm, votedFor, leaderId>>

\* Apply committed log entries to state machine
ApplyLogEntry(n) ==
    LET idx == lastApplied[n] + 1
        entry == log[n][idx]
    IN
    idx <= commitIndex[n] /\ idx <= Len(log[n])
    /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
    /\ IF entry.op.type = "Put" THEN
           kvStore' = [kvStore EXCEPT ![n][entry.op.key] = entry.op.value]
       ELSE IF entry.op.type = "Delete" THEN
           kvStore' = [kvStore EXCEPT ![n][entry.op.key] = NULL]
       ELSE \* "Get" - no state change
           UNCHANGED kvStore
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, leaderId, msgs, nextOp, electionTimer>>

\* Non-deterministically expire election timer
ElectionTimerExpire(n) ==
    electionTimer[n] = "normal"
    /\ electionTimer' = [electionTimer EXCEPT ![n] = "expired"]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
                  nextIndex, matchIndex, votes, leaderId, kvStore, msgs, nextOp>>

\* Non-deterministically generate client request
NewClientRequest(op) ==
    nextOp = NULL
    /\ nextOp' = op
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
                  nextIndex, matchIndex, votes, leaderId, kvStore, msgs, electionTimer>>

\* Next-state relation
Next == 
    \/ \E n \in Nodes : ElectionTimerExpire(n)
    \/ \E n \in Nodes : Timeout(n)
    \/ \E msg \in msgs : 
           \E n \in Nodes : 
                  /\ msg.to = n
                  /\ \/ (msg.type = "RequestVote") /\ HandleRequestVote(n, msg)
                     \/ (msg.type = "RequestVoteResponse") /\ HandleRequestVoteResponse(n, msg)
                     \/ (msg.type = "AppendEntries") /\ HandleAppendEntries(n, msg)
                     \/ (msg.type = "AppendEntriesResponse") /\ IsLeader(n) /\ HandleAppendEntriesResponse(n, msg)
           /\ msgs' = msgs \ {msg}
    \/ \E n \in Nodes : 
          /\ IsLeader(n) 
          /\ nextOp # NULL 
          /\ LeaderAppend(n, nextOp)
    \/ \E n \in Nodes : ApplyLogEntry(n)
    \/ \E op \in Op : NewClientRequest(op)

\* Safety properties
TypeOK == 
    /\ state \in [Nodes -> {"Follower", "Candidate", "Leader", "PreCandidate"}]
    /\ currentTerm \in [Nodes -> Nat]
    /\ votedFor \in [Nodes -> (Nodes \cup {None})]
    /\ log \in [Nodes -> Seq([term: Nat, op: Op])]
    /\ commitIndex \in [Nodes -> Nat]
    /\ lastApplied \in [Nodes -> Nat]
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ votes \in [Nodes -> SUBSET Nodes]
    /\ leaderId \in [Nodes -> (Nodes \cup {None})]
    /\ kvStore \in [Nodes -> [Keys -> (Values \cup {NULL})]]
    /\ msgs \subseteq [type: {"RequestVote","RequestVoteResponse","AppendEntries","AppendEntriesResponse"},
                      from: Nodes, to: Nodes, term: Nat, 
                      lastLogIndex: Nat, lastLogTerm: Nat, voteGranted: BOOLEAN,
                      prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq([term: Nat, op: Op]), 
                      leaderCommit: Nat, success: BOOLEAN, matchIndex: Nat]
    /\ nextOp \in Op \cup {NULL}
    /\ electionTimer \in [Nodes -> {"normal", "expired"}]

\* At most one leader per term
OneLeaderPerTerm ==
    \A n1, n2 \in Nodes: 
        (state[n1] = "Leader" /\ state[n2] = "Leader" /\ n1 # n2) 
        => currentTerm[n1] # currentTerm[n2]

\* Committed entries are same across nodes
CommittedAgreement ==
    \A n1, n2 \in Nodes, idx \in 1..Min(commitIndex[n1], commitIndex[n2]) : 
        idx <= Len(log[n1]) /\ idx <= Len(log[n2]) => log[n1][idx] = log[n2][idx]

\* State machine safety
StateMachineSafety ==
    \A n1, n2 \in Nodes, idx \in 1..Min(lastApplied[n1], lastApplied[n2]) : 
        idx <= Len(log[n1]) /\ idx <= Len(log[n2]) /\ log[n1][idx] = log[n2][idx] => 
            kvStore[n1][log[n1][idx].op.key] = kvStore[n2][log[n2][idx].op.key]

\* Term invariant
TermInvariant ==
    \A n \in Nodes : 
        commitIndex[n] <= LastLogIndex(n) /\ lastApplied[n] <= commitIndex[n]

Invariants == 
    /\ TypeOK
    /\ OneLeaderPerTerm
    /\ CommittedAgreement
    /\ StateMachineSafety
    /\ TermInvariant

\* Temporal properties
Termination == <>(\E n \in Nodes: state[n] = "Leader")
Liveness == \A op \in Op : <>( \E n \in Nodes: lastApplied[n] > 0 /\ log[n][lastApplied[n]].op = op)

====================================================================
```