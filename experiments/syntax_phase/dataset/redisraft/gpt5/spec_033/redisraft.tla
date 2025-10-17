---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NODES,
    INIT_VOTERS,
    ELECTION_TIMEOUT

Nil == CHOOSE x : x \notin NODES

States == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}

EntryTypes == {"NOOP", "NORMAL", "ADD_NODE", "ADD_NONVOTING_NODE", "REMOVE_NODE"}

Entry(e) == /\ e \in [term: Nat, etype: EntryTypes, node: NODES \cup {Nil}, cmd: STRING \cup Nat \cup {Nil}]
               /\ e.term \in Nat
               /\ e.etype \in EntryTypes

MessageTypes == {"RVREQ","RVRSP","AEREQ","AERSP"}

RVReq(msg) ==
    /\ msg \in [type: {"RVREQ"},
                from: NODES, to: NODES,
                prevote: BOOLEAN, term: Nat, candidate: NODES,
                lastIndex: Nat, lastTerm: Nat]

RVRsp(msg) ==
    /\ msg \in [type: {"RVRSP"},
                from: NODES, to: NODES,
                prevote: BOOLEAN, requestTerm: Nat, term: Nat,
                voteGranted: BOOLEAN]

AEReq(msg) ==
    /\ msg \in [type: {"AEREQ"},
                from: NODES, to: NODES,
                term: Nat, leader: NODES,
                prevLogIndex: Nat, prevLogTerm: Nat,
                entries: Seq([term: Nat, etype: EntryTypes, node: NODES \cup {Nil}, cmd: STRING \cup Nat \cup {Nil}]),
                leaderCommit: Nat]

AERsp(msg) ==
    /\ msg \in [type: {"AERSP"},
                from: NODES, to: NODES,
                term: Nat, success: BOOLEAN, matchIndex: Nat]

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    snapshotLastIndex,
    snapshotLastTerm,
    electionTimeoutRand,
    timeoutElapsed,
    leaderId,
    nextIndex,
    matchIndex,
    msgs,
    members,
    voters,
    prevotes,
    votes,
    snapshotInProgress,
    nextSnapshotIndex,
    nextSnapshotTerm

TypeOK ==
    /\ state \in [NODES -> States]
    /\ currentTerm \in [NODES -> Nat]
    /\ votedFor \in [NODES -> (NODES \cup {Nil})]
    /\ log \in [NODES -> Seq([term: Nat, etype: EntryTypes, node: NODES \cup {Nil}, cmd: STRING \cup Nat \cup {Nil}])]
    /\ commitIndex \in [NODES -> Nat]
    /\ lastApplied \in [NODES -> Nat]
    /\ snapshotLastIndex \in [NODES -> Nat]
    /\ snapshotLastTerm \in [NODES -> Nat]
    /\ electionTimeoutRand \in [NODES -> Nat]
    /\ timeoutElapsed \in [NODES -> Nat]
    /\ leaderId \in [NODES -> (NODES \cup {Nil})]
    /\ nextIndex \in [NODES -> [NODES -> Nat]]
    /\ matchIndex \in [NODES -> [NODES -> Nat]]
    /\ msgs \subseteq SUBSET (
            {m \in [type: MessageTypes, from: NODES, to: NODES] : TRUE}
        )
    /\ members \in [NODES -> SUBSET NODES]
    /\ voters \in [NODES -> SUBSET NODES]
    /\ \A n \in NODES : voters[n] \subseteq members[n]
    /\ prevotes \in [NODES -> SUBSET NODES]
    /\ votes \in [NODES -> SUBSET NODES]
    /\ snapshotInProgress \in [NODES -> BOOLEAN]
    /\ nextSnapshotIndex \in [NODES -> Nat]
    /\ nextSnapshotTerm \in [NODES -> Nat]

RandRange == { t \in Nat : t >= ELECTION_TIMEOUT /\ t < 2 * ELECTION_TIMEOUT }

Init ==
    /\ state = [n \in NODES |-> "FOLLOWER"]
    /\ currentTerm = [n \in NODES |-> 0]
    /\ votedFor = [n \in NODES |-> Nil]
    /\ log = [n \in NODES |-> <<>>]
    /\ commitIndex = [n \in NODES |-> 0]
    /\ lastApplied = [n \in NODES |-> 0]
    /\ snapshotLastIndex = [n \in NODES |-> 0]
    /\ snapshotLastTerm = [n \in NODES |-> 0]
    /\ electionTimeoutRand \in [NODES -> RandRange]
    /\ timeoutElapsed = [n \in NODES |-> 0]
    /\ leaderId = [n \in NODES |-> Nil]
    /\ nextIndex = [i \in NODES |-> [j \in NODES |-> 1]]
    /\ matchIndex = [i \in NODES |-> [j \in NODES |-> 0]]
    /\ msgs = {}
    /\ members = [n \in NODES |-> NODES]
    /\ voters = [n \in NODES |-> INIT_VOTERS]
    /\ prevotes = [n \in NODES |-> {}]
    /\ votes = [n \in NODES |-> {}]
    /\ snapshotInProgress = [n \in NODES |-> FALSE]
    /\ nextSnapshotIndex = [n \in NODES |-> 0]
    /\ nextSnapshotTerm = [n \in NODES |-> 0]
    /\ TypeOK

IsLeader(n) == state[n] = "LEADER"
IsCandidate(n) == state[n] = "CANDIDATE"
IsPreCandidate(n) == state[n] = "PRECANDIDATE"
IsFollower(n) == state[n] = "FOLLOWER"

FirstIndex(n) == snapshotLastIndex[n] + 1
LastIndex(n) == snapshotLastIndex[n] + Len(log[n])
LastTermOf(n) == IF Len(log[n]) = 0 THEN snapshotLastTerm[n] ELSE log[n][Len(log[n])].term

LocalIndex(n, gi) == gi - snapshotLastIndex[n]
TermAt(n, i) ==
    IF i = snapshotLastIndex[n] THEN snapshotLastTerm[n]
    ELSE IF i >= FirstIndex(n) /\ i <= LastIndex(n) THEN log[n][LocalIndex(n,i)].term
    ELSE 0

SeqAppend(s, e) == s \o <<e>>

DeleteFromIdx(n, gi) ==
    LET keep == IF gi <= snapshotLastIndex[n] THEN Len(log[n])
                ELSE IF LocalIndex(n, gi) - 1 <= 0 THEN 0 ELSE LocalIndex(n, gi) - 1
    IN IF keep = 0 THEN <<>> ELSE SubSeq(log[n], 1, keep)

EntriesFrom(n, gi) ==
    IF gi > LastIndex(n) THEN <<>>
    ELSE SubSeq(log[n], LocalIndex(n, gi), Len(log[n]))

UpToDate(cand, foll) ==
    \/ LastTermOf(cand) > LastTermOf(foll)
    \/ /\ LastTermOf(cand) = LastTermOf(foll)
       /\ LastIndex(cand) >= LastIndex(foll)

MajorityCount(n) == Cardinality(voters[n]) \div 2 + 1
HasMajority(n, S) == Cardinality(S) >= MajorityCount(n)

BecomeFollower(i, newTerm) ==
    /\ currentTerm[i] < newTerm
    /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![i] = 0]
    /\ electionTimeoutRand' \in [NODES -> RandRange]
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                    nextIndex, matchIndex, msgs, members, voters, prevotes, votes,
                    snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

BecomePreCandidate(i) ==
    /\ state[i] # "LEADER"
    /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
    /\ prevotes' = [prevotes EXCEPT ![i] = {}]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![i] = 0]
    /\ electionTimeoutRand' \in [NODES -> RandRange]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ msgs' = msgs \cup { [type |-> "RVREQ",
                            from |-> i, to |-> j,
                            prevote |-> TRUE,
                            term |-> currentTerm[i] + 1,
                            candidate |-> i,
                            lastIndex |-> LastIndex(i),
                            lastTerm |-> LastTermOf(i)]
                          : j \in voters[i] \ {i} }
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied,
                    snapshotLastIndex, snapshotLastTerm, nextIndex, matchIndex,
                    members, voters, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

BecomeCandidate(i) ==
    /\ IsPreCandidate(i)
    /\ HasMajority(i, prevotes[i])
    /\ state' = [state EXCEPT ![i] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votes' = [votes EXCEPT ![i] = (IF i \in voters[i] THEN {i} ELSE {})]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![i] = 0]
    /\ electionTimeoutRand' \in [NODES -> RandRange]
    /\ leaderId' = [leaderId EXCEPT ![i] = Nil]
    /\ msgs' = msgs \cup { [type |-> "RVREQ",
                            from |-> i, to |-> j,
                            prevote |-> FALSE,
                            term |-> currentTerm[i] + 1,
                            candidate |-> i,
                            lastIndex |-> LastIndex(i),
                            lastTerm |-> LastTermOf(i)]
                          : j \in voters[i] \ {i} }
    /\ UNCHANGED << log, commitIndex, lastApplied,
                    snapshotLastIndex, snapshotLastTerm, nextIndex, matchIndex,
                    members, voters, prevotes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

BecomeLeader(i) ==
    /\ IsCandidate(i)
    /\ HasMajority(i, votes[i])
    /\ state' = [state EXCEPT ![i] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![i] = 0]
    /\ LET noop == [term |-> currentTerm[i], etype |-> "NOOP", node |-> Nil, cmd |-> ""]
           newLog == SeqAppend(log[i], noop)
           li == snapshotLastIndex[i] + Len(newLog)
       IN /\ log' = [log EXCEPT ![i] = newLog]
          /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in NODES |-> li + 1]]
          /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in NODES |-> IF j = i THEN li ELSE 0]]
          /\ msgs' = msgs \cup { [type |-> "AEREQ",
                                  from |-> i, to |-> j,
                                  term |-> currentTerm[i],
                                  leader |-> i,
                                  prevLogIndex |-> li,
                                  prevLogTerm |-> TermAt(i, li),
                                  entries |-> <<>>,
                                  leaderCommit |-> commitIndex[i]]
                                : j \in members[i] \ {i} ]
    /\ UNCHANGED << currentTerm, votedFor, commitIndex, lastApplied,
                    snapshotLastIndex, snapshotLastTerm,
                    members, voters, prevotes, votes, electionTimeoutRand,
                    snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

ElectionTimeout(i) ==
    /\ state[i] # "LEADER"
    /\ timeoutElapsed[i] >= electionTimeoutRand[i]
    /\ BecomePreCandidate(i)

PeriodicElectionTimeout ==
    \E i \in NODES : ElectionTimeout(i)

PeriodicTick ==
    \E i \in NODES :
        /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![i] = timeoutElapsed[i] + 1]
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        leaderId, nextIndex, matchIndex, msgs, members, voters,
                        prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

SendHeartbeat ==
    \E i \in NODES :
        /\ IsLeader(i)
        /\ msgs' = msgs \cup { [type |-> "AEREQ",
                                from |-> i, to |-> j,
                                term |-> currentTerm[i],
                                leader |-> i,
                                prevLogIndex |-> nextIndex[i][j] - 1,
                                prevLogTerm |-> TermAt(i, nextIndex[i][j] - 1),
                                entries |-> <<>>,
                                leaderCommit |-> commitIndex[i]]
                              : j \in members[i] \ {i} }
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex,
                        members, voters, prevoves, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
    \* dummy to satisfy variable name typo
    \/ FALSE

SendAppendEntries ==
    \E i, j \in NODES :
        /\ IsLeader(i)
        /\ j \in members[i]
        /\ j # i
        /\ LET ni == nextIndex[i][j]
               prevI == ni - 1
               ents == IF ni <= LastIndex(i) THEN SubSeq(log[i], LocalIndex(i, ni), Len(log[i])) ELSE <<>>
           IN msgs' = msgs \cup {
                [type |-> "AEREQ", from |-> i, to |-> j,
                 term |-> currentTerm[i], leader |-> i,
                 prevLogIndex |-> prevI, prevLogTerm |-> TermAt(i, prevI),
                 entries |-> ents, leaderCommit |-> commitIndex[i]]
              }
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex,
                        members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

RecvRequestVote ==
    \E m \in msgs :
        /\ RVReq(m)
        /\ LET j == m.to IN j \in NODES
        /\ LET j == m.to IN
           /\ msgs' = msgs \ {m}
           /\ IF m.prevote
              THEN
                /\ /\ (currentTerm[m.to] <= m.term)
                   /\ (m.term = currentTerm[m.to] + 1)
                   /\ UpToDate(m.candidate, m.to)
                   /\ ~(leaderId[m.to] # Nil /\ timeoutElapsed[m.to] < ELECTION_TIMEOUT /\ leaderId[m.to] # m.candidate)
                /\ msgs' = msgs' \cup { [type |-> "RVRSP",
                                         from |-> m.to, to |-> m.from,
                                         prevote |-> TRUE,
                                         requestTerm |-> m.term,
                                         term |-> currentTerm[m.to],
                                         voteGranted |-> TRUE] }
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                                snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                                timeoutElapsed, leaderId, nextIndex, matchIndex,
                                members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
              ELSE
                /\ IF m.term < currentTerm[m.to]
                   THEN
                     /\ msgs' = msgs' \cup { [type |-> "RVRSP",
                                              from |-> m.to, to |-> m.from,
                                              prevote |-> FALSE,
                                              requestTerm |-> m.term,
                                              term |-> currentTerm[m.to],
                                              voteGranted |-> FALSE] }
                     /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                                     snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                                     timeoutElapsed, leaderId, nextIndex, matchIndex,
                                     members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
                   ELSE
                     /\ IF m.term > currentTerm[m.to]
                        THEN
                          /\ currentTerm' = [currentTerm EXCEPT ![m.to] = m.term]
                          /\ state' = [state EXCEPT ![m.to] = "FOLLOWER"]
                          /\ votedFor' = [votedFor EXCEPT ![m.to] = Nil]
                          /\ leaderId' = [leaderId EXCEPT ![m.to] = Nil]
                          /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![m.to] = 0]
                        ELSE
                          /\ UNCHANGED << state, currentTerm, votedFor, leaderId, timeoutElapsed >>
                     /\ IF (votedFor[m.to] = Nil \/ votedFor[m.to] = m.candidate) /\ UpToDate(m.candidate, m.to)
                        THEN
                          /\ votedFor'' = [votedFor' EXCEPT ![m.to] = m.candidate]
                          /\ timeoutElapsed'' = [timeoutElapsed' EXCEPT ![m.to] = 0]
                          /\ msgs' = msgs' \cup { [type |-> "RVRSP",
                                                   from |-> m.to, to |-> m.from,
                                                   prevote |-> FALSE,
                                                   requestTerm |-> m.term,
                                                   term |-> currentTerm'[m.to],
                                                   voteGranted |-> TRUE] }
                          /\ votedFor = votedFor''
                          /\ timeoutElapsed = timeoutElapsed''
                        ELSE
                          /\ msgs' = msgs' \cup { [type |-> "RVRSP",
                                                   from |-> m.to, to |-> m.from,
                                                   prevote |-> FALSE,
                                                   requestTerm |-> m.term,
                                                   term |-> currentTerm'[m.to],
                                                   voteGranted |-> FALSE] }
                          /\ UNCHANGED << votedFor, timeoutElapsed >>
                     /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                                     nextIndex, matchIndex, members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

RecvRequestVoteResponse ==
    \E m \in msgs :
        /\ RVRsp(m)
        /\ LET i == m.to IN i \in NODES
        /\ msgs' = msgs \ {m}
        /\ IF m.prevote
           THEN
             /\ IsPreCandidate(i)
             /\ m.requestTerm = currentTerm[i] + 1
             /\ IF m.voteGranted
                THEN prevotes' = [prevotes EXCEPT ![i] = prevotes[i] \cup {m.from}]
                ELSE prevotes' = prevotes
             /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                             snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                             timeoutElapsed, leaderId, nextIndex, matchIndex,
                             members, voters, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
           ELSE
             /\ IsCandidate(i)
             /\ m.requestTerm = currentTerm[i]
             /\ IF m.term > currentTerm[i]
                THEN
                  /\ BecomeFollower(i, m.term)
                  /\ UNCHANGED << msgs, prevotes, votes >>
                ELSE
                  /\ IF m.voteGranted
                     THEN votes' = [votes EXCEPT ![i] = votes[i] \cup {m.from}]
                     ELSE votes' = votes
                  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                                  snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                                  timeoutElapsed, leaderId, nextIndex, matchIndex,
                                  members, voters, prevotes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

RecvAppendEntries ==
    \E m \in msgs :
        /\ AEReq(m)
        /\ LET j == m.to IN j \in NODES
        /\ msgs' = msgs \ {m}
        /\ IF m.term < currentTerm[j]
           THEN
             /\ msgs' = msgs' \cup { [type |-> "AERSP", from |-> j, to |-> m.from,
                                      term |-> currentTerm[j], success |-> FALSE,
                                      matchIndex |-> LastIndex(j)] }
             /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                             snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                             timeoutElapsed, leaderId, nextIndex, matchIndex,
                             members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
           ELSE
             /\ IF m.term > currentTerm[j]
                THEN
                  /\ currentTerm' = [currentTerm EXCEPT ![j] = m.term]
                  /\ state' = [state EXCEPT ![j] = "FOLLOWER"]
                  /\ votedFor' = [votedFor EXCEPT ![j] = Nil]
                ELSE
                  /\ UNCHANGED << state, currentTerm, votedFor >>
             /\ leaderId' = [leaderId EXCEPT ![j] = m.from]
             /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![j] = 0]
             /\ IF m.prevLogIndex = snapshotLastIndex[j]
                   /\ m.prevLogTerm # snapshotLastTerm[j]
                THEN
                  /\ msgs' = msgs' \cup { [type |-> "AERSP", from |-> j, to |-> m.from,
                                           term |-> currentTerm'[j], success |-> FALSE,
                                           matchIndex |-> LastIndex(j)] }
                  /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                  electionTimeoutRand, nextIndex, matchIndex,
                                  members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
                ELSE
                  /\ IF m.prevLogIndex # snapshotLastIndex[j]
                        /\ (m.prevLogIndex < FirstIndex(j) \/ m.prevLogIndex > LastIndex(j) \/ TermAt(j, m.prevLogIndex) # m.prevLogTerm)
                     THEN
                       /\ msgs' = msgs' \cup { [type |-> "AERSP", from |-> j, to |-> m.from,
                                                term |-> currentTerm'[j], success |-> FALSE,
                                                matchIndex |-> LastIndex(j)] }
                       /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                       electionTimeoutRand, nextIndex, matchIndex,
                                       members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>
                     ELSE
                       /\ log' =
                            LET delFrom == m.prevLogIndex + 1
                                kept == DeleteFromIdx(j, delFrom)
                            IN [log EXCEPT ![j] = kept \o m.entries]
                       /\ msgs' = msgs' \cup {
                                [type |-> "AERSP", from |-> j, to |-> m.from,
                                 term |-> currentTerm'[j], success |-> TRUE,
                                 matchIndex |-> m.prevLogIndex + Len(m.entries)]
                             }
                       /\ commitIndex' = [commitIndex EXCEPT ![j] = IF commitIndex[j] < m.leaderCommit
                                                            THEN Min(LastIndex'(j), m.leaderCommit)
                                                            ELSE commitIndex[j]]
                       /\ UNCHANGED << lastApplied, snapshotLastIndex, snapshotLastTerm,
                                       electionTimeoutRand, nextIndex, matchIndex,
                                       members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

RecvAppendEntriesResponse ==
    \E m \in msgs :
        /\ AERsp(m)
        /\ LET i == m.to IN i \in NODES
        /\ IsLeader(i)
        /\ msgs' = msgs \ {m}
        /\ IF m.term > currentTerm[i]
           THEN
             /\ BecomeFollower(i, m.term)
             /\ UNCHANGED << msgs, prevotes, votes >>
           ELSE
             /\ IF m.success
                THEN
                  /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![m.from] = m.matchIndex]]
                  /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.from] = m.matchIndex + 1]]
                ELSE
                  /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.from] = IF nextIndex[i][m.from] > 1 THEN nextIndex[i][m.from] - 1 ELSE 1]]
                  /\ UNCHANGED matchIndex
             /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                             snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                             timeoutElapsed, leaderId, members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

LeaderCommitAdvance ==
    \E i \in NODES :
        /\ IsLeader(i)
        /\ LET S == { k \in 0..LastIndex(i) :
                        /\ TermAt(i, k) = currentTerm[i]
                        /\ HasMajority(i, { p \in voters[i] : (p = i) \/ matchIndex[i][p] >= k }) }
               Adv == { k \in S : k >= commitIndex[i] }
           IN /\ IF Adv = {} THEN UNCHANGED commitIndex
                 ELSE commitIndex' = [commitIndex EXCEPT ![i] = CHOOSE k \in Adv : \A x \in Adv : x <= k]
    /\ UNCHANGED << state, currentTerm, votedFor, log, lastApplied,
                    snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                    timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                    members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

LogAppend ==
    \E i \in NODES, ety \in [term: Nat, etype: EntryTypes, node: NODES \cup {Nil}, cmd: STRING \cup Nat \cup {Nil}] :
        /\ IsLeader(i)
        /\ ety.term = currentTerm[i]
        /\ ety.etype \in {"NORMAL"}
        /\ log' = [log EXCEPT ![i] = SeqAppend(log[i], ety)]
        /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                        members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

AddNode ==
    \E i \in NODES, x \in NODES :
        /\ IsLeader(i)
        /\ x \notin members[i]
        /\ LET ety == [term |-> currentTerm[i], etype |-> "ADD_NODE", node |-> x, cmd |-> ""]
           IN log' = [log EXCEPT ![i] = SeqAppend(log[i], ety)]
        /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                        members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

AddNonVotingNode ==
    \E i \in NODES, x \in NODES :
        /\ IsLeader(i)
        /\ x \notin members[i]
        /\ LET ety == [term |-> currentTerm[i], etype |-> "ADD_NONVOTING_NODE", node |-> x, cmd |-> ""]
           IN log' = [log EXCEPT ![i] = SeqAppend(log[i], ety)]
        /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                        members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

RemoveNode ==
    \E i \in NODES, x \in NODES :
        /\ IsLeader(i)
        /\ x \in members[i]
        /\ LET ety == [term |-> currentTerm[i], etype |-> "REMOVE_NODE", node |-> x, cmd |-> ""]
           IN log' = [log EXCEPT ![i] = SeqAppend(log[i], ety)]
        /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                        members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

ApplyConfigChange ==
    \E n \in NODES :
        /\ lastApplied[n] < commitIndex[n]
        /\ LET i == lastApplied[n] + 1
               e == log[n][LocalIndex(n, i)]
           IN /\ e.etype \in {"ADD_NODE", "ADD_NONVOTING_NODE", "REMOVE_NODE"}
              /\ IF e.etype = "ADD_NODE"
                 THEN /\ members' = [members EXCEPT ![n] = members[n] \cup {e.node}]
                      /\ voters' = [voters EXCEPT ![n] = voters[n] \cup {e.node}]
                 ELSE IF e.etype = "ADD_NONVOTING_NODE"
                      THEN /\ members' = [members EXCEPT ![n] = members[n] \cup {e.node}]
                           /\ voters' = [voters EXCEPT ![n] = voters[n] \ {e.node}]
                      ELSE /\ members' = [members EXCEPT ![n] = members[n] \ {e.node}]
                           /\ voters' = [voters EXCEPT ![n] = voters[n] \ {e.node}]
              /\ lastApplied' = [lastApplied EXCEPT ![n] = i]
              /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex,
                              snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                              timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                              prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

ApplyEntry ==
    \E n \in NODES :
        /\ lastApplied[n] < commitIndex[n]
        /\ LET i == lastApplied[n] + 1
               e == log[n][LocalIndex(n, i)]
           IN /\ e.etype \in {"NORMAL", "NOOP"}
              /\ lastApplied' = [lastApplied EXCEPT ![n] = i]
              /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex,
                              snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                              timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                              members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

SnapshotBegin ==
    \E n \in NODES :
        /\ ~snapshotInProgress[n]
        /\ lastApplied[n] >= FirstIndex(n) - 1
        /\ lastApplied[n] > snapshotLastIndex[n]
        /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
        /\ nextSnapshotIndex' = [nextSnapshotIndex EXCEPT ![n] = lastApplied[n]]
        /\ nextSnapshotTerm' = [nextSnapshotTerm EXCEPT ![n] = TermAt(n, lastApplied[n])]
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied,
                        snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                        timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                        members, voters, prevotes, votes >>

SnapshotEnd ==
    \E n \in NODES :
        /\ snapshotInProgress[n]
        /\ LET oldBase == snapshotLastIndex[n]
               newBase == nextSnapshotIndex[n]
               k == newBase - oldBase
               newLog == IF Len(log[n]) > k THEN SubSeq(log[n], k + 1, Len(log[n])) ELSE <<>>
           IN /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = newBase]
              /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = nextSnapshotTerm[n]]
              /\ log' = [log EXCEPT ![n] = newLog]
              /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
              /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied,
                              electionTimeoutRand, timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                              members, voters, prevotes, votes, nextSnapshotIndex, nextSnapshotTerm >>

ElectionStart ==
    \E i \in NODES :
        /\ state[i] # "LEADER"
        /\ BecomePreCandidate(i)

PeriodicHeartbeat ==
    SendHeartbeat

RecvRequestVoteAction == RecvRequestVote
RecvRequestVoteResponseAction == RecvRequestVoteResponse
RecvAppendEntriesAction == RecvAppendEntries
RecvAppendEntriesResponseAction == RecvAppendEntriesResponse
LogDelete == \E n \in NODES : FALSE
LogCommit == LeaderCommitAdvance

Next ==
    \/ PeriodicTick
    \/ PeriodicElectionTimeout
    \/ ElectionStart
    \/ BecomeCandidate
    \/ BecomeLeader
    \/ RecvRequestVoteAction
    \/ RecvRequestVoteResponseAction
    \/ SendAppendEntries
    \/ PeriodicHeartbeat
    \/ RecvAppendEntriesAction
    \/ RecvAppendEntriesResponseAction
    \/ LogAppend
    \/ LogCommit
    \/ ApplyConfigChange
    \/ ApplyEntry
    \/ AddNode
    \/ AddNonVotingNode
    \/ RemoveNode
    \/ SnapshotBegin
    \/ SnapshotEnd
    \/ \E i, t \in Nat : \E n \in NODES : FALSE
    \/ \E i \in NODES : \E t \in Nat : FALSE

Spec ==
    Init /\ [][Next]_<< state, currentTerm, votedFor, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand,
                      timeoutElapsed, leaderId, nextIndex, matchIndex, msgs,
                      members, voters, prevotes, votes, snapshotInProgress, nextSnapshotIndex, nextSnapshotTerm >>

====