---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  Node,
  ELECTION_TIMEOUT_MIN,
  ELECTION_TIMEOUT_MAX,
  REQUEST_TIMEOUT,
  None

EntryTypes == {"NOOP","NORMAL","ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"}

MessageTypes == {"AppendEntries","AppendEntriesResp","RequestVote","RequestVoteResp","Snapshot","SnapshotResp"}

VARIABLES
  Members,
  Voters,
  state,
  currentTerm,
  votedFor,
  log,
  commitIndex,
  lastApplied,
  leaderId,
  nextIndex,
  matchIndex,
  electionTimer,
  electionTimeout,
  requestTimer,
  messages,
  prevoteGranted,
  voteGranted,
  snapshotIndex,
  snapshotTerm,
  snapshotInProgress,
  snapshotTarget

Vars ==
  << Members, Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
     nextIndex, matchIndex, electionTimer, electionTimeout, requestTimer, messages,
     prevoteGranted, voteGranted, snapshotIndex, snapshotTerm, snapshotInProgress, snapshotTarget >>

IsMember(n) == n \in Members
IsVoter(n) == n \in Voters

LenLog(n) == Len(log[n])

GlobalLastIndex(n) == snapshotIndex[n] + LenLog(n)

LocalPos(n, gi) == IF gi <= snapshotIndex[n] THEN 0 ELSE gi - snapshotIndex[n]

HasEntryAt(n, gi) ==
  /\ gi > snapshotIndex[n]
  /\ gi <= snapshotIndex[n] + LenLog(n)

TermAt(n, gi) ==
  IF gi = snapshotIndex[n] THEN snapshotTerm[n]
  ELSE IF HasEntryAt(n, gi) THEN log[n][LocalPos(n, gi)].term ELSE 0

LastLogTerm(n) ==
  IF LenLog(n) = 0 THEN snapshotTerm[n] ELSE log[n][LenLog(n)].term

Majority(S) == Cardinality(S) > Cardinality(Voters) \div 2

RequestVoteMsg(m) ==
  /\ m \in [mtype: {"RequestVote"},
            from: Node, to: Node, term: Nat, prevote: BOOLEAN,
            lastLogIndex: Nat, lastLogTerm: Nat]

RequestVoteRespMsg(m) ==
  /\ m \in [mtype: {"RequestVoteResp"},
            from: Node, to: Node, requestTerm: Nat, term: Nat, prevote: BOOLEAN,
            voteGranted: BOOLEAN]

AppendEntriesMsg(m) ==
  /\ m \in [mtype: {"AppendEntries"},
            from: Node, to: Node, term: Nat, leader: Node,
            prevLogIndex: Nat, prevLogTerm: Nat,
            entries: Seq([term: Nat, type: EntryTypes, node: Node \cup {None}, cmd: Nat]),
            leaderCommit: Nat]

AppendEntriesRespMsg(m) ==
  /\ m \in [mtype: {"AppendEntriesResp"},
            from: Node, to: Node, term: Nat, success: BOOLEAN, matchIndex: Nat]

SnapshotMsg(m) ==
  /\ m \in [mtype: {"Snapshot"},
            from: Node, to: Node, term: Nat, snapshotIndex: Nat, snapshotTerm: Nat]

SnapshotRespMsg(m) ==
  /\ m \in [mtype: {"SnapshotResp"},
            from: Node, to: Node, term: Nat, success: BOOLEAN, snapshotIndex: Nat]

AppendEntriesPayload(n,p) ==
  LET pos == LocalPos(n, nextIndex[n][p]) IN
    IF pos <= 0 \/ pos > LenLog(n) THEN << >> ELSE SubSeq(log[n], pos, LenLog(n))

Init ==
  /\ Members = Node
  /\ Voters = Node
  /\ state = [n \in Node |-> "FOLLOWER"]
  /\ currentTerm = [n \in Node |-> 0]
  /\ votedFor = [n \in Node |-> None]
  /\ log = [n \in Node |-> << >>]
  /\ commitIndex = [n \in Node |-> 0]
  /\ lastApplied = [n \in Node |-> 0]
  /\ leaderId = [n \in Node |-> None]
  /\ nextIndex = [n \in Node |-> [p \in Node |-> 1]]
  /\ matchIndex = [n \in Node |-> [p \in Node |-> 0]]
  /\ electionTimer = [n \in Node |-> 0]
  /\ electionTimeout \in [n \in Node |-> ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX]
  /\ requestTimer = [n \in Node |-> 0]
  /\ messages = {}
  /\ prevoteGranted = [n \in Node |-> {}]
  /\ voteGranted = [n \in Node |-> {}]
  /\ snapshotIndex = [n \in Node |-> 0]
  /\ snapshotTerm = [n \in Node |-> 0]
  /\ snapshotInProgress = [n \in Node |-> FALSE]
  /\ snapshotTarget = [n \in Node |-> 0]

BecomeFollower(n) ==
  /\ IsMember(n)
  /\ state[n] # "FOLLOWER"
  /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
  /\ leaderId' = [leaderId EXCEPT ![n] = None]
  /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
  /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX : TRUE]
  /\ UNCHANGED << Members,Voters,currentTerm,votedFor,log,commitIndex,lastApplied,
                  nextIndex,matchIndex,requestTimer,messages,prevoteGranted,voteGranted,
                  snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

BecomePreCandidate(n) ==
  /\ IsMember(n)
  /\ state[n] \in {"FOLLOWER","CANDIDATE"}
  /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
  /\ prevoteGranted' = [prevoteGranted EXCEPT ![n] = (IF IsVoter(n) THEN {n} ELSE {})]
  /\ voteGranted' = [voteGranted EXCEPT ![n] = {}]
  /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
  /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX : TRUE]
  /\ messages' =
      messages \cup
      { [mtype |-> "RequestVote",
         from |-> n, to |-> p, term |-> currentTerm[n] + 1,
         prevote |-> TRUE,
         lastLogIndex |-> GlobalLastIndex(n),
         lastLogTerm |-> LastLogTerm(n)]
        : p \in Voters \ {n} }
  /\ UNCHANGED << Members,Voters,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                  nextIndex,matchIndex,requestTimer,voteGranted,snapshotIndex,snapshotTerm,
                  snapshotInProgress,snapshotTarget >>

BecomeCandidate(n) ==
  /\ IsMember(n)
  /\ state[n] \in {"PRECANDIDATE","FOLLOWER"}
  /\ LET newTerm == currentTerm[n] + 1 IN
     /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
     /\ votedFor' = [votedFor EXCEPT ![n] = n]
     /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
     /\ leaderId' = [leaderId EXCEPT ![n] = None]
     /\ voteGranted' = [voteGranted EXCEPT ![n] = (IF IsVoter(n) THEN {n} ELSE {})]
     /\ prevoteGranted' = [prevoteGranted EXCEPT ![n] = {}]
     /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
     /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX : TRUE]
     /\ messages' =
          messages \cup
          { [mtype |-> "RequestVote",
             from |-> n, to |-> p, term |-> newTerm,
             prevote |-> FALSE,
             lastLogIndex |-> GlobalLastIndex(n),
             lastLogTerm |-> LastLogTerm(n)]
            : p \in Voters \ {n} }
  /\ UNCHANGED << Members,Voters,log,commitIndex,lastApplied,nextIndex,matchIndex,requestTimer,
                  snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

BecomeLeader(n) ==
  /\ IsMember(n)
  /\ state[n] = "CANDIDATE"
  /\ Majority(voteGranted[n])
  /\ state' = [state EXCEPT ![n] = "LEADER"]
  /\ leaderId' = [leaderId EXCEPT ![n] = n]
  /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "NOOP", node |-> None, cmd |-> 0])]
  /\ nextIndex' =
      [nextIndex EXCEPT ![n] =
        [p \in Node |-> GlobalLastIndex(n) + 1]]
  /\ matchIndex' =
      [matchIndex EXCEPT ![n] =
        [p \in Node |-> IF p = n THEN GlobalLastIndex(n) ELSE 0]]
  /\ requestTimer' = [requestTimer EXCEPT ![n] = 0]
  /\ UNCHANGED << Members,Voters,currentTerm,votedFor,commitIndex,lastApplied,electionTimer,electionTimeout,
                  messages,prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

ElectionStart(n) == BecomePreCandidate(n)

ElectionTimeout(n) ==
  /\ IsMember(n)
  /\ state[n] \in {"FOLLOWER","PRECANDIDATE","CANDIDATE"}
  /\ electionTimer[n] >= electionTimeout[n]
  /\ BecomePreCandidate(n)

RecvRequestVote ==
  \E m \in messages :
    /\ RequestVoteMsg(m)
    /\ IsMember(m.to)
    /\ LET n == m.to IN
       LET messages1 == messages \ {m} IN
       LET leaderId1 == leaderId IN
       /\ IF m.prevote THEN
            /\ /\ (currentTerm[n] <= m.term)
                 /\ (leaderId[n] = None \/ electionTimer[n] >= electionTimeout[n])
                 /\ (m.lastLogTerm > LastLogTerm(n)
                    \/ (m.lastLogTerm = LastLogTerm(n) /\ m.lastLogIndex >= GlobalLastIndex(n)))
               \/ /\ TRUE
                  /\ TRUE
            /\ messages' =
                 messages1 \cup
                 { [mtype |-> "RequestVoteResp",
                    from |-> n, to |-> m.from,
                    requestTerm |-> m.term,
                    term |-> currentTerm[n],
                    prevote |-> TRUE,
                    voteGranted |-> /\ (currentTerm[n] <= m.term)
                                     /\ (leaderId[n] = None \/ electionTimer[n] >= electionTimeout[n])
                                     /\ (m.lastLogTerm > LastLogTerm(n)
                                        \/ (m.lastLogTerm = LastLogTerm(n) /\ m.lastLogIndex >= GlobalLastIndex(n)))] }
            /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                            nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
          ELSE
            /\ IF m.term > currentTerm[n]
               THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                    /\ votedFor' = [votedFor EXCEPT ![n] = None]
               ELSE /\ UNCHANGED << currentTerm,state,votedFor >>
            /\ LET canGrant ==
                   /\ m.term = currentTerm'[n]
                   /\ (votedFor[n] = None \/ votedFor[n] = m.from)
                   /\ (m.lastLogTerm > LastLogTerm(n)
                      \/ (m.lastLogTerm = LastLogTerm(n) /\ m.lastLogIndex >= GlobalLastIndex(n)))
               IN
               /\ votedFor' = [votedFor EXCEPT ![n] = IF canGrant THEN m.from ELSE votedFor[n]]
               /\ electionTimer' = [electionTimer EXCEPT ![n] = IF canGrant THEN 0 ELSE electionTimer[n]]
               /\ leaderId' = [leaderId EXCEPT ![n] = IF canGrant THEN None ELSE leaderId1[n]]
               /\ messages' = messages1 \cup
                  { [mtype |-> "RequestVoteResp",
                     from |-> n, to |-> m.from,
                     requestTerm |-> m.term,
                     term |-> currentTerm'[n],
                     prevote |-> FALSE,
                     voteGranted |-> canGrant] }
               /\ UNCHANGED << Members,Voters,log,commitIndex,lastApplied,nextIndex,matchIndex,
                               electionTimeout,requestTimer,prevoteGranted,voteGranted,
                               snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

RecvRequestVoteResponse ==
  \E m \in messages :
    /\ RequestVoteRespMsg(m)
    /\ IsMember(m.to)
    /\ LET n == m.to IN
       LET messages0 == messages \ {m} IN
       /\ IF m.term > currentTerm[n] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
            /\ votedFor' = [votedFor EXCEPT ![n] = None]
            /\ messages' = messages0
            /\ UNCHANGED << Members,Voters,log,commitIndex,lastApplied,leaderId,
                            nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
          ELSE
            /\ IF m.prevote THEN
                 /\ state[n] = "PRECANDIDATE"
                 /\ IF m.requestTerm = currentTerm[n] + 1 /\ m.voteGranted THEN
                      /\ prevoteGranted' = [prevoteGranted EXCEPT ![n] = prevoteGranted[n] \cup {m.from}]
                    ELSE /\ UNCHANGED prevoteGranted
                 /\ IF Majority(prevoteGranted'[n]) THEN
                      /\ LET newTerm == currentTerm[n] + 1 IN
                         /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
                         /\ votedFor' = [votedFor EXCEPT ![n] = n]
                         /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
                         /\ leaderId' = [leaderId EXCEPT ![n] = None]
                         /\ voteGranted' = [voteGranted EXCEPT ![n] = (IF IsVoter(n) THEN {n} ELSE {})]
                         /\ prevoteGranted' = [prevoteGranted EXCEPT ![n] = {}]
                         /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
                         /\ electionTimeout' = [electionTimeout EXCEPT ![n] = CHOOSE t \in ELECTION_TIMEOUT_MIN..ELECTION_TIMEOUT_MAX : TRUE]
                         /\ messages' =
                              messages0 \cup
                              { [mtype |-> "RequestVote",
                                 from |-> n, to |-> p, term |-> newTerm,
                                 prevote |-> FALSE,
                                 lastLogIndex |-> GlobalLastIndex(n),
                                 lastLogTerm |-> LastLogTerm(n)]
                                : p \in Voters \ {n} }
                         /\ UNCHANGED << Members,Voters,log,commitIndex,lastApplied,nextIndex,matchIndex,requestTimer,
                                         snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
                    ELSE
                      /\ messages' = messages0
                      /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                                      nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                                      voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
               ELSE
                 /\ state[n] = "CANDIDATE"
                 /\ IF m.requestTerm = currentTerm[n] /\ m.voteGranted THEN
                      /\ voteGranted' = [voteGranted EXCEPT ![n] = voteGranted[n] \cup {m.from}]
                    ELSE /\ UNCHANGED voteGranted
                 /\ IF Majority(voteGranted'[n]) THEN
                      /\ state' = [state EXCEPT ![n] = "LEADER"]
                      /\ leaderId' = [leaderId EXCEPT ![n] = n]
                      /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "NOOP", node |-> None, cmd |-> 0])]
                      /\ nextIndex' =
                          [nextIndex EXCEPT ![n] =
                            [p \in Node |-> GlobalLastIndex(n) + 1]]
                      /\ matchIndex' =
                          [matchIndex EXCEPT ![n] =
                            [p \in Node |-> IF p = n THEN GlobalLastIndex(n) ELSE 0]]
                      /\ requestTimer' = [requestTimer EXCEPT ![n] = 0]
                      /\ messages' = messages0
                      /\ UNCHANGED << Members,Voters,currentTerm,votedFor,commitIndex,lastApplied,electionTimer,electionTimeout,
                                      prevoteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
                    ELSE
                      /\ messages' = messages0
                      /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                                      nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                                      prevoteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

SendAppendEntries ==
  \E n \in Members :
    /\ state[n] = "LEADER"
    /\ \E p \in Members \ {n} :
         /\ IF nextIndex[n][p] <= snapshotIndex[n] THEN
              /\ messages' = messages \cup
                 { [mtype |-> "Snapshot", from |-> n, to |-> p,
                    term |-> currentTerm[n],
                    snapshotIndex |-> snapshotIndex[n],
                    snapshotTerm |-> snapshotTerm[n]] }
            ELSE
              /\ LET prevIdx == nextIndex[n][p] - 1 IN
                 /\ messages' = messages \cup
                     { [mtype |-> "AppendEntries",
                        from |-> n, to |-> p, term |-> currentTerm[n], leader |-> n,
                        prevLogIndex |-> prevIdx, prevLogTerm |-> TermAt(n, prevIdx),
                        entries |-> AppendEntriesPayload(n,p),
                        leaderCommit |-> commitIndex[n]] }
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                    prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

SendHeartbeat ==
  \E n \in Members :
    /\ state[n] = "LEADER"
    /\ messages' =
        messages \cup
        { [mtype |-> "AppendEntries",
           from |-> n, to |-> p, term |-> currentTerm[n], leader |-> n,
           prevLogIndex |-> GlobalLastIndex(n),
           prevLogTerm |-> LastLogTerm(n),
           entries |-> << >>,
           leaderCommit |-> commitIndex[n]]
          : p \in Members \ {n} }
    /\ requestTimer' = [requestTimer EXCEPT ![n] = 0]
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimer,electionTimeout,prevoteGranted,voteGranted,
                    snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

RecvAppendEntries ==
  \E m \in messages :
    /\ AppendEntriesMsg(m)
    /\ IsMember(m.to)
    /\ LET n == m.to IN
       LET messages1 == messages \ {m} IN
       /\ IF m.term < currentTerm[n] THEN
            /\ messages' = messages1 \cup
               { [mtype |-> "AppendEntriesResp",
                  from |-> n, to |-> m.from,
                  term |-> currentTerm[n], success |-> FALSE,
                  matchIndex |-> GlobalLastIndex(n)] }
            /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                            nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
          ELSE
            /\ IF m.term > currentTerm[n]
               THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
               ELSE /\ UNCHANGED << currentTerm,state >>
            /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
            /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
            /\ LET okPrev ==
                   \/ m.prevLogIndex = snapshotIndex[n] /\ m.prevLogTerm = snapshotTerm[n]
                   \/ /\ HasEntryAt(n, m.prevLogIndex)
                      /\ TermAt(n, m.prevLogIndex) = m.prevLogTerm
               IN
               IF ~okPrev THEN
                 /\ messages' = messages1 \cup
                    { [mtype |-> "AppendEntriesResp",
                       from |-> n, to |-> m.from,
                       term |-> currentTerm'[n], success |-> FALSE,
                       matchIndex |-> GlobalLastIndex(n)] }
                 /\ UNCHANGED << Members,Voters,votedFor,log,commitIndex,lastApplied,nextIndex,matchIndex,
                                 electionTimeout,requestTimer,prevoteGranted,voteGranted,
                                 snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
               ELSE
                 /\ LET dropFrom == m.prevLogIndex + 1 IN
                    /\ log' =
                         [log EXCEPT ![n] =
                           LET pre ==
                               IF dropFrom <= snapshotIndex[n] THEN << >>
                               ELSE SubSeq(log[n], 1, LocalPos(n, dropFrom) - 1)
                           IN Append(pre, m.entries)]
                    /\ commitIndex' =
                         [commitIndex EXCEPT ![n] = Min(GlobalLastIndex'(n), m.leaderCommit)]
                    /\ messages' = messages1 \cup
                       { [mtype |-> "AppendEntriesResp",
                          from |-> n, to |-> m.from,
                          term |-> currentTerm'[n], success |-> TRUE,
                          matchIndex |-> GlobalLastIndex'(n)] }
                    /\ UNCHANGED << Members,Voters,votedFor,lastApplied,nextIndex,matchIndex,
                                    electionTimeout,requestTimer,prevoteGranted,voteGranted,
                                    snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

RecvAppendEntriesResponse ==
  \E m \in messages :
    /\ AppendEntriesRespMsg(m)
    /\ IsMember(m.to)
    /\ LET n == m.to IN
       /\ state[n] = "LEADER"
       /\ messages' = messages \ {m}
       /\ IF m.term > currentTerm[n] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
            /\ votedFor' = [votedFor EXCEPT ![n] = None]
            /\ UNCHANGED << Members,Voters,log,commitIndex,lastApplied,leaderId,
                            nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
          ELSE
            /\ IF m.success THEN
                 /\ matchIndex' =
                      [matchIndex EXCEPT ![n] =
                         [matchIndex[n] EXCEPT ![m.from] = Max(matchIndex[n][m.from], m.matchIndex)]]
                 /\ nextIndex' =
                      [nextIndex EXCEPT ![n] =
                         [nextIndex[n] EXCEPT ![m.from] = matchIndex'[n][m.from] + 1]]
               ELSE
                 /\ nextIndex' =
                      [nextIndex EXCEPT ![n] =
                         [nextIndex[n] EXCEPT ![m.from] = Max(1, nextIndex[n][m.from] - 1)]]
                 /\ UNCHANGED matchIndex
            /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                            electionTimer,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

LogCommit ==
  \E n \in Members :
    /\ state[n] = "LEADER"
    /\ \E idx \in Nat :
         /\ idx <= GlobalLastIndex(n)
         /\ idx > commitIndex[n]
         /\ TermAt(n, idx) = currentTerm[n]
         /\ LET supporters == { v \in Voters : v = n \/ matchIndex[n][v] >= idx } IN
            /\ Majority(supporters)
            /\ commitIndex' = [commitIndex EXCEPT ![n] = idx]
            /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,lastApplied,leaderId,
                            nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

ApplyConfigChange ==
  \E n \in Members :
    /\ lastApplied[n] < commitIndex[n]
    /\ LET nextIdx == lastApplied[n] + 1 IN
       /\ HasEntryAt(n, nextIdx)
       /\ LET e == log[n][LocalPos(n, nextIdx)] IN
          /\ lastApplied' = [lastApplied EXCEPT ![n] = nextIdx]
          /\ IF e.type = "ADD_NODE" THEN
               /\ Members' = Members \cup {e.node}
               /\ Voters' = Voters \cup {e.node}
             ELSE IF e.type = "ADD_NONVOTING_NODE" THEN
               /\ Members' = Members \cup {e.node}
               /\ Voters' = Voters \ {e.node}
             ELSE IF e.type = "REMOVE_NODE" THEN
               /\ Members' = Members \ {e.node}
               /\ Voters' = Voters \ {e.node}
             ELSE
               /\ UNCHANGED << Members,Voters >>
          /\ UNCHANGED << state,currentTerm,votedFor,log,commitIndex,leaderId,
                          nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                          prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

AddNode ==
  \E n \in Members, x \in Node :
    /\ state[n] = "LEADER"
    /\ x \notin Members
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "ADD_NODE", node |-> x, cmd |-> 0])]
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                    prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

RemoveNode ==
  \E n \in Members, x \in Members :
    /\ state[n] = "LEADER"
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "REMOVE_NODE", node |-> x, cmd |-> 0])]
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                    prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

LogAppend ==
  \E n \in Members :
    /\ state[n] = "LEADER"
    /\ \E ety \in [term: {currentTerm[n]}, type: EntryTypes, node: Node \cup {None}, cmd: Nat] :
         /\ log' = [log EXCEPT ![n] = Append(log[n], ety)]
         /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,commitIndex,lastApplied,leaderId,
                         nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                         prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

LogDelete ==
  \E n \in Members :
    /\ FALSE

PeriodicElectionTimeout ==
  \E n \in Members :
    /\ electionTimer' = [electionTimer EXCEPT ![n] = electionTimer[n] + 1]
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimeout,requestTimer,messages,prevoteGranted,voteGranted,
                    snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

PeriodicHeartbeat ==
  \E n \in Members :
    /\ state[n] = "LEADER"
    /\ requestTimer[n] >= REQUEST_TIMEOUT
    /\ messages' =
        messages \cup
        { [mtype |-> "AppendEntries",
           from |-> n, to |-> p, term |-> currentTerm[n], leader |-> n,
           prevLogIndex |-> GlobalLastIndex(n),
           prevLogTerm |-> LastLogTerm(n),
           entries |-> << >>,
           leaderCommit |-> commitIndex[n]]
          : p \in Members \ {n} }
    /\ requestTimer' = [requestTimer EXCEPT ![n] = 0]
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimer,electionTimeout,prevoteGranted,voteGranted,
                    snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

ElectionTickAndTrigger ==
  \E n \in Members :
    /\ electionTimer[n] >= electionTimeout[n]
    /\ ElectionTimeout(n)

RecvSnapshot ==
  \E m \in messages :
    /\ SnapshotMsg(m)
    /\ IsMember(m.to)
    /\ LET n == m.to IN
       LET messages1 == messages \ {m} IN
       /\ IF m.term < currentTerm[n] THEN
            /\ messages' = messages1 \cup
               { [mtype |-> "SnapshotResp",
                  from |-> n, to |-> m.from,
                  term |-> currentTerm[n], success |-> FALSE,
                  snapshotIndex |-> snapshotIndex[n]] }
            /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                            nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>
          ELSE
            /\ IF m.term > currentTerm[n]
               THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
               ELSE /\ UNCHANGED << currentTerm,state >>
            /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
            /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
            /\ IF m.snapshotIndex > snapshotIndex[n] THEN
                 /\ snapshotIndex' = [snapshotIndex EXCEPT ![n] = m.snapshotIndex]
                 /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = m.snapshotTerm]
                 /\ log' = [log EXCEPT ![n] = << >>]
                 /\ commitIndex' = [commitIndex EXCEPT ![n] = Max(commitIndex[n], m.snapshotIndex)]
                 /\ lastApplied' = [lastApplied EXCEPT ![n] = Max(lastApplied[n], m.snapshotIndex)]
               ELSE
                 /\ UNCHANGED << snapshotIndex,snapshotTerm,log,commitIndex,lastApplied >>
            /\ messages' = messages1 \cup
               { [mtype |-> "SnapshotResp",
                  from |-> n, to |-> m.from,
                  term |-> currentTerm'[n], success |-> TRUE,
                  snapshotIndex |-> snapshotIndex'[n]] }
            /\ UNCHANGED << Members,Voters,votedFor,nextIndex,matchIndex,electionTimeout,requestTimer,
                            prevoteGranted,voteGranted,snapshotInProgress,snapshotTarget >>

RecvSnapshotResponse ==
  \E m \in messages :
    /\ SnapshotRespMsg(m)
    /\ IsMember(m.to)
    /\ LET n == m.to IN
       /\ state[n] = "LEADER"
       /\ messages' = messages \ {m}
       /\ IF m.term > currentTerm[n] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
            /\ votedFor' = [votedFor EXCEPT ![n] = None]
          ELSE UNCHANGED << state,currentTerm,votedFor >>
       /\ UNCHANGED << Members,Voters,log,commitIndex,lastApplied,leaderId,nextIndex,matchIndex,
                       electionTimer,electionTimeout,requestTimer,prevoteGranted,voteGranted,
                       snapshotIndex,snapshotTerm,snapshotInProgress,snapshotTarget >>

SnapshotBegin ==
  \E n \in Members :
    /\ ~snapshotInProgress[n]
    /\ commitIndex[n] > snapshotIndex[n]
    /\ lastApplied[n] = commitIndex[n]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
    /\ snapshotTarget' = [snapshotTarget EXCEPT ![n] = lastApplied[n]]
    /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,log,commitIndex,lastApplied,leaderId,
                    nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                    prevoteGranted,voteGranted,snapshotIndex,snapshotTerm >>

SnapshotEnd ==
  \E n \in Members :
    /\ snapshotInProgress[n]
    /\ snapshotTarget[n] >= snapshotIndex[n]
    /\ LET tgt == snapshotTarget[n] IN
       /\ snapshotIndex' = [snapshotIndex EXCEPT ![n] = tgt]
       /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = TermAt(n, tgt)]
       /\ log' =
            [log EXCEPT ![n] =
               IF tgt < snapshotIndex[n] + 1 THEN log[n]
               ELSE
                 LET keepFrom == tgt + 1 IN
                 IF keepFrom > GlobalLastIndex(n) THEN << >>
                 ELSE SubSeq(log[n], LocalPos(n, keepFrom), LenLog(n))]
       /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
       /\ UNCHANGED << Members,Voters,state,currentTerm,votedFor,commitIndex,lastApplied,leaderId,
                       nextIndex,matchIndex,electionTimer,electionTimeout,requestTimer,messages,
                       prevoteGranted,voteGranted,snapshotTarget >>

PeriodicApply ==
  \E n \in Members :
    /\ lastApplied[n] < commitIndex[n]
    /\ ApplyConfigChange

Next ==
  \/ BecomeFollower(\E n \in Members : n)
  \/ BecomePreCandidate(\E n \in Members : n)
  \/ BecomeCandidate(\E n \in Members : n)
  \/ BecomeLeader(\E n \in Members : n)
  \/ RecvRequestVote
  \/ RecvRequestVoteResponse
  \/ RecvAppendEntries
  \/ RecvAppendEntriesResponse
  \/ SendAppendEntries
  \/ SendHeartbeat
  \/ LogCommit
  \/ LogAppend
  \/ LogDelete
  \/ PeriodicElectionTimeout
  \/ PeriodicHeartbeat
  \/ ElectionTimeout(\E n \in Members : n)
  \/ ElectionTickAndTrigger
  \/ RecvSnapshot
  \/ RecvSnapshotResponse
  \/ SnapshotBegin
  \/ SnapshotEnd
  \/ ApplyConfigChange
  \/ AddNode
  \/ RemoveNode
  \/ PeriodicApply

Spec == Init /\ [][Next]_Vars

(*
Minimal fixes:
- Converted invalid in-action uses of "==" for local bindings to proper LET ... IN forms.
  Specifically wrapped:
    messages1 == messages \ {m}
    messages0 == messages \ {m}
    leaderId1 == leaderId
  with LET-bindings in RecvRequestVote, RecvRequestVoteResponse, RecvAppendEntries, and RecvSnapshot.
- Preserved all original logic and structure; no semantic changes.
- Prior minimal fix retained: EXCEPT does not support "\in" – kept CHOOSE form for electionTimeout'.
*)

====