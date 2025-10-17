---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS AllNodes, Emin, Emax, HB, Nil

VARIABLES
  Nodes,
  Voters,
  State,
  Term,
  VotedFor,
  Log,
  CommitIndex,
  LastApplied,
  Leader,
  NextIndex,
  MatchIndex,
  ElectionTimeout,
  Elapsed,
  HeartbeatElapsed,
  Msgs,
  SnapshotLastIndex,
  SnapshotLastTerm,
  SnapshotInProgress,
  SnapPendingIndex,
  SnapPendingTerm,
  PreVotes,
  CandVotes

vars == <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,HeartbeatElapsed,Msgs,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes>>

NodeStates == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}

EntryTypes == {"normal","noop","addNode","removeNode"}

Entry(e) == e \in [term: Nat, type: EntryTypes, node: AllNodes \cup {Nil}]

MessageTypes == {"RVReq","RVResp","AEReq","AEResp"}

Message(msg) ==
  msg \in
    [type: MessageTypes,
     from: AllNodes, to: AllNodes,
     term: Nat,
     prevote: BOOLEAN,
     requestTerm: Nat,
     voteGranted: BOOLEAN,
     lastLogIndex: Nat,
     lastLogTerm: Nat,
     leaderCommit: Nat,
     prevLogIndex: Nat,
     prevLogTerm: Nat,
     entries: Seq([term: Nat, type: EntryTypes, node: AllNodes \cup {Nil}]),
     success: BOOLEAN,
     matchIndex: Nat]

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

TypeOK ==
  /\ Nodes \subseteq AllNodes /\ Voters \subseteq Nodes
  /\ State \in [AllNodes -> NodeStates]
  /\ Term \in [AllNodes -> Nat]
  /\ VotedFor \in [AllNodes -> (AllNodes \cup {Nil})]
  /\ Log \in [AllNodes -> Seq([term: Nat, type: EntryTypes, node: AllNodes \cup {Nil}])]
  /\ CommitIndex \in [AllNodes -> Nat]
  /\ LastApplied \in [AllNodes -> Nat]
  /\ Leader \in [AllNodes -> (AllNodes \cup {Nil})]
  /\ NextIndex \in [AllNodes -> [AllNodes -> Nat]]
  /\ MatchIndex \in [AllNodes -> [AllNodes -> Nat]]
  /\ ElectionTimeout \in [AllNodes -> Nat]
  /\ Elapsed \in [AllNodes -> Nat]
  /\ HeartbeatElapsed \in [AllNodes -> Nat]
  /\ SnapshotLastIndex \in [AllNodes -> Nat]
  /\ SnapshotLastTerm \in [AllNodes -> Nat]
  /\ SnapshotInProgress \in [AllNodes -> BOOLEAN]
  /\ SnapPendingIndex \in [AllNodes -> Nat]
  /\ SnapPendingTerm \in [AllNodes -> Nat]
  /\ PreVotes \in [AllNodes -> SUBSET AllNodes]
  /\ CandVotes \in [AllNodes -> SUBSET AllNodes]
  /\ \A n \in AllNodes: ElectionTimeout[n] \in (Emin..Emax) \cup {0}
  /\ \A n \in AllNodes: Elapsed[n] \in Nat /\ HeartbeatElapsed[n] \in Nat
  /\ \A n \in AllNodes: CommitIndex[n] <= SnapshotLastIndex[n] + Len(Log[n])
  /\ \A n \in AllNodes: LastApplied[n] <= CommitIndex[n]
  /\ \A n \in AllNodes: SnapshotLastIndex[n] = 0 => SnapshotLastTerm[n] = 0
  /\ \A n \in AllNodes: NextIndex[n] \in [AllNodes -> Nat] /\ MatchIndex[n] \in [AllNodes -> Nat]
  /\ Msgs \subseteq
      { m \in
          [type: MessageTypes,
           from: AllNodes, to: AllNodes,
           term: Nat,
           prevote: BOOLEAN,
           requestTerm: Nat,
           voteGranted: BOOLEAN,
           lastLogIndex: Nat,
           lastLogTerm: Nat,
           leaderCommit: Nat,
           prevLogIndex: Nat,
           prevLogTerm: Nat,
           entries: Seq([term: Nat, type: EntryTypes, node: AllNodes \cup {Nil}]),
           success: BOOLEAN,
           matchIndex: Nat] : TRUE }

LastIndex(n) == SnapshotLastIndex[n] + Len(Log[n])

LastLogTerm(n) ==
  IF Len(Log[n]) = 0 THEN SnapshotLastTerm[n] ELSE Log[n][Len(Log[n])].term

EntryTermAt(n,i) ==
  IF i = 0 THEN 0
  ELSE IF i = SnapshotLastIndex[n] THEN SnapshotLastTerm[n]
  ELSE IF i > SnapshotLastIndex[n] /\ i <= LastIndex(n)
       THEN Log[n][i - SnapshotLastIndex[n]].term
       ELSE 0

InLog(n,i) == i > SnapshotLastIndex[n] /\ i <= LastIndex(n)

DeleteSuffixFrom(n, i) ==
  [Log EXCEPT ![n] =
     IF i <= SnapshotLastIndex[n] + 1 THEN <<>>
     ELSE SubSeq(Log[n], 1, i - SnapshotLastIndex[n] - 1)]

AppendEntry(n, e) ==
  /\ Entry(e)
  /\ Log' = [Log EXCEPT ![n] = Append(Log[n], e)]

ResetTimeout(n) ==
  /\ \E t \in Emin..Emax: ElectionTimeout' = [ElectionTimeout EXCEPT ![n] = t]
  /\ Elapsed' = [Elapsed EXCEPT ![n] = 0]
  /\ UNCHANGED HeartbeatElapsed

Majority(S) == 2 * Cardinality(S \cap Voters) > Cardinality(Voters)

Init ==
  /\ Nodes \in SUBSET AllNodes /\ Nodes # {}
  /\ Voters = Nodes
  /\ State = [n \in AllNodes |-> "FOLLOWER"]
  /\ Term = [n \in AllNodes |-> 0]
  /\ VotedFor = [n \in AllNodes |-> Nil]
  /\ Log = [n \in AllNodes |-> <<>>]
  /\ CommitIndex = [n \in AllNodes |-> 0]
  /\ LastApplied = [n \in AllNodes |-> 0]
  /\ Leader = [n \in AllNodes |-> Nil]
  /\ NextIndex = [n \in AllNodes |-> [m \in AllNodes |-> 1]]
  /\ MatchIndex = [n \in AllNodes |-> [m \in AllNodes |-> 0]]
  /\ ElectionTimeout \in [AllNodes -> Emin..Emax]
  /\ Elapsed = [n \in AllNodes |-> 0]
  /\ HeartbeatElapsed = [n \in AllNodes |-> 0]
  /\ SnapshotLastIndex = [n \in AllNodes |-> 0]
  /\ SnapshotLastTerm = [n \in AllNodes |-> 0]
  /\ SnapshotInProgress = [n \in AllNodes |-> FALSE]
  /\ SnapPendingIndex = [n \in AllNodes |-> 0]
  /\ SnapPendingTerm = [n \in AllNodes |-> 0]
  /\ PreVotes = [n \in AllNodes |-> {}]
  /\ CandVotes = [n \in AllNodes |-> {}]
  /\ Msgs = {}
  /\ TypeOK

UpToDate(cand, me) ==
  \/ LastLogTerm(cand) > LastLogTerm(me)
  \/ /\ LastLogTerm(cand) = LastLogTerm(me)
     /\ LastIndex(cand) >= LastIndex(me)

ElectionTimeoutAction(n) ==
  /\ n \in Nodes /\ State[n] # "LEADER"
  /\ Elapsed[n] >= ElectionTimeout[n]
  /\ ElectionStart(n)

ElectionStart(n) ==
  /\ BecomePreCandidate(n)

BecomePreCandidate(n) ==
  /\ State[n] # "LEADER"
  /\ State' = [State EXCEPT ![n] = "PRECANDIDATE"]
  /\ Leader' = [Leader EXCEPT ![n] = Nil]
  /\ PreVotes' = [PreVotes EXCEPT ![n] = {}]
  /\ CandVotes' = [CandVotes EXCEPT ![n] = {}]
  /\ Msgs' =
       Msgs \cup
       { [type |-> "RVReq",
          from |-> n, to |-> v, term |-> Term[n] + 1, prevote |-> TRUE,
          requestTerm |-> 0, voteGranted |-> FALSE,
          lastLogIndex |-> LastIndex(n), lastLogTerm |-> LastLogTerm(n),
          leaderCommit |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0,
          entries |-> <<>>, success |-> FALSE, matchIndex |-> 0]
         : v \in Voters \ {n} }
  /\ ResetTimeout(n)
  /\ UNCHANGED <<Nodes,Voters,Term,VotedFor,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,HeartbeatElapsed>>

BecomeCandidate(n) ==
  /\ n \in Nodes
  /\ State[n] \in {"PRECANDIDATE","FOLLOWER","CANDIDATE"}
  /\ State' = [State EXCEPT ![n] = "CANDIDATE"]
  /\ Term' = [Term EXCEPT ![n] = Term[n] + 1]
  /\ VotedFor' = [VotedFor EXCEPT ![n] = n]
  /\ CandVotes' = [CandVotes EXCEPT ![n] = {n}]
  /\ PreVotes' = [PreVotes EXCEPT ![n] = {}]
  /\ Msgs' =
       Msgs \cup
       { [type |-> "RVReq",
          from |-> n, to |-> v, term |-> Term[n] + 1, prevote |-> FALSE,
          requestTerm |-> 0, voteGranted |-> FALSE,
          lastLogIndex |-> LastIndex(n), lastLogTerm |-> LastLogTerm(n),
          leaderCommit |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0,
          entries |-> <<>>, success |-> FALSE, matchIndex |-> 0]
         : v \in Voters \ {n} }
  /\ ResetTimeout(n)
  /\ UNCHANGED <<Nodes,Voters,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,HeartbeatElapsed>>

BecomeLeader(n) ==
  /\ n \in Nodes
  /\ State[n] = "CANDIDATE"
  /\ Majority(CandVotes[n])
  /\ LET newLast == LastIndex(n) + 1 IN
     /\ Log' = [Log EXCEPT ![n] = Append(Log[n], [term |-> Term[n], type |-> "noop", node |-> Nil])]
     /\ State' = [State EXCEPT ![n] = "LEADER"]
     /\ Leader' = [Leader EXCEPT ![n] = n]
     /\ NextIndex' = [NextIndex EXCEPT ![n] = [m \in AllNodes |-> newLast + 1]]
     /\ MatchIndex' = [MatchIndex EXCEPT ![n] = [m \in AllNodes |-> IF m = n THEN newLast ELSE 0]]
     /\ HeartbeatElapsed' = [HeartbeatElapsed EXCEPT ![n] = 0]
     /\ UNCHANGED <<Nodes,Voters,Term,VotedFor,CommitIndex,LastApplied,ElectionTimeout,Elapsed,Msgs,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes>>

BecomeFollower(n, t) ==
  /\ n \in Nodes
  /\ State' = [State EXCEPT ![n] = "FOLLOWER"]
  /\ Term' = [Term EXCEPT ![n] = t]
  /\ VotedFor' = [VotedFor EXCEPT ![n] = Nil]
  /\ Leader' = [Leader EXCEPT ![n] = Nil]
  /\ ResetTimeout(n)
  /\ UNCHANGED <<Nodes,Voters,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,Msgs,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

SendRequestVote(n, to, prev) ==
  /\ n \in Nodes /\ to \in Voters \ {n}
  /\ State[n] \in {"PRECANDIDATE","CANDIDATE"}
  /\ Msgs' = Msgs \cup {
      [type |-> "RVReq",
       from |-> n, to |-> to,
       term |-> IF prev THEN Term[n] + 1 ELSE Term[n],
       prevote |-> prev, requestTerm |-> 0, voteGranted |-> FALSE,
       lastLogIndex |-> LastIndex(n),
       lastLogTerm |-> LastLogTerm(n),
       leaderCommit |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0,
       entries |-> <<>>, success |-> FALSE, matchIndex |-> 0] }
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

RecvRequestVote(self, msg) ==
  /\ self \in Nodes
  /\ msg \in Msgs /\ msg.type = "RVReq" /\ msg.to = self
  /\ LET msgs1 == Msgs \ {msg} IN
     IF msg.term < Term[self] THEN
       /\ Msgs' = msgs1 \cup {
           [type |-> "RVResp", from |-> self, to |-> msg.from,
            term |-> Term[self], prevote |-> msg.prevote,
            requestTerm |-> msg.term, voteGranted |-> FALSE,
            lastLogIndex |-> 0, lastLogTerm |-> 0,
            leaderCommit |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0,
            entries |-> <<>>, success |-> FALSE, matchIndex |-> 0] }
       /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Leader,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>
     ELSE
       /\ LET
            newTerm == IF msg.prevote THEN Term[self] ELSE Max(Term[self], msg.term)
            st1 == IF ~msg.prevote /\ msg.term >= Term[self] THEN [State EXCEPT ![self] = "FOLLOWER"] ELSE State
            trm1 == [Term EXCEPT ![self] = newTerm]
            vf1 == IF ~msg.prevote /\ msg.term > Term[self] THEN [VotedFor EXCEPT ![self] = Nil] ELSE VotedFor
            canGrant ==
               /\ (newTerm = msg.term \/ msg.prevote)
               /\ (vf1[self] = Nil \/ vf1[self] = msg.from \/ msg.prevote)
               /\ UpToDate(msg.from, self)
               /\ (msg.prevote => (Leader[self] \in {Nil, msg.from} \/ Elapsed[self] >= ElectionTimeout[self]))
            voteGranted == canGrant
            vf2 == IF ~msg.prevote /\ voteGranted THEN [vf1 EXCEPT ![self] = msg.from] ELSE vf1
            rsp ==
              [type |-> "RVResp", from |-> self, to |-> msg.from,
               term |-> newTerm, prevote |-> msg.prevote,
               requestTerm |-> msg.term, voteGranted |-> voteGranted,
               lastLogIndex |-> 0, lastLogTerm |-> 0,
               leaderCommit |-> 0, prevLogIndex |-> 0, prevLogTerm |-> 0,
               entries |-> <<>>, success |-> FALSE, matchIndex |-> 0]
          IN
            /\ Msgs' = msgs1 \cup {rsp}
            /\ State' = st1
            /\ Term' = trm1
            /\ VotedFor' = vf2
            /\ Leader' = IF ~msg.prevote THEN [Leader EXCEPT ![self] = Nil] ELSE Leader
            /\ ResetTimeout(self)
            /\ UNCHANGED <<Nodes,Voters,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

RecvRequestVoteResponse(self, msg) ==
  /\ self \in Nodes
  /\ msg \in Msgs /\ msg.type = "RVResp" /\ msg.to = self
  /\ Msgs' = Msgs \ {msg}
  /\ IF msg.term > Term[self]
     THEN
       /\ State' = [State EXCEPT ![self] = "FOLLOWER"]
       /\ Term' = [Term EXCEPT ![self] = msg.term]
       /\ VotedFor' = [VotedFor EXCEPT ![self] = Nil]
       /\ Leader' = [Leader EXCEPT ![self] = Nil]
       /\ UNCHANGED <<Nodes,Voters,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>
     ELSE
       /\ IF msg.prevote
          THEN
            /\ PreVotes' =
                 [PreVotes EXCEPT ![self] =
                    IF State[self] = "PRECANDIDATE" /\ msg.requestTerm = Term[self] + 1 /\ msg.voteGranted
                    THEN PreVotes[self] \cup {msg.from} ELSE PreVotes[self]]
            /\ CandVotes' = CandVotes
          ELSE
            /\ CandVotes' =
                 [CandVotes EXCEPT ![self] =
                    IF State[self] = "CANDIDATE" /\ msg.requestTerm = Term[self] /\ msg.voteGranted
                    THEN CandVotes[self] \cup {msg.from} ELSE CandVotes[self]]
            /\ PreVotes' = PreVotes
       /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,HeartbeatElapsed>>

PromoteOnPreVoteMajority(n) ==
  /\ n \in Nodes
  /\ State[n] = "PRECANDIDATE" /\ Majority(PreVotes[n])
  /\ BecomeCandidate(n)

SendAppendEntries(l, f) ==
  /\ l \in Nodes /\ f \in Nodes /\ f # l
  /\ State[l] = "LEADER"
  /\ LET
       LetNext == Max(SnapshotLastIndex[l] + 1, NextIndex[l][f])
       prevIdx == LetNext - 1
       prevTerm == EntryTermAt(l, prevIdx)
       pos == Max(1, LetNext - SnapshotLastIndex[l])
       ents == IF LetNext <= LastIndex(l) THEN SubSeq(Log[l], pos, Len(Log[l])) ELSE <<>>
     IN
       /\ Msgs' = Msgs \cup {
           [type |-> "AEReq", from |-> l, to |-> f, term |-> Term[l],
            prevote |-> FALSE, requestTerm |-> 0, voteGranted |-> FALSE,
            lastLogIndex |-> 0, lastLogTerm |-> 0,
            leaderCommit |-> CommitIndex[l],
            prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
            entries |-> ents, success |-> FALSE, matchIndex |-> 0] }
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

SendHeartbeat(l, f) ==
  /\ l \in Nodes /\ f \in Nodes /\ f # l
  /\ State[l] = "LEADER"
  /\ Msgs' = Msgs \cup {
        [type |-> "AEReq", from |-> l, to |-> f, term |-> Term[l],
         prevote |-> FALSE, requestTerm |-> 0, voteGranted |-> FALSE,
         lastLogIndex |-> 0, lastLogTerm |-> 0,
         leaderCommit |-> CommitIndex[l],
         prevLogIndex |-> LastIndex(l), prevLogTerm |-> LastLogTerm(l),
         entries |-> <<>>, success |-> FALSE, matchIndex |-> 0] }
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

RecvAppendEntries(self, msg) ==
  /\ self \in Nodes
  /\ msg \in Msgs /\ msg.type = "AEReq" /\ msg.to = self
  /\ LET msgs1 == Msgs \ {msg} IN
     IF msg.term < Term[self] THEN
       /\ Msgs' = msgs1 \cup {
           [type |-> "AEResp", from |-> self, to |-> msg.from, term |-> Term[self],
            prevote |-> FALSE, requestTerm |-> 0, voteGranted |-> FALSE,
            lastLogIndex |-> 0, lastLogTerm |-> 0,
            leaderCommit |-> 0,
            prevLogIndex |-> 0, prevLogTerm |-> 0,
            entries |-> <<>>, success |-> FALSE, matchIndex |-> LastIndex(self)] }
       /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Leader,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>
     ELSE
       /\ LET
            st1 == [State EXCEPT ![self] = "FOLLOWER"]
            trm1 == [Term EXCEPT ![self] = Max(Term[self], msg.term)]
            vf1 == IF msg.term > Term[self] THEN [VotedFor EXCEPT ![self] = Nil] ELSE VotedFor
            leader1 == [Leader EXCEPT ![self] = msg.from]
            PrevOK ==
              \/ msg.prevLogIndex = SnapshotLastIndex[self] /\ msg.prevLogTerm = SnapshotLastTerm[self]
              \/ /\ InLog(self, msg.prevLogIndex)
                 /\ EntryTermAt(self, msg.prevLogIndex) = msg.prevLogTerm
            log1 ==
              IF ~PrevOK THEN Log
              ELSE
                IF Len(msg.entries) = 0 THEN Log
                ELSE
                  LET start == msg.prevLogIndex + 1 IN
                  LET k == start - SnapshotLastIndex[self] IN
                  LET conflict ==
                        \E i \in 1..Len(msg.entries):
                          /\ InLog(self, msg.prevLogIndex + i)
                          /\ Log[self][k + i - 1].term # msg.entries[i].term
                  IN
                    IF conflict
                    THEN [Log EXCEPT ![self] = Append(SubSeq(Log[self], 1, k - 1), msg.entries)]
                    ELSE
                      IF start > LastIndex(self)
                      THEN [Log EXCEPT ![self] = Append(Log[self], msg.entries)]
                      ELSE Log
            newLast == SnapshotLastIndex[self] + Len(log1[self])
            commit1 ==
              [CommitIndex EXCEPT ![self] =
                 IF CommitIndex[self] < msg.leaderCommit
                 THEN Min(msg.leaderCommit, newLast)
                 ELSE CommitIndex[self]]
            rsp2 ==
              [type |-> "AEResp", from |-> self, to |-> msg.from, term |-> trm1[self],
               prevote |-> FALSE, requestTerm |-> 0, voteGranted |-> FALSE,
               lastLogIndex |-> 0, lastLogTerm |-> 0, leaderCommit |-> 0,
               prevLogIndex |-> 0, prevLogTerm |-> 0,
               entries |-> <<>>, success |-> PrevOK, matchIndex |-> (IF PrevOK THEN newLast ELSE LastIndex(self))]
          IN
            /\ Msgs' = msgs1 \cup {rsp2}
            /\ Log' = log1
            /\ CommitIndex' = commit1
            /\ State' = st1
            /\ Term' = trm1
            /\ VotedFor' = vf1
            /\ Leader' = leader1
            /\ ResetTimeout(self)
            /\ UNCHANGED <<Nodes,Voters,LastApplied,NextIndex,MatchIndex,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

RecvAppendEntriesResponse(l, msg) ==
  /\ l \in Nodes
  /\ msg \in Msgs /\ msg.type = "AEResp" /\ msg.to = l
  /\ State[l] = "LEADER"
  /\ Msgs' = Msgs \ {msg}
  /\ IF msg.term > Term[l]
     THEN
       /\ State' = [State EXCEPT ![l] = "FOLLOWER"]
       /\ Term' = [Term EXCEPT ![l] = msg.term]
       /\ VotedFor' = [VotedFor EXCEPT ![l] = Nil]
       /\ Leader' = [Leader EXCEPT ![l] = Nil]
       /\ UNCHANGED <<Nodes,Voters,Log,CommitIndex,LastApplied,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>
     ELSE
       /\ IF msg.success
          THEN
            /\ MatchIndex' = [MatchIndex EXCEPT ![l][msg.from] = msg.matchIndex]
            /\ NextIndex' = [NextIndex EXCEPT ![l][msg.from] = Max(SnapshotLastIndex[l] + 1, msg.matchIndex + 1)]
          ELSE
            /\ MatchIndex' = MatchIndex
            /\ NextIndex' = [NextIndex EXCEPT ![l][msg.from] = Max(SnapshotLastIndex[l] + 1, NextIndex[l][msg.from] - 1)]
       /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,ElectionTimeout,Elapsed,Leader,HeartbeatElapsed>>

LogCommit(l) ==
  /\ l \in Nodes
  /\ State[l] = "LEADER"
  /\ \E idx \in ({MatchIndex[l][v] : v \in Voters} \cup {LastIndex(l)}):
       /\ idx > CommitIndex[l]
       /\ \A v \in Voters: MatchIndex[l][v] >= idx \/ v = l
       /\ EntryTermAt(l, idx) = Term[l]
       /\ CommitIndex' = [CommitIndex EXCEPT ![l] = idx]
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,LastApplied,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

LogAppend(l, e) ==
  /\ l \in Nodes /\ State[l] = "LEADER"
  /\ Entry(e) /\ e.term = Term[l]
  /\ Log' = [Log EXCEPT ![l] = Append(Log[l], e)]
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

LogDelete(self, i) ==
  /\ self \in Nodes
  /\ i > SnapshotLastIndex[self] /\ i <= LastIndex(self)
  /\ Log' = DeleteSuffixFrom(self, i)
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

PeriodicElectionTimeout(n) ==
  /\ n \in Nodes /\ State[n] # "LEADER"
  /\ Elapsed' = [Elapsed EXCEPT ![n] = Elapsed[n] + 1]
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

PeriodicHeartbeat(n) ==
  /\ n \in Nodes /\ State[n] = "LEADER"
  /\ LET
       h == [HeartbeatElapsed EXCEPT ![n] = HeartbeatElapsed[n] + 1]
       newHB == IF h[n] >= HB THEN [h EXCEPT ![n] = 0] ELSE h
     IN
       /\ HeartbeatElapsed' = newHB
       /\ IF h[n] >= HB
          THEN
            /\ \E f \in Nodes \ {n}:
                 Msgs' = Msgs \cup {
                   [type |-> "AEReq", from |-> n, to |-> f, term |-> Term[n],
                    prevote |-> FALSE, requestTerm |-> 0, voteGranted |-> FALSE,
                    lastLogIndex |-> 0, lastLogTerm |-> 0,
                    leaderCommit |-> CommitIndex[n],
                    prevLogIndex |-> LastIndex(n), prevLogTerm |-> LastLogTerm(n),
                    entries |-> <<>>, success |-> FALSE, matchIndex |-> 0] }
          ELSE
            /\ Msgs' = Msgs
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes>>

AddNode(l, x) ==
  /\ l \in Nodes /\ State[l] = "LEADER"
  /\ x \in AllNodes \ Nodes
  /\ LogAppend(l, [term |-> Term[l], type |-> "addNode", node |-> x])

RemoveNode(l, x) ==
  /\ l \in Nodes /\ State[l] = "LEADER"
  /\ x \in Nodes /\ x # l
  /\ LogAppend(l, [term |-> Term[l], type |-> "removeNode", node |-> x])

ApplyConfigChange(n) ==
  /\ n \in Nodes
  /\ LastApplied[n] < CommitIndex[n]
  /\ LET
       idx == LastApplied[n] + 1
       e == Log[n][idx - SnapshotLastIndex[n]]
     IN
       /\ InLog(n, idx)
       /\ e.type \in {"addNode","removeNode"}
       /\ LastApplied' = [LastApplied EXCEPT ![n] = idx]
       /\ IF e.type = "addNode"
          THEN /\ Nodes' = Nodes \cup {e.node}
               /\ Voters' = Voters \cup {e.node}
          ELSE /\ Nodes' = Nodes \ {e.node}
               /\ Voters' = Voters \ {e.node}
       /\ UNCHANGED <<State,Term,VotedFor,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,HeartbeatElapsed>>
       /\ Log' = Log
       /\ CommitIndex' = CommitIndex
       /\ SnapshotLastIndex' = SnapshotLastIndex
       /\ SnapshotLastTerm' = SnapshotLastTerm
       /\ SnapshotInProgress' = SnapshotInProgress
       /\ SnapPendingIndex' = SnapPendingIndex
       /\ SnapPendingTerm' = SnapPendingTerm
       /\ PreVotes' = PreVotes
       /\ CandVotes' = CandVotes

ApplyNormalOrNoop(n) ==
  /\ n \in Nodes
  /\ LastApplied[n] < CommitIndex[n]
  /\ LET
       idx == LastApplied[n] + 1
       e == Log[n][idx - SnapshotLastIndex[n]]
     IN
       /\ InLog(n, idx)
       /\ e.type \in {"normal","noop"}
       /\ LastApplied' = [LastApplied EXCEPT ![n] = idx]
       /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

SnapshotBegin(n) ==
  /\ n \in Nodes
  /\ ~SnapshotInProgress[n]
  /\ LastApplied[n] > SnapshotLastIndex[n]
  /\ SnapshotInProgress' = [SnapshotInProgress EXCEPT ![n] = TRUE]
  /\ SnapPendingIndex' = [SnapPendingIndex EXCEPT ![n] = LastApplied[n]]
  /\ SnapPendingTerm' = [SnapPendingTerm EXCEPT ![n] = EntryTermAt(n, LastApplied[n])]
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,PreVotes,CandVotes,HeartbeatElapsed>>

SnapshotEnd(n) ==
  /\ n \in Nodes
  /\ SnapshotInProgress[n]
  /\ SnapshotLastIndex' = [SnapshotLastIndex EXCEPT ![n] = SnapPendingIndex[n]]
  /\ SnapshotLastTerm' = [SnapshotLastTerm EXCEPT ![n] = SnapPendingTerm[n]]
  /\ Log' =
       [Log EXCEPT ![n] =
          IF SnapPendingIndex[n] <= SnapshotLastIndex[n]
          THEN Log[n]
          ELSE
            LET cut == SnapPendingIndex[n] - SnapshotLastIndex[n]
            IN IF cut >= Len(Log[n]) THEN <<>> ELSE SubSeq(Log[n], cut + 1, Len(Log[n]))]
  /\ SnapshotInProgress' = [SnapshotInProgress EXCEPT ![n] = FALSE]
  /\ SnapPendingIndex' = [SnapPendingIndex EXCEPT ![n] = 0]
  /\ SnapPendingTerm' = [SnapPendingTerm EXCEPT ![n] = 0]
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,Msgs,ElectionTimeout,Elapsed,PreVotes,CandVotes,HeartbeatElapsed>>

SendHeartbeatAll(n) ==
  /\ n \in Nodes /\ State[n] = "LEADER"
  /\ Msgs' =
       Msgs \cup
       { [type |-> "AEReq", from |-> n, to |-> f, term |-> Term[n],
          prevote |-> FALSE, requestTerm |-> 0, voteGranted |-> FALSE,
          lastLogIndex |-> 0, lastLogTerm |-> 0,
          leaderCommit |-> CommitIndex[n],
          prevLogIndex |-> LastIndex(n), prevLogTerm |-> LastLogTerm(n),
          entries |-> <<>>, success |-> FALSE, matchIndex |-> 0] : f \in Nodes \ {n} }
  /\ UNCHANGED <<Nodes,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,Leader,NextIndex,MatchIndex,ElectionTimeout,Elapsed,SnapshotLastIndex,SnapshotLastTerm,SnapshotInProgress,SnapPendingIndex,SnapPendingTerm,PreVotes,CandVotes,HeartbeatElapsed>>

ElectionManagement ==
  \E n \in Nodes:
    \/ ElectionTimeoutAction(n)
    \/ PromoteOnPreVoteMajority(n)

LeaderOperations ==
  \E l \in Nodes:
    \/ \E f \in Nodes \ {l}: SendAppendEntries(l, f)
    \/ \E f \in Nodes \ {l}: SendHeartbeat(l, f)
    \/ SendHeartbeatAll(l)

VoteProcessing ==
  \/ \E self \in Nodes, msg \in Msgs: RecvRequestVote(self, msg)
  \/ \E self \in Nodes, msg \in Msgs: RecvRequestVoteResponse(self, msg)

LogReplication ==
  \/ \E self \in Nodes, msg \in Msgs: RecvAppendEntries(self, msg)
  \/ \E l \in Nodes, msg \in Msgs: RecvAppendEntriesResponse(l, msg)

LogManagement ==
  \/ \E l \in Nodes, e \in [term: Nat, type: EntryTypes, node: AllNodes \cup {Nil}]:
       /\ e.type \in {"normal","noop"} /\ LogAppend(l, [term |-> Term[l], type |-> e.type, node |-> e.node])
  \/ \E self \in Nodes, i \in Nat: LogDelete(self, i)
  \/ \E l \in Nodes: LogCommit(l)

PeriodicTasks ==
  \/ \E n \in Nodes: PeriodicElectionTimeout(n)
  \/ \E n \in Nodes: PeriodicHeartbeat(n)

NodeManagement ==
  \/ \E l \in Nodes, x \in AllNodes: AddNode(l, x)
  \/ \E l \in Nodes, x \in AllNodes: RemoveNode(l, x)

SnapshotHandling ==
  \/ \E n \in Nodes: SnapshotBegin(n)
  \/ \E n \in Nodes: SnapshotEnd(n)

Configuration ==
  \/ \E n \in Nodes: ApplyConfigChange(n)

ApplyEntries ==
  \/ \E n \in Nodes: ApplyNormalOrNoop(n)

StateTransitions ==
  \/ \E n \in Nodes: BecomeCandidate(n)
  \/ \E n \in Nodes: BecomeLeader(n)

Next ==
  TypeOK /\
  \/ ElectionManagement
  \/ VoteProcessing
  \/ LogReplication
  \/ LeaderOperations
  \/ LogManagement
  \/ PeriodicTasks
  \/ NodeManagement
  \/ SnapshotHandling
  \/ Configuration
  \/ ApplyEntries
  \/ StateTransitions

Spec == Init /\ [][Next]_vars

====