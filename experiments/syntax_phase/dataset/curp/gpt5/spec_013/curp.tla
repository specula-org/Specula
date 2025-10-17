---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    REPLICAS,
    COMMANDS,
    KEYSET,
    Keys

VARIABLES
    leader,
    term,
    SpecPool,
    UCPool,
    Log,
    ReplicatedBy,
    Committed,
    Pending,
    UseFast,
    ERReady,
    ConflictL,
    FollowerAcks,
    RespStatus,
    Applied

vars == << leader, term, SpecPool, UCPool, Log, ReplicatedBy, Committed, Pending, UseFast, ERReady, ConflictL, FollowerAcks, RespStatus, Applied >>

N == Cardinality(REPLICAS)
Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

RespNone == "None"
RespER == "ER"
RespERASR == "ER_ASR"

Range(f) == { f[x] : x \in DOMAIN f }

KeysConflict(c1, c2) == (Keys[c1] \cap Keys[c2]) # {}

ConflictsWithSet(cmd, S) == \E x \in S : KeysConflict(cmd, x)

LogLen == Len(Log)

LogCmd(i) == Log[i].cmd
LogTerm(i) == Log[i].term
LogCommitted(i) == Log[i].committed

InLog(cmd) == \E i \in 1..LogLen : LogCmd(i) = cmd

UncommittedCmdsOf(log) ==
    { log[i].cmd : i \in 1..Len(log) /\ ~log[i].committed }

SeqFromSet(S) ==
    CHOOSE s \in Seq(S) : Len(s) = Cardinality(S) /\ Range(s) = S

Init ==
    /\ leader \in REPLICAS
    /\ term = 0
    /\ SpecPool \in [REPLICAS -> SUBSET COMMANDS]
    /\ SpecPool = [r \in REPLICAS |-> {}]
    /\ UCPool \in [REPLICAS -> SUBSET COMMANDS]
    /\ UCPool = [r \in REPLICAS |-> {}]
    /\ Log = << >>
    /\ ReplicatedBy = << >>
    /\ Committed \subseteq COMMANDS
    /\ Committed = {}
    /\ Pending \subseteq COMMANDS
    /\ Pending = {}
    /\ UseFast \in [COMMANDS -> BOOLEAN]
    /\ UseFast = [c \in COMMANDS |-> FALSE]
    /\ ERReady \in [COMMANDS -> BOOLEAN]
    /\ ERReady = [c \in COMMANDS |-> FALSE]
    /\ ConflictL \in [COMMANDS -> BOOLEAN]
    /\ ConflictL = [c \in COMMANDS |-> FALSE]
    /\ FollowerAcks \in [COMMANDS -> Nat]
    /\ FollowerAcks = [c \in COMMANDS |-> 0]
    /\ RespStatus \in [COMMANDS -> {RespNone, RespER, RespERASR}]
    /\ RespStatus = [c \in COMMANDS |-> RespNone]
    /\ Applied \in [REPLICAS -> SUBSET COMMANDS]
    /\ Applied = [r \in REPLICAS |-> {}]

Propose(cmd) ==
    /\ cmd \in COMMANDS
    /\ cmd \notin Pending
    /\ RespStatus[cmd] = RespNone
    /\ LET uf == CHOOSE b \in BOOLEAN : TRUE IN
        /\ Pending' = Pending \cup {cmd}
        /\ UseFast' = [UseFast EXCEPT ![cmd] = uf]
        /\ FollowerAcks' = [FollowerAcks EXCEPT ![cmd] = 0]
        /\ ConflictL' = [ConflictL EXCEPT ![cmd] = FALSE]
        /\ ERReady' = [ERReady EXCEPT ![cmd] = FALSE]
        /\ UNCHANGED << leader, term, SpecPool, UCPool, Log, ReplicatedBy, Committed, RespStatus, Applied >>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in Pending
    /\ LET sp == SpecPool[leader]
           uc == UCPool[leader]
           conflict == ConflictsWithSet(cmd, sp \cup uc)
       IN
       /\ IF ~conflict /\ ~InLog(cmd) /\ cmd \notin sp /\ cmd \notin uc
             THEN
                 /\ SpecPool' = [SpecPool EXCEPT ![leader] = @ \cup {cmd}]
                 /\ UCPool' = [UCPool EXCEPT ![leader] = @ \cup {cmd}]
                 /\ Log' = Append(Log, [cmd |-> cmd, term |-> term, committed |-> FALSE])
                 /\ ReplicatedBy' = Append(ReplicatedBy, {leader})
             ELSE
                 /\ UNCHANGED << SpecPool, UCPool, Log, ReplicatedBy >>
       /\ ConflictL' = [ConflictL EXCEPT ![cmd] = conflict]
       /\ ERReady' = [ERReady EXCEPT ![cmd] = TRUE]
       /\ UNCHANGED << leader, term, Committed, Pending, UseFast, FollowerAcks, RespStatus, Applied >>

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in REPLICAS
    /\ r # leader
    /\ cmd \in Pending
    /\ LET sp == SpecPool[r]
           conflict == ConflictsWithSet(cmd, sp)
       IN
       /\ ~conflict
       /\ cmd \notin sp
       /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \cup {cmd}]
       /\ FollowerAcks' = [FollowerAcks EXCEPT ![cmd] = @ + 1]
       /\ UNCHANGED << leader, term, UCPool, Log, ReplicatedBy, Committed, Pending, UseFast, ERReady, ConflictL, RespStatus, Applied >>

DeliverFastResp(cmd) ==
    /\ cmd \in Pending
    /\ UseFast[cmd]
    /\ ERReady[cmd]
    /\ ~ConflictL[cmd]
    /\ FollowerAcks[cmd] >= (SuperQuorum(N) - 1)
    /\ RespStatus[cmd] = RespNone
    /\ RespStatus' = [RespStatus EXCEPT ![cmd] = RespER]
    /\ UNCHANGED << leader, term, SpecPool, UCPool, Log, ReplicatedBy, Committed, Pending, UseFast, ERReady, ConflictL, FollowerAcks, Applied >>

Commit ==
    /\ LogLen >= 1
    /\ \E i \in 1..LogLen :
        /\ ~LogCommitted(i)
        /\ LogTerm(i) = term
        /\ \E add \in SUBSET REPLICAS :
            /\ Cardinality(ReplicatedBy[i] \cup add) >= Quorum(N)
            /\ LET newEntry == [Log[i] EXCEPT !.committed = TRUE] IN
               /\ Log' = [Log EXCEPT ![i] = newEntry]
               /\ ReplicatedBy' = [ReplicatedBy EXCEPT ![i] = (ReplicatedBy[i] \cup add)]
               /\ Committed' = Committed \cup {LogCmd(i)}
               /\ UNCHANGED << leader, term, SpecPool, UCPool, Pending, UseFast, ERReady, ConflictL, FollowerAcks, RespStatus, Applied >>

ProcessCommitMsg(r, cmd) ==
    /\ r \in REPLICAS
    /\ cmd \in Committed
    /\ cmd \notin Applied[r]
    /\ Applied' = [Applied EXCEPT ![r] = @ \cup {cmd}]
    /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \ {cmd}]
    /\ UCPool' = [UCPool EXCEPT ![r] = @ \ {cmd}]
    /\ RespStatus' = [RespStatus EXCEPT ![cmd] = RespERASR]
    /\ UNCHANGED << leader, term, Log, ReplicatedBy, Committed, Pending, UseFast, ERReady, ConflictL, FollowerAcks >>

LeaderChange(l) ==
    /\ l \in REPLICAS
    /\ LET Q == CHOOSE q \in SUBSET REPLICAS : Cardinality(q) >= Quorum(N)
           counts(cmd) == Cardinality({ r \in Q : cmd \in SpecPool[r] })
           inLogSet == { Log[i].cmd : i \in 1..LogLen }
           recSet == { c \in COMMANDS :
                          counts(c) >= RecoverQuorum(N)
                          /\ c \notin inLogSet }
           s == SeqFromSet(recSet)
           newLen == LogLen + Len(s)
           newLog ==
             [ i \in 1..newLen |->
                 IF i <= LogLen THEN Log[i]
                 ELSE [ cmd |-> s[i - LogLen], term |-> term + 1, committed |-> FALSE ] ]
           newRep ==
             [ i \in 1..newLen |->
                 IF i <= Len(ReplicatedBy) THEN ReplicatedBy[i]
                 ELSE Q \cup {l} ]
           newUCLdr == UncommittedCmdsOf(newLog)
       IN
       /\ leader' = l
       /\ term' = term + 1
       /\ Log' = newLog
       /\ ReplicatedBy' = newRep
       /\ SpecPool' = [SpecPool EXCEPT ![l] = @ \cup recSet]
       /\ UCPool' = [UCPool EXCEPT ![l] = newUCLdr]
       /\ UNCHANGED << Committed, Pending, UseFast, ERReady, ConflictL, FollowerAcks, RespStatus, Applied >>

Next ==
    \/ \E cmd \in COMMANDS : Propose(cmd)
    \/ \E cmd \in COMMANDS : ProcessProposeLeader(leader, cmd)
    \/ \E r \in REPLICAS, cmd \in COMMANDS : ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in COMMANDS : DeliverFastResp(cmd)
    \/ Commit
    \/ \E r \in REPLICAS, cmd \in COMMANDS : ProcessCommitMsg(r, cmd)
    \/ \E l \in REPLICAS : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====