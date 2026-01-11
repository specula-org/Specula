---- MODULE Tracecurp ----
EXTENDS curp, Json, IOUtils, Sequences, SequencesExt, FiniteSets, TLC

\* Trace validation is designed for BFS.
ASSUME TLCGet("config").mode = "bfs"

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "../harness/traces/trace-1.ndjson"

OriginTraceLog ==
    SelectSeq(ndJsonDeserialize(JsonFile), LAMBDA l: "event" \in DOMAIN l)

TraceLog ==
    TLCEval(
        IF "MAX_TRACE" \in DOMAIN IOEnv
        THEN SubSeq(OriginTraceLog, 1, atoi(IOEnv.MAX_TRACE))
        ELSE OriginTraceLog)

ProgressStride ==
    IF Len(TraceLog) < 100 THEN 1 ELSE Len(TraceLog) \div 100

Range(f) == { f[x] : x \in DOMAIN f }

VARIABLE l
logline == TraceLog[l]

HasUpdate(ops) ==
    /\ Len(ops) = 1
    /\ ops[1].op = "Update"
    /\ ops[1].path = <<>>
    /\ Len(ops[1].args) = 1

UpdateValue(ops) == ops[1].args[1]

HasSpecPool(line) ==
    "spec_pool" \in DOMAIN line \/ "speculativePool" \in DOMAIN line

SpecPoolOps(line) ==
    IF "spec_pool" \in DOMAIN line THEN line.spec_pool ELSE line.speculativePool

SpecPoolValue(line) ==
    UpdateValue(SpecPoolOps(line))

HasUncommitted(line) ==
    "uncommitted_pool" \in DOMAIN line \/ "uncommittedPool" \in DOMAIN line

UncommittedOps(line) ==
    IF "uncommitted_pool" \in DOMAIN line THEN line.uncommitted_pool ELSE line.uncommittedPool

UncommittedValue(line) ==
    UpdateValue(UncommittedOps(line))

HasCommitted(line) ==
    "committedCommands" \in DOMAIN line

CommittedValue(line) ==
    UpdateValue(line.committedCommands)

LeaderValue(line) == UpdateValue(line.leader)
RoleValue(line) == UpdateValue(line.role)
TermValue(line) == UpdateValue(line.term)

CmdsInSeq(seq) == { seq[i] : i \in 1..Len(seq) }

CmdsInPool(pool) ==
    UNION { CmdsInSeq(pool[n]) : n \in DOMAIN pool }

CmdsInLogline(line) ==
    (IF HasSpecPool(line) THEN CmdsInPool(SpecPoolValue(line)) ELSE {})
    \cup (IF HasUncommitted(line) THEN CmdsInSeq(UncommittedValue(line)) ELSE {})
    \cup (IF HasCommitted(line) THEN CmdsInSeq(CommittedValue(line)) ELSE {})

RolesInLogline(line) ==
    IF "role" \in DOMAIN line THEN Range(RoleValue(line)) ELSE {}

TraceServer ==
    TLCEval(FoldSeq(
        LAMBDA x, y:
            y
            \cup (IF "leader" \in DOMAIN x THEN {LeaderValue(x)} ELSE {})
            \cup (IF "spec_pool" \in DOMAIN x THEN DOMAIN UpdateValue(x.spec_pool) ELSE {})
            \cup (IF "speculativePool" \in DOMAIN x THEN DOMAIN UpdateValue(x.speculativePool) ELSE {})
            \cup (IF "role" \in DOMAIN x THEN DOMAIN UpdateValue(x.role) ELSE {}),
        {}, TraceLog))

TraceCmdSet ==
    TLCEval(FoldSeq(LAMBDA x, y: y \cup CmdsInLogline(x), {}, TraceLog))

TraceRoleSet ==
    TLCEval(
        LET roles == FoldSeq(LAMBDA x, y: y \cup RolesInLogline(x), {}, TraceLog)
        IN IF roles = {} THEN {"Leader", "Follower"} ELSE roles
    )

DefaultRole ==
    IF "Follower" \in TraceRoleSet THEN "Follower" ELSE CHOOSE r \in TraceRoleSet: TRUE

TraceInitLeader ==
    IF "leader" \in DOMAIN TraceLog[1] THEN LeaderValue(TraceLog[1])
    ELSE CHOOSE s \in TraceServer: TRUE

TraceInitRole ==
    IF "role" \in DOMAIN TraceLog[1] THEN RoleValue(TraceLog[1])
    ELSE [i \in TraceServer |-> DefaultRole]

TraceInitTerm ==
    IF "term" \in DOMAIN TraceLog[1] THEN TermValue(TraceLog[1]) ELSE 0

TraceInitSpecPool ==
    IF HasSpecPool(TraceLog[1]) THEN SpecPoolValue(TraceLog[1])
    ELSE [i \in TraceServer |-> <<>>]

TraceInitUncommittedPool ==
    IF HasUncommitted(TraceLog[1]) THEN UncommittedValue(TraceLog[1]) ELSE <<>>

TraceInitCommittedCommands ==
    IF HasCommitted(TraceLog[1]) THEN CommittedValue(TraceLog[1]) ELSE <<>>

Prefix(seq, n) ==
    IF n = 0 THEN <<>> ELSE SubSeq(seq, 1, n)

Suffix(seq, n) ==
    IF n = Len(seq) THEN <<>> ELSE SubSeq(seq, n + 1, Len(seq))

InsertCmd(old, new, cmd) ==
    \E i \in 0..Len(old):
        new = Prefix(old, i) \o <<cmd>> \o Suffix(old, i)

RemovePrefix(old, new) ==
    \E k \in 1..Len(old):
        new = Suffix(old, k)

RemoveSuffix(old, new) ==
    \E k \in 1..Len(old):
        new = Prefix(old, Len(old) - k)

RemovePrefixOrSuffix(old, new) ==
    RemovePrefix(old, new) \/ RemoveSuffix(old, new)

SpecPoolInsertAll ==
    \E cmd \in CmdSet:
        \A n \in Server: InsertCmd(spec_pool[n], spec_pool'[n], cmd)

SpecPoolInsertOne ==
    \E n \in Server, cmd \in CmdSet:
        /\ InsertCmd(spec_pool[n], spec_pool'[n], cmd)
        /\ \A m \in Server \ {n}: spec_pool'[m] = spec_pool[m]

SpecPoolRemoveOne ==
    \E n \in Server:
        /\ spec_pool[n] /= <<>>
        /\ RemovePrefixOrSuffix(spec_pool[n], spec_pool'[n])
        /\ \A m \in Server \ {n}: spec_pool'[m] = spec_pool[m]

UncommittedInsertOne ==
    \E cmd \in CmdSet: InsertCmd(uncommitted_pool, uncommitted_pool', cmd)

UncommittedReplaceOne ==
    \E cmd \in CmdSet: uncommitted_pool' = <<cmd>>

CommittedAppendOne ==
    \E cmd \in CmdSet: committed_commands' = Append(committed_commands, cmd)

SpecPoolDomainOK ==
    ~HasSpecPool(logline) \/ DOMAIN spec_pool' = Server

RoleDomainOK ==
    ~("role" \in DOMAIN logline) \/ DOMAIN role' = Server

TermNondecreasing ==
    ~("term" \in DOMAIN logline) \/ term' >= term

RoleLeaderConsistent ==
    IF "role" \in DOMAIN logline
    THEN
        LET roleMap == RoleValue(logline)
            leaderId == LeaderValue(logline)
            leaders == {i \in DOMAIN roleMap: roleMap[i] = "Leader"}
        IN
            /\ leaderId \in DOMAIN roleMap
            /\ roleMap[leaderId] = "Leader"
            /\ Cardinality(leaders) = 1
    ELSE TRUE

StepToNextTrace ==
    /\ l' = l + 1
    /\ l % ProgressStride = 0 => PrintT(<< "Progress %:", (l * 100) \div Len(TraceLog)>>)
    /\ l' > Len(TraceLog) => PrintT(<< "Progress %:", 100>>)

ApplyLoglineUpdates ==
    /\ leader' = IF "leader" \in DOMAIN logline THEN LeaderValue(logline) ELSE leader
    /\ role' = IF "role" \in DOMAIN logline THEN RoleValue(logline) ELSE role
    /\ term' = IF "term" \in DOMAIN logline THEN TermValue(logline) ELSE term
    /\ spec_pool' = IF HasSpecPool(logline) THEN SpecPoolValue(logline) ELSE spec_pool
    /\ uncommitted_pool' =
        IF HasUncommitted(logline) THEN UncommittedValue(logline) ELSE uncommitted_pool
    /\ committed_commands' =
        IF HasCommitted(logline) THEN CommittedValue(logline) ELSE committed_commands

LoglineIsEvent(e) ==
    /\ l <= Len(TraceLog)
    /\ logline.event = e

LeaderChangeLogged ==
    /\ LoglineIsEvent("LeaderChange")
    /\ ApplyLoglineUpdates
    /\ SpecPoolDomainOK
    /\ RoleDomainOK
    /\ RoleLeaderConsistent
    /\ TermNondecreasing
    /\ StepToNextTrace

ProposeLogged ==
    /\ LoglineIsEvent("Propose")
    /\ ApplyLoglineUpdates
    /\ SpecPoolDomainOK
    /\ RoleDomainOK
    /\ RoleLeaderConsistent
    /\ TermNondecreasing
    /\ (~HasSpecPool(logline) \/ spec_pool' = spec_pool \/ SpecPoolInsertAll)
    /\ (~HasUncommitted(logline) \/ uncommitted_pool' = uncommitted_pool)
    /\ (~HasCommitted(logline) \/ committed_commands' = committed_commands)
    /\ StepToNextTrace

ProcessProposeNonLeaderLogged ==
    /\ LoglineIsEvent("ProcessProposeNonLeader")
    /\ ApplyLoglineUpdates
    /\ SpecPoolDomainOK
    /\ RoleDomainOK
    /\ RoleLeaderConsistent
    /\ TermNondecreasing
    /\ (~HasSpecPool(logline) \/ spec_pool' = spec_pool \/ SpecPoolInsertOne)
    /\ (~HasUncommitted(logline) \/ uncommitted_pool' = uncommitted_pool)
    /\ (~HasCommitted(logline) \/ committed_commands' = committed_commands)
    /\ StepToNextTrace

ProcessProposeLeaderLogged ==
    /\ LoglineIsEvent("ProcessProposeLeader")
    /\ ApplyLoglineUpdates
    /\ SpecPoolDomainOK
    /\ RoleDomainOK
    /\ RoleLeaderConsistent
    /\ TermNondecreasing
    /\ (~HasSpecPool(logline) \/ spec_pool' = spec_pool \/ SpecPoolInsertOne)
    /\ (~HasUncommitted(logline) \/ uncommitted_pool' = uncommitted_pool
        \/ UncommittedInsertOne \/ UncommittedReplaceOne)
    /\ (~HasCommitted(logline) \/ committed_commands' = committed_commands)
    /\ StepToNextTrace

CommitLogged ==
    /\ LoglineIsEvent("Commit")
    /\ ApplyLoglineUpdates
    /\ SpecPoolDomainOK
    /\ RoleDomainOK
    /\ RoleLeaderConsistent
    /\ TermNondecreasing
    /\ (~HasSpecPool(logline) \/ spec_pool' = spec_pool)
    /\ (~HasUncommitted(logline) \/ uncommitted_pool' = uncommitted_pool)
    /\ (~HasCommitted(logline) \/ CommittedAppendOne)
    /\ StepToNextTrace

ProcessCommitMsgLogged ==
    /\ LoglineIsEvent("ProcessCommitMsg")
    /\ ApplyLoglineUpdates
    /\ SpecPoolDomainOK
    /\ RoleDomainOK
    /\ RoleLeaderConsistent
    /\ TermNondecreasing
    /\ (~HasSpecPool(logline) \/ spec_pool' = spec_pool \/ SpecPoolRemoveOne)
    /\ (~HasUncommitted(logline) \/ uncommitted_pool' = uncommitted_pool)
    /\ (~HasCommitted(logline) \/ committed_commands' = committed_commands)
    /\ StepToNextTrace

TraceInit ==
    /\ l = 1
    /\ Init

TraceNext ==
    \/ LeaderChangeLogged
    \/ ProposeLogged
    \/ ProcessProposeNonLeaderLogged
    \/ ProcessProposeLeaderLogged
    \/ CommitLogged
    \/ ProcessCommitMsgLogged

TraceSpec ==
    TraceInit /\ [][TraceNext]_<<l, vars>>

TraceView ==
    <<vars, l>>

ASSUME TLCGet("config").worker = 1

TraceMatched ==
    [](l <= Len(TraceLog) => [](TLCGet("queue") = 1 \/ l > Len(TraceLog)))

====
