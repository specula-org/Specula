---- MODULE Tracecurp ----
EXTENDS curp, Json, IOUtils, Sequences, TLC

ASSUME TLCGet("config").mode = "bfs"

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "./trace.ndjson"

OriginTraceLog ==
    SelectSeq(ndJsonDeserialize(JsonFile), LAMBDA l: "event" \in DOMAIN l)

TraceLog ==
    TLCEval(
        IF "MAX_TRACE" \in DOMAIN IOEnv
        THEN SubSeq(OriginTraceLog, 1, atoi(IOEnv.MAX_TRACE))
        ELSE OriginTraceLog)

ProgressStride ==
    IF Len(TraceLog) < 100 THEN 1 ELSE Len(TraceLog) \div 100

VARIABLE l

logline == TraceLog[l]
initline == TraceLog[1]

HasSpecPool ==
    "speculativePool" \in DOMAIN logline \/ "spec_pool" \in DOMAIN logline

HasCommitted ==
    "committedCommands" \in DOMAIN logline

HasCoreFields ==
    /\ "event" \in DOMAIN logline
    /\ "leader" \in DOMAIN logline
    /\ HasSpecPool

ActionIs(a) ==
    logline.event = a

UpdateValueFrom(log, field) ==
    log[field][1].args[1]

FieldValue(log, primary, fallback, default) ==
    IF primary \in DOMAIN log THEN UpdateValueFrom(log, primary)
    ELSE IF fallback \in DOMAIN log THEN UpdateValueFrom(log, fallback)
    ELSE default

TraceLeader == FieldValue(logline, "leader", "leader", "")
TraceCommitted ==
    IF HasCommitted THEN UpdateValueFrom(logline, "committedCommands") ELSE committed
TraceSpecPoolMap == FieldValue(logline, "speculativePool", "spec_pool", {})

PoolFromStringSeq(seq) ==
    {seq[i] : i \in 1..Len(seq)}

PoolFromRecordSeq(seq) ==
    {seq[i].key : i \in 1..Len(seq)}

PoolForServer(m, s, useRecord) ==
    IF s \in DOMAIN m THEN
        IF useRecord THEN PoolFromRecordSeq(m[s]) ELSE PoolFromStringSeq(m[s])
    ELSE {}

TraceSpecPool ==
    [s \in Servers |-> PoolForServer(TraceSpecPoolMap, s, "spec_pool" \in DOMAIN logline)]

InitLeader == UpdateValueFrom(initline, "leader")
InitCommitted ==
    IF "committedCommands" \in DOMAIN initline
    THEN UpdateValueFrom(initline, "committedCommands")
    ELSE <<>>
InitSpecPoolMap == FieldValue(initline, "speculativePool", "spec_pool", {})
InitSpecPool ==
    [s \in Servers |-> PoolForServer(InitSpecPoolMap, s, "spec_pool" \in DOMAIN initline)]

StepToNextTrace ==
    /\ l' = l + 1
    /\ l % ProgressStride = 0 => PrintT(<< "Progress %:", (l * 100) \div Len(TraceLog)>>)
    /\ l' > Len(TraceLog) => PrintT(<< "Progress %:", 100>>)

TraceInit ==
    /\ l = 2
    /\ Init
    /\ leader = InitLeader
    /\ specPool = InitSpecPool
    /\ committed = InitCommitted

LeaderChangeLogged ==
    /\ HasCoreFields
    /\ ActionIs("LeaderChange")
    /\ LET newLeader == TraceLeader IN
        /\ LeaderChange(newLeader)
        /\ specPool' = TraceSpecPool
        /\ IF HasCommitted THEN committed' = TraceCommitted ELSE TRUE
    /\ StepToNextTrace

ProposeLogged ==
    /\ HasCoreFields
    /\ ActionIs("Propose")
    /\ \E c \in Cmds :
        /\ Propose(c)
        /\ specPool' = TraceSpecPool
        /\ IF HasCommitted THEN committed' = TraceCommitted ELSE TRUE
        /\ leader' = TraceLeader
    /\ StepToNextTrace

ProcessProposeLeaderLogged ==
    /\ HasCoreFields
    /\ ActionIs("ProcessProposeLeader")
    /\ (\/ \E c \in Cmds :
            /\ ProcessProposeLeader(c)
            /\ specPool' = TraceSpecPool
            /\ IF HasCommitted THEN committed' = TraceCommitted ELSE TRUE
            /\ leader' = TraceLeader
        \/ /\ TraceSpecPool = specPool
           /\ specPool[leader] = {}
           /\ IF HasCommitted THEN TraceCommitted = committed ELSE TRUE
           /\ TraceLeader = leader
           /\ specPool' = specPool
           /\ committed' = committed
           /\ uncommittedPool' = uncommittedPool
           /\ leader' = TraceLeader)
    /\ StepToNextTrace

ProcessProposeNonLeaderLogged ==
    /\ HasCoreFields
    /\ ActionIs("ProcessProposeNonLeader")
    /\ \E s \in Servers, c \in Cmds :
        /\ ProcessProposeNonLeader(s, c)
        /\ specPool' = TraceSpecPool
        /\ IF HasCommitted THEN committed' = TraceCommitted ELSE TRUE
        /\ leader' = TraceLeader
    /\ StepToNextTrace

CommitLogged ==
    /\ HasCoreFields
    /\ ActionIs("Commit")
    /\ LET targetCommitted == TraceCommitted IN
        /\ IF HasCommitted
            THEN
                /\ Len(targetCommitted) = Len(committed) + 1
                /\ \E c \in Cmds :
                    /\ targetCommitted = Append(committed, c)
                    /\ (\/ /\ Commit(c)
                        \/ /\ c \notin specPool[leader]
                           /\ committed' = targetCommitted
                           /\ uncommittedPool' = [uncommittedPool EXCEPT ![leader] = @ \ {c}])
            ELSE
                /\ \E c \in Cmds :
                    /\ Commit(c)
        /\ specPool' = TraceSpecPool
        /\ leader' = TraceLeader
    /\ StepToNextTrace

ProcessCommitMsgLogged ==
    /\ HasCoreFields
    /\ ActionIs("ProcessCommitMsg")
    /\ \E s \in Servers, c \in Cmds :
        /\ ProcessCommitMsg(s, c)
        /\ specPool' = TraceSpecPool
        /\ IF HasCommitted THEN committed' = TraceCommitted ELSE TRUE
        /\ leader' = TraceLeader
    /\ StepToNextTrace

TraceNext ==
    /\ l <= Len(TraceLog)
    /\ (LeaderChangeLogged \/ ProposeLogged \/ ProcessProposeLeaderLogged \/
        ProcessProposeNonLeaderLogged \/ CommitLogged \/ ProcessCommitMsgLogged)

TraceSpec ==
    TraceInit /\ [][TraceNext]_<<l, vars>>

TraceView ==
    <<vars, l>>

ASSUME TLCGet("config").worker = 1

TraceMatched ==
    [](l <= Len(TraceLog) => [](TLCGet("queue") = 1 \/ l > Len(TraceLog)))

====
