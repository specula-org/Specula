---- MODULE Traceringbuffer ----
EXTENDS ringbuffer, Json, IOUtils, Sequences, TLC

ASSUME TLCGet("config").mode = "bfs"

RawJsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "./trace.jsonl"

OriginTraceLog ==
    SelectSeq(ndJsonDeserialize(RawJsonFile), LAMBDA l: "action" \in DOMAIN l)

TraceLog ==
    TLCEval(
        IF "MAX_TRACE" \in DOMAIN IOEnv
        THEN SubSeq(OriginTraceLog, 1, atoi(IOEnv.MAX_TRACE))
        ELSE OriginTraceLog)

ProgressStride ==
    IF Len(TraceLog) < 100 THEN 1 ELSE Len(TraceLog) \div 100

VARIABLE l

logline == TraceLog[l]

HasCoreFields ==
    /\ "rb" \in DOMAIN logline
    /\ "head" \in DOMAIN logline
    /\ "tail" \in DOMAIN logline
    /\ "capacity" \in DOMAIN logline
    /\ "success" \in DOMAIN logline
    /\ "actor" \in DOMAIN logline
    /\ "action" \in DOMAIN logline

SeqMatches ==
    IF "seq" \in DOMAIN logline THEN logline.seq = l - 1 ELSE TRUE

ActionIs(a) ==
    logline.action = a

ActorIs(a) ==
    logline.actor = a

RBMatchesState(rb) ==
    /\ rb \in DOMAIN rbs
    /\ rbs[rb].capacity = logline.capacity

StepToNextTrace ==
    /\ l' = l + 1
    /\ l % ProgressStride = 0 => PrintT(<< "Progress %:", (l * 100) \div Len(TraceLog)>>)
    /\ l' > Len(TraceLog) => PrintT(<< "Progress %:", 100>>)

CreateLogged ==
    /\ HasCoreFields
    /\ SeqMatches
    /\ ActionIs("Create")
    /\ ActorIs("system")
    /\ logline.success = TRUE
    /\ logline.head = 0
    /\ logline.tail = 0
    /\ Create(logline.rb, logline.capacity)
    /\ StepToNextTrace

SplitLogged ==
    /\ HasCoreFields
    /\ SeqMatches
    /\ ActionIs("Split")
    /\ ActorIs("system")
    /\ logline.success = TRUE
    /\ RBMatchesState(logline.rb)
    /\ LET st == rbs[logline.rb] IN
        /\ logline.head = st.head
        /\ logline.tail = st.tail
    /\ Split(logline.rb)
    /\ StepToNextTrace

PushLogged ==
    /\ HasCoreFields
    /\ SeqMatches
    /\ ActionIs("Push")
    /\ ActorIs("producer")
    /\ RBMatchesState(logline.rb)
    /\ IF logline.success
        THEN
            LET st == rbs[logline.rb] IN
                /\ logline.head = st.head
                /\ logline.tail = st.tail + 1
                /\ PushItems(logline.rb, 1)
        ELSE
            LET st == rbs[logline.rb] IN
                /\ logline.head = st.head
                /\ logline.tail = st.tail
                /\ st.tail - st.head = st.capacity
                /\ UNCHANGED rbs
    /\ StepToNextTrace

PushSliceLogged ==
    /\ HasCoreFields
    /\ SeqMatches
    /\ ActionIs("PushSlice")
    /\ ActorIs("producer")
    /\ RBMatchesState(logline.rb)
    /\ IF logline.success
        THEN
            LET st == rbs[logline.rb] IN
                /\ logline.head = st.head
                /\ logline.tail >= st.tail
                /\ IF logline.tail = st.tail
                    THEN UNCHANGED rbs
                    ELSE PushItems(logline.rb, logline.tail - st.tail)
        ELSE
            LET st == rbs[logline.rb] IN
                /\ logline.head = st.head
                /\ logline.tail = st.tail
                /\ UNCHANGED rbs
    /\ StepToNextTrace

PopLogged ==
    /\ HasCoreFields
    /\ SeqMatches
    /\ ActionIs("Pop")
    /\ ActorIs("consumer")
    /\ RBMatchesState(logline.rb)
    /\ IF logline.success
        THEN
            LET st == rbs[logline.rb] IN
                /\ logline.tail = st.tail
                /\ logline.head = st.head + 1
                /\ PopItems(logline.rb, 1)
        ELSE
            LET st == rbs[logline.rb] IN
                /\ logline.head = st.head
                /\ logline.tail = st.tail
                /\ st.tail = st.head
                /\ UNCHANGED rbs
    /\ StepToNextTrace

PopSliceLogged ==
    /\ HasCoreFields
    /\ SeqMatches
    /\ ActionIs("PopSlice")
    /\ ActorIs("consumer")
    /\ RBMatchesState(logline.rb)
    /\ IF logline.success
        THEN
            LET st == rbs[logline.rb] IN
                /\ logline.tail = st.tail
                /\ logline.head >= st.head
                /\ IF logline.head = st.head
                    THEN UNCHANGED rbs
                    ELSE PopItems(logline.rb, logline.head - st.head)
        ELSE
            LET st == rbs[logline.rb] IN
                /\ logline.head = st.head
                /\ logline.tail = st.tail
                /\ UNCHANGED rbs
    /\ StepToNextTrace

TraceInit ==
    /\ l = 1
    /\ Init

TraceNext ==
    /\ l <= Len(TraceLog)
    /\ (CreateLogged \/ SplitLogged \/ PushLogged \/ PushSliceLogged \/ PopLogged \/ PopSliceLogged)

TraceSpec ==
    TraceInit /\ [][TraceNext]_<<l, vars>>

TraceView ==
    <<vars, l>>

ASSUME TLCGet("config").worker = 1

TraceMatched ==
    [](l <= Len(TraceLog) => [](TLCGet("queue") = 1 \/ l > Len(TraceLog)))

====
