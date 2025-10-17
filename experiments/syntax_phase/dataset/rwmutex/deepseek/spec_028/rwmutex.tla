---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANT Threads, NULL

(* State representation matching Rust AtomicUsize bit fields *)
VARIABLES 
    lock_state,      \* [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    wait_queue,      \* Sequence of waiting threads with their operation type
    active_threads   \* Set of threads currently holding locks with their type

vars == <<lock_state, wait_queue, active_threads>>

TypeOK == 
    /\ lock_state \in [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    /\ wait_queue \in Seq([type: {"read", "write", "upread"}, thread: Threads])
    /\ active_threads \in SUBSET ([type: {"read", "write", "upread"}, thread: Threads])
    /\ (lock_state.writer => (lock_state.reader_count = 0 /\ ~lock_state.being_upgraded))
    /\ (lock_state.upreader => ~lock_state.writer)
    /\ (lock_state.being_upgraded => lock_state.upreader)
    /\ \A t \in active_threads: 
        CASE t.type = "read" -> lock_state.reader_count > 0
        [] t.type = "write" -> lock_state.writer
        [] t.type = "upread" -> lock_state.upreader

Init == 
    /\ lock_state = [writer |-> FALSE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ wait_queue = <<>>
    /\ active_threads = {}

CanAcquireRead == 
    ~lock_state.writer /\ ~lock_state.being_upgraded

CanAcquireWrite == 
    lock_state.writer = FALSE /\ lock_state.upreader = FALSE /\ lock_state.being_upgraded = FALSE /\ lock_state.reader_count = 0

CanAcquireUpread ==
    ~lock_state.writer /\ ~lock_state.upreader

AcquireRead(thread) ==
    /\ thread \in Threads
    /\ ~(\E t \in active_threads: t.thread = thread)
    /\ IF CanAcquireRead THEN
        /\ lock_state' = [lock_state EXCEPT !.reader_count = lock_state.reader_count + 1]
        /\ active_threads' = active_threads \union {[type |-> "read", thread |-> thread]}
        /\ wait_queue' = wait_queue
    ELSE
        /\ wait_queue' = Append(wait_queue, [type |-> "read", thread |-> thread])
        /\ UNCHANGED <<lock_state, active_threads>>

AcquireWrite(thread) ==
    /\ thread \in Threads
    /\ ~(\E t \in active_threads: t.thread = thread)
    /\ IF CanAcquireWrite THEN
        /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
        /\ active_threads' = active_threads \union {[type |-> "write", thread |-> thread]}
        /\ wait_queue' = wait_queue
    ELSE
        /\ wait_queue' = Append(wait_queue, [type |-> "write", thread |-> thread])
        /\ UNCHANGED <<lock_state, active_threads>>

AcquireUpread(thread) ==
    /\ thread \in Threads
    /\ ~(\E t \in active_threads: t.thread = thread)
    /\ IF CanAcquireUpread THEN
        /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
        /\ active_threads' = active_threads \union {[type |-> "upread", thread |-> thread]}
        /\ wait_queue' = wait_queue
    ELSE
        /\ wait_queue' = Append(wait_queue, [type |-> "upread", thread |-> thread])
        /\ UNCHANGED <<lock_state, active_threads>>

ReleaseRead(thread) ==
    /\ \E t \in active_threads: t.thread = thread /\ t.type = "read"
    /\ LET new_reader_count == lock_state.reader_count - 1 IN
       LET new_lock_state == [lock_state EXCEPT !.reader_count = new_reader_count] IN
       LET new_active_threads == active_threads \ {[type |-> "read", thread |-> thread]} IN
       /\ IF new_reader_count = 0 THEN  \* Last reader releasing
            /\ IF wait_queue /= <<>> THEN
                LET head == Head(wait_queue) IN
                IF head.type = "read" /\ 
                   [new_lock_state EXCEPT !.reader_count = new_reader_count + 1] \in 
                   [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat] THEN
                    /\ lock_state' = [new_lock_state EXCEPT !.reader_count = new_reader_count + 1]
                    /\ active_threads' = new_active_threads \union {head}
                    /\ wait_queue' = Tail(wait_queue)
                ELSE
                    /\ wait_queue' = wait_queue  \* wake_one semantics: only wake if head can acquire
                    /\ lock_state' = new_lock_state
                    /\ active_threads' = new_active_threads
            ELSE
                /\ wait_queue' = wait_queue
                /\ lock_state' = new_lock_state
                /\ active_threads' = new_active_threads
       ELSE
            /\ wait_queue' = wait_queue
            /\ lock_state' = new_lock_state
            /\ active_threads' = new_active_threads

ReleaseWrite(thread) ==
    /\ \E t \in active_threads: t.thread = thread /\ t.type = "write"
    /\ LET new_lock_state == [lock_state EXCEPT !.writer = FALSE] IN
       LET new_active_threads == active_threads \ {[type |-> "write", thread |-> thread]} IN
       /\ IF wait_queue /= <<>> THEN
            LET head == Head(wait_queue) IN
            IF head.type = "read" /\ ~new_lock_state.writer /\ ~new_lock_state.being_upgraded THEN
                /\ lock_state' = [new_lock_state EXCEPT !.reader_count = new_lock_state.reader_count + 1]
                /\ active_threads' = new_active_threads \union {head}
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF head.type = "write" /\ new_lock_state.writer = FALSE /\ new_lock_state.upreader = FALSE /\ new_lock_state.being_upgraded = FALSE /\ new_lock_state.reader_count = 0 THEN
                /\ lock_state' = [new_lock_state EXCEPT !.writer = TRUE]
                /\ active_threads' = new_active_threads \union {head}
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF head.type = "upread" /\ ~new_lock_state.writer /\ ~new_lock_state.upreader THEN
                /\ lock_state' = [new_lock_state EXCEPT !.upreader = TRUE]
                /\ active_threads' = new_active_threads \union {head}
                /\ wait_queue' = Tail(wait_queue)
            ELSE
                /\ wait_queue' = wait_queue
                /\ lock_state' = new_lock_state
                /\ active_threads' = new_active_threads
       ELSE
            /\ wait_queue' = wait_queue
            /\ lock_state' = new_lock_state
            /\ active_threads' = new_active_threads

ReleaseUpread(thread) ==
    /\ \E t \in active_threads: t.thread = thread /\ t.type = "upread"
    /\ LET new_lock_state == [lock_state EXCEPT !.upreader = FALSE] IN
       LET new_active_threads == active_threads \ {[type |-> "upread", thread |-> thread]} IN
       /\ IF wait_queue /= <<>> THEN
            LET head == Head(wait_queue) IN
            IF head.type = "read" /\ ~new_lock_state.writer /\ ~new_lock_state.being_upgraded THEN
                /\ lock_state' = [new_lock_state EXCEPT !.reader_count = new_lock_state.reader_count + 1]
                /\ active_threads' = new_active_threads \union {head}
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF head.type = "write" /\ new_lock_state.writer = FALSE /\ new_lock_state.upreader = FALSE /\ new_lock_state.being_upgraded = FALSE /\ new_lock_state.reader_count = 0 THEN
                /\ lock_state' = [new_lock_state EXCEPT !.writer = TRUE]
                /\ active_threads' = new_active_threads \union {head}
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF head.type = "upread" /\ ~new_lock_state.writer /\ ~new_lock_state.upreader THEN
                /\ lock_state' = [new_lock_state EXCEPT !.upreader = TRUE]
                /\ active_threads' = new_active_threads \union {head}
                /\ wait_queue' = Tail(wait_queue)
            ELSE
                /\ wait_queue' = wait_queue
                /\ lock_state' = new_lock_state
                /\ active_threads' = new_active_threads
       ELSE
            /\ wait_queue' = wait_queue
            /\ lock_state' = new_lock_state
            /\ active_threads' = new_active_threads

StartUpgrade(thread) ==
    /\ \E t \in active_threads: t.thread = thread /\ t.type = "upread"
    /\ ~lock_state.being_upgraded
    /\ lock_state' = [lock_state EXCEPT !.being_upgraded = TRUE]
    /\ UNCHANGED <<wait_queue, active_threads>>

FinishUpgrade(thread) ==
    /\ \E t \in active_threads: t.thread = thread /\ t.type = "upread"  
    /\ lock_state.being_upgraded
    /\ lock_state.reader_count = 0
    /\ lock_state' = [writer |-> TRUE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ active_threads' = (active_threads \ {[type |-> "upread", thread |-> thread]}) \union {[type |-> "write", thread |-> thread]}
    /\ UNCHANGED <<wait_queue>>

Downgrade(thread) ==
    /\ \E t \in active_threads: t.thread = thread /\ t.type = "write"
    /\ lock_state' = [writer |-> FALSE, upreader |-> TRUE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ active_threads' = (active_threads \ {[type |-> "write", thread |-> thread]}) \union {[type |-> "upread", thread |-> thread]}
    /\ UNCHANGED <<wait_queue>>

Next == 
    \/ \E thread \in Threads: AcquireRead(thread)
    \/ \E thread \in Threads: AcquireWrite(thread) 
    \/ \E thread \in Threads: AcquireUpread(thread)
    \/ \E thread \in Threads: ReleaseRead(thread)
    \/ \E thread \in Threads: ReleaseWrite(thread)
    \/ \E thread \in Threads: ReleaseUpread(thread)
    \/ \E thread \in Threads: StartUpgrade(thread)
    \/ \E thread \in Threads: FinishUpgrade(thread)
    \/ \E thread \in Threads: Downgrade(thread)

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

====