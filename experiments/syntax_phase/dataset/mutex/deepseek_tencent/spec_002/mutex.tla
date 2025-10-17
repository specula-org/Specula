
---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
ASSUME NULL \notin Threads
VARIABLES lock, holder, queue, state
TypeOK == 
    /\ lock \in BOOLEAN
    /\ holder \in Threads \union {NULL}
    /\ queue \in Seq(Threads)
    /\ state \in [Threads -> {"idle", "waiting", "critical"}]
    /\ (holder = NULL <=> lock = FALSE)
    /\ (lock = TRUE => (holder \in Threads /\ state[holder] = "critical"))
    /\ \A t \in Threads: 
          (state[t] = "critical" => holder = t)
          /\ (state[t] = "waiting" => t \in Range(queue))
          /\ (state[t] = "idle" => (t \notin Range(queue) /\ t \neq holder))
Init == 
    /\ lock = FALSE
    /\ holder = NULL
    /\ queue = << >>
    /\ state = [t \in Threads |-> "idle"]
Lock(t) == 
    /\ state[t] = "idle"
    /\ IF lock = FALSE
       THEN /\ lock' = TRUE
            /\ holder' = t
            /\ state' = [state EXCEPT ![t] = "critical"]
            /\ queue' = queue
       ELSE /\ state' = [state EXCEPT ![t] = "waiting"]
            /\ queue' = Append(queue, t)
            /\ lock' = lock
            /\ holder' = holder
TryLock(t) == 
    /\ state[t] = "idle"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ holder' = t
    /\ state' = [state EXCEPT ![t] = "critical"]
    /\ queue' = queue
Unlock(t) == 
    /\ state[t] = "critical"
    /\ holder = t
    /\ lock' = FALSE
    /\ holder' = NULL
    /\ IF queue = <<>>
       THEN /\ state' = [state EXCEPT ![t] = "idle"]
            /\ queue' = queue
       ELSE /\ LET u == Head(queue) IN
            /\ state' = [state EXCEPT ![t] = "idle", ![u] = "idle"]
            /\ queue' = Tail(queue)
Next == \E t \in Threads: Lock(t) \/ TryLock(t) \/ Unlock(t)
Vars == << lock, holder, queue, state >>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====