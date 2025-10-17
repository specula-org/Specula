---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Thread
ASSUME IsFiniteSet(Thread)

VARIABLES
    lock,
    queue,
    holder,
    pc

Nil == CHOOSE v: v \notin Thread
vars == <<lock, queue, holder, pc>>

TypeOK ==
    /\ lock \in BOOLEAN
    /\ queue \in Seq(Thread)
    /\ holder \in Thread \cup {Nil}
    /\ pc \in [Thread -> {"idle", "req_lock", "waiting", "critical"}]
    /\ (lock = FALSE) => (holder = Nil)
    /\ (lock = TRUE) => (holder \in Thread)
    /\ \A i, j \in DOMAIN queue: (i /= j) => (queue[i] /= queue[j])

Init ==
    /\ lock = FALSE
    /\ queue = <<>>
    /\ holder = Nil
    /\ pc = [t \in Thread |-> "idle"]

(* A thread attempts a non-blocking lock acquisition. *)
TryLock(self) ==
    /\ pc[self] = "idle"
    /\ IF lock = FALSE
       THEN (* Success: acquire lock and move to critical section *)
            /\ lock' = TRUE
            /\ holder' = self
            /\ pc' = [pc EXCEPT ![self] = "critical"]
            /\ UNCHANGED <<queue>>
       ELSE (* Failure: remain idle, does not block *)
            /\ pc' = [pc EXCEPT ![self] = "idle"]
            /\ UNCHANGED <<lock, queue, holder>>

(* A thread initiates a blocking lock request. *)
RequestLock(self) ==
    /\ pc[self] = "idle"
    /\ pc' = [pc EXCEPT ![self] = "req_lock"]
    /\ UNCHANGED <<lock, queue, holder>>

(* A thread with a pending lock request attempts to acquire the lock or waits. *)
(* This models the core logic of `wait_until`. *)
AttemptAcquireOrWait(self) ==
    /\ pc[self] = "req_lock"
    /\ IF lock = FALSE
       THEN (* Success: acquire lock and move to critical section *)
            /\ lock' = TRUE
            /\ holder' = self
            /\ pc' = [pc EXCEPT ![self] = "critical"]
            /\ UNCHANGED <<queue>>
       ELSE (* Failure: enqueue and move to waiting state *)
            /\ pc' = [pc EXCEPT ![self] = "waiting"]
            /\ queue' = Append(queue, self)
            /\ UNCHANGED <<lock, holder>>

(* The thread holding the lock releases it, modeling MutexGuard drop. *)
Unlock(self) ==
    /\ pc[self] = "critical"
    /\ holder = self
    /\ lock' = FALSE
    /\ holder' = Nil
    /\ IF queue = <<>>
       THEN (* No waiting threads, just unlock *)
            /\ pc' = [pc EXCEPT ![self] = "idle"]
            /\ UNCHANGED <<queue>>
       ELSE (* Wake up the next thread in the FIFO queue *)
            /\ LET woken_thread == Head(queue)
            IN  /\ queue' = Tail(queue)
                /\ pc' = [pc EXCEPT ![self] = "idle", ![woken_thread] = "req_lock"]

Next == \E self \in Thread:
            \/ TryLock(self)
            \/ RequestLock(self)
            \/ AttemptAcquireOrWait(self)
            \/ Unlock(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====