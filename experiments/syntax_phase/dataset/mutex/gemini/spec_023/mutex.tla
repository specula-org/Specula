---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Thread, Nil

VARIABLES
    lock_state,
    wait_queue,
    thread_state,
    lock_holder

vars == << lock_state, wait_queue, thread_state, lock_holder >>

ThreadStates == {"idle", "locking", "in_cs", "waiting"}

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ wait_queue \in Seq(Thread)
    /\ thread_state \in [Thread -> ThreadStates]
    /\ lock_holder \in Thread \cup {Nil}
    /\ (lock_state = FALSE) => (lock_holder = Nil)
    /\ (lock_state = TRUE) => (lock_holder \in Thread /\ thread_state[lock_holder] = "in_cs")
    /\ \A t \in Thread: (t \in SeqToSet(wait_queue)) <=> (thread_state[t] = "waiting")

Init ==
    /\ lock_state = FALSE
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Thread |-> "idle"]
    /\ lock_holder = Nil

(* A thread decides to acquire the lock via the blocking lock() method. *)
RequestLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "locking"]
    /\ UNCHANGED << lock_state, wait_queue, lock_holder >>

(* A thread in the "locking" state attempts to acquire the lock.
   This models the core logic of wait_until(), which tries to acquire
   and blocks if it cannot. *)
AttemptAcquire(t) ==
    /\ thread_state[t] = "locking"
    /\ IF lock_state = FALSE
       THEN (* Successfully acquire the lock *)
            /\ lock_state' = TRUE
            /\ lock_holder' = t
            /\ thread_state' = [thread_state EXCEPT ![t] = "in_cs"]
            /\ UNCHANGED <<wait_queue>>
       ELSE (* Fail to acquire, so block and wait *)
            /\ wait_queue' = Append(wait_queue, t)
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock_state, lock_holder>>

(* A thread attempts to acquire the lock via the non-blocking try_lock() method. *)
TryLock(t) ==
    /\ thread_state[t] = "idle"
    /\ IF lock_state = FALSE
       THEN (* Successfully acquire the lock *)
            /\ lock_state' = TRUE
            /\ lock_holder' = t
            /\ thread_state' = [thread_state EXCEPT ![t] = "in_cs"]
            /\ UNCHANGED <<wait_queue>>
       ELSE (* Fail to acquire, remain idle. This is a stuttering step for the mutex. *)
            /\ UNCHANGED vars

(* A thread holding the lock releases it. This corresponds to the MutexGuard being dropped. *)
Unlock(t) ==
    /\ thread_state[t] = "in_cs"
    /\ lock_holder = t
    /\ lock_state' = FALSE
    /\ lock_holder' = Nil
    /\ IF Len(wait_queue) > 0
       THEN (* Wake up the next thread in the FIFO queue *)
            LET woken_thread == Head(wait_queue)
            IN  /\ wait_queue' = Tail(wait_queue)
                /\ thread_state' = [thread_state EXCEPT ![t] = "idle", ![woken_thread] = "locking"]
       ELSE (* No threads are waiting *)
            /\ wait_queue' = wait_queue
            /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]

Next ==
    \E t \in Thread:
        \/ RequestLock(t)
        \/ AttemptAcquire(t)
        \/ TryLock(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====