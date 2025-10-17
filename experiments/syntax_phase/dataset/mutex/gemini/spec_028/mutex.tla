---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Thread
ASSUME Thread \subseteq STRING

VARIABLES
    \* @type: Str -> Str;
    pc,
    \* @type: Bool;
    lock,
    \* @type: Str;
    holder,
    \* @type: Seq(Str);
    queue

Nil == "Nil"
ASSUME Nil \notin Thread

Vars == << pc, lock, holder, queue >>

TypeOK ==
    /\ pc \in [Thread -> {"idle", "req_lock", "req_try_lock", "waiting", "in_cs", "req_unlock"}]
    /\ lock \in BOOLEAN
    /\ holder \in Thread \cup {Nil}
    /\ queue \in Seq(Thread)

Init ==
    /\ pc = [t \in Thread |-> "idle"]
    /\ lock = FALSE
    /\ holder = Nil
    /\ queue = <<>>

\* A thread decides it wants to acquire the lock via the blocking lock() method.
RequestLock(self) ==
    /\ pc[self] = "idle"
    /\ pc' = [pc EXCEPT ![self] = "req_lock"]
    /\ UNCHANGED << lock, holder, queue >>

\* A thread decides it wants to acquire the lock via the non-blocking try_lock() method.
RequestTryLock(self) ==
    /\ pc[self] = "idle"
    /\ pc' = [pc EXCEPT ![self] = "req_try_lock"]
    /\ UNCHANGED << lock, holder, queue >>

\* A thread attempts to acquire the lock. This corresponds to the compare_exchange.
\* If it succeeds, it enters the critical section.
\* If it fails, it enqueues itself and waits.
AttemptLock(self) ==
    /\ pc[self] = "req_lock"
    \/ /\ lock = FALSE
       /\ lock' = TRUE
       /\ holder' = self
       /\ pc' = [pc EXCEPT ![self] = "in_cs"]
       /\ UNCHANGED << queue >>
    \/ /\ lock = TRUE
       /\ pc' = [pc EXCEPT ![self] = "waiting"]
       /\ queue' = Append(queue, self)
       /\ UNCHANGED << lock, holder >>

\* A thread attempts to acquire the lock non-blockingly.
\* If it succeeds, it enters the critical section.
\* If it fails, it immediately returns to idle.
AttemptTryLock(self) ==
    /\ pc[self] = "req_try_lock"
    \/ /\ lock = FALSE
       /\ lock' = TRUE
       /\ holder' = self
       /\ pc' = [pc EXCEPT ![self] = "in_cs"]
       /\ UNCHANGED << queue >>
    \/ /\ lock = TRUE
       /\ pc' = [pc EXCEPT ![self] = "idle"]
       /\ UNCHANGED << lock, holder, queue >>

\* The MutexGuard is about to be dropped, so the thread prepares to unlock.
RequestUnlock(self) ==
    /\ pc[self] = "in_cs"
    /\ holder = self
    /\ pc' = [pc EXCEPT ![self] = "req_unlock"]
    /\ UNCHANGED << lock, holder, queue >>

\* The thread releases the lock and wakes one waiting thread if the queue is not empty.
UnlockAndWake(self) ==
    /\ pc[self] = "req_unlock"
    /\ holder = self
    /\ lock' = FALSE
    /\ holder' = Nil
    /\ IF queue = <<>>
       THEN /\ pc' = [pc EXCEPT ![self] = "idle"]
            /\ UNCHANGED << queue >>
       ELSE /\ LET woken_thread == Head(queue)
            IN  /\ queue' = Tail(queue)
                /\ pc' = [pc EXCEPT ![self] = "idle", ![woken_thread] = "req_lock"]

Next ==
    \E self \in Thread:
        \/ RequestLock(self)
        \/ RequestTryLock(self)
        \/ AttemptLock(self)
        \/ AttemptTryLock(self)
        \/ RequestUnlock(self)
        \/ UnlockAndWake(self)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====