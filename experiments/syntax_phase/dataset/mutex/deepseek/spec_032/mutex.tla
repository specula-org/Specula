---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NULL

VARIABLES lock_state, wait_queue, thread_states, critical_section

TypeOK == 
    /\ lock_state \in BOOLEAN
    /\ wait_queue \in Seq(Threads)
    /\ thread_states \in [Threads -> {"idle", "trying_lock", "trying_trylock", "waiting", "in_cs"}]
    /\ critical_section \in Threads \cup {NULL}

Init == 
    /\ lock_state = FALSE
    /\ wait_queue = <<>>
    /\ thread_states = [t \in Threads |-> "idle"]
    /\ critical_section = NULL

AcquireLock(t) ==
    /\ thread_states[t] \in {"trying_lock", "trying_trylock"}
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_states' = [thread_states EXCEPT ![t] = "in_cs"]
    /\ critical_section' = t
    /\ wait_queue' = wait_queue

TryLockSuccess(t) ==
    /\ thread_states[t] = "trying_trylock"
    /\ AcquireLock(t)

TryLockFail(t) ==
    /\ thread_states[t] = "trying_trylock"
    /\ lock_state = TRUE
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_state, wait_queue, critical_section>>

BlockOnLock(t) ==
    /\ thread_states[t] = "trying_lock"
    /\ lock_state = TRUE
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting"]
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, critical_section>>

Unlock(t) ==
    /\ critical_section = t
    /\ lock_state = TRUE
    /\ IF wait_queue = <<>> THEN
        /\ lock_state' = FALSE
        /\ critical_section' = NULL
        /\ wait_queue' = wait_queue
      ELSE
        /\ LET front_thread == Head(wait_queue)
           IN /\ lock_state' = TRUE
              /\ critical_section' = front_thread
              /\ wait_queue' = Tail(wait_queue)
              /\ thread_states' = [thread_states EXCEPT ![front_thread] = "in_cs"]
      END
    /\ thread_states' = [thread_states' EXCEPT ![t] = "idle"]

StartLock(t) ==
    /\ thread_states[t] = "idle"
    /\ thread_states' = [thread_states EXCEPT ![t] = "trying_lock"]
    /\ UNCHANGED <<lock_state, wait_queue, critical_section>>

StartTryLock(t) ==
    /\ thread_states[t] = "idle"
    /\ thread_states' = [thread_states EXCEPT ![t] = "trying_trylock"]
    /\ UNCHANGED <<lock_state, wait_queue, critical_section>>

Next == 
    \/ \E t \in Threads : StartLock(t)
    \/ \E t \in Threads : StartTryLock(t)
    \/ \E t \in Threads : TryLockSuccess(t)
    \/ \E t \in Threads : TryLockFail(t)
    \/ \E t \in Threads : BlockOnLock(t)
    \/ \E t \in Threads : Unlock(t)

Vars == <<lock_state, wait_queue, thread_states, critical_section>>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====