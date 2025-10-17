---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANT Proc

VARIABLES lock_state, pc

vars == <<lock_state, pc>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ pc \in [Proc -> {"idle", "locking", "try_locking", "in_cs"}]

Init ==
    /\ lock_state = FALSE
    /\ pc = [p \in Proc |-> "idle"]

(* A process decides to call lock() and will spin until it succeeds. *)
CallLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "locking"]
    /\ UNCHANGED <<lock_state>>

(* A process decides to call try_lock(). *)
CallTryLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "try_locking"]
    /\ UNCHANGED <<lock_state>>

(*
 The core atomic operation: compare_exchange(false, true).
 This action models a successful acquisition for both lock() and try_lock().
 The process obtains the lock and enters the critical section.
*)
Acquire(p) ==
    /\ pc[p] \in {"locking", "try_locking"}
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "in_cs"]

(*
 For a process in the "locking" state (from a lock() call), if the lock
 is already held, it cannot perform the Acquire action. It remains in the
 "locking" state, implicitly modeling the spin_loop. TLA+ handles this
 by not enabling the Acquire(p) action for this process until lock_state
 becomes FALSE.
*)

(*
 A process that called try_lock() finds the lock is already held.
 It gives up and returns to the idle state immediately.
*)
TryLockFail(p) ==
    /\ pc[p] = "try_locking"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lock_state>>

(*
 The process is finished with the critical section. The SpinLockGuard is
 dropped, which atomically releases the lock.
*)
Release(p) ==
    /\ pc[p] = "in_cs"
    /\ lock_state' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next ==
    \E p \in Proc:
        \/ CallLock(p)
        \/ CallTryLock(p)
        \/ Acquire(p)
        \/ TryLockFail(p)
        \/ Release(p)

Spec == Init /\ [][Next]_vars

(* --- Properties --- *)

(*
 MutualExclusion: At most one process can be in the critical section at any time.
 This is the fundamental safety property of a lock.
*)
MutualExclusion ==
    Cardinality({p \in Proc : pc[p] = "in_cs"}) <= 1

(*
 LockStateConsistency: The lock_state variable accurately reflects whether
 a process is in the critical section.
*)
LockStateConsistency ==
    lock_state <=> (Cardinality({p \in Proc : pc[p] = "in_cs"}) = 1)

(*
 Liveness: Under fairness, any process that starts trying to acquire the lock
 via lock() will eventually succeed. This property would fail without a
 fairness assumption, as a process could spin forever while other processes
 acquire and release the lock.
*)
Fairness == \A p \in Proc: WF_vars(Acquire(p)) /\ WF_vars(Release(p))
Liveness == \A p \in Proc: (pc[p] = "locking") ~> (pc[p] = "in_cs")

=============================================================================