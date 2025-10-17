---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREADS

VARIABLES lock, waitQ, guard, mode

ModeSet == {"Idle", "Waiting", "Woken", "Holding"}

InSeq(q, x) == ∃ i ∈ 1..Len(q): q[i] = x

Head(q) == q[1]
Tail(q) == IF Len(q) = 0 THEN <<>> ELSE SubSeq(q, 2, Len(q))

TypeOK ==
    /\ lock \in BOOLEAN
    /\ waitQ \in Seq(THREADS)
    /\ guard \in [THREADS -> BOOLEAN]
    /\ mode \in [THREADS -> ModeSet]

Init ==
    /\ lock = FALSE
    /\ waitQ = <<>>
    /\ guard = [t \in THREADS |-> FALSE]
    /\ mode = [t \in THREADS |-> "Idle"]
    /\ TypeOK

TryLockSuccess(t) ==
    /\ t \in THREADS
    /\ mode[t] \in {"Idle", "Woken"}
    /\ guard[t] = FALSE
    /\ ~InSeq(waitQ, t)
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ guard' = [guard EXCEPT ![t] = TRUE]
    /\ mode' = [mode EXCEPT ![t] = "Holding"]
    /\ waitQ' = waitQ

TryLockFail(t) ==
    /\ t \in THREADS
    /\ mode[t] \in {"Idle", "Woken"}
    /\ guard[t] = FALSE
    /\ lock = TRUE
    /\ UNCHANGED << lock, waitQ, guard, mode >>

LockImmediate(t) ==
    /\ t \in THREADS
    /\ mode[t] = "Idle"
    /\ guard[t] = FALSE
    /\ ~InSeq(waitQ, t)
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ guard' = [guard EXCEPT ![t] = TRUE]
    /\ mode' = [mode EXCEPT ![t] = "Holding"]
    /\ waitQ' = waitQ

EnqueueAndBlock(t) ==
    /\ t \in THREADS
    /\ mode[t] = "Idle"
    /\ guard[t] = FALSE
    /\ lock = TRUE
    /\ ~InSeq(waitQ, t)
    /\ waitQ' = Append(waitQ, t)
    /\ mode' = [mode EXCEPT ![t] = "Waiting"]
    /\ UNCHANGED << lock, guard >>

Unlock(t) ==
    /\ t \in THREADS
    /\ mode[t] = "Holding"
    /\ guard[t] = TRUE
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ guard' = [guard EXCEPT ![t] = FALSE]
    /\ IF Len(waitQ) = 0 THEN
         /\ waitQ' = waitQ
         /\ mode' = [mode EXCEPT ![t] = "Idle"]
       ELSE
         LET u == Head(waitQ) IN
         /\ waitQ' = Tail(waitQ)
         /\ mode' = [mode EXCEPT ![t] = "Idle", ![u] = "Woken"]

Next ==
    \E t \in THREADS:
        TryLockSuccess(t)
      \/ TryLockFail(t)
      \/ LockImmediate(t)
      \/ EnqueueAndBlock(t)
      \/ Unlock(t)

Vars == << lock, waitQ, guard, mode >>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====