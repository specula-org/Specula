---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, None

VARIABLES
    lock,
    owner,
    waitQ,
    nextEligible,
    guard

vars == << lock, owner, waitQ, nextEligible, guard >>

ElemSet(s) == { s[i] : i \in DOMAIN s }

CanAcquireImmediately(t) ==
    /\ t \in Threads
    /\ owner = None
    /\ lock = FALSE
    /\ waitQ = << >>

CanAcquireEligible(t) ==
    /\ t \in Threads
    /\ owner = None
    /\ lock = FALSE
    /\ nextEligible = t

TypeOK ==
    /\ lock \in BOOLEAN
    /\ owner \in Threads \cup {None}
    /\ guard \in Threads \cup {None}
    /\ IsSeq(waitQ) /\ ElemSet(waitQ) \subseteq Threads
    /\ nextEligible \in Threads \cup {None}
    /\ None \notin Threads

Init ==
    /\ TypeOK
    /\ lock = FALSE
    /\ owner = None
    /\ guard = None
    /\ waitQ = << >>
    /\ nextEligible = None

TryLockSuccess(t) ==
    /\ t \in Threads
    /\ CanAcquireImmediately(t)
    /\ lock' = TRUE
    /\ owner' = t
    /\ guard' = t
    /\ nextEligible' = None
    /\ waitQ' = waitQ

LockEnqueue(t) ==
    /\ t \in Threads
    /\ t # owner
    /\ ~(t \in ElemSet(waitQ))
    /\ ~CanAcquireImmediately(t)
    /\ ~CanAcquireEligible(t)
    /\ waitQ' = Append(waitQ, t)
    /\ UNCHANGED << lock, owner, nextEligible, guard >>

EligibleAcquire(t) ==
    /\ t \in Threads
    /\ CanAcquireEligible(t)
    /\ lock' = TRUE
    /\ owner' = t
    /\ guard' = t
    /\ nextEligible' = None
    /\ waitQ' = waitQ

UnlockDrop(t) ==
    /\ t \in Threads
    /\ owner = t
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ owner' = None
    /\ guard' = None
    /\ IF Len(waitQ) > 0
       THEN /\ nextEligible' = Head(waitQ)
            /\ waitQ' = Tail(waitQ)
       ELSE /\ nextEligible' = None
            /\ waitQ' = << >>

Next ==
    \/ \E t \in Threads : TryLockSuccess(t)
    \/ \E t \in Threads : LockEnqueue(t)
    \/ \E t \in Threads : EligibleAcquire(t)
    \/ \E t \in Threads : UnlockDrop(t)

Spec ==
    Init
    /\ [][Next]_vars
    /\ \A t \in Threads : SF_vars(EligibleAcquire(t))

====