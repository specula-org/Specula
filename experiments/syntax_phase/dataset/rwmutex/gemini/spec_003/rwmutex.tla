---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads
ASSUME Threads = 1..2

Noone == "Noone"
ThreadOrNoone == Threads \cup {Noone}
ReqType == {"read", "write", "upread"}
Waiter == [id: Threads, req: ReqType]

VARIABLES
    readers,
    writer,
    upgradable,
    upgrading,
    wait_queue,
    active_waiters

vars == <<readers, writer, upgradable, upgrading, wait_queue, active_waiters>>

TypeOK ==
    /\ readers \subseteq Threads
    /\ writer \in ThreadOrNoone
    /\ upgradable \in ThreadOrNoone
    /\ upgrading \in BOOLEAN
    /\ wait_queue \in Seq(Waiter)
    /\ active_waiters \subseteq Waiter

Init ==
    /\ readers = {}
    /\ writer = Noone
    /\ upgradable = Noone
    /\ upgrading = FALSE
    /\ wait_queue = <<>>
    /\ active_waiters = {}

IsIdle(t) ==
    /\ t \notin readers
    /\ t /= writer
    /\ t /= upgradable
    /\ \forall p \in active_waiters: p.id /= t
    /\ \forall i \in DOMAIN wait_queue: wait_queue[i].id /= t

Request(t, req) ==
    /\ IsIdle(t)
    /\ req \in ReqType
    /\ active_waiters' = active_waiters \cup {[id |-> t, req |-> req]}
    /\ UNCHANGED <<readers, writer, upgradable, upgrading, wait_queue>>

CanAcquire(p) ==
    LET req == p.req IN
    CASE req = "read"   -> writer = Noone /\ \lnot upgrading
    []   req = "write"  -> writer = Noone /\ upgradable = Noone /\ Cardinality(readers) = 0
    []   req = "upread" -> writer = Noone /\ upgradable = Noone

AcquireSuccess(p) ==
    /\ p \in active_waiters
    /\ CanAcquire(p)
    /\ LET t == p.id
           req == p.req
    IN
       /\ active_waiters' = active_waiters \ {p}
       /\ UNCHANGED <<wait_queue>>
       /\ (CASE req = "read" ->
                readers' = readers \cup {t}
                /\ UNCHANGED <<writer, upgradable, upgrading>>
           [] req = "write" ->
                writer' = t
                /\ UNCHANGED <<readers, upgradable, upgrading>>
           [] req = "upread" ->
                upgradable' = t
                /\ UNCHANGED <<readers, writer, upgrading>>)

AcquireFail(p) ==
    /\ p \in active_waiters
    /\ \lnot CanAcquire(p)
    /\ wait_queue' = Append(wait_queue, p)
    /\ active_waiters' = active_waiters \ {p}
    /\ UNCHANGED <<readers, writer, upgradable, upgrading>>

Acquire(p) == AcquireSuccess(p) \/ AcquireFail(p)

ReleaseRead(t) ==
    /\ t \in readers
    /\ readers' = readers \ {t}
    /\ (IF Cardinality(readers) = 1 /\ Len(wait_queue) > 0 THEN
           active_waiters' = active_waiters \cup {Head(wait_queue)}
           /\ wait_queue' = Tail(wait_queue)
       ELSE
           UNCHANGED <<active_waiters, wait_queue>>)
    /\ UNCHANGED <<writer, upgradable, upgrading>>

ReleaseWrite(t) ==
    /\ writer = t
    /\ writer' = Noone
    /\ active_waiters' = active_waiters \cup SeqToSet(wait_queue)
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<readers, upgradable, upgrading>>

ReleaseUpgradable(t) ==
    /\ upgradable = t
    /\ upgradable' = Noone
    /\ upgrading' = FALSE
    /\ active_waiters' = active_waiters \cup SeqToSet(wait_queue)
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<readers, writer>>

StartUpgrade(t) ==
    /\ upgradable = t
    /\ \lnot upgrading
    /\ upgrading' = TRUE
    /\ UNCHANGED <<readers, writer, upgradable, wait_queue, active_waiters>>

CompleteUpgrade(t) ==
    /\ upgradable = t
    /\ upgrading
    /\ Cardinality(readers) = 0
    /\ writer' = t
    /\ upgradable' = Noone
    /\ upgrading' = FALSE
    /\ UNCHANGED <<readers, wait_queue, active_waiters>>

Downgrade(t) ==
    /\ writer = t
    /\ writer' = Noone
    /\ upgradable' = t
    /\ UNCHANGED <<readers, upgrading, wait_queue, active_waiters>>

Next ==
    \/ \E t \in Threads, req \in ReqType: Request(t, req)
    \/ \E p \in active_waiters: Acquire(p)
    \/ \E t \in readers: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpgradable(t)
    \/ \E t \in Threads: StartUpgrade(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====