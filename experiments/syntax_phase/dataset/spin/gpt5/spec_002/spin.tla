---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads /= {}

EventType == {"Acquire", "Release"}
Event == [type: EventType, thr: Threads, epoch: Nat]

PhaseSet == {"idle", "trying", "spinning", "locked"}
ReqSet == {"none", "blocking", "nonblocking"}

VARIABLES lock, phase, req, guards, spinCount, epoch, acqEpoch, relEpoch, events

Vars == << lock, phase, req, guards, spinCount, epoch, acqEpoch, relEpoch, events >>

TypeOK ==
    /\ lock \in BOOLEAN
    /\ phase \in [Threads -> PhaseSet]
    /\ req \in [Threads -> ReqSet]
    /\ guards \in [Threads -> BOOLEAN]
    /\ spinCount \in [Threads -> Nat]
    /\ epoch \in Nat
    /\ acqEpoch \in [Threads -> Nat]
    /\ relEpoch \in [Threads -> Nat]
    /\ events \in Seq(Event)

Init ==
    /\ TypeOK
    /\ lock = FALSE
    /\ phase = [t \in Threads |-> "idle"]
    /\ req = [t \in Threads |-> "none"]
    /\ guards = [t \in Threads |-> FALSE]
    /\ spinCount = [t \in Threads |-> 0]
    /\ epoch = 0
    /\ acqEpoch = [t \in Threads |-> 0]
    /\ relEpoch = [t \in Threads |-> 0]
    /\ events = << >>

StartLock(t) ==
    /\ t \in Threads
    /\ phase[t] = "idle"
    /\ req[t] = "none"
    /\ phase' = [phase EXCEPT ![t] = "trying"]
    /\ req' = [req EXCEPT ![t] = "blocking"]
    /\ UNCHANGED << lock, guards, spinCount, epoch, acqEpoch, relEpoch, events >>

StartTryLock(t) ==
    /\ t \in Threads
    /\ phase[t] = "idle"
    /\ req[t] = "none"
    /\ phase' = [phase EXCEPT ![t] = "trying"]
    /\ req' = [req EXCEPT ![t] = "nonblocking"]
    /\ UNCHANGED << lock, guards, spinCount, epoch, acqEpoch, relEpoch, events >>

CAS_Acquire(t) ==
    /\ t \in Threads
    /\ phase[t] \in {"trying", "spinning"}
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ guards' = [guards EXCEPT ![t] = TRUE]
    /\ phase' = [phase EXCEPT ![t] = "locked"]
    /\ req' = [req EXCEPT ![t] = "none"]
    /\ epoch' = epoch + 1
    /\ acqEpoch' = [acqEpoch EXCEPT ![t] = epoch']
    /\ events' = Append(events, [type |-> "Acquire", thr |-> t, epoch |-> epoch'])
    /\ UNCHANGED << spinCount, relEpoch >>

CAS_Fail_Blocking(t) ==
    /\ t \in Threads
    /\ phase[t] = "trying"
    /\ req[t] = "blocking"
    /\ lock = TRUE
    /\ phase' = [phase EXCEPT ![t] = "spinning"]
    /\ UNCHANGED << lock, req, guards, spinCount, epoch, acqEpoch, relEpoch, events >>

CAS_Fail_NonBlocking(t) ==
    /\ t \in Threads
    /\ phase[t] = "trying"
    /\ req[t] = "nonblocking"
    /\ lock = TRUE
    /\ phase' = [phase EXCEPT ![t] = "idle"]
    /\ req' = [req EXCEPT ![t] = "none"]
    /\ UNCHANGED << lock, guards, spinCount, epoch, acqEpoch, relEpoch, events >>

SpinLoop(t) ==
    /\ t \in Threads
    /\ req[t] = "blocking"
    /\ phase[t] = "spinning"
    /\ spinCount' = [spinCount EXCEPT ![t] = @ + 1]
    /\ UNCHANGED << lock, req, guards, phase, epoch, acqEpoch, relEpoch, events >>

Unlock(t) ==
    /\ t \in Threads
    /\ phase[t] = "locked"
    /\ guards[t] = TRUE
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ guards' = [guards EXCEPT ![t] = FALSE]
    /\ phase' = [phase EXCEPT ![t] = "idle"]
    /\ epoch' = epoch + 1
    /\ relEpoch' = [relEpoch EXCEPT ![t] = epoch']
    /\ events' = Append(events, [type |-> "Release", thr |-> t, epoch |-> epoch'])
    /\ UNCHANGED << req, spinCount, acqEpoch >>

Next ==
    \E t \in Threads :
        StartLock(t)
        \/ StartTryLock(t)
        \/ CAS_Acquire(t)
        \/ CAS_Fail_Blocking(t)
        \/ CAS_Fail_NonBlocking(t)
        \/ SpinLoop(t)
        \/ Unlock(t)

Spec ==
    Init /\ [][Next]_Vars
    /\ \A t \in Threads : WF_Vars(CAS_Acquire(t))
    /\ \A t \in Threads : WF_Vars(Unlock(t))
    /\ \A t \in Threads : WF_Vars(CAS_Fail_Blocking(t))

====