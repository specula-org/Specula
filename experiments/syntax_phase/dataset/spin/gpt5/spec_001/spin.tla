---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock, owner, tstate, reqType, result, data, epochV, acqEpoch

Vars == << lock, owner, tstate, reqType, result, data, epochV, acqEpoch >>

States == {"idle", "trying", "spinning", "locked"}
ReqKinds == {"Blocking", "NonBlocking"}
ReqVals == {"None"} \cup ReqKinds
ResVals == {"None", "Success", "Failure"}

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in Threads \cup {"NoOwner"}
  /\ tstate \in [Threads -> States]
  /\ reqType \in [Threads -> ReqVals]
  /\ result \in [Threads -> ResVals]
  /\ data \in Nat
  /\ epochV \in Nat
  /\ acqEpoch \in [Threads -> Nat]

Init ==
  /\ lock = FALSE
  /\ owner = "NoOwner"
  /\ tstate = [t \in Threads |-> "idle"]
  /\ reqType = [t \in Threads |-> "None"]
  /\ result = [t \in Threads |-> "None"]
  /\ data = 0
  /\ epochV = 0
  /\ acqEpoch = [t \in Threads |-> 0]

RequestLockBlocking(t) ==
  /\ tstate[t] = "idle"
  /\ reqType' = [reqType EXCEPT ![t] = "Blocking"]
  /\ tstate' = [tstate EXCEPT ![t] = "trying"]
  /\ UNCHANGED << lock, owner, result, data, epochV, acqEpoch >>

RequestTryLock(t) ==
  /\ tstate[t] = "idle"
  /\ reqType' = [reqType EXCEPT ![t] = "NonBlocking"]
  /\ tstate' = [tstate EXCEPT ![t] = "trying"]
  /\ result' = [result EXCEPT ![t] = "None"]
  /\ UNCHANGED << lock, owner, data, epochV, acqEpoch >>

CASSuccessBlocking(t) ==
  /\ reqType[t] = "Blocking"
  /\ tstate[t] \in {"trying", "spinning"}
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ owner' = t
  /\ tstate' = [tstate EXCEPT ![t] = "locked"]
  /\ reqType' = [reqType EXCEPT ![t] = "None"]
  /\ acqEpoch' = [acqEpoch EXCEPT ![t] = epochV]
  /\ UNCHANGED << result, data, epochV >>

CASSuccessNonBlocking(t) ==
  /\ reqType[t] = "NonBlocking"
  /\ tstate[t] = "trying"
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ owner' = t
  /\ tstate' = [tstate EXCEPT ![t] = "locked"]
  /\ reqType' = [reqType EXCEPT ![t] = "None"]
  /\ result' = [result EXCEPT ![t] = "Success"]
  /\ acqEpoch' = [acqEpoch EXCEPT ![t] = epochV]
  /\ UNCHANGED << data, epochV >>

CASFailBlocking(t) ==
  /\ reqType[t] = "Blocking"
  /\ tstate[t] \in {"trying", "spinning"}
  /\ lock = TRUE
  /\ tstate' = [tstate EXCEPT ![t] = "spinning"]
  /\ UNCHANGED << lock, owner, reqType, result, data, epochV, acqEpoch >>

CASFailNonBlocking(t) ==
  /\ reqType[t] = "NonBlocking"
  /\ tstate[t] = "trying"
  /\ lock = TRUE
  /\ tstate' = [tstate EXCEPT ![t] = "idle"]
  /\ reqType' = [reqType EXCEPT ![t] = "None"]
  /\ result' = [result EXCEPT ![t] = "Failure"]
  /\ UNCHANGED << lock, owner, data, epochV, acqEpoch >>

RetryFromSpin(t) ==
  /\ reqType[t] = "Blocking"
  /\ tstate[t] = "spinning"
  /\ tstate' = [tstate EXCEPT ![t] = "trying"]
  /\ UNCHANGED << lock, owner, reqType, result, data, epochV, acqEpoch >>

SpinStep(t) ==
  /\ reqType[t] = "Blocking"
  /\ tstate[t] = "spinning"
  /\ UNCHANGED Vars

Unlock(t) ==
  /\ owner = t
  /\ tstate[t] = "locked"
  /\ lock = TRUE
  /\ lock' = FALSE
  /\ owner' = "NoOwner"
  /\ tstate' = [tstate EXCEPT ![t] = "idle"]
  /\ epochV' = epochV + 1
  /\ UNCHANGED << reqType, result, data, acqEpoch >>

CritOp(t) ==
  /\ owner = t
  /\ tstate[t] = "locked"
  /\ lock = TRUE
  /\ data' = data + 1
  /\ UNCHANGED << lock, owner, tstate, reqType, result, epochV, acqEpoch >>

Next ==
  \E t \in Threads :
    \/ RequestLockBlocking(t)
    \/ RequestTryLock(t)
    \/ CASSuccessBlocking(t)
    \/ CASSuccessNonBlocking(t)
    \/ CASFailBlocking(t)
    \/ CASFailNonBlocking(t)
    \/ RetryFromSpin(t)
    \/ SpinStep(t)
    \/ Unlock(t)
    \/ CritOp(t)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A t \in Threads : SF_Vars(CASSuccessBlocking(t))
  /\ \A t \in Threads : WF_Vars(Unlock(t))

epoch == epochV <= 2 /\ data <= 3
(<=) == epochV <= 2 /\ data <= 3

====