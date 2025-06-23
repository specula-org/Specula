--------------------------- MODULE specTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, SpinLock, TraceSpec, TVOperators


TraceNil == "null"

(* Extract system configuration from first trace line *)
TraceThreads == ToSet(Trace[1].Threads)

(* Default variable initialization *)
DefaultImpl(varName) ==
    CASE varName = "lock" -> FALSE
     [] varName = "waiting" -> {}
     [] varName = "pc" -> [t \in Threads |-> "idle"]

(* State variable update logic *)
UpdateVariablesImpl(t) ==
    /\ IF "lock" \in DOMAIN t
       THEN lock' = UpdateVariable(lock, "lock", t)
       ELSE TRUE
    /\ IF "waiting" \in DOMAIN t
       THEN waiting' = UpdateVariable(waiting, "waiting", t)
       ELSE TRUE
    /\ IF "pc" \in DOMAIN t
       THEN pc' = UpdateVariable(pc, "pc", t)
       ELSE TRUE

(* Action event matching *)

IsTryAcquire ==
    /\ IsEvent("TryAcquire")
    /\ \E t \in TraceThreads :
        TryAcquire(t)

IsRelease ==
    /\ IsEvent("Release")
    /\ \E t \in TraceThreads :
        Release(t)

(* State transition definition *)
TraceNextImpl ==
    \/ IsTryAcquire
    \/ IsRelease


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\ [][Next \/ ComposedNext]_vars

=============================================================================

