---- MODULE Trace ----
(***************************************************************************)
(* Trace validation spec for DPDK rte_ring.                                *)
(* Replays NDJSON traces from instrumented rte_ring against the base spec. *)
(***************************************************************************)

EXTENDS base, Json, IOUtils, Sequences, TLC

\* ========================================================================
\* Trace Loading
\* ========================================================================

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
    ELSE "../traces/trace.ndjson"

TraceLog ==
    ndJsonDeserialize(JsonFile)

\* ========================================================================
\* Cursor variable
\* ========================================================================

VARIABLE l
traceVars == <<l>>

\* ========================================================================
\* Helpers
\* ========================================================================

logline == TraceLog[l]

IsEvent(name) == l <= Len(TraceLog) /\ logline.event = name

\* Map thread ID string from trace to Thread constant
ThreadOf == logline.thread

\* Map mode string from trace to Mode constant
ModeOf(m) ==
    CASE m = "MPMC" -> "MPMC"
      [] m = "HTS"  -> "HTS"
      [] m = "RTS"  -> "RTS"

\* ========================================================================
\* Post-state validation
\* ========================================================================

\* Strong validation: check all ring positions after an action (primed state)
ValidatePostState ==
    /\ prodHead'  = logline.state.prodHead
    /\ prodTail'  = logline.state.prodTail
    /\ consHead'  = logline.state.consHead
    /\ consTail'  = logline.state.consTail

\* Weak validation: check only heads (for async/partial-state traces)
ValidatePostStateWeak ==
    /\ prodHead'  = logline.state.prodHead
    /\ consHead'  = logline.state.consHead

\* ========================================================================
\* Trace Action Wrappers
\* ========================================================================

\* --- ReserveProd: thread reserves producer slots ---
TraceReserveProd ==
    /\ IsEvent("ReserveProd")
    /\ LET t == ThreadOf
           n == logline.n
       IN
       /\ ReserveProd(t)
       /\ reservedN'[t] = n
       /\ ValidatePostStateWeak
    /\ l' = l + 1

\* --- ReserveCons: thread reserves consumer slots ---
TraceReserveCons ==
    /\ IsEvent("ReserveCons")
    /\ LET t == ThreadOf
           n == logline.n
       IN
       /\ ReserveCons(t)
       /\ reservedN'[t] = n
       /\ ValidatePostStateWeak
    /\ l' = l + 1

\* --- WriteData: thread copies data to/from ring ---
TraceWriteData ==
    /\ IsEvent("WriteData")
    /\ LET t == ThreadOf
       IN
       /\ WriteData(t)
    /\ l' = l + 1

\* --- PublishTail: thread updates tail ---
TracePublishTail ==
    /\ IsEvent("PublishTail")
    /\ LET t == ThreadOf
       IN
       /\ PublishTail(t)
       /\ ValidatePostState
    /\ l' = l + 1

\* --- PeekStart: thread starts peek operation ---
TracePeekStart ==
    /\ IsEvent("PeekStart")
    /\ LET t == ThreadOf
           n == logline.n
       IN
       /\ PeekStart(t)
       /\ reservedN'[t] = n
       /\ ValidatePostStateWeak
    /\ l' = l + 1

\* --- PeekFinish: thread finishes peek operation ---
TracePeekFinish ==
    /\ IsEvent("PeekFinish")
    /\ LET t == ThreadOf
           n == logline.commitN
       IN
       /\ PeekFinish(t, n)
       /\ ValidatePostState
    /\ l' = l + 1

\* --- Stall: thread stalls between phases ---
TraceStall ==
    /\ IsEvent("Stall")
    /\ LET t == ThreadOf
       IN
       /\ Stall(t)
    /\ l' = l + 1

\* ========================================================================
\* Silent Actions
\* ========================================================================

\* StaleRead can happen between any traced events, but must be constrained
\* to avoid state explosion. Only fire if the next event requires a different
\* visible tail than what the thread currently has.
SilentStaleRead ==
    /\ l <= Len(TraceLog)
    \* Only fire if the next event is a Reserve that needs updated visibility
    /\ logline.event \in {"ReserveProd", "ReserveCons"}
    /\ \E t \in Thread :
        /\ StaleRead(t)
    /\ UNCHANGED traceVars

\* ========================================================================
\* Trace Init and Next
\* ========================================================================

TraceInit ==
    /\ Init
    /\ l = 1
    \* Override initial state from trace if present
    \* (trace event 0 may contain initial ring state)

TraceNext ==
    \/ TraceReserveProd
    \/ TraceReserveCons
    \/ TraceWriteData
    \/ TracePublishTail
    \/ TracePeekStart
    \/ TracePeekFinish
    \/ TraceStall
    \/ SilentStaleRead

TraceSpec == TraceInit /\ [][TraceNext]_<<allVars, traceVars>>

\* ========================================================================
\* Trace completion check
\* ========================================================================

\* Deadlock-based: TLC finds deadlock when l > Len(TraceLog) and no action
\* is enabled. If trace is fully consumed, that's success (not a real deadlock).
TraceFinished == l > Len(TraceLog)

\* Alternatively, as a temporal property (requires fairness):
TraceMatched == <>(l > Len(TraceLog))

====
